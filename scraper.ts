// Parses the development applications at the South Australian The Rural City of Murray Bridge web
// site and places them in a database.
//
// Michael Bone
// 18th August 2018

"use strict";

import * as cheerio from "cheerio";
import * as request from "request-promise-native";
import * as sqlite3 from "sqlite3";
import * as urlparser from "url";
import * as moment from "moment";
import * as pdfjs from "pdfjs-dist";
import * as tesseract from "tesseract.js";
import * as jimp from "jimp";
import * as pngjs2 from "pngjs2";
import * as fs from "fs";

sqlite3.verbose();

const DevelopmentApplicationsUrl = "http://www.murraybridge.sa.gov.au/page.aspx?u=1022";
const CommentUrl = "mailto:council@murraybridge.sa.gov.au";

declare const global: any;
declare const process: any;

// All valid suburb names.

let SuburbNames = null;

// Sets up an sqlite database.

async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text, [on_notice_from] text, [on_notice_to] text)");
            resolve(database);
        });
    });
}

// Inserts a row in the database if it does not already exist.

async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or ignore into [data] values (?, ?, ?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate,
            null,
            null
        ], function(error, row) {
            if (error) {
                console.error(error);
                reject(error);
            } else {
                if (this.changes > 0)
                    console.log(`    Inserted: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\" and description \"${developmentApplication.description}\" into the database.`);
                else
                    console.log(`    Skipped: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\" and description \"${developmentApplication.description}\" because it was already present in the database.`);
                sqlStatement.finalize();  // releases any locks
                resolve(row);
            }
        });
    });
}

// A bounding rectangle.

interface Rectangle {
    x: number,
    y: number,
    width: number,
    height: number
}

// An element (consisting of text and a bounding rectangle) in a PDF document.

interface Element extends Rectangle {
    text: string
}

// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.

function getRowTop(elements: Element[], startElement: Element) {
    let top = Number.MAX_VALUE;
    for (let element of elements)
        if (element.y < startElement.y + startElement.height && element.y + element.height > startElement.y)
            if (element.y < top)
                top = element.y;
    return top;
}

// Constructs a rectangle based on the intersection of the two specified rectangles.

function constructIntersection(rectangle1: Rectangle, rectangle2: Rectangle): Rectangle {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}

// Gets the text to the right in a rectangle, where the rectangle is delineated by the positions in
// which the three specified strings of (case sensitive) text are found.

function getRightText(elements: Element[], topLeftText: string, rightText: string, bottomText: string) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.

    let topLeftElement = elements.find(element => element.text.trim() == topLeftText);
    let rightElement = (rightText === undefined) ? undefined : elements.find(element => element.text.trim() == rightText);
    let bottomElement = (bottomText === undefined) ? undefined: elements.find(element => element.text.trim() == bottomText);
    if (topLeftElement === undefined)
        return undefined;

    let x = topLeftElement.x + topLeftElement.width;
    let y = topLeftElement.y;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);

    let bounds: Rectangle = { x: x, y: y, width: width, height: height };

    // Gather together all elements that are at least 50% within the bounding rectangle.

    let intersectingElements: Element[] = []
    for (let element of elements) {
        let intersectingBounds = constructIntersection(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }

    // Sort the elements by Y co-ordinate and then by X co-ordinate.

    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);

    // Join the elements into a single string.

    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}

// Gets the text downwards in a rectangle, where the rectangle is delineated by the positions in
// which the three specified strings of (case sensitive) text are found.

function getDownText(elements: Element[], topText: string, rightText: string, bottomText: string) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.

    let topElement = elements.find(element => element.text.trim() == topText);
    let rightElement = (rightText === undefined) ? undefined : elements.find(element => element.text.trim() == rightText);
    let bottomElement = (bottomText === undefined) ? undefined: elements.find(element => element.text.trim() == bottomText);
    if (topElement === undefined)
        return undefined;

    let x = topElement.x;
    let y = topElement.y + topElement.height;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);

    let bounds: Rectangle = { x: x, y: y, width: width, height: height };

    // Gather together all elements that are at least 50% within the bounding rectangle.

    let intersectingElements: Element[] = []
    for (let element of elements) {
        let intersectingBounds = constructIntersection(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }

    // Sort the elements by Y co-ordinate and then by X co-ordinate.

    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);

    // Join the elements into a single string.

    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}

// Parses the details from the elements associated with a single development application.

function parseApplicationElements(elements: Element[], informationUrl: string) {
    let applicationNumber = getRightText(elements, "Application No", "Application Date", "Applicants Name");
    let receivedDate = getRightText(elements, "Application Date", "Planning Approval", "Application received");
    let houseNumber = getRightText(elements, "Property House No", "Planning Conditions", "Lot");
    let streetName = getRightText(elements, "Property street", "Planning Conditions", "Property suburb");
    let suburbName = getRightText(elements, "Property suburb", "Planning Conditions", "Title");
    let description = getDownText(elements, "Development Description", "Relevant Authority", undefined);

    let address = "";
    if (houseNumber !== undefined)
        address += houseNumber.trim();
    if (streetName !== undefined)
        address += ((address === "") ? "" : " ") + streetName.trim();
    if (suburbName === undefined || suburbName.trim() === "")
        address = "";  // ignore the application because there is no suburb
    
    // Attempt to add the state and post code to the suburb.

    let suburbNameAndPostCode = SuburbNames[suburbName.trim()];
    if (suburbNameAndPostCode === undefined)
        suburbNameAndPostCode = suburbName.trim();

    address += ((address === "") ? "" : ", ") + suburbNameAndPostCode;
    address = address.trim();

    // A valid application must at least have an application number and an address.

    if (applicationNumber === "" || address === "")
        return undefined;

    let parsedReceivedDate = moment(receivedDate, "D/MM/YYYY", true);  // allows the leading zero of the day to be omitted
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description === "") ? "No description provided" : description),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: parsedReceivedDate.isValid() ? parsedReceivedDate.format("YYYY-MM-DD") : ""
    }
}

// Parses an image (from a PDF file).

async function parseImage(image: any, bounds: Rectangle, scaleFactor: number) {
    // Minimise memory usage.
    
    if (global.gc)
        global.gc();

    // Convert the image data into a format that can be used by jimp.

    let pixelSize = (8 * image.data.length) / (image.width * image.height);
    let jimpImage = null;

    if (pixelSize === 1) {
        // A monochrome image (one bit per pixel).

        jimpImage = new (jimp as any)(image.width, image.height);
        for (let x = 0; x < image.width; x++) {
            for (let y = 0; y < image.height; y++) {
                let index = y * (image.width / 8);
                let bitIndex = x % 8;
                let byteIndex = (x - bitIndex) / 8;
                index += byteIndex;
                let color = null;
                if ((image.data[index] & (128 >> bitIndex)) === 0)
                    color = jimp.rgbaToInt(0, 0, 0, 255);  // black pixel
                else
                    color = jimp.rgbaToInt(255, 255, 255, 255);  // white pixel
                jimpImage.setPixelColor(color, x, y);
            }
        }
    } else {
        // Assume a 24 bit colour image (3 bytes per pixel).

        jimpImage = new (jimp as any)(image.width, image.height);
        for (let x = 0; x < image.width; x++) {
            for (let y = 0; y < image.height; y++) {
                let index = (y * image.width * 3) + (x * 3);
                let color = jimp.rgbaToInt(image.data[index], image.data[index + 1], image.data[index + 2], 255);
                jimpImage.setPixelColor(color, x, y);
            }
        }
    }

    jimpImage.scale(scaleFactor, jimp.RESIZE_BEZIER);
    let imageBuffer = await (new Promise((resolve, reject) => jimpImage.getBuffer(jimp.MIME_PNG, (error, buffer) => resolve(buffer))));
    let result: any = await new Promise((resolve, reject) => { tesseract.recognize(imageBuffer).then(function(result) { resolve(result); }) });

    tesseract.terminate();
    if (global.gc)
        global.gc();

    // Simplify the lines (remove most of the information generated by tesseract.js).

    let lines = [];
    if (result.blocks && result.blocks.length)
        for (let block of result.blocks)
            for (let paragraph of block.paragraphs)
                for (let line of paragraph.lines)
                    lines.push(line.words.map(word => { return { text: word.text, confidence: word.confidence, choices: word.choices.length, bounds: { x: word.bbox.x0 + bounds.x, y: word.bbox.y0 + bounds.y, width: word.bbox.x1 - word.bbox.x0, height: word.bbox.y1 - word.bbox.y0 } }; }));

    console.log(lines);
}

async function parsePdf(url: string) {
    let scaleFactor = 3.0;
    let developmentApplications = [];

    // Read the PDF.

    let buffer = await request({ url: url, encoding: null, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);

    // Parse the PDF.  Each page has the details of multiple applications.

    let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });

    for (let index = 0; index < pdf.numPages; index++) {
        console.log(`Page ${index + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(index + 1);
        let viewportTest = await page.getViewport(1.0);
        let operators = await page.getOperatorList();

        // Find and parse any images in the current PDF page.

        for (let index = 0; index < operators.fnArray.length; index++) {
            if (operators.fnArray[index] !== pdfjs.OPS.paintImageXObject && operators.fnArray[index] !== pdfjs.OPS.paintImageMaskXObject)
                continue;

            // The operator either contains the name of an image or an actual image.

            let image = operators.argsArray[index][0];
            if (typeof image === "string")
                image = page.objs.get(image);  // get the actual image using its name

            // Obtain the transform that applies to the image.

            let transform = (index - 1 >= 0 && operators.fnArray[index - 1] === pdfjs.OPS.transform) ? operators.argsArray[index - 1] : undefined;
            if (transform === undefined) {
                console.log(`Could not find a transform to apply to the image with size ${image.width}×${image.height}.  Any text in the image will be ignored.`);
                continue;
            }

            // Process the image.

            let bounds = {
                x: (transform[4] * image.height) / transform[3],
                y: ((viewportTest.height - transform[5] - transform[3]) * image.height) / transform[3],
                width: image.width,
                height: image.height
            };

            console.log(`Parsing the image at [${Math.round(bounds.x)}, ${Math.round(bounds.y)}] with size ${bounds.width}×${bounds.height}.`);
            let imageDevelopmentApplications = await parseImage(image, bounds, scaleFactor);
            developmentApplications = developmentApplications.concat(imageDevelopmentApplications);
        }

return [];
        
        // Construct a text element for each item from the parsed PDF information.

        let textContent = await page.getTextContent();
        let viewport = await page.getViewport(1.0);
        let elements: Element[] = textContent.items.map(item => {
            let transform = pdfjs.Util.transform(viewport.transform, item.transform, [ 1, 0, 0, -1, 0, 0 ]);
            
            // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
            // exaggerated).  The problem seems to be that the height value is too large in some
            // PDFs.  Provide an alternative, more accurate height value by using a calculation
            // based on the transform matrix.

            let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);
            return { text: item.str, x: transform[4], y: transform[5], width: item.width, height: workaroundHeight };
        })
        
        // Group the elements into sections based on where the "Application No" text starts (and
        // any other element the "Application No" element lines up with horizontally).

        let startElements = elements.filter(element => element.text.trim().startsWith("Application No"));
        let yComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
        startElements.sort(yComparer);

        let applicationElementGroups: Element[][] = [];
        for (let index = 0; index < startElements.length; index++) {
            // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
            // the current page).

            let rowTop = getRowTop(elements, startElements[index]);
            let nextRowTop = (index + 1 < startElements.length) ? getRowTop(elements, startElements[index + 1]) : Number.MAX_VALUE;

            // Extract all elements between the two rows.

            applicationElementGroups.push(elements.filter(element => element.y >= rowTop && element.y + element.height < nextRowTop));
        }

        // Parse the development application from each section.

        for (let applicationElements of applicationElementGroups) {
            let developmentApplication = parseApplicationElements(applicationElements, url);
            if (developmentApplication !== undefined)
                developmentApplications.push(developmentApplication);
        }
    }
    
    return developmentApplications;
}

// Gets a random integer in the specified range: [minimum, maximum).

function getRandom(minimum: number, maximum: number) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}

// Pauses for the specified number of milliseconds.

function sleep(milliseconds) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}

// Parses the development applications.

async function main() {
    // Ensure that the database exists.

    let database = await initializeDatabase();
    
    // Read the files containing all possible suburb names.

    SuburbNames = {};
    for (let suburb of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n"))
        SuburbNames[suburb.split(",")[0]] = suburb.split(",")[1];

    // Retrieve the page that contains the links to the PDFs.

    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);

    let body = await request({ url: DevelopmentApplicationsUrl, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);
    
    let pdfUrls: string[] = [];
    for (let element of $("td.uContentListDesc a[href$='.pdf']").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl);
        pdfUrl.protocol = "http";  // force to use HTTP instead of HTTPS
        if (!pdfUrls.some(url => url === pdfUrl.href))  // avoid duplicates
            pdfUrls.push(pdfUrl.href);
    }

    if (pdfUrls.length === 0) {
        console.log("No PDF URLs were found on the page.");
        return;
    }

    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).

    let selectedPdfUrls: string[] = [];
    selectedPdfUrls.push(pdfUrls.shift());
    if (pdfUrls.length > 0)
        selectedPdfUrls.push(pdfUrls[getRandom(1, pdfUrls.length)]);
    if (getRandom(0, 2) === 0)
        selectedPdfUrls.reverse();

selectedPdfUrls = [ "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20July%202018.pdf", "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20February%202017.pdf" ];

    for (let pdfUrl of selectedPdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl);
        console.log(`Parsed ${developmentApplications.length} development application(s) from document: ${pdfUrl}`);

        // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
        // current process being terminated by morph.io).

        if (global.gc)
            global.gc();

//        for (let developmentApplication of developmentApplications)
//            await insertRow(database, developmentApplication);
    }
}

main().then(() => console.log("Complete.")).catch(error => console.error(error));
