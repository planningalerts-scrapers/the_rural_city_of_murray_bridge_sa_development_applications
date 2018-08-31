// Parses the development applications at the South Australian The Rural City of Murray Bridge web
// site and places them in a database.
//
// Michael Bone
// 18th August 2018
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const cheerio = require("cheerio");
const request = require("request-promise-native");
const sqlite3 = require("sqlite3");
const urlparser = require("url");
const moment = require("moment");
const pdfjs = require("pdfjs-dist");
const tesseract = require("tesseract.js");
const jimp = require("jimp");
const didyoumean = require("didyoumean2");
const fs = require("fs");
sqlite3.verbose();
const DevelopmentApplicationsUrl = "http://www.murraybridge.sa.gov.au/page.aspx?u=1022";
const CommentUrl = "mailto:council@murraybridge.sa.gov.au";
// All valid street and suburb names.
let SuburbNames = null;
let StreetSuffixes = null;
let StreetNames = null;
// Sets up an sqlite database.
async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text)");
            resolve(database);
        });
    });
}
// Inserts a row in the database if it does not already exist.
async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or ignore into [data] values (?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate
        ], function (error, row) {
            if (error) {
                console.error(error);
                reject(error);
            }
            else {
                if (this.changes > 0)
                    console.log(`    Inserted: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\" and description \"${developmentApplication.description}\" into the database.`);
                else
                    console.log(`    Skipped: application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\" and description \"${developmentApplication.description}\" because it was already present in the database.`);
                sqlStatement.finalize(); // releases any locks
                resolve(row);
            }
        });
    });
}
// Returns the text of the element with all whitespace removed, changed to lowercase and some
// punctuation removed (for example, the full stop from "Dev App No.").
function condenseText(element) {
    if (element === undefined || element.text === undefined)
        return undefined;
    return element.text.trim().replace(/[\s.,]/g, "").toLowerCase();
}
// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.
function getRowTop(elements, startElement) {
    let top = Number.MAX_VALUE;
    for (let element of elements)
        if (element.y < startElement.y + startElement.height && element.y + element.height > startElement.y)
            if (element.y < top)
                top = element.y;
    return top;
}
// Constructs a rectangle based on the intersection of the two specified rectangles.
function constructIntersection(rectangle1, rectangle2) {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}
// Constructs a rectangle based on the union of the two specified rectangles.
function constructUnion(rectangle1, rectangle2) {
    let x1 = Math.min(rectangle1.x, rectangle2.x);
    let x2 = Math.max(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y1 = Math.min(rectangle1.y, rectangle2.y);
    let y2 = Math.max(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
}
// Calculates the area of a rectangle.
function getArea(rectangle) {
    return rectangle.width * rectangle.height;
}
// Calculates the square of the Euclidean distance between two elements.
function calculateDistance(element1, element2) {
    let point1 = { x: element1.x + element1.width, y: element1.y + element1.height / 2 };
    let point2 = { x: element2.x, y: element2.y + element2.height / 2 };
    if (point2.x < point1.x - element1.width / 5) // arbitrary overlap factor of 20%
        return Number.MAX_VALUE;
    return (point2.x - point1.x) * (point2.x - point1.x) + (point2.y - point1.y) * (point2.y - point1.y);
}
// Determines whether there is vertical overlap between two elements.
function isVerticalOverlap(element1, element2) {
    return element2.y < element1.y + element1.height && element2.y + element2.height > element1.y;
}
// Gets the percentage of vertical overlap between two elements (0 means no overlap and 100 means
// 100% overlap; and, for example, 20 means that 20% of the second element overlaps somewhere
// with the first element).
function getVerticalOverlapPercentage(element1, element2) {
    let y1 = Math.max(element1.y, element2.y);
    let y2 = Math.min(element1.y + element1.height, element2.y + element2.height);
    return (y2 < y1) ? 0 : (((y2 - y1) * 100) / element2.height);
}
// Gets the element immediately to the right of the specified element.
function getRightElement(elements, element) {
    let closestElement = { text: undefined, x: Number.MAX_VALUE, y: Number.MAX_VALUE, width: 0, height: 0 };
    for (let rightElement of elements)
        if (isVerticalOverlap(element, rightElement) && calculateDistance(element, rightElement) < calculateDistance(element, closestElement))
            closestElement = rightElement;
    return (closestElement.text === undefined) ? undefined : closestElement;
}
// Gets the text to the right of the specified startElement up to the left hand side of the
// specified middleElement (adjusted left by 20% of the width of the middleElement as a safety
// precaution).  Only elements that overlap 50% or more in the vertical direction with the
// specified startElement are considered (ie. elements on the same "row").
function getRightRowText(elements, startElement, middleElement) {
    let rowElements = elements.filter(element => element.x > startElement.x + startElement.width &&
        element.x < middleElement.x - 0.2 * middleElement.width &&
        getVerticalOverlapPercentage(element, startElement) > 50);
    // Sort and then join the elements into a single string.
    let xComparer = (a, b) => (a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0);
    rowElements.sort(xComparer);
    return rowElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}
// Gets the text to the right in a rectangle, where the rectangle is delineated by the positions in
// which the three specified strings of (case sensitive) text are found.
function getRightText(elements, topLeftText, rightText, bottomText) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.
    let topLeftElement = elements.find(element => element.text.trim() == topLeftText);
    let rightElement = (rightText === undefined) ? undefined : elements.find(element => element.text.trim() == rightText);
    let bottomElement = (bottomText === undefined) ? undefined : elements.find(element => element.text.trim() == bottomText);
    if (topLeftElement === undefined)
        return undefined;
    let x = topLeftElement.x + topLeftElement.width;
    let y = topLeftElement.y;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);
    let bounds = { x: x, y: y, width: width, height: height };
    // Gather together all elements that are at least 50% within the bounding rectangle.
    let intersectingElements = [];
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
// Reads all the address information into global objects.
function readAddressInformation() {
    StreetNames = {};
    for (let line of fs.readFileSync("streetnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetNameTokens = line.split(",");
        let streetName = streetNameTokens[0].trim();
        let suburbName = streetNameTokens[1].trim();
        if (StreetNames[streetName] === undefined)
            StreetNames[streetName] = [];
        StreetNames[streetName].push(suburbName); // several suburbs may exist for the same street name
    }
    StreetSuffixes = {};
    for (let line of fs.readFileSync("streetsuffixes.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetSuffixTokens = line.split(",");
        StreetSuffixes[streetSuffixTokens[0].trim().toLowerCase()] = streetSuffixTokens[1].trim();
    }
    SuburbNames = {};
    for (let line of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let suburbTokens = line.split(",");
        let suburbName = suburbTokens[0].trim().toLowerCase();
        let suburbStateAndPostCode = suburbTokens[1].trim();
        SuburbNames[suburbName] = suburbStateAndPostCode;
    }
}
// Formats (and corrects) an address.
function formatAddress(address) {
    if (address.trim() === "")
        return "";
    let tokens = address.split(" ");
    // It is common for an invalid postcode of "0" to appear on the end of an address.  Remove
    // this if it is present.  For example, "Bremer Range RD CALLINGTON 0".   
    let postCode = tokens[tokens.length - 1];
    if (/^[0-9]{4}$/.test(postCode))
        tokens.pop();
    else if (postCode === "O" || postCode === "0") {
        postCode = "";
        tokens.pop();
    }
    else
        postCode = "";
    // Pop tokens from the end of the array until a valid suburb name is encountered (allowing
    // for a few spelling errors).
    let suburbName = null;
    for (let index = 1; index <= 4; index++) {
        let suburbNameMatch = didyoumean(tokens.slice(-index).join(" "), Object.keys(SuburbNames), { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true });
        if (suburbNameMatch !== null) {
            suburbName = SuburbNames[suburbNameMatch];
            tokens.splice(-index, index); // remove elements from the end of the array           
            break;
        }
    }
    if (suburbName === null) // suburb name not found (or not recognised)
        return tokens.join(" ");
    // Expand an abbreviated street suffix.  For example, expand "RD" to "Road".
    let streetSuffixAbbreviation = tokens.pop() || "";
    let streetSuffix = StreetSuffixes[streetSuffixAbbreviation.toLowerCase()] || streetSuffixAbbreviation;
    // Allow minor spelling corrections in the remaining tokens to construct a street name.
    let streetName = (tokens.join(" ") + " " + streetSuffix).trim();
    let streetSuburbNames = undefined;
    let streetNameMatch = didyoumean(streetName, Object.keys(StreetNames), { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true });
    if (streetNameMatch !== null) {
        streetName = streetNameMatch;
        streetSuburbNames = StreetNames[streetNameMatch];
    }
    console.log(`Address: ${address}`);
    console.log(`  Street Name: ${streetName}`);
    console.log(`  Street Suffix: ${streetSuffix}`);
    console.log(`  Suburb Name: ${suburbName}`);
    console.log(`  Street Suburb Names: ${streetSuburbNames}`);
    console.log(`  Post Code: ${postCode}`);
    return (streetName + ((streetName === "") ? "" : ", ") + suburbName).trim();
}
// Gets the text downwards in a rectangle, where the rectangle is delineated by the positions in
// which the three specified strings of (case sensitive) text are found.
function getDownText(elements, topText, rightText, bottomText) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.
    let topElement = elements.find(element => element.text.trim() == topText);
    let rightElement = (rightText === undefined) ? undefined : elements.find(element => element.text.trim() == rightText);
    let bottomElement = (bottomText === undefined) ? undefined : elements.find(element => element.text.trim() == bottomText);
    if (topElement === undefined)
        return undefined;
    let x = topElement.x;
    let y = topElement.y + topElement.height;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);
    let bounds = { x: x, y: y, width: width, height: height };
    // Gather together all elements that are at least 50% within the bounding rectangle.
    let intersectingElements = [];
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
function parseApplicationElements(elements, startElement, informationUrl) {
    console.log("----------Elements for one Application----------");
    for (let element of elements)
        console.log(`    [${element.text}] (${element.x},${element.y}) ${element.width}×${element.height} confidence=${Math.round(element.confidence)}%`);
    // console.log(`    [${element.text}] (${Math.round(element.x)},${Math.round(element.y)}) ${element.width}×${element.height} confidence=${Math.round((element as any).confidence)}%`);
    console.log("Refactor assessment number logic to a separate function.");
    // Find the "Assessment Number" text (allowing for spelling errors).
    let assessmentNumberElement = elements.find(element => element.y > startElement.y &&
        didyoumean(element.text, ["Assessment Number"], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true }) !== null);
    if (assessmentNumberElement === undefined) {
        // Find any occurrences of the text "Assessment".
        let assessmentElements = elements.filter(element => element.y > startElement.y &&
            didyoumean(element.text, ["Assessment"], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true }) !== null);
        // Check if any of those occurrences of "Assessment" are followed by "Number".
        for (let assessmentElement of assessmentElements) {
            let assessmentRightElement = getRightElement(elements, assessmentElement);
            if (assessmentRightElement !== null && didyoumean(assessmentRightElement.text, ["Number"], { caseSensitive: false, returnType: "first-closest-match", thresholdType: "edit-distance", threshold: 2, trimSpace: true }) !== null) {
                assessmentNumberElement = assessmentElement;
                break;
            }
        }
    }
    if (assessmentNumberElement === undefined) {
        console.log("Could not find the \"Assessment Number\" text on the PDF page for the current development application.  The development application will be ignored.");
        return undefined;
    }
    // Find the "Applicant" text.
    let applicantElement = elements.find(element => element.y > startElement.y && element.text.trim().toLowerCase() === "applicant");
    if (applicantElement === undefined)
        console.log("    Could not find applicantElement.");
    // Find the "Builder" text.
    let builderElement = elements.find(element => element.y > startElement.y && element.text.trim().toLowerCase() === "builder");
    if (builderElement === undefined)
        console.log("    Could not find builderElement.");
    // One of either the applicant or builder elements is required in order to determine where
    // the description text starts on the X axis (and where the development application number
    // and address end on the X axis).
    let middleElement = (applicantElement === undefined) ? builderElement : applicantElement;
    if (middleElement === undefined) {
        console.log("Could not find the \"Applicant\" or \"Builder\" text on the PDF page for the current development application.  The development application will be ignored.");
        return undefined;
    }
    let applicationNumber = getRightRowText(elements, startElement, middleElement).trim().replace(/\s/g, "");
    applicationNumber = applicationNumber.replace(/[IlL\[\]\|]/g, "/"); // for example, converts "17I2017" to "17/2017"
    if (applicationNumber === "") {
        console.log("Could not find the application number on the PDF page for the current development application.  The development application will be ignored.");
        return undefined;
    }
    console.log(`Application Number: ${applicationNumber}`);
    console.log("Refactor received date logic to a separate function.");
    // Search to the right of "Dev App No." for the lodged date (including up and down a few
    // "lines" from the "Dev App No." text because sometimes the lodged date is offset vertically
    // by a fair amount; in some cases offset up and in other cases offset down).
    let dateElements = elements.filter(element => element.x >= middleElement.x &&
        element.y + element.height > startElement.y - startElement.height &&
        element.y < startElement.y + 2 * startElement.height &&
        moment(element.text.trim(), "D/MM/YYYY", true).isValid());
    // Select the left most date (ie. favour the "lodged" date over the "final descision" date).
    let receivedDate = undefined;
    let receivedDateElement = dateElements.reduce((previous, current) => ((previous === undefined || previous.x > current.x) ? current : previous), undefined);
    if (receivedDateElement !== undefined)
        receivedDate = moment(receivedDateElement.text.trim(), "D/MM/YYYY", true);
    console.log(`Received Date: ${receivedDate.isValid() ? receivedDate.format("YYYY-MM-DD") : ""}`);
    console.log("Refactor description logic to a separate function.");
    // Set the element which delineates the top of the description text.
    let descriptionTopElement = (receivedDateElement === null) ? startElement : receivedDateElement;
    // Set the element which delineates the bottom left of the description text.
    let descriptionBottomLeftElement = middleElement;
    // Extract the description text.
    let descriptionElements = elements.filter(element => element.y > descriptionTopElement.y + descriptionTopElement.height &&
        element.y < descriptionBottomLeftElement.y &&
        element.x > descriptionBottomLeftElement.x - 0.2 * descriptionBottomLeftElement.width);
    // Sort the description elements by Y co-ordinate and then by X co-ordinate (the Math.max
    // expressions exist to allow for the Y co-ordinates of elements to be not exactly aligned;
    // for example, hyphens in text such as "Retail Fitout - Shop 7").
    let elementComparer = (a, b) => (a.y > b.y + (Math.max(a.height, b.height) * 2) / 3) ? 1 : ((a.y < b.y - (Math.max(a.height, b.height) * 2) / 3) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    descriptionElements.sort(elementComparer);
    // Construct the description from the description elements.
    let description = descriptionElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ").replace(/ﬁ/g, "fi").replace(/ﬂ/g, "fl");
    console.log(`Description: ${description}`);
    console.log("Refactor address logic to a separate function.");
    // Find the elements above (at least a "line" above) the "Assessment Number" text and to the
    // left of the middleElement.  These elements correspond to the address (assumed to be on one
    // single line).
    let addressElements = elements.filter(element => element.y < assessmentNumberElement.y - assessmentNumberElement.height &&
        element.x < middleElement.x - 0.2 * middleElement.width);
    // Find the lowest address element (this is assumed to form part of the single line of the
    // address).
    let addressBottomElement = addressElements.reduce((previous, current) => ((previous === undefined || current.y > previous.y) ? current : previous), undefined);
    if (addressBottomElement === undefined) {
        console.log(`Application number ${applicationNumber} will be ignored because an address was not found (searching upwards from the "Assessment Number" text).`);
        return undefined;
    }
    console.log(`addressBottomElement is (${addressBottomElement.x},${addressBottomElement.y}) width=${addressBottomElement.width} height=${addressBottomElement.height}`);
    // Obtain all elements on the same "line" as the lowest address element.
    console.log(`assessmentNumberElement is (${assessmentNumberElement.x},${assessmentNumberElement.y}) width=${assessmentNumberElement.width} height=${assessmentNumberElement.height}`);
    console.log(`middleElement is (x=${middleElement.x},y=${middleElement.y}) width=${middleElement.width} height=${middleElement.height}`);
    addressElements = elements.filter(element => element.y < assessmentNumberElement.y - assessmentNumberElement.height &&
        element.x < middleElement.x - 0.2 * middleElement.width &&
        element.y >= addressBottomElement.y - Math.max(element.height, addressBottomElement.height));
    // Sort the address elements by Y co-ordinate and then by X co-ordinate (the Math.max
    // expressions exist to allow for the Y co-ordinates of elements to be not exactly aligned).
    elementComparer = (a, b) => (a.y > b.y + Math.max(a.height, b.height)) ? 1 : ((a.y < b.y - Math.max(a.height, b.height)) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    addressElements.sort(elementComparer);
    // Remove any smaller elements (say less than half the area) that are 90% or more encompassed
    // by another element (this then avoids some artefacts of the text recognition, ie. elements
    // such as "r~" and "-" that can otherwise overlap the main text).
    console.log("-----Address elements before:");
    for (let element of addressElements)
        console.log(`    [${element.text}] (${element.x},${element.y}) ${element.width}×${element.height} confidence=${Math.round(element.confidence)}%`);
    addressElements = addressElements.filter(element => !addressElements.some(otherElement => getArea(otherElement) > 2 * getArea(element) && // smaller element (ie. the other element is at least double the area)
        getArea(element) > 0 &&
        getArea(constructIntersection(element, otherElement)) / getArea(element) > 0.9));
    console.log("-----Address elements after:");
    for (let element of addressElements)
        console.log(`    [${element.text}] (${element.x},${element.y}) ${element.width}×${element.height} confidence=${Math.round(element.confidence)}%`);
    // Construct the address from the discovered address elements.
    let address = addressElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ").replace(/ﬁ/g, "fi").replace(/ﬂ/g, "fl");
    address = formatAddress(address);
    console.log(`Address: ${address}`);
    // for (let element of elements)
    //     console.log(`[${Math.round(element.x)},${Math.round(element.y)}] ${element.text}`);
    console.log("----------");
    return [];
    // let applicationNumber = getRightText(elements, "Application No", "Application Date", "Applicants Name");
    // let receivedDate = getRightText(elements, "Application Date", "Planning Approval", "Application received");
    let houseNumber = getRightText(elements, "Property House No", "Planning Conditions", "Lot");
    let streetName = getRightText(elements, "Property street", "Planning Conditions", "Property suburb");
    let suburbName = getRightText(elements, "Property suburb", "Planning Conditions", "Title");
    // let description = getDownText(elements, "Development Description", "Relevant Authority", undefined);
    // let address = "";
    if (houseNumber !== undefined)
        address += houseNumber.trim();
    if (streetName !== undefined)
        address += ((address === "") ? "" : " ") + streetName.trim();
    if (suburbName === undefined || suburbName.trim() === "")
        address = ""; // ignore the application because there is no suburb
    // Attempt to add the state and post code to the suburb.
    let suburbNameAndPostCode = SuburbNames[suburbName.trim()];
    if (suburbNameAndPostCode === undefined)
        suburbNameAndPostCode = suburbName.trim();
    address += ((address === "") ? "" : ", ") + suburbNameAndPostCode;
    address = address.trim();
    // A valid application must at least have an application number and an address.
    if (applicationNumber === "" || address === "")
        return undefined;
    let parsedReceivedDate = moment(receivedDate, "D/MM/YYYY", true); // allows the leading zero of the day to be omitted
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description === "") ? "No description provided" : description),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: parsedReceivedDate.isValid() ? parsedReceivedDate.format("YYYY-MM-DD") : ""
    };
}
// Parses an image (from a PDF document).
async function parseImage(image, bounds) {
    // Convert the image data into a format that can be used by jimp.
    let pixelSize = (8 * image.data.length) / (image.width * image.height);
    let jimpImage = null;
    if (pixelSize === 1) {
        // A monochrome image (one bit per pixel).
        jimpImage = new jimp(image.width, image.height);
        for (let x = 0; x < image.width; x++) {
            for (let y = 0; y < image.height; y++) {
                let index = y * (image.width / 8);
                let bitIndex = x % 8;
                let byteIndex = (x - bitIndex) / 8;
                index += byteIndex;
                let color = null;
                if ((image.data[index] & (128 >> bitIndex)) === 0)
                    color = jimp.rgbaToInt(0, 0, 0, 255); // black pixel
                else
                    color = jimp.rgbaToInt(255, 255, 255, 255); // white pixel
                jimpImage.setPixelColor(color, x, y);
            }
        }
    }
    else {
        // Assume a 24 bit colour image (3 bytes per pixel).
        jimpImage = new jimp(image.width, image.height);
        for (let x = 0; x < image.width; x++) {
            for (let y = 0; y < image.height; y++) {
                let index = (y * image.width * 3) + (x * 3);
                let color = jimp.rgbaToInt(image.data[index], image.data[index + 1], image.data[index + 2], 255);
                jimpImage.setPixelColor(color, x, y);
            }
        }
    }
    // Note that textord_old_baselines is set to 0 so that text that is offset by half the height
    // of the the font is correctly recognised.
    let imageBuffer = await new Promise((resolve, reject) => jimpImage.getBuffer(jimp.MIME_PNG, (error, buffer) => error ? reject(error) : resolve(buffer)));
    let result = await new Promise((resolve, reject) => { tesseract.recognize(imageBuffer, { textord_old_baselines: "0" }).then(function (result) { resolve(result); }); });
    tesseract.terminate();
    if (global.gc)
        global.gc();
    // Simplify the lines (remove most of the information generated by tesseract.js).
    let elements = [];
    if (result.blocks && result.blocks.length)
        for (let block of result.blocks)
            for (let paragraph of block.paragraphs)
                for (let line of paragraph.lines)
                    elements = elements.concat(line.words.map(word => {
                        return {
                            text: word.text,
                            confidence: word.confidence,
                            choiceCount: word.choices.length,
                            x: word.bbox.x0 + bounds.x,
                            y: word.bbox.y0 + bounds.y,
                            width: (word.bbox.x1 - word.bbox.x0),
                            height: (word.bbox.y1 - word.bbox.y0)
                        };
                    }));
    return elements;
}
// Parses a PDF document.
async function parsePdf(url) {
    let developmentApplications = [];
    // Read the PDF.
    let buffer = await request({ url: url, encoding: null, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    // Parse the PDF.  Each page has the details of multiple applications.
    let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
    console.log("Only parsing the first few pages for testing purposes.");
    console.log("Get \"Records\" from first page and ensure that total is correct.");
    for (let index = 0; index < pdf.numPages; index++) {
        // for (let index = 8; index < 9; index++) {
        console.log(`Page ${index + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(index + 1);
        let viewportTest = await page.getViewport(1.0);
        let operators = await page.getOperatorList();
        // Find and parse any images in the current PDF page.
        let elements = [];
        for (let index = 0; index < operators.fnArray.length; index++) {
            if (operators.fnArray[index] !== pdfjs.OPS.paintImageXObject && operators.fnArray[index] !== pdfjs.OPS.paintImageMaskXObject)
                continue;
            // The operator either contains the name of an image or an actual image.
            let image = operators.argsArray[index][0];
            if (typeof image === "string")
                image = page.objs.get(image); // get the actual image using its name
            // Obtain the transform that applies to the image.
            let transform = (index - 1 >= 0 && operators.fnArray[index - 1] === pdfjs.OPS.transform) ? operators.argsArray[index - 1] : undefined;
            if (transform === undefined) // a transform is needed
                continue;
            // Parse the text from the image.
            let bounds = {
                x: (transform[4] * image.height) / transform[3],
                y: ((viewportTest.height - transform[5] - transform[3]) * image.height) / transform[3],
                width: image.width,
                height: image.height
            };
            elements = elements.concat(await parseImage(image, bounds));
        }
        // Sort the elements by Y co-ordinate and then by X co-ordinate.
        let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
        elements.sort(elementComparer);
        // Group the elements into sections based on where the "Dev App No." text starts (and
        // any other element the "Dev Ap No." elements line up with horizontally with a margin
        // of error equal to about the height of the "Dev App No." text; in order to capture the
        // lodged date, which may be higher up than the "Dev App No." text).
        let startElements = [];
        for (let startElement of elements.filter(element => element.text.trim().toLowerCase().startsWith("dev"))) {
            // Check that the elements next to "Dev" produce the text "Dev App No.".  Take care
            // as the text may possibly be spread across one, two or three elements (allow for
            // all these possibilities).
            let startText = condenseText(startElement);
            if (startText === "dev") {
                startElement = getRightElement(elements, startElement);
                startText = condenseText(startElement);
                if (startText === "app") {
                    startElement = getRightElement(elements, startElement);
                    startText = condenseText(startElement);
                    if (startText !== "no")
                        continue; // not "Dev App No."
                }
                else if (startText !== "appno") {
                    continue; // not "Dev App No."
                }
            }
            else if (startText === "devapp") {
                startElement = getRightElement(elements, startElement);
                startText = condenseText(startElement);
                if (startText !== "no")
                    continue; // not "Dev App No."
            }
            else if (startText !== "devappno") {
                continue; // not "Dev App No."
            }
            startElements.push(startElement);
        }
        let yComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
        startElements.sort(yComparer);
        let applicationElementGroups = [];
        for (let index = 0; index < startElements.length; index++) {
            // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
            // the current page).  Allow some leeway vertically (add some extra height) because
            // in some cases the lodged date is a fair bit higher up than the "Dev App No." text.
            let startElement = startElements[index];
            let raisedStartElement = {
                text: startElement.text,
                x: startElement.x,
                y: startElement.y - 2 * startElement.height,
                width: startElement.width,
                height: startElement.height
            };
            let rowTop = getRowTop(elements, raisedStartElement);
            let nextRowTop = (index + 1 < startElements.length) ? getRowTop(elements, startElements[index + 1]) : Number.MAX_VALUE;
            // Extract all elements between the two rows.
            applicationElementGroups.push({ startElement: startElements[index], elements: elements.filter(element => element.y >= rowTop && element.y + element.height < nextRowTop) });
        }
        // Parse the development application from each group of elements (ie. a section of the
        // current page of the PDF document).
        for (let applicationElementGroup of applicationElementGroups) {
            let developmentApplication = parseApplicationElements(applicationElementGroup.elements, applicationElementGroup.startElement, url);
            if (developmentApplication !== undefined)
                developmentApplications.push(developmentApplication);
        }
    }
    return developmentApplications;
}
// Gets a random integer in the specified range: [minimum, maximum).
function getRandom(minimum, maximum) {
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
    // Read all street, street suffix, suburb, state and post code information.
    readAddressInformation();
    // Retrieve the page that contains the links to the PDFs.
    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);
    let body = await request({ url: DevelopmentApplicationsUrl, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);
    let pdfUrls = [];
    for (let element of $("td.uContentListDesc a[href$='.pdf']").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl);
        pdfUrl.protocol = "http"; // force to use HTTP instead of HTTPS
        if (!pdfUrls.some(url => url === pdfUrl.href)) // avoid duplicates
            pdfUrls.push(pdfUrl.href);
    }
    if (pdfUrls.length === 0) {
        console.log("No PDF URLs were found on the page.");
        return;
    }
    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).
    let selectedPdfUrls = [];
    selectedPdfUrls.push(pdfUrls.shift());
    if (pdfUrls.length > 0)
        selectedPdfUrls.push(pdfUrls[getRandom(1, pdfUrls.length)]);
    if (getRandom(0, 2) === 0)
        selectedPdfUrls.reverse();
    // selectedPdfUrls = [ "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20July%202018.pdf", "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20February%202017.pdf" ];
    // selectedPdfUrls = [ "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20July%202018.pdf" ];
    selectedPdfUrls = ["http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20February%202017.pdf"];
    for (let pdfUrl of selectedPdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl);
        console.log(`Parsed ${developmentApplications.length} development application(s) from document: ${pdfUrl}`);
        // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
        // current process being terminated by morph.io).
        if (global.gc)
            global.gc();
        for (let developmentApplication of developmentApplications)
            await insertRow(database, developmentApplication);
    }
}
main().then(() => console.log("Complete.")).catch(error => console.error(error));
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoic2NyYXBlci5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbInNjcmFwZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsa0dBQWtHO0FBQ2xHLHNDQUFzQztBQUN0QyxFQUFFO0FBQ0YsZUFBZTtBQUNmLG1CQUFtQjtBQUVuQixZQUFZLENBQUM7O0FBRWIsbUNBQW1DO0FBQ25DLGtEQUFrRDtBQUNsRCxtQ0FBbUM7QUFDbkMsaUNBQWlDO0FBQ2pDLGlDQUFpQztBQUNqQyxvQ0FBb0M7QUFDcEMsMENBQTBDO0FBQzFDLDZCQUE2QjtBQUM3QiwwQ0FBMEM7QUFDMUMseUJBQXlCO0FBRXpCLE9BQU8sQ0FBQyxPQUFPLEVBQUUsQ0FBQztBQUVsQixNQUFNLDBCQUEwQixHQUFHLG9EQUFvRCxDQUFDO0FBQ3hGLE1BQU0sVUFBVSxHQUFHLHVDQUF1QyxDQUFDO0FBSzNELHFDQUFxQztBQUVyQyxJQUFJLFdBQVcsR0FBRyxJQUFJLENBQUM7QUFDdkIsSUFBSSxjQUFjLEdBQUcsSUFBSSxDQUFDO0FBQzFCLElBQUksV0FBVyxHQUFHLElBQUksQ0FBQztBQUV2Qiw4QkFBOEI7QUFFOUIsS0FBSyxVQUFVLGtCQUFrQjtJQUM3QixPQUFPLElBQUksT0FBTyxDQUFDLENBQUMsT0FBTyxFQUFFLE1BQU0sRUFBRSxFQUFFO1FBQ25DLElBQUksUUFBUSxHQUFHLElBQUksT0FBTyxDQUFDLFFBQVEsQ0FBQyxhQUFhLENBQUMsQ0FBQztRQUNuRCxRQUFRLENBQUMsU0FBUyxDQUFDLEdBQUcsRUFBRTtZQUNwQixRQUFRLENBQUMsR0FBRyxDQUFDLDhMQUE4TCxDQUFDLENBQUM7WUFDN00sT0FBTyxDQUFDLFFBQVEsQ0FBQyxDQUFDO1FBQ3RCLENBQUMsQ0FBQyxDQUFDO0lBQ1AsQ0FBQyxDQUFDLENBQUM7QUFDUCxDQUFDO0FBRUQsOERBQThEO0FBRTlELEtBQUssVUFBVSxTQUFTLENBQUMsUUFBUSxFQUFFLHNCQUFzQjtJQUNyRCxPQUFPLElBQUksT0FBTyxDQUFD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