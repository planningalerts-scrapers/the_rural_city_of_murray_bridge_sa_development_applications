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
    return element.text.trim().replace(/[\s.,\-_]/g, "").toLowerCase();
}
// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.
function getRowTop(elements, startElement) {
    let top = startElement.y;
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
    else if (postCode === "O" || postCode === "0" || postCode === "D") {
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
    // for (let element of elements)
    //     console.log(`    [${element.text}] (${element.x},${element.y}) ${element.width}×${element.height} confidence=${Math.round((element as any).confidence)}%`);
    //     // console.log(`    [${element.text}] (${Math.round(element.x)},${Math.round(element.y)}) ${element.width}×${element.height} confidence=${Math.round((element as any).confidence)}%`);
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
    applicationNumber = applicationNumber.replace(/[IlL\[\]\|’,]/g, "/"); // for example, converts "17I2017" to "17/2017"
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
    if (receivedDate !== undefined)
        console.log(`Received Date: ${receivedDate.isValid() ? receivedDate.format("YYYY-MM-DD") : ""}`);
    console.log("Refactor description logic to a separate function.");
    // Set the element which delineates the top of the description text.
    let descriptionTopElement = (receivedDateElement === undefined) ? startElement : receivedDateElement;
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
    // Remove any address elements that occur after a sizeable gap.  Any such elements are very
    // likely part of the description (not the address) because sometimes the description is
    // moved to the left, closer to the address (see "Crystal Report - DevAppSeptember 2015.pdf").
    for (let index = 1; index < addressElements.length; index++) {
        if (addressElements[index].x - (addressElements[index - 1].x + addressElements[index - 1].width) > 50) { // gap greater than 50 pixels
            addressElements.length = index; // remove the element and all following elements that appear after a large gap
            break;
        }
    }
    console.log("-----Address elements after:");
    for (let element of addressElements)
        console.log(`    [${element.text}] (${element.x},${element.y}) ${element.width}×${element.height} confidence=${Math.round(element.confidence)}%`);
    // Construct the address from the discovered address elements (and attempt to correct some
    // spelling errors).
    let address = addressElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ").replace(/ﬁ/g, "fi").replace(/ﬂ/g, "fl");
    address = formatAddress(address);
    console.log(`Address: ${address}`);
    // for (let element of elements)
    //     console.log(`[${Math.round(element.x)},${Math.round(element.y)}] ${element.text}`);
    console.log("----------");
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description === "") ? "No description provided" : description),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: (receivedDate !== undefined && receivedDate.isValid()) ? receivedDate.format("YYYY-MM-DD") : ""
    };
}
// Segments an image vertically and horizontally based on blocks of white (or almost white) pixels
// in order to avoid using too much memory.  Very often a large image will be mostly white space.
// A very simple horizontal and then vertical search is performed for consecutive lines of white
// (or mostly white) pixels.
let imageCount = 0;
let imageSegmentedCount = 0;
function segmentImage(jimpImage) {
    let segments = [];
    let bounds = { x: 0, y: 0, width: jimpImage.bitmap.width, height: jimpImage.bitmap.height };
    // imageCount++;
    // console.log(`Writing image ${imageCount}`);
    // jimpImage.write(`C:\\Temp\\Murray Bridge\\Reconstructed\\Reconstructed.Images.${imageCount}.png`);
    // Only segment large images (do not waste time on small images which are already small enough
    // that they will not cause too much memory to be used).
    if (jimpImage.bitmap.width * jimpImage.bitmap.height > 500 * 500) {
        let rectangles = [];
        let verticalRectangles = segmentImageVertically(jimpImage, bounds);
        for (let verticalRectangle of verticalRectangles)
            rectangles = rectangles.concat(segmentImageHorizontally(jimpImage, verticalRectangle));
        for (let rectangle of rectangles) {
            let croppedJimpImage = new jimp(rectangle.width, rectangle.height);
            croppedJimpImage.blit(jimpImage, 0, 0, rectangle.x, rectangle.y, rectangle.width, rectangle.height);
            // imageSegmentedCount++;
            // console.log(`    Writing segmented image ${imageSegmentedCount} to file.`);
            // croppedJimpImage.write(`C:\\Temp\\Murray Bridge\\Problem\\Large Image.${imageConvertCount}.Segment${imageSegmentedCount}.${rectangle.width}×${rectangle.height}.png`);
            segments.push({ image: croppedJimpImage, bounds: rectangle });
        }
    }
    if (segments.length === 0)
        segments.push({ image: jimpImage, bounds: bounds });
    return segments;
}
// Segments an image vertically (within the specified bounds) by searching for blocks of
// consecutive, white (or close to white) horizontal lines.
function segmentImageVertically(jimpImage, bounds) {
    let whiteBlocks = [];
    let isPreviousWhiteLine = false;
    for (let y = bounds.y; y < bounds.y + bounds.height; y++) {
        // Count the number of white pixels across the current horizontal line.
        let whiteCount = 0;
        for (let x = bounds.x; x < bounds.x + bounds.width; x++) {
            let value = jimpImage.getPixelColor(x, y);
            if (value === 0xffffffff) // performance improvement (for the common case of a pure white pixel)
                whiteCount++;
            else {
                let color = jimp.intToRGBA(value);
                if (color.r > 240 && color.g > 240 && color.b > 240) // white or just off-white
                    whiteCount++;
            }
        }
        // If the line is mostly white pixels then it is considered a white line.
        let isWhiteLine = (whiteCount >= bounds.width - 2); // allow up to two non-white pixels
        if (isWhiteLine) {
            if (isPreviousWhiteLine)
                whiteBlocks[whiteBlocks.length - 1].height++; // increase the size of the current block
            else
                whiteBlocks.push({ y: y, height: 1 }); // start a new block
        }
        isPreviousWhiteLine = isWhiteLine;
    }
    // Only keep blocks of white that consist of 25 consecutive lines or more (an arbitrary value).
    whiteBlocks = whiteBlocks.filter(whiteBlock => whiteBlock.height >= 25);
    // Determine the bounds of the rectangles that remain when the blocks of white are removed.
    let rectangles = [];
    for (let index = 0; index <= whiteBlocks.length; index++) {
        let y = (index === 0) ? 0 : (whiteBlocks[index - 1].y + whiteBlocks[index - 1].height);
        let height = ((index === whiteBlocks.length) ? (bounds.y + bounds.height) : whiteBlocks[index].y) - y;
        if (height > 0)
            rectangles.push({ x: bounds.x, y: y, width: bounds.width, height: height });
    }
    return rectangles;
}
// Segments an image horizontally (within the specified bounds) by searching for blocks of
// consecutive, white (or close to white) vertical lines.
function segmentImageHorizontally(jimpImage, bounds) {
    let whiteBlocks = [];
    let isPreviousWhiteLine = false;
    for (let x = bounds.x; x < bounds.x + bounds.width; x++) {
        // Count the number of white pixels across the current vertical line.
        let whiteCount = 0;
        for (let y = bounds.y; y < bounds.y + bounds.height; y++) {
            let value = jimpImage.getPixelColor(x, y);
            if (value === 0xffffffff) // performance improvement (for the common case of a pure white pixel)
                whiteCount++;
            else {
                let color = jimp.intToRGBA(value);
                if (color.r > 240 && color.g > 240 && color.b > 240) // white or just off-white
                    whiteCount++;
            }
        }
        // If the line is mostly white pixels then it is considered a white line.
        let isWhiteLine = (whiteCount >= bounds.height - 2); // allow up to two non-white pixels
        if (isWhiteLine) {
            if (isPreviousWhiteLine)
                whiteBlocks[whiteBlocks.length - 1].width++; // increase the size of the current block
            else
                whiteBlocks.push({ x: x, width: 1 }); // start a new block
        }
        isPreviousWhiteLine = isWhiteLine;
    }
    // Only keep blocks of white that consist of 25 consecutive lines or more (an arbitrary value).
    whiteBlocks = whiteBlocks.filter(whiteBlock => whiteBlock.width >= 25);
    // Determine the bounds of the rectangles that remain when the blocks of white are removed.
    let rectangles = [];
    for (let index = 0; index <= whiteBlocks.length; index++) {
        let x = (index === 0) ? 0 : (whiteBlocks[index - 1].x + whiteBlocks[index - 1].width);
        let width = ((index === whiteBlocks.length) ? (bounds.x + bounds.width) : whiteBlocks[index].x) - x;
        if (width > 0)
            rectangles.push({ x: x, y: bounds.y, width: width, height: bounds.height });
    }
    return rectangles;
}
// Converts image data from the PDF to a Jimp format image.
let imageConvertCount = 0;
function convertToJimpImage(image) {
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
    // imageConvertCount++;
    // console.log(`Writing image ${imageConvertCount} to file.`);
    // jimpImage.write(`C:\\Temp\\Murray Bridge\\Problem\\Large Image.${imageConvertCount}.${image.width}×${image.height}.png`);
    return jimpImage;
}
// Parses an image (from a PDF document).
async function parseImage(image, bounds) {
    // Convert the image data into a format that can be used by jimp and then segment the image
    // based on blocks of white.
    let segments = segmentImage(convertToJimpImage(image));
    if (global.gc)
        global.gc();
    let elements = [];
    for (let segment of segments) {
        // Note that textord_old_baselines is set to 0 so that text that is offset by half the height
        // of the the font is correctly recognised.
        let imageBuffer = await new Promise((resolve, reject) => segment.image.getBuffer(jimp.MIME_PNG, (error, buffer) => error ? reject(error) : resolve(buffer)));
        let result = await new Promise((resolve, reject) => { tesseract.recognize(imageBuffer, { textord_old_baselines: "0" }).then(function (result) { resolve(result); }); });
        tesseract.terminate();
        if (global.gc)
            global.gc();
        // Simplify the lines (remove most of the information generated by tesseract.js).
        if (result.blocks && result.blocks.length)
            for (let block of result.blocks)
                for (let paragraph of block.paragraphs)
                    for (let line of paragraph.lines)
                        elements = elements.concat(line.words.map(word => {
                            return {
                                text: word.text,
                                confidence: word.confidence,
                                choiceCount: word.choices.length,
                                x: word.bbox.x0 + bounds.x + segment.bounds.x,
                                y: word.bbox.y0 + bounds.y + segment.bounds.y,
                                width: (word.bbox.x1 - word.bbox.x0),
                                height: (word.bbox.y1 - word.bbox.y0)
                            };
                        }));
    }
    return elements;
}
// Parses a PDF document.
async function parsePdf(url) {
    let developmentApplications = [];
    // Read the PDF.
    let hasAlreadyParsed = true;
    let fileName = decodeURI(new urlparser.URL(url).pathname.split("/").pop());
    console.log(`Reading "${fileName}" from local disk.`);
    let buffer = fs.readFileSync(`C:\\Temp\\Murray Bridge\\Problem\\${fileName}`);
    // let buffer = await request({ url: url, encoding: null, proxy: process.env.MORPH_PROXY });
    // await sleep(2000 + getRandom(0, 5) * 1000);
    // Parse the PDF.  Each page has the details of multiple applications.
    let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
    console.log("Get \"Records\" from first page and ensure that total is correct.");
    for (let index = 0; index < pdf.numPages; index++) {
        console.log(`Page ${index + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(index + 1);
        let viewportTest = await page.getViewport(1.0);
        let operators = await page.getOperatorList();
        // Find and parse any images in the current PDF page.
        let elements = [];
        if (hasAlreadyParsed) {
            console.log("Reading pre-parsed elements.");
            console.log(`Reading pre-parsed elements for page ${index + 1} of ${fileName}.`);
            elements = JSON.parse(fs.readFileSync(`C:\\Temp\\Murray Bridge\\Test Set\\${fileName}.Page${index + 1}.txt`, "utf8"));
        }
        else {
            console.log("Parsing using slow approach.");
            for (let index = 0; index < operators.fnArray.length; index++) {
                if (operators.fnArray[index] !== pdfjs.OPS.paintImageXObject && operators.fnArray[index] !== pdfjs.OPS.paintImageMaskXObject)
                    continue;
                // The operator either contains the name of an image or an actual image.
                let image = operators.argsArray[index][0];
                if (typeof image === "string")
                    image = page.objs.get(image); // get the actual image using its name
                else
                    operators.argsArray[index][0] = undefined; // attempt to release memory used by images
                // Obtain the transform that applies to the image.  Note that the first image in the
                // PDF typically has a pdfjs.OPS.dependency element in the fnArray between it and its
                // transform (pdfjs.OPS.transform).
                let transform = undefined;
                if (index - 1 >= 0 && operators.fnArray[index - 1] === pdfjs.OPS.transform)
                    transform = operators.argsArray[index - 1];
                else if (index - 2 >= 0 && operators.fnArray[index - 1] === pdfjs.OPS.dependency && operators.fnArray[index - 2] === pdfjs.OPS.transform)
                    transform = operators.argsArray[index - 2];
                else
                    continue;
                let bounds = {
                    x: (transform[4] * image.height) / transform[3],
                    y: ((viewportTest.height - transform[5] - transform[3]) * image.height) / transform[3],
                    width: image.width,
                    height: image.height
                };
                // console.log(`    Image: ${image.width}×${image.height}`);
                // Parse the text from the image.
                elements = elements.concat(await parseImage(image, bounds));
                if (global.gc)
                    global.gc();
            }
            // Reconstruct the image.
            //
            // let maximumWidth = Math.ceil(elements.reduce((maximum, element) => Math.max(maximum, element.x + element.width), 0));
            // let maximumHeight = Math.ceil(elements.reduce((maximum, element) => Math.max(maximum, element.y + element.height), 0));
            // console.log(`maximumWidth: ${maximumWidth}, maximumHeight: ${maximumHeight}, elements.length: ${elements.length}`);
            //
            // let reconstructedImage: any = await new Promise((resolve, reject) => new (jimp as any)(maximumWidth, maximumHeight, (error, image) => error ? reject(error) : resolve(image)));
            // let font = await (jimp as any).loadFont(jimp.FONT_SANS_16_BLACK);
            //
            // for (let element of elements) {
            //     let wordImage = new (jimp as any)(Math.round(element.width), Math.round(element.height), 0x776677ff);
            //     reconstructedImage.blit(wordImage, element.x, element.y, 0, 0, element.width, element.height);
            //     reconstructedImage.print(font, element.x, element.y, element.text);
            // }
            //
            // console.log(`Writing reconstructed image for page ${index + 1} of ${fileName}.`);
            // reconstructedImage.write(`C:\\Temp\\Murray Bridge\\Reconstructed\\Reconstructed.${fileName}.Page${index + 1}.png`);
            console.log(`Saving the elements for page ${index + 1} of ${fileName}.`);
            fs.writeFileSync(`C:\\Temp\\Murray Bridge\\Problem\\${fileName}.Page${index + 1}.txt`, JSON.stringify(elements));
            continue;
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
            // let startText = condenseText(startElement);
            // if (startText === "dev") {
            //     startElement = getRightElement(elements, startElement);
            //     startText = condenseText(startElement);
            //     if (startText !== "app")
            //         continue;  // not "Dev App"
            // } else if (startText !== "devapp") {
            //     continue;  // not "Dev App"
            // }
            let startText = condenseText(startElement);
            if (startText === "dev") {
                startElement = getRightElement(elements, startElement);
                startText = condenseText(startElement);
                if (startText === "app") {
                    startElement = getRightElement(elements, startElement);
                    startText = condenseText(startElement);
                    if (startText !== "no" && startText !== "n0" && startText !== "n°" && startText !== "\"o" && startText !== "\"0" && startText !== "\"°")
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
    console.log("Temporarily skipping read of page (for test set purposes).");
    if (false) {
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
        // let selectedPdfUrls: string[] = [];
        // selectedPdfUrls.push(pdfUrls.shift());
        // if (pdfUrls.length > 0)
        //     selectedPdfUrls.push(pdfUrls[getRandom(1, pdfUrls.length)]);
        // if (getRandom(0, 2) === 0)
        //     selectedPdfUrls.reverse();
        // selectedPdfUrls = [ "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20July%202018.pdf", "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20February%202017.pdf" ];
        // selectedPdfUrls = [ "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20July%202018.pdf" ];
        // selectedPdfUrls = [ "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20February%202017.pdf" ];
    }
    let selectedPdfUrls = [
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20July%202018.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20June%202018.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20May%202018.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Development%20Decisions%20April%202018-1.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20February%202018.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20January%202018.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/December%202017.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20November%202017.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20October%202017.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20September%202017.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20August%202017.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20July%202017.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20June%202017.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20May%202017.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20April%202017-1.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20April%202017.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20February%202017.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20January%202017.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20December%202016.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20November%202016.pdf",  // crashed on this PDF 01-Sep-2018
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20October%202016.pdf",  // crashed on this PDF 10-Sep-2018
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20September%202016.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20August%202016.pdf",  // crashed on this PDF 11-Sep-2018
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20July%202016.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20June%202016.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20May%202016.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20April%202016.pdf",  // try this one
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20March%202016.pdf", 
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20February%202016.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20January%202016.pdf",
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20November%202015.pdf",  // images not parsed 20-Sep-2018
        // "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevApp%20October%202015.pdf",
        "http://www.murraybridge.sa.gov.au/webdata/resources/files/Crystal%20Report%20-%20DevAppSeptember%202015.pdf",
    ];
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