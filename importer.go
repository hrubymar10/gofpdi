package gofpdi

import (
	"fmt"
	"io"
)

// The Importer class to be used by a pdf generation library
type Importer struct {
	sourceFile    string
	readers       map[string]*PdfReader
	writers       map[string]*PdfWriter
	tplMap        map[int]*TplInfo
	tplN          int
	writer        *PdfWriter
	importedPages map[string]int
}

type TplInfo struct {
	SourceFile string
	Writer     *PdfWriter
	TemplateId int
}

func (importer *Importer) GetReader() *PdfReader {
	return importer.GetReaderForFile(importer.sourceFile)
}

func (importer *Importer) GetWriter() *PdfWriter {
	return importer.GetWriterForFile(importer.sourceFile)
}

func (importer *Importer) GetReaderForFile(file string) *PdfReader {
	if _, ok := importer.readers[file]; ok {
		return importer.readers[file]
	}

	return nil
}

func (importer *Importer) GetWriterForFile(file string) *PdfWriter {
	if _, ok := importer.writers[file]; ok {
		return importer.writers[file]
	}

	return nil
}

func NewImporter() *Importer {
	importer := &Importer{}
	importer.init()

	return importer
}

func (importer *Importer) init() {
	importer.readers = make(map[string]*PdfReader, 0)
	importer.writers = make(map[string]*PdfWriter, 0)
	importer.tplMap = make(map[int]*TplInfo, 0)
	importer.writer, _ = NewPdfWriter("")
	importer.importedPages = make(map[string]int, 0)
}

func (importer *Importer) SetSourceFile(f string) error {
	importer.sourceFile = f

	// If reader hasn't been instantiated, do that now
	if _, ok := importer.readers[importer.sourceFile]; !ok {
		reader, err := NewPdfReader(importer.sourceFile)
		if err != nil {
			return err
		}
		importer.readers[importer.sourceFile] = reader
	}

	// If writer hasn't been instantiated, do that now
	if _, ok := importer.writers[importer.sourceFile]; !ok {
		writer, err := NewPdfWriter("")
		if err != nil {
			return err
		}

		// Make the next writer start template numbers at importer.tplN
		writer.SetTplIdOffset(importer.tplN)
		importer.writers[importer.sourceFile] = writer
	}

	return nil
}

func (importer *Importer) SetSourceStream(rs *io.ReadSeeker) error {
	importer.sourceFile = fmt.Sprintf("%v", rs)

	if _, ok := importer.readers[importer.sourceFile]; !ok {
		reader, err := NewPdfReaderFromStream(*rs)
		if err != nil {
			return err
		}
		importer.readers[importer.sourceFile] = reader
	}

	// If writer hasn't been instantiated, do that now
	if _, ok := importer.writers[importer.sourceFile]; !ok {
		writer, err := NewPdfWriter("")
		if err != nil {
			return err
		}

		// Make the next writer start template numbers at importer.tplN
		writer.SetTplIdOffset(importer.tplN)
		importer.writers[importer.sourceFile] = writer
	}

	return nil
}

func (importer *Importer) GetNumPages() (int, error) {
	return importer.GetReader().getNumPages()
}

func (importer *Importer) GetPageSizes() (map[int]map[string]map[string]float64, error) {
	return importer.GetReader().getAllPageBoxes(1.0)
}

func (importer *Importer) ImportPage(pageno int, box string) (int, error) {
	// If page has already been imported, return existing tplN
	pageNameNumber := fmt.Sprintf("%s-%04d", importer.sourceFile, pageno)
	if _, ok := importer.importedPages[pageNameNumber]; ok {
		return importer.importedPages[pageNameNumber], nil
	}

	res, err := importer.GetWriter().ImportPage(importer.GetReader(), pageno, box)
	if err != nil {
		return 0, err
	}

	// Get current template id
	tplN := importer.tplN

	// Set tpl info
	importer.tplMap[tplN] = &TplInfo{SourceFile: importer.sourceFile, TemplateId: res, Writer: importer.GetWriter()}

	// Increment template id
	importer.tplN++

	// Cache imported page tplN
	importer.importedPages[pageNameNumber] = tplN

	return tplN, nil
}

func (importer *Importer) SetNextObjectID(objId int) {
	importer.GetWriter().SetNextObjectID(objId)
}

// Put form xobjects and get back a map of template names (e.g. /GOFPDITPL1) and their object ids (int)
func (importer *Importer) PutFormXobjects() (map[string]int, error) {
	res := make(map[string]int, 0)
	tplNamesIds, err := importer.GetWriter().PutFormXobjects(importer.GetReader())
	if err != nil {
		return nil, err
	}
	for tplName, pdfObjId := range tplNamesIds {
		res[tplName] = pdfObjId.id
	}
	return res, nil
}

// Put form xobjects and get back a map of template names (e.g. /GOFPDITPL1) and their object ids (sha1 hash)
func (importer *Importer) PutFormXobjectsUnordered() (map[string]string, error) {
	importer.GetWriter().SetUseHash(true)
	res := make(map[string]string, 0)
	tplNamesIds, err := importer.GetWriter().PutFormXobjects(importer.GetReader())
	if err != nil {
		return nil, err
	}
	for tplName, pdfObjId := range tplNamesIds {
		res[tplName] = pdfObjId.hash
	}
	return res, nil
}

// Get object ids (int) and their contents (string)
func (importer *Importer) GetImportedObjects() map[int]string {
	res := make(map[int]string, 0)
	pdfObjIdBytes := importer.GetWriter().GetImportedObjects()
	for pdfObjId, bytes := range pdfObjIdBytes {
		res[pdfObjId.id] = string(bytes)
	}
	return res
}

// Get object ids (sha1 hash) and their contents ([]byte)
// The contents may have references to other object hashes which will need to be replaced by the pdf generator library
// The positions of the hashes (sha1 - 40 characters) can be obtained by calling GetImportedObjHashPos()
func (importer *Importer) GetImportedObjectsUnordered() map[string][]byte {
	res := make(map[string][]byte, 0)
	pdfObjIdBytes := importer.GetWriter().GetImportedObjects()
	for pdfObjId, bytes := range pdfObjIdBytes {
		res[pdfObjId.hash] = bytes
	}
	return res
}

// Get the positions of the hashes (sha1 - 40 characters) within each object, to be replaced with
// actual objects ids by the pdf generator library
func (importer *Importer) GetImportedObjHashPos() map[string]map[int]string {
	res := make(map[string]map[int]string, 0)
	pdfObjIdPosHash := importer.GetWriter().GetImportedObjHashPos()
	for pdfObjId, posHashMap := range pdfObjIdPosHash {
		res[pdfObjId.hash] = posHashMap
	}
	return res
}

// For a given template id (returned from ImportPage), get the template name (e.g. /GOFPDITPL1) and
// the 4 float64 values necessary to draw the template a x,y for a given width and height.
func (importer *Importer) UseTemplate(tplid int, _x float64, _y float64, _w float64, _h float64) (string, float64, float64, float64, float64) {
	// Look up template id in importer tpl map
	tplInfo := importer.tplMap[tplid]
	return tplInfo.Writer.UseTemplate(tplInfo.TemplateId, _x, _y, _w, _h)
}
