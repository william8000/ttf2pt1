#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <time.h>
#include <netinet/in.h>

#include "ttf.h"

typedef struct glyph {
    int char_no; /* Encoding of glyph */
    int unicode; /* Unicode value of glyph */
    char *name;  /* Postscript name of glyph */
    int xMin, yMin, xMax, yMax;
    int width, lsb;
} GLYPH;

static GLYPH *glyph_list;
static short encoding[256]; /* inverse of glyph[].char_no */

static FILE *pfa_file, *afm_file;
static TTF_DIRECTORY *directory;
static TTF_DIR_ENTRY *dir_entry ;
static char *filebuffer;
static TTF_NAME *name_table = NULL;
static TTF_NAME_REC *name_record;
static TTF_HEAD *head_table = NULL;
static TTF_HHEA *hhea_table = NULL;
static TTF_KERN *kern_table = NULL;
static TTF_CMAP *cmap_table = NULL;
static LONGHORMETRIC *hmtx_table = NULL;
static TTF_GLYF *glyf_table;
static BYTE *glyf_start = NULL;
static TTF_MAXP *maxp_table = NULL;
static TTF_POST_HEAD *post_table = NULL;
static USHORT *short_loca_table = NULL;
static ULONG *long_loca_table = NULL;
static int ttf_file, numglyphs, long_offsets, ncurves;

static short cmap_n_segs;
static USHORT *cmap_seg_start, *cmap_seg_end;
static short *cmap_idDelta, *cmap_idRangeOffset;
static int ps_fmt_3 = 0, unicode = 0;
static float scale_factor;

static char *Unknown_glyph = "UNKN";

static char name_buffer[2000];
static char *name_fields[8];

static char *ISOLatin1Encoding[256] = {
    ".null",          ".notdef",        ".notdef",        ".notdef",
    ".notdef",        ".notdef",        ".notdef",        ".notdef",
    ".notdef",        ".notdef",        ".notdef",        ".notdef",
    ".notdef",        "CR",             ".notdef",        ".notdef",
    ".notdef",        ".notdef",        ".notdef",        ".notdef",
    ".notdef",        ".notdef",        ".notdef",        ".notdef",
    ".notdef",        ".notdef",        ".notdef",        ".notdef",
    ".notdef",        ".notdef",        ".notdef",        ".notdef",
    "space",          "exclam",         "quotedbl",       "numbersign",
    "dollar",         "percent",        "ampersand",      "quoteright",
    "parenleft",      "parenright",     "asterisk",       "plus",
    "comma",          "hyphen",         "period",         "slash",
    "zero",           "one",            "two",            "three",
    "four",           "five",           "six",            "seven",
    "eight",          "nine",           "colon",          "semicolon",
    "less",           "equal",          "greater",        "question",
    "at",             "A",              "B",              "C",
    "D",              "E",              "F",              "G",
    "H",              "I",              "J",              "K",
    "L",              "M",              "N",              "O",
    "P",              "Q",              "R",              "S",
    "T",              "U",              "V",              "W",
    "X",              "Y",              "Z",              "bracketleft",
    "backslash",      "bracketright",   "asciicircum",    "underscore",
    "grave",          "a",              "b",              "c",
    "d",              "e",              "f",              "g",
    "h",              "i",              "j",              "k",
    "l",              "m",              "n",              "o",
    "p",              "q",              "r",              "s",
    "t",              "u",              "v",              "w",
    "x",              "y",              "z",              "braceleft",
    "bar",            "braceright",     "asciitilde",     ".notdef",
    ".notdef",        ".notdef",        "quotesinglbase", "florin",
    "quotedblbase",   "ellipsis",       "dagger",         "daggerdbl",
    "circumflex",     "perthousand",    "Scaron",         "guilsinglleft",
    "OE",             ".notdef",        ".notdef",        ".notdef",
    ".notdef",        "quoteleft",      "quoteright",     "quotedblleft",
    "quotedblright",  "bullet",         "endash",         "emdash",
    "tilde",          "trademark",      "scaron",         "guilsinglright",
    "oe",             ".notdef",        ".notdef",        "Ydieresis",
    "nbspace",        "exclamdown",     "cent",           "sterling",
    "currency",       "yen",            "brokenbar",      "section",
    "dieresis",       "copyright",      "ordfeminine",    "guillemotleft",
    "logicalnot",     "sfthyphen",      "registered",     "macron",
    "degree",         "plusminus",      "twosuperior",    "threesuperior",
    "acute",          "mu",             "paragraph",      "periodcentered",
    "cedilla",        "onesuperior",    "ordmasculine",   "guillemotright",
    "onequarter",     "onehalf",        "threequarters",  "questiondown",
    "Agrave",         "Aacute",         "Acircumflex",    "Atilde",
    "Adieresis",      "Aring",          "AE",             "Ccedilla",
    "Egrave",         "Eacute",         "Ecircumflex",    "Edieresis",
    "Igrave",         "Iacute",         "Icircumflex",    "Idieresis",
    "Eth",            "Ntilde",         "Ograve",         "Oacute",
    "Ocircumflex",    "Otilde",         "Odieresis",      "multiply",
    "Oslash",         "Ugrave",         "Uacute",         "Ucircumflex",
    "Udieresis",      "Yacute",         "Thorn",          "germandbls",
    "agrave",         "aacute",         "acircumflex",    "atilde",
    "adieresis",      "aring",          "ae",             "ccedilla",
    "egrave",         "eacute",         "ecircumflex",    "edieresis",
    "igrave",         "iacute",         "icircumflex",    "idieresis",
    "eth",            "ntilde",         "ograve",         "oacute",
    "ocircumflex",    "otilde",         "odieresis",      "divide",
    "oslash",         "ugrave",         "uacute",         "ucircumflex",
    "udieresis",      "yacute",         "thorn",          "ydieresis"};

static char *adobe_StandardEncoding[256] = {
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    "space","exclam","quotedbl","numbersign",
    "dollar","percent","ampersand","quoteright",
    "parenleft","parenright","asterisk","plus",
    "comma","hyphen","period","slash",
    "zero","one","two","three",
    "four","five","six","seven",
    "eight","nine","colon","semicolon",
    "less","equal","greater","question",
    "at","A","B","C","D","E","F","G",
    "H","I","J","K","L","M","N","O",
    "P","Q","R","S","T","U","V","W",
    "X","Y","Z","bracketleft",
    "backslash","bracketright","asciicircum","underscore",
    "grave","a","b","c","d","e","f","g",
    "h","i","j","k","l","m","n","o",
    "p","q","r","s","t","u","v","w",
    "x","y","z","braceleft",
    "bar","braceright","asciitilde",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef","exclamdown","cent","sterling",
    "fraction","yen","florin","section",
    "currency","quotesingle","quotedblleft","guillemotleft",
    "guilsinglleft","guilsinglright","fi","fl",
    ".notdef","endash","dagger","daggerdbl",
    "periodcentered",".notdef","paragraph","bullet",
    "quotesinglbase","quotedblbase","quotedblright","guillemotright",
    "ellipsis","perthousand",".notdef","questiondown",
    ".notdef","grave","acute","circumflex",
    "tilde","macron","breve","dotaccent",
    "dieresis",".notdef","ring","cedilla",
    ".notdef","hungarumlaut","ogonek","caron",
    "emdash",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef","AE",".notdef","ordfeminine",
    ".notdef",".notdef",".notdef",".notdef",
    "Lslash","Oslash","OE","ordmasculine",
    ".notdef",".notdef",".notdef",".notdef",
    ".notdef","ae",".notdef",".notdef",
    ".notdef","dotlessi",".notdef",".notdef",
    "lslash","oslash","oe","germandbls",
    ".notdef",".notdef",".notdef",".notdef"};

static char *mac_glyph_names[258] = {
    ".notdef",         ".null",          "CR",
    "space",          "exclam",         "quotedbl",       "numbersign",
    "dollar",         "percent",        "ampersand",      "quotesingle",
    "parenleft",      "parenright",     "asterisk",       "plus",
    "comma",          "hyphen",         "period",         "slash",
    "zero",           "one",            "two",            "three",
    "four",           "five",           "six",            "seven",
    "eight",          "nine",           "colon",          "semicolon",
    "less",           "equal",          "greater",        "question",
    "at",             "A",              "B",              "C",
    "D",              "E",              "F",              "G",
    "H",              "I",              "J",              "K",
    "L",              "M",              "N",              "O",
    "P",              "Q",              "R",              "S",
    "T",              "U",              "V",              "W",
    "X",              "Y",              "Z",              "bracketleft",
    "backslash",      "bracketright",   "asciicircum",    "underscore",
    "grave",          "a",              "b",              "c",
    "d",              "e",              "f",              "g",
    "h",              "i",              "j",              "k",
    "l",              "m",              "n",              "o",
    "p",              "q",              "r",              "s",
    "t",              "u",              "v",              "w",
    "x",              "y",              "z",              "braceleft",
    "bar",            "braceright",     "asciitilde",     "Adieresis",
    "Aring",          "Ccedilla",       "Eacute",         "Ntilde",
    "Odieresis",      "Udieresis",      "aacute",         "agrave",
    "acircumflex",    "adieresis",      "atilde",         "aring",
    "ccedilla",       "eacute",         "egrave",         "ecircumflex",
    "edieresis",      "iacute",         "igrave",         "icircumflex",
    "idieresis",      "ntilde",         "oacute",         "ograve",
    "ocircumflex",    "odieresis",      "otilde",         "uacute",
    "ugrave",         "ucircumflex",    "udieresis",      "dagger",
    "degree",         "cent",           "sterling",       "section",
    "bullet",         "paragraph",      "germandbls",     "registered",
    "copyright",      "trademark",      "acute",          "dieresis",
    "notequal",       "AE",             "Oslash",         "infinity",
    "plusminus",      "lessequal",      "greaterequal",   "yen",
    "mu",             "partialdiff",    "summation",      "product",
    "pi",             "integral",       "ordfeminine",    "ordmasculine",
    "Omega",          "ae",             "oslash",         "questiondown",
    "exclamdown",     "logicalnot",     "radical",        "florin",
    "approxequal",    "increment",      "guillemotleft",  "guillemotright",
    "ellipsis",       "nbspace",        "Agrave",         "Atilde",
    "Otilde",         "OE",             "oe",             "endash",
    "emdash",         "quotedblleft",   "quotedblright",  "quoteleft",
    "quoteright",     "divide",         "lozenge",        "ydieresis",
    "Ydieresis",      "fraction",       "currency",       "guilsinglleft",
    "guilsinglright", "fi",             "fl",             "daggerdbl",
    "periodcentered", "quotesinglbase", "quotedblbase",   "perthousand",
    "Acircumflex",    "Ecircumflex",    "Aacute",         "Edieresis",
    "Egrave",         "Iacute",         "Icircumflex",    "Idieresis",
    "Igrave",         "Oacute",         "Ocircumflex",    "applelogo",
    "Ograve",         "Uacute",         "Ucircumflex",    "Ugrave",
    "dotlessi",       "circumflex",     "tilde",          "macron",
    "breve",          "dotaccent",      "ring",           "cedilla",
    "hungarumlaut",   "ogonek",         "caron",          "Lslash",
    "lslash",         "Scaron",         "scaron",         "Zcaron",
    "zcaron",         "brokenbar",      "Eth",            "eth",
    "Yacute",         "yacute",         "Thorn",          "thorn",
    "minus",          "multiply",       "onesuperior",    "twosuperior",
    "threesuperior",  "onehalf",        "onequarter",     "threequarters",
    "franc",          "Gbreve",         "gbreve",         "Idot",
    "Scedilla",       "scedilla",       "Cacute",         "cacute",
    "Ccaron",         "ccaron",         "dmacron"};

static int unicode_to_win31 (int unival)
{
    if (unival <= 0x0081) {
        return unival;
    } else if (unival >= 0x00a0 && unival <= 0x00ff) {
        return unival;
    } else {
        switch (unival) {
            case 0x008d: return 0x8d;
            case 0x008e: return 0x8e;
            case 0x008f: return 0x8f;
            case 0x0090: return 0x90;
            case 0x009d: return 0x9d;
            case 0x009e: return 0x9e;
            case 0x0152: return 0x8c;
            case 0x0153: return 0x9c;
            case 0x0160: return 0x8a;
            case 0x0161: return 0x9a;
            case 0x0178: return 0x9f;
            case 0x0192: return 0x83;
            case 0x02c6: return 0x88;
            case 0x02dc: return 0x98;
            case 0x2013: return 0x96;
            case 0x2014: return 0x97;
            case 0x2018: return 0x91;
            case 0x2019: return 0x92;
            case 0x201a: return 0x82;
            case 0x201c: return 0x93;
            case 0x201d: return 0x94;
            case 0x201e: return 0x84;
            case 0x2020: return 0x86;
            case 0x2021: return 0x87;
            case 0x2022: return 0x95;
            case 0x2026: return 0x85;
            case 0x2030: return 0x89;
            case 0x2039: return 0x8b;
            case 0x203a: return 0x9b;
            case 0x2122: return 0x99;
            default: return 0xffff;
        }
    }
}

static void handle_name ()
{
    int j, k, lang, len, platform;
    char *p, *ptr, *string_area;
    char *nbp = name_buffer;
    int found3 = 0;

    string_area = (char *)name_table + ntohs(name_table->offset);
    name_record = &(name_table->nameRecords);

    for (j=0; j<8; j++) {
        name_fields[j] = NULL;
    }

    for (j=0; j < ntohs(name_table->numberOfNameRecords); j++) {

        platform = ntohs(name_record->platformID);

        if (platform == 3) {

            found3 = 1;
            lang = ntohs(name_record->languageID) & 0xff;
            len = ntohs(name_record->stringLength);
            if (lang == 0 || lang == 9) {
                k = ntohs(name_record->nameID);
                if (k < 8) {
                    name_fields[k] = nbp;

                    p = string_area+ntohs(name_record->stringOffset);
                    for ( k = 0; k < len; k++) {
                        if (p[k] != '\0') {
                            if (p[k] == '(') {
                                *nbp = '[';
                            } else if (p[k] == ')') {
                                *nbp = ']';
                            } else {
                                *nbp = p[k];
                            }
                            nbp ++;
                        }
                    }
                    *nbp = '\0';
                    nbp ++;
                }
            }
        }
        name_record++;
    }

    string_area = (char *)name_table + ntohs(name_table->offset);
    name_record = &(name_table->nameRecords);

    if (!found3) {
        for (j=0; j < ntohs(name_table->numberOfNameRecords); j++) {

            platform = ntohs(name_record->platformID);

            if (platform == 1) {

                found3 = 1;
                lang = ntohs(name_record->languageID) & 0xff;
                len = ntohs(name_record->stringLength);
                if (lang == 0 || lang == 9) {
                    k = ntohs(name_record->nameID);
                    if (k < 8) {
                        name_fields[k] = nbp;

                        p = string_area+ntohs(name_record->stringOffset);
                        for ( k = 0; k < len; k++) {
                            if (p[k] != '\0') {
                                if (p[k] == '(') {
                                    *nbp = '[';
                                } else if (p[k] == ')') {
                                    *nbp = ']';
                                } else {
                                    *nbp = p[k];
                                }
                                nbp ++;
                            }
                        }
                        *nbp = '\0';
                        nbp ++;
                    }
                }
            }
            name_record++;
        }
    }

    if (!found3) {
        fprintf(stderr, "**** Cannot decode font name fields ****\n");
        exit(-1);
    }

    if (name_fields[6] == NULL) {
        name_fields[6] = name_fields[4];
    }

    p = name_fields[6];
    while (*p != '\0') {
        if (!isalnum(*p)) {
            *p = '_';
        }
        p++;
    }
}

static void handle_cmap ()
{
    int num_tables = ntohs(cmap_table->numberOfEncodingTables);
    BYTE *ptr;
    int i, j, k, kk, size, format, offset, seg_c2, found, set_ok;
    int platform, encoding_id;
    TTF_CMAP_ENTRY *table_entry;
    TTF_CMAP_FMT0 *encoding0;
    TTF_CMAP_FMT4 *encoding4;
    USHORT start, end, ro;
    short delta, n;

    found = 0;

    for (i=0; i<256; i++) {
        encoding[i] = 0;
    }

    for (i=0; i < num_tables && !found; i++) {
        table_entry = &(cmap_table->encodingTable[i]);
        offset = ntohl(table_entry->offset);
        encoding4 = (TTF_CMAP_FMT4 *) ((BYTE *)cmap_table + offset);
        format = ntohs(encoding4->format);
        platform = ntohs(table_entry->platformID);
        encoding_id = ntohs(table_entry->encodingID);

        if (platform == 3 && format == 4) {
            switch (encoding_id) {
                case 0: fputs("Found Symbol Encoding\n", stderr);
                        break;
                case 1: fputs("Found Unicode Encoding\n", stderr);
                        unicode = 1;
                        break;
                default: fprintf(stderr,
                                 "****MS Encoding ID %d not supported****\n",
                                 encoding_id);
                        exit(-1);
                        break;
            }

            found = 1;
            seg_c2 = ntohs(encoding4->segCountX2);
            cmap_n_segs = seg_c2 >> 1;
            ptr = (BYTE *)encoding4 + 14;
            cmap_seg_end = (USHORT *) ptr;
            cmap_seg_start = (USHORT *) (ptr + seg_c2 + 2);
            cmap_idDelta = (short *) (ptr + (seg_c2 * 2 )+ 2);
            cmap_idRangeOffset = (short *) (ptr + (seg_c2 * 3) + 2);

            for (j=0; j < cmap_n_segs-1; j++) {
                start = ntohs(cmap_seg_start[j]);
                end   = ntohs(cmap_seg_end[j]);
                delta = ntohs(cmap_idDelta[j]);
                ro    = ntohs(cmap_idRangeOffset[j]);

                for (k = start; k <= end; k++)
                {
                    if (delta != 0) {
                        n = k + delta;
                    } else {
                        n = ntohs(*( (ro >> 1) + (k - start) +
                                    &(cmap_idRangeOffset[j])));
                    }
                    if (glyph_list[n].unicode != -1) {
                        if (strcmp(glyph_list[n].name, ".notdef") != 0) {
                            fprintf(stderr,
                                    "Glyph %s has >= two encodings (A), %4.4x & %4.4x\n",
                                    glyph_list[n].name,
                                    glyph_list[n].unicode,
                                    k);
                        }
                        set_ok = 0;
                    } else {
                        set_ok = 1;
                    }
                    if (unicode) {
                        kk = unicode_to_win31 (k);
                        if (set_ok) {
                            glyph_list[n].unicode = k;
                            glyph_list[n].char_no = kk;
                        }
                        if (kk <= 0xff) encoding[kk] = n;
                    } else {
                        if ((k & 0xff00) == 0xf000)
                        {
                            encoding[k & 0x00ff] = n;
                            if (set_ok) {
                                glyph_list[n].char_no = k & 0x00ff;
                                glyph_list[n].unicode = k;
                            }
                        } else {
                            if (set_ok) {
                                glyph_list[n].char_no = k;
                                glyph_list[n].unicode = k;
                            }
                            fprintf(stderr,
                                    "Glyph %s has non-symbol encoding %4.4x\n",
                                    glyph_list[n].name,
                                    k & 0xffff);
                        }
                    }
                }
            }
        }
    }

    if (!found) {
        fputs ("No Microsoft encoding, looking for MAC encoding\n", stderr);
        for (i=0; i < num_tables && !found; i++) {
            table_entry = &(cmap_table->encodingTable[i]);
            offset = ntohl(table_entry->offset);
            encoding0 = (TTF_CMAP_FMT0 *) ((BYTE *)cmap_table + offset);
            format = ntohs(encoding0->format);
            platform = ntohs(table_entry->platformID);
            encoding_id = ntohs(table_entry->encodingID);

            if (format == 0) {
                found = 1;
                size = ntohs(encoding0->length) - 6;
                for (j=0; j<size; j++) {
                    n = encoding0->glyphIdArray[j];
                    if (glyph_list[n].char_no != -1) {
                        fprintf(stderr,
                                "Glyph %s has >= two encodings (B), %4.4x & %4.4x\n",
                                glyph_list[n].name,
                                glyph_list[n].char_no,
                                j);
                    } else {
                        glyph_list[n].char_no = j;
                        if (j < 256) {
                            encoding[j] = n;
                        }
                    }
                }
            }
        }
    }

    if (!found) {
        fprintf(stderr, "**** No Recognised Encoding Table ****\n");
        exit(-1);
    }
}

static void handle_head ()
{
    long_offsets = ntohs(head_table->indexToLocFormat);
    if (long_offsets != 0 && long_offsets != 1) {
        fprintf(stderr, "**** indexToLocFormat wrong ****\n");
        exit(-1);
    }
}

static void draw_glyf(int glyphno, int parent)
{
    int i, j, k, k1, len, first, cs, ce;
    int finished, nguide, contour_start, contour_end;
    short ncontours, n_inst, last_point;
    USHORT *contour_end_pt;
    BYTE *ptr;
    short xcoord[2000], ycoord[2000], xrel[2000], yrel[2000];
    BYTE flags[2000];

    if (long_offsets) {
        glyf_table = (TTF_GLYF *) (glyf_start + ntohl(long_loca_table[glyphno]));
        len = ntohl(long_loca_table[glyphno+1]) - ntohl(long_loca_table[glyphno]);
    } else {
        glyf_table = (TTF_GLYF *) (glyf_start + (ntohs(short_loca_table[glyphno]) << 1));
        len = (ntohs(short_loca_table[glyphno+1]) - ntohs(short_loca_table[glyphno])) << 1;
    }

    if (len <= 0) {
        fprintf(stderr,
            "**** Composite glyph %s refers to non-existent glyph %s ****\n",
            glyph_list[parent].name,
            glyph_list[glyphno].name);
        fprintf(pfa_file,
            "\n%%**** Composite glyph %s refers to non-existent glyph %s ****\n",
            glyph_list[parent].name,
            glyph_list[glyphno].name);
        return;
    }

    ncontours = ntohs(glyf_table->numberOfContours);
    if (ncontours <= 0) {
        fprintf(stderr,
                "**** Composite glyph %s refers to composite glyph %s ****\n",
                glyph_list[parent].name,
                glyph_list[glyphno].name);
        fprintf(pfa_file,
                "\n%%**** Composite glyph %s refers to composite glyph %s ****\n",
                glyph_list[parent].name,
                glyph_list[glyphno].name);
        return;
    }

    contour_end_pt = (USHORT *) ((char *)glyf_table + sizeof(TTF_GLYF));

    last_point = ntohs(contour_end_pt[ncontours-1]);
    n_inst = ntohs(contour_end_pt[ncontours]);

    ptr = ((BYTE *)contour_end_pt) + (ncontours << 1) + n_inst + 2;
    j = k = 0;
    while (k <= last_point) {
        flags[k] = ptr[j];

        if (ptr[j] & REPEAT) {
            for (k1=0; k1 < ptr[j+1]; k1++) {
                k++;
                flags[k] = ptr[j];
            }
            j++;
        }
        j++; k++;
    }

    for (k=0; k <= last_point; k++) {
        if (flags[k] & XSHORT) {
            if (flags[k] & XSAME) {
                xrel[k] = ptr[j];
            } else {
                xrel[k] = - ptr[j];
            }
            j++;
        } else if (flags[k] & XSAME) {
            xrel[k] = 0;
        } else {
            xrel[k] = ptr[j] * 256 + ptr[j+1];
            j += 2;
        }
        if (k==0) {
            xcoord[k] = xrel[k];
        } else {
            xcoord[k] = xrel[k] + xcoord[k-1];
        }
    }

    for (k=0; k <= last_point; k++) {
        if (flags[k] & YSHORT) {
            if (flags[k] & YSAME) {
                yrel[k] = ptr[j];
            } else {
                yrel[k] = - ptr[j];
            }
            j++;
        } else if (flags[k] & YSAME) {
            yrel[k] = 0;
        } else {
            yrel[k] = ptr[j] * 256 + ptr[j+1];
            j += 2;
        }
        if (k==0) {
            ycoord[k] = yrel[k];
        } else {
            ycoord[k] = yrel[k] + ycoord[k-1];
        }
    }

    i = j = 0;
    first = 1;

    while (i <= ntohs(contour_end_pt[ncontours-1])) {
        contour_end = ntohs(contour_end_pt[j]);

        if (first) {
            fprintf(pfa_file, "%d %d moveto\n", xcoord[i], ycoord[i]);
            ncurves ++;
            contour_start = i;
            first = 0;
        } else if (flags[i] & ONOROFF) {
            fprintf(pfa_file, "%d %d lineto\n", xcoord[i], ycoord[i]);
            ncurves ++;
        } else {
            cs = i-1;
            finished = nguide = 0;
            while (!finished) {
                if (i == contour_end+1) {
                    ce = contour_start;
                    finished = 1;
                } else if (flags[i] & ONOROFF) {
                    ce = i;
                    finished = 1;
                } else {
                    i++;
                    nguide++;
                }
            }

            switch (nguide) {
                case 0: fprintf( pfa_file,"%d %d lineto\n",
                                 xcoord[ce], ycoord[ce]);
                        ncurves ++;
                        break;

                case 1: fprintf( pfa_file, "%d %d %d %d %d %d curveto\n",
                                (xcoord[cs]+2*xcoord[cs+1])/3,
                                (ycoord[cs]+2*ycoord[cs+1])/3,
                                (2*xcoord[cs+1]+xcoord[ce])/3,
                                (2*ycoord[cs+1]+ycoord[ce])/3,
                                xcoord[ce], ycoord[ce]);
                        ncurves ++;
                        break;

                case 2: fprintf( pfa_file, "%d %d %d %d %d %d curveto\n",
                                (-xcoord[cs]+4*xcoord[cs+1])/3,
                                (-ycoord[cs]+4*ycoord[cs+1])/3,
                                (4*xcoord[cs+2]-xcoord[ce])/3,
                                (4*ycoord[cs+2]-ycoord[ce])/3,
                                xcoord[ce], ycoord[ce]);
                        ncurves ++;
                        break;

                case 3: fprintf( pfa_file, "%d %d %d %d %d %d curveto\n",
                                (xcoord[cs]+2*xcoord[cs+1])/3,
                                (ycoord[cs]+2*ycoord[cs+1])/3,
                                (5*xcoord[cs+1]+xcoord[cs+2])/6,
                                (5*ycoord[cs+1]+ycoord[cs+2])/6,
                                (xcoord[cs+1]+xcoord[cs+2])/2,
                                (ycoord[cs+1]+ycoord[cs+2])/2);
                        fprintf( pfa_file, "%d %d %d %d %d %d curveto\n",
                                (xcoord[cs+1]+5*xcoord[cs+2])/6,
                                (ycoord[cs+1]+5*ycoord[cs+2])/6,
                                (5*xcoord[cs+2]+xcoord[cs+3])/6,
                                (5*ycoord[cs+2]+ycoord[cs+3])/6,
                                (xcoord[cs+3]+xcoord[cs+2])/2,
                                (ycoord[cs+3]+ycoord[cs+2])/2);
                        fprintf( pfa_file, "%d %d %d %d %d %d curveto\n",
                                (xcoord[cs+2]+5*xcoord[cs+3])/6,
                                (ycoord[cs+2]+5*ycoord[cs+3])/6,
                                (2*xcoord[cs+3]+xcoord[ce])/3,
                                (2*ycoord[cs+3]+ycoord[ce])/3,
                                xcoord[ce], ycoord[ce]);
                        ncurves += 3;
                        break;

                default:k1 = cs + nguide;

                        fprintf( pfa_file, "%d %d %d %d %d %d curveto\n",
                                (xcoord[cs]+2*xcoord[cs+1])/3,
                                (ycoord[cs]+2*ycoord[cs+1])/3,
                                (5*xcoord[cs+1]+xcoord[cs+2])/6,
                                (5*ycoord[cs+1]+ycoord[cs+2])/6,
                                (xcoord[cs+1]+xcoord[cs+2])/2,
                                (ycoord[cs+1]+ycoord[cs+2])/2);
                        for (k = cs+2; k <= k1-1; k++) {
                            fprintf( pfa_file, "%d %d %d %d %d %d curveto\n",
                                    (xcoord[k-1]+5*xcoord[k])/6,
                                    (ycoord[k-1]+5*ycoord[k])/6,
                                    (5*xcoord[k]+xcoord[k+1])/6,
                                    (5*ycoord[k]+ycoord[k+1])/6,
                                    (xcoord[k]+xcoord[k+1])/2,
                                    (ycoord[k]+ycoord[k+1])/2);
                        }
                        fprintf( pfa_file, "%d %d %d %d %d %d curveto\n",
                                (xcoord[k1-1]+5*xcoord[k1])/6,
                                (ycoord[k1-1]+5*ycoord[k1])/6,
                                (2*xcoord[k1]+xcoord[ce])/3,
                                (2*ycoord[k1]+ycoord[ce])/3,
                                xcoord[ce], ycoord[ce]);
                        ncurves += nguide;
                        break;
            }
        }
        if (i >= contour_end) {
            fprintf(pfa_file, " closepath ");
            first = 1;
            i = contour_end + 1;
            j++;
        } else {
            i++;
        }
    }
}

static float f2dot14 (short x)
{
    short y = ntohs(x);
    return (y >> 14) + ((y & 0x3fff) / 16384.0);
}

static void do_glyf(int glyphno)
{
    int len, c;
    short ncontours;
    USHORT flagbyte, glyphindex, xscale, yscale, scale01, scale10;
    SHORT arg1, arg2;
    BYTE *ptr;
    char *bptr;
    SHORT *sptr;
    float matrix[4];

    ncurves = 0;

    if (long_offsets) {
        glyf_table = (TTF_GLYF *) (glyf_start + ntohl(long_loca_table[glyphno]));
        len = ntohl(long_loca_table[glyphno+1]) - ntohl(long_loca_table[glyphno]);
    } else {
        glyf_table = (TTF_GLYF *) (glyf_start + (ntohs(short_loca_table[glyphno]) << 1));
        len = (ntohs(short_loca_table[glyphno+1]) - ntohs(short_loca_table[glyphno])) << 1;
    }

    if (unicode) {
        fprintf(pfa_file,
            "/%s { %% %d - U+%4.4x\n",
            glyph_list[glyphno].name,
            glyphno,
            (unsigned short)glyph_list[glyphno].unicode);
    } else {
        fprintf(pfa_file,
            "/%s { %% %d - 0x%2.2x\n",
            glyph_list[glyphno].name,
            glyphno,
            (unsigned short)glyph_list[glyphno].char_no);
    }

    c = glyph_list[glyphno].char_no;
    fprintf(afm_file, "C %d ; WX %.0f ; N %s ; B %.0f %.0f %.0f %.0f ;\n",
        c < 256 ? c : -1,
        scale_factor * glyph_list[glyphno].width,
        glyph_list[glyphno].name,
        scale_factor * (short)ntohs(glyf_table->xMin),
        scale_factor * (short)ntohs(glyf_table->yMin),
        scale_factor * (short)ntohs(glyf_table->xMax),
        scale_factor * (short)ntohs(glyf_table->yMax));

    fprintf(pfa_file, "%d 0 %hd %hd %hd %hd setcachedevice\n",
        glyph_list[glyphno].width,
        (short)ntohs(glyf_table->xMin),
        (short)ntohs(glyf_table->yMin),
        (short)ntohs(glyf_table->xMax),
        (short)ntohs(glyf_table->yMax));

    if (len != 0) {
        ncontours = ntohs(glyf_table->numberOfContours);

        if (ncontours <= 0) {
            ptr = ((BYTE *)glyf_table + sizeof(TTF_GLYF));
            sptr = (SHORT *) ptr;
            do {
                flagbyte = ntohs(*sptr); sptr ++;
                glyphindex = ntohs(*sptr); sptr ++;
                fprintf(pfa_file, "%% flags %x glyph %s\n",
                        flagbyte, glyph_list[glyphindex].name);

                if (flagbyte & ARG_1_AND_2_ARE_WORDS) {
                    arg1 = ntohs(*sptr); sptr++;
                    arg2 = ntohs(*sptr); sptr++;
                } else {
                    bptr = (char *)sptr;
                    arg1 = (signed char)bptr[0];
                    arg2 = (signed char)bptr[1];
                    sptr ++;
                }
                matrix[1] = matrix[2] = 0.0;

                if (flagbyte & WE_HAVE_A_SCALE) {
                    matrix[0] = matrix[3] = f2dot14(*sptr);
                    sptr ++;
                }
                else if (flagbyte & WE_HAVE_AN_X_AND_Y_SCALE) {
                    matrix[0] = f2dot14(*sptr); sptr ++;
                    matrix[3] = f2dot14(*sptr); sptr ++;
                }
                else if (flagbyte & WE_HAVE_A_TWO_BY_TWO) {
                    matrix[0] = f2dot14(*sptr); sptr ++;
                    matrix[1] = f2dot14(*sptr); sptr ++;
                    matrix[2] = f2dot14(*sptr); sptr ++;
                    matrix[3] = f2dot14(*sptr); sptr ++;
                } else {
                    matrix[0] = matrix[3] = 1.0;
                }

                fprintf(pfa_file,
                        "matrix currentmatrix\n[ %9.7f %9.7f %9.7f %9.7f %hd %hd ] concat\n",
                        matrix[0], matrix[1], matrix[2], matrix[3],
                        arg1, arg2);

                draw_glyf(glyphindex, glyphno);

                /*fputs("setmatrix closepath\n", pfa_file);*/
                fputs("setmatrix\n", pfa_file);

            } while (flagbyte & MORE_COMPONENTS);
        } else {
            draw_glyf(glyphno, glyphno);
            /*fprintf( pfa_file, "closepath ");*/
        }
        if (ncurves > 100) {
            fprintf(stderr,
                    "**Glyf %s is too long, may have to be removed**\n",
                    glyph_list[glyphno].name);
            fprintf(pfa_file,
                    "\n%%**Glyf %s is too long, may have to be removed**\n",
                    glyph_list[glyphno].name);
        }
    }
    fprintf(pfa_file, "fill } bind def\n");
}

static void handle_hmtx()
{
    int i;
    int n_hmetrics = ntohs(hhea_table->numberOfHMetrics);
    GLYPH *g;
    LONGHORMETRIC *hmtx_entry = hmtx_table;
    FWORD *lsblist;

    for (i = 0; i < n_hmetrics; i++) {
        g = &(glyph_list[i]);
        g->width = ntohs(hmtx_entry->advanceWidth);
        g->lsb = ntohs(hmtx_entry->lsb);
        hmtx_entry++;
    }

    lsblist = (FWORD *)hmtx_entry;
    hmtx_entry--;

    for (i = n_hmetrics; i < numglyphs; i++) {
        g = &(glyph_list[i]);
        g->width = ntohs(hmtx_entry->advanceWidth);
        g->lsb = ntohs(lsblist [i-n_hmetrics]);
    }
}

static void handle_post()
{
    int i, len, n, found;
    unsigned int format;
    USHORT *name_index;
    char *ptr;
    char **ps_name_ptr = (char **) malloc (numglyphs * sizeof (char *));
    int *ps_name_len = (int *) malloc (numglyphs * sizeof (int));
    int n_ps_names;

    format = ntohl(post_table->formatType);

    if (format == 0x00010000) {
        for (i=0; i<258; i++) {
            glyph_list[i].name = mac_glyph_names[i];
        }
    } else if (format == 0x00020000) {
        n = ntohs(post_table->numGlyphs);
        if (numglyphs != n) {
            fprintf(stderr, "**** Postscript table size mismatch %d/%d ****\n", n, numglyphs);
            exit(-1);
        }
        ptr = (char *)post_table + 34 + (numglyphs << 1);
        n_ps_names = 0;
        while (*ptr > 0) {
            len = ps_name_len[n_ps_names] = *ptr;
            ps_name_ptr[n_ps_names] = ptr+1;
            *ptr = '\0';
            n_ps_names ++;
            ptr += len + 1;
        }
        *ptr = '\0';
        /* for (i=0; i<n_ps_names; i++) {
            fprintf(stderr, "i=%d, len=%d, name=%s\n",
                    i, ps_name_len[i], ps_name_ptr[i]);
        }*/
        name_index = &(post_table->glyphNameIndex);
        for (i=0; i<numglyphs; i++) {
            n = ntohs(name_index[i]);
            if (n < 258) {
                glyph_list[i].name = mac_glyph_names[n];
            } else if (n < 258 + n_ps_names) {
                glyph_list[i].name = ps_name_ptr[n-258];
            } else {
                glyph_list[i].name = malloc(10);
                sprintf(glyph_list[i].name, "_%d", n);
                fprintf(stderr,
                        "**** Glyph No. %d has no postscript name, becomes %s ****\n",
                        i, glyph_list[n].name);
            }
        }
    } else if (format == 0x00030000) {
        fputs ("No postscript table, using default\n", stderr);
        ps_fmt_3 = 1;
    } else if (format == 0x00028000) {
        ptr = (char *)&(post_table->numGlyphs);
        for (i=0; i<numglyphs; i++) {
            glyph_list[i].name = mac_glyph_names[i + ptr[i]];
        }
    } else {
        fprintf(stderr,
                "**** Postscript table in wrong format %x ****\n",
                format);
        exit(-1);
    }

    if (!ps_fmt_3) {
        for (n = 0; n < numglyphs; n++) {
            found = 0;
            for (i = 0; i < n && !found; i++) {
                if (strcmp(glyph_list[i].name, glyph_list[n].name) == 0) {
                    glyph_list[n].name = malloc(10);
                    sprintf(glyph_list[n].name, "_%d", n);
                    fprintf(stderr,
                            "Glyph %d has the same name as %d: (%s), changing to %s\n",
                            n, i,
                            glyph_list[i].name,
                            glyph_list[n].name);
                    found = 1;
                }
            }
        }
    }
}

static void handle_kern()
{
    TTF_KERN_SUB *subtable;
    TTF_KERN_ENTRY *kern_entry;
    int i, j;
    int ntables = ntohs(kern_table->nTables);
    int npairs;
    char *ptr = (char *)kern_table + 4;

    for (i=0; i < ntables; i++) {
        subtable = (TTF_KERN_SUB *)ptr;
        if ((ntohs(subtable->coverage) & 0xff00) == 0) {
            npairs = (short)ntohs(subtable->nPairs);
            fprintf(afm_file, "StartKernPairs %hd\n", npairs);
            kern_entry = (TTF_KERN_ENTRY *)(ptr + sizeof(TTF_KERN_SUB));
            for (j=0; j<npairs; j++) {
                fprintf(afm_file, "KPX %s %s %.0f\n",
                        glyph_list[ntohs(kern_entry->left)].name,
                        glyph_list[ntohs(kern_entry->right)].name,
                        scale_factor * (short) ntohs(kern_entry->value));
                kern_entry ++;
            }
            fprintf(afm_file, "EndKernPairs\n");
        }
        ptr += subtable->length;
    }
}

main (int argc, char **argv)
{
    int i;
    time_t now;
    float italic_angle;
    struct stat statbuf;
    char filename[100];

    if (argc != 3) {
        fputs("ttf2pfa <ttf-file> <fontname>\n", stderr);
        exit(-1);
    }

    if (stat(argv[1], &statbuf) == -1) {
        fprintf(stderr, "**** Cannot access %s ****\n", argv[1]);
        exit(-1);
    }

    if ((filebuffer = malloc (statbuf.st_size)) == NULL) {
        fprintf(stderr, "**** Cannot malloc space for file ****\n");
        exit(-1);
    }

    if ((ttf_file=open(argv[1], O_RDONLY, 0)) == -1) {
        fprintf(stderr, "**** Cannot open %s ****\n", argv[1]);
        exit(-1);
    } else {
        fprintf(stderr, "Processing file %s\n", argv[1]);
    }

    if (read (ttf_file, filebuffer, statbuf.st_size) != statbuf.st_size) {
        fprintf(stderr, "**** Could not read whole file ****\n");
        exit(-1);
    }

    directory = (TTF_DIRECTORY *) filebuffer;

    if (ntohl(directory->sfntVersion) != 0x00010000) {
        fprintf(stderr,
                "****Unknown File Version number [%x], or not a TrueType file****\n",
                directory->sfntVersion);
        exit(-1);
    }

	if(argv[2][0]=='-' && argv[2][1]==0) {
		pfa_file=stdout;
		if ((afm_file = fopen("/dev/null", "w+")) == NULL) {
			fprintf(stderr, "**** Cannot create %s ****\n", filename);
			exit(-1);
		}
	} else {
		sprintf(filename, "%s.pfa", argv[2]) ;
		if ((pfa_file = fopen(filename, "w+")) == NULL) {
			fprintf(stderr, "**** Cannot create %s ****\n", filename);
			exit(-1);
		} else {
			fprintf(stderr, "Creating file %s\n", filename);
		}

		sprintf(filename, "%s.afm", argv[2]) ;
		if ((afm_file = fopen(filename, "w+")) == NULL) {
			fprintf(stderr, "**** Cannot create %s ****\n", filename);
			exit(-1);
		}
	}

    dir_entry = &(directory->list);

    for (i=0; i < ntohs(directory->numTables); i++) {

        if (memcmp(dir_entry->tag, "name", 4) == 0) {
            name_table = (TTF_NAME *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "head", 4) == 0) {
            head_table = (TTF_HEAD *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "hhea", 4) == 0) {
            hhea_table = (TTF_HHEA *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "post", 4) == 0) {
            post_table = (TTF_POST_HEAD *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "glyf", 4) == 0) {
            glyf_start = (BYTE *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "cmap", 4) == 0) {
            cmap_table = (TTF_CMAP *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "kern", 4) == 0) {
            kern_table = (TTF_KERN *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "maxp", 4) == 0) {
            maxp_table = (TTF_MAXP *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "hmtx", 4) == 0) {
            hmtx_table = (LONGHORMETRIC *) (filebuffer+ntohl(dir_entry->offset));
        } else if (memcmp(dir_entry->tag, "loca", 4) == 0) {
            long_loca_table = (ULONG *) (filebuffer+ntohl(dir_entry->offset));
            short_loca_table = (USHORT *) long_loca_table;
        } else if (memcmp(dir_entry->tag, "EBDT", 4) == 0 ||
                   memcmp(dir_entry->tag, "EBLC", 4) == 0 ||
                   memcmp(dir_entry->tag, "EBSC", 4) == 0) {
            fprintf (stderr, "Font contains bitmaps\n");
        }
        dir_entry++;
    }

    handle_name();

    handle_head();

    numglyphs = ntohs(maxp_table->numGlyphs);
    fprintf(stderr, "numglyphs = %d\n", numglyphs);

    glyph_list = (GLYPH *) malloc (numglyphs * sizeof (GLYPH));

    for (i=0; i<numglyphs; i++) {
        glyph_list[i].char_no = -1;
        glyph_list[i].unicode = -1;
        glyph_list[i].name = Unknown_glyph;
    }

    handle_post();

    handle_hmtx();

    handle_cmap();

    if (ps_fmt_3) {
        for (i=0; i<255; i++) {
            if (encoding[i] != 0) {
                glyph_list[encoding[i]].name = ISOLatin1Encoding[i];
            } else {
                glyph_list[encoding[i]].name = ".notdef";
            }
        }
    }

    fprintf(pfa_file, "%%!PS-Adobe-3.0 Resource-Font\n");
    time(&now);
    fprintf(pfa_file, "%%%%CreationDate: %s", ctime(&now));
    fprintf(pfa_file, "%%%%BeginFont: %s\n", name_fields[6]);
    fprintf(pfa_file, "%% Converted from TrueType font %s by ttf2pfa program\n%%\n", argv[1]);

    fprintf(afm_file, "StartFontMetrics 4.1\n");
    fprintf(pfa_file, "20 dict begin\n/FontType 3 def\n");

    fprintf(afm_file, "FontName %s\n", name_fields[6]);
    fprintf(stderr, "FontName %s\n", name_fields[6]);
    fprintf(pfa_file, "/FontName (%s) def\n", name_fields[6]);

    fprintf(pfa_file, "/FontInfo 9 dict dup begin\n");

    fprintf(pfa_file, "/FullName (%s) def\n", name_fields[4]);
    fprintf(afm_file, "FullName %s\n", name_fields[4]);

    fprintf(pfa_file, "/Notice (%s) def\n", name_fields[0]);
    fprintf(afm_file, "Notice %s\n", name_fields[0]);

    fprintf(pfa_file, "/FamilyName (%s) def\n", name_fields[1]);
    fprintf(afm_file, "FamilyName %s\n", name_fields[1]);

    fprintf(pfa_file, "/Weight (%s) def\n", name_fields[2]);
    fprintf(afm_file, "Weight %s\n", name_fields[2]);

    fprintf(pfa_file, "/version (%s) def\n", name_fields[5]);
    fprintf(afm_file, "Version %s\n", name_fields[5]);

    fprintf(afm_file, "Characters %d\n", numglyphs);

    italic_angle = (short)(ntohs(post_table->italicAngle.upper)) +
                    (ntohs(post_table->italicAngle.lower) / 65536.0);
    fprintf(pfa_file, "/italicAngle %f def\n", italic_angle);
    fprintf(afm_file, "ItalicAngle %f\n", italic_angle);

    scale_factor = 1000.0 / ntohs(head_table->unitsPerEm);

    fprintf(afm_file, "Ascender %.0f\n",
            scale_factor * (short)ntohs(hhea_table->ascender));
    fprintf(afm_file, "Descender %.0f\n",
            scale_factor * (short)ntohs(hhea_table->descender));

    fprintf(pfa_file, "/underlineThickness %hd def\n",
            (short)ntohs(post_table->underlineThickness));
    fprintf(afm_file, "UnderlineThickness %.0f\n",
            scale_factor * (short)ntohs(post_table->underlineThickness));

    fprintf(pfa_file, "/underlinePosition %hd def\n",
            (short)ntohs(post_table->underlinePosition));
    fprintf(afm_file, "UnderlinePosition %.0f\n",
            scale_factor * (short)ntohs(post_table->underlinePosition));

    fprintf(pfa_file, "/isFixedPitch %s def end def\n",
            ntohl(post_table->isFixedPitch) ? "true" : "false" );
    fprintf(afm_file, "IsFixedPitch %s\n",
            ntohl(post_table->isFixedPitch) ? "true" : "false" );

    fprintf(pfa_file, "/FontMatrix [%9.7f 0 0 %9.7f 0 0] def\n",
            scale_factor/1000.0, scale_factor/1000.0);

    fprintf(pfa_file, "/FontBBox [%hd %hd %hd %hd] def\n",
            (short)ntohs(head_table->xMin),
            (short)ntohs(head_table->yMin),
            (short)ntohs(head_table->xMax),
            (short)ntohs(head_table->yMax));

    fprintf(afm_file, "FontBBox %.0f %.0f %.0f %.0f\n",
            scale_factor * (short)ntohs(head_table->xMin),
            scale_factor * (short)ntohs(head_table->yMin),
            scale_factor * (short)ntohs(head_table->xMax),
            scale_factor * (short)ntohs(head_table->yMax));

    fprintf(pfa_file, "/Encoding [\n");
    for (i=0; i<256; i++) {
        fprintf(pfa_file,
                "/%s ",
                glyph_list[encoding[i]].name);
        if (i%4 == 3) {
            fprintf(pfa_file, "%% 0x%x\n", i-3);
        }
    }
    fprintf(pfa_file,
            "] def\n/CharProcs %d dict def CharProcs begin\n",
            numglyphs+1);

    fprintf(afm_file, "StartCharMetrics %d\n", numglyphs);

    for (i=0; i<numglyphs; i++) {
        do_glyf(i);
    }

    fprintf(afm_file, "EndCharMetrics\n");

    if (kern_table != NULL) {
        fprintf(afm_file, "StartKernData\n");
        handle_kern();
        fprintf(afm_file, "EndKernData\n");
    } else {
        fputs("No Kerning data\n", stderr);
    }

    fprintf(pfa_file, "end\n/BuildGlyph {\n");
    fprintf(pfa_file, "exch /CharProcs get exch\n");
    fprintf(pfa_file, "2 copy known not {pop /.notdef} if ");
    fprintf(pfa_file, "get exec } bind def\n");
    fprintf(pfa_file, "/BuildChar { 1 index /Encoding get exch get\n");
    fprintf(pfa_file, "1 index /Encoding get exec } bind def\n");
    fprintf(pfa_file,
            "currentdict end /%s exch definefont pop\n",
            name_fields[6]);

    fprintf(afm_file, "EndFontMetrics\n");
    fprintf(pfa_file, "%%%%EndFont\n");

    fclose(afm_file);
    fclose(pfa_file);

    fprintf(stderr, "Finished - font files created\n");
}
