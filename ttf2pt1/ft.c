/*
 * The font parser using the FreeType library version 2.
 *
 * see COPYRIGHT
 *
 */

#ifdef USE_FREETYPE

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <sys/types.h>
#include <freetype/freetype.h>
#include <freetype/ftglyph.h>
#include <freetype/ftnames.h>
#include <freetype/ttnameid.h>
#include <freetype/ftoutln.h>
#include "pt1.h"
#include "global.h"

/* prototypes of call entries */
static void openfont(char *fname, char *arg);
static void closefont( void);
static int getnglyphs ( void);
static int glnames( GLYPH *glyph_list);
static void glmetrics( GLYPH *glyph_list);
static int glenc( GLYPH *glyph_list, int *encoding, int *unimap);
static void fnmetrics( struct font_metrics *fm);
static void glpath( int glyphno, GLYPH *glyph_list);
static void prkern( GLYPH *glyph_list, FILE *afm_file);

/* globals */

/* front-end descriptor */
struct frontsw freetype_sw = {
	/*name*/       "ft",
	/*descr*/      "based on the FreeType library",
	/*suffix*/     { "ttf", "TTF" },
	/*open*/       openfont,
	/*close*/      closefont,
	/*nglyphs*/    getnglyphs,
	/*glnames*/    glnames,
	/*glmetrics*/  glmetrics,
	/*glenc*/      glenc,
	/*fnmetrics*/  fnmetrics,
	/*glpath*/     glpath,
	/*prkern*/     prkern,
};

/* statics */

static FT_Library library;
static FT_Face face;

/* SFNT functions do not seem to be included by default in FT2beta8 */
#undef ENABLE_SFNT

/*
 * Open font and prepare to return information to the main driver.
 * May print error and warning messages.
 * Exit on error.
 */

static void
openfont(
	char *fname,
	char *arg /* unused now */
)
{
	FT_Error error;

	if( FT_Init_FreeType( &library ) ) {
		fprintf(stderr, "** FreeType initialization failed\n");
		exit(1);
	}

	if( error = FT_New_Face( library, fname, 0, &face ) ) {
		if ( error == FT_Err_Unknown_File_Format )
			fprintf(stderr, "**** %s has format unknown to FreeType\n", fname);
		else
			fprintf(stderr, "**** Cannot access %s ****\n", fname);
		exit(1);
	}

	if(FT_HAS_FIXED_SIZES(face)) {
		WARNING_1 fprintf(stderr, "Font contains bitmaps\n");
	}
	if(FT_HAS_MULTIPLE_MASTERS(face)) {
		WARNING_1 fprintf(stderr, "Font contains multiple masters, using default\n");
	}

	if(ISDBG(FT)) fprintf(stderr," %d units per EM\n", face->units_per_EM);
}

/*
 * Close font.
 * Exit on error.
 */

static void
closefont(
	void
)
{
	if( FT_Done_Face(face) ) {
		WARNING_1 fprintf(stderr, "Errors when closing the font file, ignored\n");
	}
	if( FT_Done_FreeType(library) ) {
		WARNING_1 fprintf(stderr, "Errors when stopping FreeType, ignored\n");
	}
}

/*
 * Get the number of glyphs in font.
 */

static int
getnglyphs (
	void
)
{
	if(ISDBG(FT)) fprintf(stderr, "%d glyphs in font\n", face->num_glyphs);
	return (int)face->num_glyphs;
}

/*
 * Get the names of the glyphs.
 * Returns 0 if the names were assigned, non-zero if the font
 * provides no glyph names.
 */

static int
glnames(
	GLYPH *glyph_list
)
{
#define MAX_NAMELEN	1024
	unsigned char bf[1024];
	int i;

	if( ! FT_HAS_GLYPH_NAMES(face) ) {
		WARNING_1 fprintf(stderr, "Font has no glyph names\n");
		return 1;
	}

	for(i=0; i < face->num_glyphs; i++) {
		if( FT_Get_Glyph_Name(face, i, bf, MAX_NAMELEN) || bf[0]==0 ) {
			sprintf(bf, "_%d", i);
			WARNING_2 fprintf(stderr,
				"**** Glyph No. %d has no postscript name, becomes %s ****\n",
				i, bf);
		}
		glyph_list[i].name = strdup(bf);
		if(ISDBG(FT)) fprintf(stderr, "%d has name %s\n", i, bf);
		if (glyph_list[i].name == NULL) {
			fprintf (stderr, "****malloc failed %s line %d\n", __FILE__, __LINE__);
			exit(255);
		}
	}
	return 0;
}

/*
 * Get the metrics of the glyphs.
 */

static void
glmetrics(
	GLYPH *glyph_list
)
{
	GLYPH          *g;
	int i;
	FT_Glyph_Metrics *met;
	FT_BBox bbox;
	FT_Glyph gly;

	for(i=0; i < face->num_glyphs; i++) {

		/* XXX workaround for a FT2beta8 bug */
		if( FT_Set_Char_Size(face,  0, face->units_per_EM, 1<<6, 1<<6) ) {
			fprintf(stderr, "**** Cannot set the EM size ****\n");
			exit(1);
		}

		if( FT_Load_Glyph(face, i, FT_LOAD_NO_BITMAP) ) {
			fprintf(stderr, "Can't load glyph %s, skipped\n", g->name);
			continue;
		}

		g = &(glyph_list[i]);
		met = &face->glyph->metrics;

		if(FT_HAS_HORIZONTAL(face)) {
			g->width = met->horiAdvance;
			g->lsb = met->horiBearingX;
		} else {
			WARNING_2 fprintf(stderr, "Glyph %s has no horizontal metrics, guessed them\n", g->name);
			g->width = met->width;
			g->lsb = 0;
		}

		/* XXX workaround for a FT2beta8 bug */
		if( FT_Set_Char_Size(face,  0, face->units_per_EM<<6, 1<<6, 1<<6) ) {
			fprintf(stderr, "**** Cannot set the EM size ****\n");
			exit(1);
		}
		if( FT_Load_Glyph(face, i, FT_LOAD_NO_BITMAP) ) {
			fprintf(stderr, "Can't load glyph %s, skipped\n", g->name);
			continue;
		}

		if( FT_Get_Glyph(face->glyph, &gly) ) {
			fprintf(stderr, "Can't access glyph %s bbox, skipped\n", g->name);
			continue;
		}

		FT_Glyph_Get_CBox(gly, ft_glyph_bbox_pixels, &bbox);
		g->xMin = bbox.xMin;
		g->yMin = bbox.yMin;
		g->xMax = bbox.xMax;
		g->yMax = bbox.yMax;

		g->ttf_pathlen = face->glyph->outline.n_points;
	}
}

/*
 * Get the original encoding of the font. 
 * Returns 1 for if the original encoding is Unicode, 2 if the
 * original encoding is other 16-bit, 0 if 8-bit.
 */

static int
glenc(
	GLYPH *glyph_list,
	int *encoding,
	int *unimap
)
{
	int i, e, type;
	unsigned code;

	type = 0;
	for(e=0; e < face->num_charmaps; e++) {
		if(face->charmaps[e]->platform_id == 3) {
			switch(face->charmaps[e]->encoding_id) {
			case 0:
				WARNING_1 fputs("Found Symbol Encoding\n", stderr);
				break;
			case 1:
				WARNING_1 fputs("Found Unicode Encoding\n", stderr);
				type = 1;
				break;
			default:
				WARNING_1 {
					fprintf(stderr,
					"****MS Encoding ID %d not supported****\n",
						face->charmaps[e]->encoding_id);
					fputs("Treating it like Symbol encoding\n", stderr);
				}
				break;
			}
			break;
		}
	}
	if(e >= face->num_charmaps) {
		WARNING_1 fputs("No Microsoft encoding, using first encoding available\n", stderr);
		e = 0;
	}
	if(forceunicode) {
		WARNING_1 fputs("Forcing Unicode Encoding\n", stderr);
	}
	
	if( FT_Set_Charmap(face, face->charmaps[e]) ) {
		fprintf(stderr, "**** Cannot set charmap in FreeType ****\n");
		exit(1);
	}

	for(i=0; i<256; i++) {
		if(encoding[i] != -1)
			continue;
		if(type == 1 || forceunicode) {
			code = unimap[i];
			if(code == (unsigned) -1)
				continue;
		} else
			code = i;

		code = FT_Get_Char_Index(face, code);
		if(0 && ISDBG(FT)) fprintf(stderr, "code of %3d is %3d\n", i, code);
		if(code == 0)
			continue; /* .notdef */
		encoding[i] = code;
	}

	return type;
}

/*
 * Get the font metrics
 */
static void 
fnmetrics(
	struct font_metrics *fm
)
{
	char *str;
	static char *fieldstocheck[3];
#ifdef ENABLE_SFNT
	FT_SfntName sn;
#endif /* ENABLE_SFNT */
	int i;

	fm->italic_angle = 0.0; /* FreeType hides the angle */
	fm->underline_position = face->underline_position;
	fm->underline_thickness = face->underline_thickness;
	fm->is_fixed_pitch = FT_IS_FIXED_WIDTH(face);

	fm->ascender = face->ascender;
	fm->descender = -face->descender;

	fm->units_per_em =  face->units_per_EM;

	fm->bbox[0] = face->bbox.xMin;
	fm->bbox[1] = face->bbox.yMin;
	fm->bbox[2] = face->bbox.xMax;
	fm->bbox[3] = face->bbox.yMax;

#ifdef ENABLE_SFNT
	if( FT_Get_Sfnt_Name(face, TT_NAME_ID_COPYRIGHT, &sn) )
#endif /* ENABLE_SFNT */
		fm->name_copyright = "";
#ifdef ENABLE_SFNT
	else
		fm->name_copyright = sn.string;
#endif /* ENABLE_SFNT */

	fm->name_family = face->family_name;

	fm->name_style = face->style_name;
	if(fm->name_style == NULL)
		fm->name_style = "";

#ifdef ENABLE_SFNT
	if( FT_Get_Sfnt_Name(face, TT_NAME_ID_FULL_NAME, &sn) ) 
#endif /* ENABLE_SFNT */
	{
		int len;

		len = strlen(fm->name_family) + strlen(fm->name_style) + 2;
		if(( fm->name_full = malloc(len) )==NULL) {
			fprintf (stderr, "****malloc failed %s line %d\n", __FILE__, __LINE__);
			exit(255);
		}
		strcpy(fm->name_full, fm->name_family);
		if(strlen(fm->name_style) != 0) {
			strcat(fm->name_full, " ");
			strcat(fm->name_full, fm->name_style);
		}
	} 
#ifdef ENABLE_SFNT
	else
		fm->name_full = sn.string;
#endif /* ENABLE_SFNT */

#ifdef ENABLE_SFNT
	if( FT_Get_Sfnt_Name(face, TT_NAME_ID_VERSION_STRING, &sn) )
#endif /* ENABLE_SFNT */
		fm->name_version = "1.0";
#ifdef ENABLE_SFNT
	else
		fm->name_version = sn.string;
#endif /* ENABLE_SFNT */

#ifdef ENABLE_SFNT
	if( FT_Get_Sfnt_Name(face, TT_NAME_ID_PS_NAME , &sn) ) {
#endif /* ENABLE_SFNT */
		if(( fm->name_ps = strdup(fm->name_full) )==NULL) {
			fprintf (stderr, "****malloc failed %s line %d\n", __FILE__, __LINE__);
			exit(255);
		}
#ifdef ENABLE_SFNT
	} else
		fm->name_ps = sn.string;
#endif /* ENABLE_SFNT */

	/* guess the boldness from the font names */
	fm->force_bold=0;

	fieldstocheck[0] = fm->name_style;
	fieldstocheck[1] = fm->name_full;
	fieldstocheck[2] = fm->name_ps;

	for(i=0; !fm->force_bold && i<sizeof fieldstocheck /sizeof(fieldstocheck[0]); i++) {
		str=fieldstocheck[i];
		for(i=0; str[i]!=0; i++) {
			if( (str[i]=='B'
				|| str[i]=='b' 
					&& ( i==0 || !isalpha(str[i-1]) )
				)
			&& !strncmp("old",&str[i+1],3)
			&& !islower(str[i+4])
			) {
				fm->force_bold=1;
				break;
			}
		}
	}
}

/*
 * Functions to decompose the outlines
 */

static GLYPH *curg;
static double lastx, lasty;

static int
outl_moveto(
	FT_Vector *to,
	void *unused
)
{
	double tox, toy;

	tox = fscale((double)to->x); toy = fscale((double)to->y);

	/* FreeType does not do explicit closepath() */
	if(curg->lastentry) {
		g_closepath(curg);
	}
	fg_rmoveto(curg, tox, toy);
	lastx = tox; lasty = toy;

	return 0;
}

static int
outl_lineto(
	FT_Vector *to,
	void *unused
)
{
	double tox, toy;

	tox = fscale((double)to->x); toy = fscale((double)to->y);

	fg_rlineto(curg, tox, toy);
	lastx = tox; lasty = toy;

	return 0;
}

static int
outl_conicto(
	FT_Vector *control1,
	FT_Vector *to,
	void *unused
)
{
	double c1x, c1y, tox, toy;

	c1x = fscale((double)control1->x); c1y = fscale((double)control1->y);
	tox = fscale((double)to->x); toy = fscale((double)to->y);

	fg_rrcurveto(curg,
		(lastx + 2.0 * c1x) / 3.0, (lasty + 2.0 * c1y) / 3.0,
		(2.0 * c1x + tox) / 3.0, (2.0 * c1y + toy) / 3.0,
		tox, toy );
	lastx = tox; lasty = toy;

	return 0;
}

static int
outl_cubicto(
	FT_Vector *control1,
	FT_Vector *control2,
	FT_Vector *to,
	void *unused
)
{
	double c1x, c1y, c2x, c2y, tox, toy;

	c1x = fscale((double)control1->x); c1y = fscale((double)control1->y);
	c2x = fscale((double)control2->x); c2y = fscale((double)control2->y);
	tox = fscale((double)to->x); toy = fscale((double)to->y);

	fg_rrcurveto(curg, c1x, c1y, c2x, c2y, tox, toy);
	lastx = tox; lasty = toy;

	return 0;
}

static FT_Outline_Funcs ft_outl_funcs = {
	outl_moveto,
	outl_lineto,
	outl_conicto,
	outl_cubicto,
	0,
	0
};

/*
 * Get the path of contrours for a glyph.
 */

static void
glpath(
	int glyphno,
	GLYPH *glyf_list
)
{
	FT_Outline *ol;

	curg = &glyf_list[glyphno];

	/* XXX workaround for a FT2beta8 bug */
	if( FT_Set_Char_Size(face,  0, face->units_per_EM<<6, 1<<6, 1<<6) ) {
		fprintf(stderr, "**** Cannot set the EM size ****\n");
		exit(1);
	}

	if( FT_Load_Glyph(face, glyphno, FT_LOAD_NO_BITMAP|FT_LOAD_NO_SCALE|FT_LOAD_NO_HINTING) 
	|| face->glyph->format != ft_glyph_format_outline ) {
		fprintf(stderr, "Can't load glyph %s, skipped\n", curg->name);
		return;
	}

	ol = &face->glyph->outline;
	lastx = 0.0; lasty = 0.0;

	if( FT_Outline_Decompose(ol, &ft_outl_funcs, NULL) ) {
		fprintf(stderr, "Can't decompose outline of glyph %s, skipped\n", curg->name);
		return;
	}

	/* FreeType does not do explicit closepath() */
	if(curg->lastentry) {
		g_closepath(curg);
	}

	if(ol->flags & ft_outline_reverse_fill) {
		assertpath(curg->entries, __FILE__, __LINE__, curg->name);
		reversepaths(curg);
	}
}

/*
 * Print out the kerning tables.
 */

static void
prkern(
	GLYPH *glyph_list,
	FILE *afm_file
)
{
	int	npairs_used, i, j, n;
	int	nglyphs = face->num_glyphs;
	char	*hashl, *hashr;
	FT_Vector k;
	GLYPH *gl;

	if( nglyphs == 0 || !FT_HAS_KERNING(face) ) {
        WARNING_1 fputs("No Kerning data\n", stderr);
		return;
	}

	if(( hashl = calloc(nglyphs, 1) )==NULL
	|| ( hashr = calloc(nglyphs, 1) )==NULL ) {
		fprintf (stderr, "****malloc failed %s line %d\n", __FILE__, __LINE__);
		exit(255);
	}

	npairs_used = 0;
	for(i=0; i<nglyphs; i++)  {
		if( (glyph_list[i].flags & GF_USED) ==0)
			continue;
		for(j=0; j<nglyphs; j++) {
			if( (glyph_list[j].flags & GF_USED) ==0)
				continue;
			if( FT_Get_Kerning(face, i, j, ft_kerning_unscaled, &k) )
				continue;
			if( k.x == 0 )
				continue;

			hashl[i] = 1; hashr[j] = 1;
			npairs_used++;
		}
	}

	fprintf(afm_file, "StartKernData\n");
	fprintf(afm_file, "StartKernPairs %hd\n", npairs_used);

	for(i=0; i<nglyphs; i++)  {
		if( !hashl[i] )
			continue;
		gl = &glyph_list[i];
		for(j=0; j<nglyphs; j++) {
			if( !hashr[j] )
				continue;
			if( FT_Get_Kerning(face, i, j, ft_kerning_unscaled, &k) )
				continue;
			if( k.x == 0 )
				continue;

			fprintf(afm_file, "KPX %s %s %d\n",
				gl->name, glyph_list[j].name,
				iscale(k.x) - (gl->scaledwidth - gl->oldwidth)
			);
		}
	}

	fprintf(afm_file, "EndKernPairs\n");
	fprintf(afm_file, "EndKernData\n");
}

#endif
