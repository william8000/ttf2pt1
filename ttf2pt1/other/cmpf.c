/*
 * see COPYRIGHT
 */

#include <stdio.h>
#include <ctype.h>
#include "t1lib.h"

/*
 * compare two [ almost the same ] fonts
 */

#define PROGNAME "cmpf"

fchkneg(file, line, rc, cmd)
	char *file;
	int line;
	int rc;
	char *cmd;
{
	if(rc<0) {
		fprintf(stderr,"%s: fatal error on line %d of %s: %d\n", 
			PROGNAME, line, file, rc);
		fprintf(stderr,"%s\n", cmd);
		exit(1);
	}
}

fchknull(file, line, rc, cmd)
	char *file;
	int line;
	void *rc;
	char *cmd;
{
	if(rc==NULL) {
		fprintf(stderr,"%s: fatal error on line %d of %s: NULL\n", 
			PROGNAME, line, file);
		fprintf(stderr,"%s\n", cmd);
		exit(1);
	}
}

#define chkneg(f)	fchkneg(__FILE__,__LINE__,(f),#f)
#define chknull(f)	fchknull(__FILE__,__LINE__,(f),#f)

#define MYFONT	"/usr/lib/X11/fonts/ttf/kudriash.koi8-r.pfa"

#define MYPAD 8

#define CHRNONE	' '
#define CHRBOTH	'.'
#define CHRONE	'1'
#define CHRTWO	'2'

#define MINSIZE 8
#define MAXSIZE 20

#define LINEWIDTH	80 /* screen line width in chars */
#define MAXLINES	(MAXSIZE*(MAXSIZE-MINSIZE+1))

static char map[MAXLINES][LINEWIDTH+1];
static char mbase, mx, mend;

/* returns 0 if the same, -1 if different */

int 
cmpglyphs(g1, g2)
	GLYPH *g1, *g2;
{
	int wd1, wd2;
	int ht1, ht2;
	int i, j;
	char *p1, *p2;

	wd1=g1->metrics.rightSideBearing - g1->metrics.leftSideBearing;
	ht1=g1->metrics.ascent - g1->metrics.descent;
	wd2=g2->metrics.rightSideBearing - g2->metrics.leftSideBearing;
	ht2=g2->metrics.ascent - g2->metrics.descent;

	if(g1->bits==NULL && g2->bits!=NULL
	|| g1->bits!=NULL && g2->bits==NULL)
		return -1;

	if(g1->metrics.ascent != g2->metrics.ascent)
		return -1;

	if(g1->metrics.descent != g2->metrics.descent)
		return -1;

	if( wd1 != wd2 )
		return -1;

	if( (p1=g1->bits) !=NULL && (p2=g2->bits) !=NULL )
		for(i=0; i<ht1; i++) {
			for(j=0; j<wd1; j+=8) {
				if( *p1++ != *p2++)
					return -1;
			}
		}
	return 0;
}

void
resetmap()
{
	int i, j;

	for(i=0; i<MAXLINES; i++)
		for(j=0; j<LINEWIDTH; j++)
			map[i][j]=' ';
	mbase=mx=mend=0;
}

void 
drawdot(row, col, val)
	unsigned row, col, val;
{
	if(row < MAXLINES && col < LINEWIDTH-1) {
		map[row][col]=val;
		if(row > mend)
			mend=row;
	}
}

void 
drawdotg1(row, col, val)
	unsigned row, col, val;
{
	if(row < MAXLINES && col < LINEWIDTH-1) {
		if(val)
			map[row][col]=CHRONE;
		else
			map[row][col]=CHRNONE;
		if(row > mend)
			mend=row;
	}
}

void 
drawdotg2(row, col, val)
	unsigned row, col, val;
{
	if(row < MAXLINES && col < LINEWIDTH-1) {
		if(val) 
			if(map[row][col]==CHRONE)
				map[row][col]=CHRBOTH;
			else
				map[row][col]=CHRTWO;
		else if(map[row][col]!=CHRONE)
			map[row][col]=CHRNONE;
		if(row > mend)
			mend=row;
	}
}

void 
drawdiff(size, g1, g2)
	int size;
	GLYPH *g1, *g2;
{
	int wd1, wd2, wdm;
	int ht1, ht2, ascm, desm;
	int i, j, k, val;
	char *p;

	wd1=g1->metrics.rightSideBearing - g1->metrics.leftSideBearing;
	ht1=g1->metrics.ascent - g1->metrics.descent;
	wd2=g2->metrics.rightSideBearing - g2->metrics.leftSideBearing;
	ht2=g2->metrics.ascent - g2->metrics.descent;

	wdm = ((wd1>wd2) ? wd1 : wd2) +1;
	if(wdm<3)
		wdm=3;

	if(g1->metrics.ascent > g2->metrics.ascent)
		ascm=g1->metrics.ascent;
	else
		ascm=g2->metrics.ascent;

	if(g1->metrics.descent < g2->metrics.descent)
		desm= -g1->metrics.ascent;
	else
		desm= -g2->metrics.ascent;

	if(mbase==0) 
		mbase=ascm+1;
	else if(LINEWIDTH-mx <= wdm) {
		mx=0; mbase=mend+ascm+2;
	}

	drawdot(mbase-ascm-1, mx, (size/10)%10+'0');
	drawdot(mbase-ascm-1, mx+1, size%10+'0');

	if( (p=g1->bits) !=NULL)
		for(i=0; i<ht1; i++) {
			for(j=0; j<wd1; j+=8) {
				val = *p++;
				for(k=0; k<8 && j+k<wd1; k++, val>>=1)
					drawdotg1(i+mbase-g1->metrics.ascent, mx+j+k, val&1);
			}
		}
	if( (p=g2->bits) !=NULL)
		for(i=0; i<ht2; i++) {
			for(j=0; j<wd2; j+=8) {
				val = *p++;
				for(k=0; k<8 && j+k<wd2; k++, val>>=1)
					drawdotg2(i+mbase-g2->metrics.ascent, mx+j+k, val&1);
			}
		}
	mx+=wdm;
	drawdot(mbase, mx-1, '-');
}

void
printmap(f)
	FILE *f;
{
	int i, j;

	for(i=0; i<=mend; i++) {
		for(j=LINEWIDTH-1; j>=0 && map[i][j]==' '; j--)
			{}
		map[i][j+1]='\n';
		map[i][j+2]=0;
		fputs(map[i], f);
	}
}

main(ac, av)
	int ac;
	char **av;
{
	int fontid1, fontid2;
	GLYPH *g1, *g2;
	int chr, size, diff, offset;

	if(ac!=3) {
		fprintf(stderr,"Use: %s font1 font2\n", PROGNAME);
		exit(1);
	}

	chkneg(T1_SetBitmapPad(MYPAD));
	chkneg(T1_InitLib(NO_LOGFILE|IGNORE_CONFIGFILE|IGNORE_FONTDATABASE));
	chkneg(fontid1=T1_AddFont(av[1]));
	chkneg(fontid2=T1_AddFont(av[2]));


	resetmap();
	for(chr=0; chr<256; chr++) {
		diff=0;
		for(size=MAXSIZE; size>=MINSIZE; size--) {
			chknull( g1=T1_CopyGlyph(T1_SetChar( fontid1, chr, (float)size, NULL)) );
			chknull( g2=T1_CopyGlyph(T1_SetChar( fontid2, chr, (float)size, NULL)) );

			if( cmpglyphs(g1, g2) ) {
				/* printf("%d %d - diff\n", chr, size); */
				diff=1;
				drawdiff(size, g1, g2);
			} 
			/*
			else
				fprintf(stderr, "%d %d - same\n", chr, size);
			*/

			chkneg(T1_FreeGlyph(g1));
			chkneg(T1_FreeGlyph(g2));
		}
		if(diff) {
			printf("*** Difference for %d==0x%x  %c\n", chr, chr,
				isprint(chr) ? chr : ' ');
			printmap(stdout);
			diff=0;
			resetmap();
		}
	}

	printf("All done!\n");
}
