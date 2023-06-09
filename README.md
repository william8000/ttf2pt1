## TTF2PT1 - A True Type to PostScript Type 1 Font Converter

\[

> Based on ttf2pfa by Andrew Weeks, and help from Frank Siegert.  
> Modification by Mark Heath.  
> Further modification by Sergey Babkin.  
> The Type1 assembler by I. Lee Hetherington with modifications by
> Kai-Uwe Herbing.

\]

Ever wanted to install a particular font on your XServer but only could
find the font you are after in True Type Format?

Ever asked comp.fonts for a True Type to Type 1 converter and got a List
of Commercial software that doesn't run on your Operating System?

Well, this program should be the answer. This program is written in C
(so it should be portable) and therefore should run on any OS. The only
limitation is that the program requires some method of converting Big
endian integers into local host integers so the network functions ntohs
and ntohl are used. These can be replaced by macros if your platform
doesn't have them. Of course the target platform requires a C compiler
and command line ability.

Ttf2pt1 is a font converter from the True Type format (and some other
formats supported by the FreeType library as well) to the Adobe Type1
format.

The versions 3.0 and later got rather extensive post-processing
algorithm that brings the converted fonts to the requirements of the
Type1 standard, tries to correct the rounding errors introduced during
conversions and some simple kinds of bugs that are typical for the
public domain TTF fonts. It also generates the hints that enable much
better rendering of fonts in small sizes that are typical for the
computer displays. But everything has its price, and some of the
optimizations may not work well for certain fonts. That's why the
options were added to the converter, to control the performed
optimizations.

The converter is simple to run, just:

> ttf2pt1 *\[-options\] ttffont.ttf \[Fontname\]*

or

> ttf2pt1 *\[-options\] ttffont.ttf -*

The first variant creates the file Fontname.pfa (or Fontname.pfb if the
option '**-b**' was used) with the converted font and Fontname.afm with
the font metrics, the second one prints the font or another file (if the
option '**-G**' was used) on the standard output from where it can be
immediately piped through some filter. If no Fontname is specified for
the first variant, the name is generated from ttffont by replacing the
.ttf filename suffix.

Most of the time no options are neccessary (with a possible exception of
'**-e**'). But if there are some troubles with the resulting font, they
may be used to control the conversion. The **options** are:

**-a** - Include all the glyphs from the source file into the converted
file. If this option is not specified then only the glyphs that have
been assigned some encoding are included, because the rest of glyphs
would be inaccessible anyway and would only consume the disk space. But
some applications are clever enough to change the encoding on the fly
and thus use the other glyphs, in this case they could benefit from
using this option. But there is a catch: the X11 library has rather low
limit for the font size. Including more glyphs increases the file size
and thus increases the chance of hitting this limit.

**-b** - Encode the resulting font to produce a ready .pfb file.

**-d *suboptions*** - Debugging options. The suboptions are:

> **a** - Print out the absolute coordinates of dots in outlines. Such a
> font can not be used by any program (that's why this option is
> incompatible with '**-e**') but it has proven to be a valuable
> debuging information.
>
> **r** - Do not reverse the direction of outlines. The TTF fonts have
> the standard direction of outlines opposite to the Type1 fonts. So
> they should be reversed during proper conversion. This option may be
> used for debugging or to handle a TTF font with wrong direction of
> outlines (possibly, converted in a broken way from a Type1 font). The
> first signs of the wrong direction are the letters like "P" or "B"
> without the unpainted "holes" inside.

**-e** - Assemble the resulting font to produce a ready .pfa file. *\[*
S.B.*: Personally I don't think that this option is particularly useful.
The same result may be achieved by piping the unassembled data through
t1asm, the Type 1 assembler. And, anyways, it's good to have the t1utils
package handy. But Mark and many users think that this functionality is
good and it took not much time to add this option. \]*

**-F** - Force the Unicode encoding: any type of MS encoding specified
in the font is ignored and the font is treated like it has Unicode
encoding. **WARNING:** *this option is intended for buggy fonts which
actually are in Unicode but are marked as something else. The effect on
the other fonts is unpredictable.*

**-G *suboptions*** - File generation options. The suboptions may be
lowercase or uppercase, the lowercase ones disable the generation of
particular files, the corresponding uppercase suboptions enable the
generation of the same kind of files. If the result of ttf2pt1 is
requested to be printed on the standard output, the last enabling
suboption of **-G** determines which file will be written to the
standard output and the rest of files will be discarded. For example,
**-G A** will request the AFM file. The suboptions to disable/enable the
generation of the files are:

> **f/F** - The font file. Depending on the other options this file will
> have one of the suffixes .t1a, .pfa or .pfb. If the conversion result
> is requested on the standard output ('-' is used as the output file
> name) then the font file will also be written there by default, if not
> overwritten by another suboption of **-G**. **Default: enabled**
>
> **a/A** - The Adobe font metrics file (.afm). **Default: enabled**
>
> **e/E** - The dvips encoding file (.enc). **Default: disabled**

**-l *language*\[+*argument*\]** - Extract the fonts for the specified
language from a multi-language Unicode font. If this option is not used
the converter tries to guess the language by the values of the shell
variable LANG. If it is not able to guess the language by LANG it tries
all the languages in the order they are listed.

After the plus sign an optional argument for the language extractor may
be specified. The format of the argument is absolutely up to the
particular language converter. The primary purpose of the argument is to
support selection of planes for the multi-plane Eastern encodings but it
can also be used in any other way. The language extractor may decide to
add the plane name in some form to the name of the resulting font. None
of the currently supported languages make any use of the argument yet.

As of now the following languages are supported:  
  latin1 - for all the languages using the Latin-1 encoding  
  latin2 - for the Central European languages  
  latin4 - for the Baltic languages  
  latin5 - for the Turkish language  
  cyrillic - for the languages with Cyrillic alphabet  
  russian - historic synonym for cyrillic  
  bulgarian - historic synonym for cyrillic  
  adobestd - for the AdobeStandard encoding used by TeX  
  plane+*argument* - to select one plane from a multi-byte encoding

The argument of the "plane" language may be in one of three forms:

  plane+**pid=***\<pid>***,eid=***\<eid>*  
  plane+**pid=***\<pid>***,eid=***\<eid>***,***\<plane_number>*  
  plane+*\<plane_number>*

Pid (TTF platform id) and eid (TTF encoding id) select a particular TTF
encoding table in the original font. They are specified as decimal
numbers. If this particular encoding table is not present in the font
file then the conversion fails. The native ("ttf") front-end parser
supports only pid=3 (Windows platform), the FreeType-based ("ft")
front-end supports any platform. If pid/eid is not specified then the
TTF encoding table is determined as usual: Unicode encoding if it's
first or an 8-bit encoding if not (and for an 8-bit encoding the plane
number is silently ignored). To prevent the converter from falling back
to an 8-bit encoding, specify the Unicode pid/eid value explicitly.

Plane_number is a hexadecimal (if starts with "**0x**") or decimal
number. It gives the values of upper bytes for which 256 characters will
be selected. If not specified, defaults to 0. It is also used as a font
name suffix (the leading "0x" is not included into the suffix).

**NOTE:** It seems that many Eastern fonts use features of the TTF
format that are not supported by the ttf2pt1's built-in front-end
parser. Because of this for now we recommend using the FreeType-based
parser (option '**-p ft**') with the "plane" language.

***NOTE:** You may notice that the language names are not uniform: some
are the names of particular languages and some are names of encodings.
This is because of the different approaches. The original idea was to
implement a conversion from Unicode to the appropriate Windows encoding
for a given language. And then use the translation tables to generate
the fonts in whatever final encodings are needed. This would allow to
pile together the Unicode fonts and the non-Unicode Windows fonts for
that language and let the program to sort them out automatically. And
then generate fonts in all the possible encodings for that language. An
example of this approach is the Russian language support. But if there
is no multiplicity of encodings used for some languages and if the
non-Unicode fonts are not considered important by the users, another way
would be simpler to implement: just provide only one table for
extraction of the target encoding from Unicode and don't bother with the
translation tables. The* latin\* *"languages" are examples of this
approach. If somebody feels that he needs the Type1 fonts both in
Latin-\* and Windows encodings he or she is absolutely welcome to submit
the code to implement it.*

**WARNING:** Some of the glyphs included into the AdobeStandard encoding
are not included into the Unicode standard. The most typical examples of
such glyphs are ligatures like 'fi', 'fl' etc. Because of this the font
designers may place them at various places. The converter tries to do
its best, if the glyphs have honest Adobe names and/or are placed at the
same codes as in the Microsoft fonts they will be picked up. Otherwise a
possible solution is to use the option '**-L**' with an external map.

**-L *file*\[+\[pid=*\<pid>*,eid=*\<eid>*,\]\[*plane*\]\]** - Extract
the fonts for the specified language from a multi-language font using
the map from this file. This is rather like the option '**-l**' but the
encoding map is not compiled into the program, it's taken from that
file, so it's easy to edit. Examples of such files are provided in
maps/adobe-standard-encoding.map, CP1250.map. (**NOTE:** *the 'standard
encoding' map does not include all the glyphs of the AdobeStandard
encoding, it's provided only as an example*.) The description of the
supported map formats is in the file maps/unicode-sample.map.

Likewise to '**-l**', an argument may be specified after the map file
name. But in this case the argument has fixed meaning: it selects the
original TTF encoding table (the syntax is the same as in '**-l
plane**') and/or a plane of the map file. The plane name also gets added
after dash to the font name. The plane is a concept used in the Eastern
fonts with big number of glyphs: one TTF font gets divided into multiple
Type1 fonts, each containing one plane of up to 256 glyphs. But with a
little creativity this concept may be used for other purposes of
combining multiple translation maps into one file. To extract multiple
planes from a TTF font ttf2pt1 must be run multiple times, each time
with a different plane name specified.

The default original TTF encoding table used for the option '**-L**' is
Unicode. The map files may include directives to specify different
original TTF encodings. However if the pid/eid pair is specified with it
overrides any original encoding specified in the map file.

**-m *type*=*value*** - Set maximal or minimal limits of resources.
These limits control the the font generation by limiting the resources
that the font is permitted to require from the PostScript interpreter.
The currently supported types of limits are:

> **h** - the maximal hint stack depth for the substituted hints. The
> default value is 128, according to the limitation in X11. This seems
> to be the lowest (and thus the safest) widespread value. To display
> the hint stack depth required by each glyph in a .t1a file use the
> script ttf2pt1_cntstems.

**-O *suboptions*** - Outline processing options. The suboptions may be
lowercase or uppercase, the lowercase ones disable the features, the
corresponding uppercase suboptions enable the same features. The
suboptions to disable/enable features are:

> **b/B** - Guessing of the ForceBold parameter. This parameter helps
> the Type1 engine to rasterize the bold fonts properly at small sizes.
> But the algorithm used to guess the proper value of this flag makes
> that guess based solely on the font name. In rare cases that may cause
> errors, in these cases you may want to disable this guessing.
> **Default: enabled**
>
> **h/H** - Autogeneration of hints. The really complex outlines may
> confuse the algorithm, so theoretically it may be useful sometimes to
> disable them. Although up to now it seems that even bad hints are
> better than no hints at all. **Default: enabled**
>
> **u/U** - Hint substitution. Hint substitution is a technique
> permitting generation of more detailed hints for the rasterizer. It
> allows to use different sets of hints for different parts of a glyph
> and change these sets as neccessary during rasterization (that's why
> "substituted"). So it should improve the quality of the fonts rendered
> at small sizes. But there are two catches: First, the X11 library has
> rather low limit for the font size. More detailed hints increase the
> file size and thus increase the chance of hitting this limit (that
> does not mean that you shall hit it but you may if your fonts are
> particularly big). This is especially probable for Unicode fonts
> converted with option '**-a**', so you may want to use '**-a**'
> together with '**-Ou**'. Second, some rasterizers (again, X11 is the
> typical example) have a limitation for total number of hints used when
> drawing a glyph (also known as the hint stack depth). If that stack
> overflows the glyph is ignored. Starting from version 3.22 ttf2pt1
> uses algorithms to minimizing this depth, with the trade-off of
> slightly bigger font files. The glyphs which still exceed the limit
> set by option '**-mh**' have all the substituted hints removed and
> only base hints left. The algorithms seem to have been refined far
> enough to make the fonts with substituted hints look better than the
> fonts without them or at least the same. Still if the original fonts
> are not well-designed the detailed hinting may emphasize the defects
> of the design, such as non-even thickness of lines. So provided that
> you are not afraid of the X11 bug the best idea would be to generate a
> font with this feature and without it, then compare the results using
> the program ttf2pt1_cmpf (see the description in
> [other/README](other/README.html)) and decide which one looks better.
> **Default: enabled**
>
> **o/O** - Space optimization of the outlines' code. This kind of
> optimization never hurts, and the only reason to disable this feature
> is for comparison of the generated fonts with the fonts generated by
> the previous versions of converter. Well, it \_almost\_ never hurts.
> As it turned out there exist some brain-damaged printers which don't
> understand it. Actually this feature does not change the outlines at
> all. The Type 1 font manual provides a set of redundant operators that
> make font description shorter, such as '10 hlineto' instead of '0 10
> rlineto' to describe a horizontal line. This feature enables use of
> these operators. **Default: enabled**
>
> **s/S** - Smoothing of outlines. If the font is broken in some way
> (even the ones that are not easily noticeable), such smoothing may
> break it further. So disabling this feature is the first thing to be
> tried if some font looks odd. But with smoothing off the hint
> generation algorithms may not work properly too. **Default: enabled**
>
> **t/T** - Auto-scaling to the 1000x1000 Type1 standard matrix. The TTF
> fonts are described in terms of an arbitrary matrix up to 4000x4000.
> The converted fonts must be scaled to conform to the Type1 standard.
> But the scaling introduces additional rounding errors, so it may be
> curious sometimes to look at the font in its original scale.
> **Default: enabled**
>
> **v/V** - Do vectorization on the bitmap fonts. Functionally
> "vectorization" is the same thing as "autotracing", a different word
> is used purely to differentiate it from the Autotrace library. It
> tries to produce nice smooth outlines from bitmaps. This feature is
> still a work in progress though the results are already mostly decent.
> **Default: disabled**
>
> **w/W** - Glyphs' width corection. This option is designed to be used
> on broken fonts which specify too narrow widths for the letters. You
> can tell that a font can benefit from this option if you see that the
> characters are smashed together without any whitespace between them.
> This option causes the converter to set the character widths to the
> actual width of this character plus the width of a typical vertical
> stem. But on the other hand the well-designed fonts may have
> characters that look better if their widths are set slightly narrower.
> Such well-designed fonts will benefit from disabling this feature. You
> may want to convert a font with and without this feature, compare the
> results and select the better one. This feature may be used only on
> proportional fonts, it has no effect on the fixed-width fonts.
> **Default: disabled**
>
> **z/Z** - Use the Autotrace library on the bitmap fonts. The results
> are horrible and **the use of this option is not recommended**. This
> option is present for experimental purposes. It may change or be
> removed in the future. The working tracing can be achieved with option
> **-OV**. **Default: disabled**

**-p *parser_name*** - Use the specified front-end parser to read the
font file. If this option is not used, ttf2pt1 selects the parser
automatically based on the suffix of the font file name, it uses the
first parser in its list that supports this font type. Now two parsers
are supported:

  ttf - built-in parser for the ttf files (suffix .ttf)  
  bdf - built-in parser for the BDF files (suffix .bdf)  
  ft - parser based on the FreeType-2 library (suffixes .ttf, .otf,
.pfa, .pfb)

The parser ft is **NOT** linked in by default. See Makefile for
instructions how to enable it. We do no support this parser on Windows:
probably it will work but nobody tried and nobody knows how to build it.

The conversion of the bitmap fonts (such as BDF) is simplistic yet,
producing jagged outlines. When converting such fonts, it might be a
good idea to turn off the hint substitution (using option **-Ou**)
because the hints produced will be huge but not adding much to the
quality of the fonts.

**-u *number*** - Mark the font with this value as its UniqueID. The
UniqueID is used by the printers with the hard disks to cache the
rasterized characters and thus significantly speed-up the printing. Some
of those printers just can't store the fonts without UniqueID on their
disk.The problem is that the ID is supposed to be unique, as it name
says. And there is no easy way to create a guaranteed unique ID. Adobe
specifies the range 4000000-4999999 for private IDs but still it's
difficult to guarantee the uniqueness within it. So if you don't really
need the UniqueID don't use it, it's optional. Luckily there are a few
millions of possible IDs, so the chances of collision are rather low. If
instead of the number a special value '**A**' is given then the
converter generates the value of UniqueID automatically, as a hash of
the font name. (**NOTE:** *in the version 3.22 the algorithm for
autogeneration of UniqueID was changed to fit the values into the
Adobe-spacified range. This means that if UniqueIDs were used then the
printer's cache may need to be flushed before replacing the fonts
converted by an old version with fonts converted by a newer version*). A
simple way to find if any of the fonts in a given directory have
duplicated UniqueIDs is to use the command:

  cat \*.pf\[ab\] \| grep UniqueID \| sort \| uniq -c \| grep -v ' 1 '

Or if you use ttf2pt1_convert it will do that for you automatically plus
it will also give the exact list of files with duplicate UIDs.

**-v *size*** - Re-scale the font to get the size of a typical uppercase
letter somewhere around the specified size. Actually, it re-scales the
whole font to get the size of one language-dependent letter to be at
least of the specified size. Now this letter is "A" in all the supported
languages. The size is specified in the points of the Type 1 coordinate
grids, the maximal value is 1000. This is an experimental option and
should be used with caution. It tries to increase the visible font size
for a given point size and thus make the font more readable. But if
overused it may cause the fonts to look out of scale. As of now the
interesting values of size for this option seem to be located mostly
between 600 and 850. This re-scaling may be quite useful but needs more
experience to understand the balance of its effects.

**-W *level*** - Select the verbosity level of the warnings. Currently
the levels from 0 to 4 are supported. Level 0 means no warnings at all,
level 4 means all the possible warnings. The default level is 3. Other
levels may be added in the future, so using the level number 99 is
recommended to get all the possible warnings. Going below level 2 is not
generally recommended because you may miss valuable information about
the problems with the fonts being converted.

**Obsolete option:** **-A** - Print the font metrics (.afm file) instead
of the font on STDOUT. Use **-GA** instead.

**Very obsolete option:**  
The algorithm that implemented the forced fixed width had major flaws,
so it was disabled. The code is still in the program and some day it
will be refined and returned back. Meanwhile the option name '**-f**'
was reused for another option. The old version was:  
**-f** - Don't try to force the fixed width of font. Normally the
converter considers the fonts in which the glyph width deviates by not
more than 5% as buggy fixed width fonts and forces them to have really
fixed width. If this is undesirable, it can be disabled by this option.

The .pfa font format supposes that the description of the characters is
binary encoded and encrypted. This converter does not encode or encrypt
the data by default, you have to specify the option '**-e**' or use the
t1asm program to assemble (that means, encode and encrypt) the font
program. The t1asm program that is included with the converter is
actually a part of the t1utils package, rather old version of which may
be obtained from

> <http://ttf2pt1.sourceforge.net/t1utils.tar.gz>

Note that t1asm from the old version of that package won't work properly
with the files generated by ttf2pt1 version 3.20 and later. Please use
t1asm packaged with ttf2pt1 or from the new version t1utils instead. For
a newer version of t1utils please look at

> <http://www.lcdf.org/~eddietwo/type/>

So, the following command lines:

> ttf2pt1 -e ttffont.ttf t1font  
> ttf2pt1 ttffont.ttf - \| t1asm \>t1font.pfa

represent two ways to get a working font. The benefit of the second form
is that other filters may be applied to the font between the converter
and assembler.

#### Installation and deinstallation of the converter

The converter may be easily installed systemwide with

> make install

and uninstalled with

> make uninstall

By default the Makefile is configured to install in the hierarchy of
directory /usr/local. This destination directory as well as the
structure of the hierarchy may be changed by editing the Makefile.

#### Installation of the fonts

Running the converter manually becomes somewhat boring if it has to be
applied to a few hundreds of fonts and then you have to generate the
fonts.scale and/or Fontmap files. The [FONTS](FONTS.html) file describes
how to use the supplied scripts to handle such cases easily. It also
discusses the installation of the fonts for a few widespread programs.

#### Other utilities

A few other small interesting programs that allow a cloase look at the
fonts are located in the subdirectory 'other'. They are described
shortly in [others/README](other/README.html).

#### Optional packages

Some auxiliary files are not needed by everyone and are big enough that
moving them to a separate package speeds up the downloads of the main
package significantly. As of now we have one such optional package:

  **ttf2pt1-chinese** - contains the Chinese conversion maps

The general versioning policy for the optional packages is the
following: These packages may have no direct dependency on the ttf2pt1
version. But they may be updated in future, as well as some versions of
optional packages may have dependencies on certain versions of ttf2pt1.
To avoid unneccessary extra releases on one hand and keep the updates in
sync with the ttf2pt1 itself on the other hand, a new version of an
optional package will be released only if there are any changes to it
and it will be given the same version number as ttf2pt1 released at the
same time. So not every release of ttf2pt1 would have a corresponding
release of all optional packages. For example, to get the correct
version of optional packages for an imaginary release 8.3.4 of ttf2pt1
you would need to look for optional packages of the highest version not
higher than (but possibly equal to) 8.3.4.

#### TO DO:

-   Improve hinting.
-   Improve the auto-tracing of bitmaps.
-   Implement the family-level hints.
-   Add generation of CID-fonts.
-   Handle the composite glyphs with relative base points.
-   Preserve the relative width of stems during scaling to 1000x1000
    matrix.
-   Add support for bitmap TTF fonts.
-   Implement better support of Asian encodings.
-   Implement automatic creation of ligatures.

#### TROUBLESHOOTING AND BUG REPORTS

Have problems with conversion of some font ? The converter dumps core ?
Or your printer refuses to understand the converted fonts ? Or some
characters are missing ? Or some characters look strange ?

Send the bug reports to the ttf2pt1 development mailing list at
<ttf2pt1-devel@lists.sourceforge.net>.

Try to collect more information about the problem and include it into
the bug report. (Of course, even better if you would provide a ready
fix, but just a detailed bug report is also good). Provide detailed
information about your problem, this will speed up the response greatly.
Don't just write "this font looks strange after conversion" but describe
what's exactly wrong with it: for example, what characters look wrong
and what exactly is wrong about their look. Providing a link to the
original font file would be also a good idea. Try to do a little
troublehooting and report its result. This not only would help with the
fix but may also give you a temporary work-around for the bug.

First, enable full warnings with option '**-W99**', save them to a file
and read carefully. Sometimes the prolem is with a not implemented
feature which is reported in the warnings. Still, reporting about such
problems may be a good idea: some features were missed to cut corners,
in hope that no real font is using them. So a report about a font using
such a feature may motivate someone to implement it. Of course, you may
be the most motivated person: after all, you are the one wishing to
convert that font. ;-) Seriously, the philosophy "scrath your own itch"
seems to be the strongest moving force behind the Open Source software.

The next step is playing with the options. This serves a dual purpose:
on one hand, it helps to localize the bug, on the other hand you may be
able to get a working version of the font for the meantime while the bug
is being fixed. The typical options to try out are: first '**-Ou**', if
it does not help then '**-Os**', then '**-Oh**', then '**-Oo**'. They
are described in a bit more detail above. Try them one by one and in
combinations. See if with them the resulting fonts look better.

On some fonts ttf2pt1 just crashes. Commonly that happens because the
font being converted is highly defective (although sometimes the bug is
in ttf2pt1 itself). In any case it should not crash, so the reports
about such cases will help to handle these defects properly in future.

We try to respond to the bug reports in a timely fashion but alas, this
may not always be possible, especially if the problem is complex. This
is a volunteer project and its resources are limited. Because of this we
would appreciate bug reports as detailed as possible, and we would
appreciate the ready fixes and contributions even more.

#### CONTACTS

[ttf2pt1-announce@lists.sourceforge.net](http://lists.sourceforge.net/mailman/listinfo/ttf2pt1-announce)  
The mailing list with announcements about ttf2pt1. It is a moderated
mailing with extremely low traffic. Everyone is encouraged to subscribe
to keep in touch with the current status of project. To subscribe use
the Web interface at
<http://lists.sourceforge.net/mailman/listinfo/ttf2pt1-announce>. If you
have only e-mail access to the Net then send a subscribe request to the
development mailing list ttf2pt1-devel@lists.sourceforge.net and
somebody will help you with subscription.

<ttf2pt1-devel@lists.sourceforge.net>  
<ttf2pt1-users@lists.sourceforge.net>  
The ttf2pt1 mailing lists for development and users issues. They have
not that much traffic either. To subscribe use the Web interface at
<http://lists.sourceforge.net/mailman/listinfo/ttf2pt1-devel> and
<http://lists.sourceforge.net/mailman/listinfo/ttf2pt1-users>. If you
have only e-mail access to the Net then send a subscribe request to the
development mailing list ttf2pt1-devel@lists.sourceforge.net and
somebody will help you with subscription.

<mheath@netspace.net.au>  
Mark Heath

<A.Weeks@mcc.ac.uk>  
Andrew Weeks

<babkin@users.sourceforge.net> (preferred)  
<sab123@hotmail.com>  
<http://members.bellatlantic.net/~babkin>  
Sergey Babkin

#### SEE ALSO

<http://ttf2pt1.sourceforge.net>  
The main page of the project.

<http://www.netspace.net.au/~mheath/ttf2pt1/>  
The old main page of the project.

<http://sourceforge.net/projects/gnuwin32>  
Precompiled binaries for Windows.

<http://www.lcdf.org/~eddietwo/type/>  
The home page of the Type 1 utilities package.

<http://www.rightbrain.com/pages/books.html>  
The first book about PostScript on the Web, "Thinking in PostScript".

<http://fonts.apple.com/TTRefMan/index.html>  
The True Type reference manual.

<http://partners.adobe.com/asn/developer/PDFS/TN/PLRM.pdf>  
Adobe PostScript reference manual.

<http://partners.adobe.com/asn/developer/PDFS/TN/T1_SPEC.PDF>  
Specification of the Type 1 font format.

<http://partners.adobe.com/asn/developer/PDFS/TN/5015.Type1_Supp.pdf>  
The Type 1 font format supplement.

<http://partners.adobe.com/asn/developer/PDFS/TN/5004.AFM_Spec.pdf>  
Specification of the Adobe font metrics file format.

<http://www.cs.wpi.edu/~matt/courses/cs563/talks/surface/bez_surf.html>  
<http://www.cs.wpi.edu/~matt/courses/cs563/talks/curves.html>  
Information about the Bezier curves.

<http://www.neuroinformatik.ruhr-uni-bochum.de/ini/PEOPLE/rmz/t1lib/t1lib.html>  
A stand-alone library supporting the Type1 fonts. Is neccessary to
compile the programs other/cmpf and other/dmpf.

<http://www.freetype.org>  
A library supporting the TTF fonts. Also many useful TTF programs are
included with it.

<http://heliotrope.homestead.com/files/printsoft.html>  
Moses Gold's collection of links to printing software.

<http://linuxartist.org/fonts/>  
Collection of font-related links.

------------------------------------------------------------------------

------------------------------------------------------------------------

Following is the Readme of ttf2pfa (true type to type 3 font converter)
It covers other issues regarding the use of this software. Please note
that although ttf2pfa is a public domain software, ttf2pt1 is instead
covered by an Open Source license. See the COPYRIGHT file for details.

Please note also that ttf2pfa has not been maintained for a long time.
All of its functionality has been integrated into ttf2pt1 and all the
development moved to ttf2pt1, including Andrew Weeks, the author of
ttf2pfa. Ttf2pfa is provided for historical reasons only. Please use
ttf2pt1 instead.

------------------------------------------------------------------------

### True Type to Postscript Font converter

My mind is still reeling from the discovery that I was able to write
this program. What it does is it reads a Microsoft TrueType font and
creates a Postscript font. '*\_A\_* postscript font', that is, not
necessarily the same font, you understand, but a fair imitation.

Run it like this:

> ttf2pfa fontfile.ttf fontname

The first parameter is the truetype filename, the second is a stem for
the output file names. The program will create a fontname.pfa containing
the Postscript font and a fontname.afm containing the metrics.

The motivation behind this is that in Linux if you do not have a
Postscript printer, but only some other printer, you can only print
Postscript by using Ghostscript. But the fonts that come with
Ghostscript are very poor (they are converted from bitmaps and look
rather lumpy). This is rather frustrating as the PC running Linux
probably has MS-Windows as well and will therefore have truetype fonts,
but which are quite useless with Linux, X or Ghostscript.

The program has been tested on over a hundred different TrueType fonts
from various sources, and seems to work fairly well. The converted
characters look OK, and the program doesn't seem to crash any more. I'm
not sure about the AFM files though, as I have no means to test them.

The fonts generated will not work with X, as the font rasterizer that
comes with X only copes with Type 1 fonts. If I have the time I may
modify ttf2pfa to generate Type 1s.

#### Copyright issues

I am putting this program into the public domain, so don't bother
sending me any money, I'd only have to declare it for income tax.

Copyright on fonts, however, is a difficult legal question. Any
copyright statements found in a font will be preserved in the output.
Whether you are entitled to translate them at all I don't know.

If you have a license to run a software package, like say MS-Windows, on
your PC, then you probably have a right to use any part of it, including
fonts, on that PC, even if not using that package for its intended
purpose.

I am not a lawyer, however, so this is not a legal opinion, and may be
garbage.

There shouldn't be a any problem with public domain fonts.

#### About the Program

It was written in C on a IBM PC running Linux.

The TrueType format was originally developed by Apple for the MAC, which
has opposite endianness to the PC, so to ensure compatibility 16 and 32
bit fields are the wrong way round from the PC's point of view. This is
the reason for all the 'ntohs' and 'ntohl' calls. Doing it this way
means the program will also work on big-endian machines like Suns.

I doubt whether it will work on a DOS-based PC though.

The program produces what technically are Type 3 rather than Type 1
fonts. They are not compressed or encrypted and are plain text. This is
so I (and you) can see what's going on, and (if you're a Postscript guru
and really want to) can alter the outlines.

I only translate the outlines, not the 'instructions' that come with
them. This latter task is probably virtually impossible anyway. TrueType
outlines are B-splines rather than the Bezier curves that Postscript
uses. I believe that my conversion algorithm is reasonably correct, if
nothing else because the characters look right.

#### Problems that may occur

Most seriously, very complex characters (with lots of outline segments)
can make Ghostscript releases 2.x.x fail with a 'limitcheck' error. It
is possible that this may happen with some older Postscript printers as
well. Such characters will be flagged by the program and there are
basically two things you can do. First is to edit the .pfa file to
simplify or remove the offending character. This is not really
recommended. The second is to use Ghostscript release 3, if you can get
it. This has much larger limits and does not seem to have any problems
with complex characters.

Then there are buggy fonts (yes, a font can have bugs). I try to deal
with these in as sane a manner as possible, but it's not always
possible.

#### Encodings

A postscript font must have a 256 element array, called an encoding,
each element of which is a name, which is also the name of a procedure
contained within the font. The 'BuildChar' command takes a byte and uses
it to index the encoding array to find a character name, and then looks
that up in the font's procedure table find the commands to draw the
glyph. However, not all characters need be in the encoding array. Those
that are not cannot be drawn (at least not using 'show'), however it is
possible to 're-encode' the font to enable these characters. There are
several standard encodings: Adobe's original, ISO-Latin1 and Symbol
being the most commonly encountered.

TrueType fonts are organised differently. As well as the glyph
descriptions there are a number of tables. One of these is a mapping
from a character set into the glyph array, and another is a mapping from
the glyph array into a set of Postscript character names. The problems
are:

1\) Microsoft uses Unicode, a 16-bit system, to encode the font.  
2) that more than one glyph is given the same Postscript name.

I deal with (1) by assuming a Latin1 encoding. The MS-Windows and
Unicode character sets are both supersets of ISO-8859-1. This usually
means that most characters will be properly encoded, but you should be
warned that some software may assume that fonts have an Adobe encoding.
Symbol, or Dingbat, fonts are in fact less of a problem, as they have
private encodings starting at 0xF000. It is easy to just lose the top
byte.

Postscript fonts can be re-encoded, either manually, or by software.
Groff, for example, generates postscript that re-encodes fonts with the
Adobe encoding. The problem here is that not all characters in the Adobe
set are in the MS-Windows set. In particular there are no fi and fl
ligatures. This means that conversions of the versions of
Times-New-Roman and Arial that come with MS-Windows cannot be used
blindly as replacements for Adobe Times-Roman and Helvetica. You can get
expanded versions of MS fonts from Microsoft's web site which do contain
these ligatures (and a lot else besides).

I deal with (2) by creating new character names. This can be error-prone
because I do not know which of them is the correct glyph to give the
name to. Some (buggy) fonts have large numbers of blank glyphs, all with
the same name.

(almost every TrueType font has three glyphs called .notdef, one of them
is usually an empty square shape, one has no outline and has zero width,
and one has no outline and a positive width. This example is not really
a problem with well formed fonts since the .notdef characters are only
used for unprintable characters, which shouldn't occur in your documents
anyway).
