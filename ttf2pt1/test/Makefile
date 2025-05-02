.PHONY: all clean veryclean distclean rebuild test check

TTF2PT1=../ttf2pt1

all:	test

URWGothicL-Demi.otf: a010015l.pfb
	fontforge -lang=ff -c 'Open($$1); Generate($$2); Close();' a010015l.pfb URWGothicL-Demi.otf

URWBookmanL-Ligh.ttf: b018012l.pfb
	fontforge -lang=ff -c 'Open($$1); Generate($$2); Close();' b018012l.pfb URWBookmanL-Ligh.ttf

URWGothicL-Demi: URWGothicL-Demi.otf $(TTF2PT1)
	$(TTF2PT1) -p ft -mh=1024 -l adobestd -a -e URWGothicL-Demi.otf URWGothicL-Demi
	@mv URWGothicL-Demi.pfa URWGothicL-Demi
	@[ -f URWGothicL-Demi.sav ] || cp -p URWGothicL-Demi URWGothicL-Demi.sav
	@[ -f URWGothicL-Demi.afm.sav ] || cp -p URWGothicL-Demi.afm URWGothicL-Demi.afm.sav

URWBookmanL-Ligh: URWBookmanL-Ligh.ttf $(TTF2PT1)
	$(TTF2PT1) -p ttf -l latin1 -e URWBookmanL-Ligh.ttf URWBookmanL-Ligh
	@mv URWBookmanL-Ligh.pfa URWBookmanL-Ligh
	@[ -f URWBookmanL-Ligh.sav ] || cp -p URWBookmanL-Ligh URWBookmanL-Ligh.sav
	@[ -f URWBookmanL-Ligh.afm.sav ] || cp -p URWBookmanL-Ligh.afm URWBookmanL-Ligh.afm.sav

test: URWGothicL-Demi URWBookmanL-Ligh
	@if diff --text <(sed -e '2,3d' URWGothicL-Demi) <(sed -e '2,3d' URWGothicL-Demi.sav) ; then echo "OTF PFA test: pass" ; else echo "OTF PFA test: fail" ; fi
	@if diff --text URWGothicL-Demi.afm URWGothicL-Demi.afm.sav ; then echo "OTF AFM test: pass" ; else echo "OTF AFM test: fail" ; fi
	@if diff --text <(sed -e '2,3d' URWBookmanL-Ligh) <(sed -e '2,3d' URWBookmanL-Ligh.sav) ; then echo "TTF PFA test: pass" ; else echo "TTF PFA test: fail" ; fi
	@if diff --text URWBookmanL-Ligh.afm URWBookmanL-Ligh.afm.sav ; then echo "TTF AFM test: pass" ; else echo "TTF AFM test: fail" ; fi

check: test

clean:
	rm -f -- *.pfa *.afm URWGothicL-Demi URWBookmanL-Ligh

veryclean: clean

distclean: veryclean

rebuild: distclean
	rm -f -- *.otf *.ttf *.sav
