FLAG = -g -pg

redlib.a : redlibmain.o redbasics.o \
	fxp.o treeman.o hashman.o \
	redparse.o finclude.o lex.redmac.o \
	tctctl.o exp.o redbop.o redstring.o \
	action.o redstream.o counter.o bisim.o redgame.o \
	access_analysis.o redsymmetry.o inactive.o zone.o zapprox.o \
	redgram.tab.o hybrid.o;
	ar -crv redlib.a \
		redlibmain.o redbasics.o fxp.o \
		treeman.o hashman.o \
		redparse.o finclude.o lex.redmac.o \
		tctctl.o exp.o redbop.o redstring.o \
		action.o redstream.o bisim.o redgame.o \
		access_analysis.o \
		counter.o redsymmetry.o inactive.o zone.o zapprox.o \
		redgram.tab.o hybrid.o

redlibmain.o : redlibmain.c redlib.h fxp.h fxp.e tc.e \
	redbasics.h redbasics.e redbop.h redbop.e redsymmetry.e \
	treeman.h treeman.e hashman.h hashman.e \
	redparse.h redparse.e tctctl.e exp.e action.e \
	bisim.h bisim.e redgame.h redgame.e redstring.e \
	counter.e inactive.e zone.h zone.e zapprox.e hybrid.h hybrid.e;
	gcc ${FLAG} -c redlibmain.c

redbasics.o : redbasics.c redbasics.h \
	fxp.h fxp.e tc.e redbop.h redbop.e \
	treeman.h treeman.e hashman.h hashman.e \
	redsymmetry.e redparse.h redparse.e exp.e action.e \
	bisim.h bisim.e redgame.h redgame.e \
	counter.e inactive.e zone.h zone.e zapprox.e hybrid.h hybrid.e;
	gcc ${FLAG} -c redbasics.c

hashman.o : treeman.h treeman.e redbop.h redbop.e redparse.h redparse.e \
	hashman.c hashman.h redbasics.h redbasics.e ;
	gcc ${FLAG} -c hashman.c
treeman.o : redbop.h redbop.e treeman.c treeman.h \
	redbasics.h redbasics.e ;
	gcc ${FLAG} -c treeman.c
redstring.o : redstring.c redbop.h redbop.e redparse.e exp.e redparse.h \
	redbasics.h redbasics.e;
	gcc ${FLAG} -c redstring.c
redgram.tab.c : redbasics.h redbasics.e redstring.e \
	redlib.e \
	lex.redlib.c redgram.y redparse.h redparse.e exp.e redbop.h redbop.e;
	yacc -v -d -bredgram -predlib redgram.y
redgram.tab.o : redgram.tab.c lex.redlib.c redlib.e \
	redbasics.h redbasics.e \
	redparse.h redparse.e exp.e redbop.h redbop.e;
	gcc ${FLAG} -c  redgram.tab.c
lex.redlib.c : redlex.l redgram.e redparse.h redparse.e exp.e ;
	flex -olex.redlib.c -Predlib redlex.l
lex.redmac.o : lex.redmac.c ;
	gcc ${FLAG} -c lex.redmac.c -lfl
lex.redmac.c : redmaclex.l ;
	flex -olex.redmac.c -Predmac redmaclex.l
redparse.o : redparse.h redparse.c finclude.e redmaclex.e \
	exp.e fxp.h fxp.e tc.e redbop.h redbop.e \
	treeman.h treeman.e hashman.h hashman.e \
	redbasics.h redbasics.e tctctl.e \
	tc.e inactive.e zone.h zone.e action.e hybrid.h hybrid.e bisim.e;
	gcc ${FLAG} -c redparse.c
finclude.o : finclude.c redbasics.h redbasics.e redbop.h hashman.h ;
	gcc ${FLAG} -c finclude.c
exp.o : exp.c redparse.h redparse.e fxp.h fxp.e tc.e redbop.h redbop.e \
	treeman.h treeman.e hashman.h hashman.e \
	redbasics.h redbasics.e tctctl.e \
	tc.e inactive.e zone.h zone.e action.e hybrid.h hybrid.e bisim.e;
	gcc ${FLAG} -c exp.c
tctctl.o : tctctl.c redparse.h redparse.e exp.e redbop.h redbop.e \
	treeman.h treeman.e hashman.h hashman.e \
	redbasics.h redbasics.e zone.h zone.e ;
	gcc ${FLAG} -c tctctl.c
redbop.o : redbop.h fxp.h counter.e action.e exp.e tctctl.e \
	treeman.h treeman.e hashman.h hashman.e \
	redbasics.h redbasics.e \
	hybrid.h hybrid.e redbop.c;
	gcc ${FLAG} -c redbop.c
redsymmetry.o : redbop.h redbop.e redsymmetry.c zone.h zone.e \
	treeman.h treeman.e hashman.h hashman.e \
	redbasics.h redbasics.e ;
	gcc ${FLAG} -c redsymmetry.c
action.o : redbop.h redbop.e zone.h zone.e action.c hybrid.h hybrid.e \
	treeman.h treeman.e hashman.h hashman.e redparse.h redparse.e exp.e \
	redbasics.h redbasics.e ;
	gcc ${FLAG} -c action.c
redstream.o : redbasics.h redbasics.e fxp.h treeman.h treeman.e \
	redbop.h redbop.e redparse.h redparse.e exp.e hashman.h hashman.e \
	action.e redstream.c
	gcc ${FLAG} -c redstream.c
counter.o : counter.c exp.e fxp.h fxp.e redbop.h redbop.e zone.h zone.e \
	hybrid.h hybrid.e \
	treeman.h treeman.e hashman.h hashman.e redstring.e action.e\
	redbasics.h redbasics.e ;
	gcc ${FLAG} -c counter.c
inactive.o : inactive.c redbop.h redbop.e redparse.h fxp.h fxp.e \
	redparse.e exp.e hybrid.h hybrid.e zone.h zone.e action.e \
	treeman.h treeman.e hashman.h hashman.e \
	redbasics.h redbasics.e ;
	gcc ${FLAG} -c inactive.c
zone.o : zone.c zone.h redbop.h redbop.e redbasics.e redbasics.h inactive.e \
	treeman.h treeman.e hashman.h hashman.e \
	redbasics.h redbasics.e \
	zapprox.e hybrid.h hybrid.e;
	gcc ${FLAG} -c zone.c
zapprox.o : zapprox.c redbop.h redbop.e inactive.e \
	treeman.h treeman.e hashman.h hashman.e \
	zone.h zone.e hybrid.h hybrid.e \
	redbasics.h redbasics.e ;
	gcc ${FLAG} -c zapprox.c
hybrid.o : hybrid.h hybrid.c redbop.h redbop.e inactive.e \
	treeman.h treeman.e hashman.h hashman.e \
	zapprox.e exp.e \
	redbasics.h redbasics.e ;
	gcc ${FLAG} -c hybrid.c
fxp.o: vindex.e redbop.h redbop.e counter.e zone.h zone.e \
	redparse.h redparse.e exp.e \
	redbasics.h redbasics.e redlib.h redlib.e action.e \
	treeman.h treeman.e hashman.h hashman.e \
	redsymmetry.e action.e inactive.e coverage.e \
	hybrid.h hybrid.e fxp.h fxp.c;
	gcc ${FLAG} -c fxp.c
access_analysis.o : access_analysis.c redbop.h redbop.e \
	treeman.h treeman.e hashman.h hashman.e fxp.h fxp.e \
	redbasics.h redbasics.e redparse.h redparse.e exp.e;
	gcc ${FLAG} -c access_analysis.c

bisim.o : bisim.c bisim.h redgame.h redgame.e \
        zone.h zone.e redbop.h redbop.e action.e \
	treeman.h treeman.e hashman.h hashman.e fxp.h fxp.e \
	redbasics.h redbasics.e redparse.h redparse.e exp.e;
	gcc ${FLAG} -c bisim.c

redgame.o : redgame.c redgame.h bisim.h bisim.e \
        zone.h zone.e redbop.h redbop.e action.e \
	treeman.h treeman.e hashman.h hashman.e fxp.h fxp.e \
	bisim.h bisim.e \
	redbasics.h redbasics.e redparse.h redparse.e exp.e;
	gcc ${FLAG} -c redgame.c
