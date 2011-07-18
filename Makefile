
RELEASE = v0.0.2
BASE	= proposal
BIBTEXOPT = 
BIBWARN = 'LaTeX Warning: Citation'
REFWARN = 'Rerun to get cross-references'
LATEXMAX = 6
FIGSCALE = 0.5

# CLASSPATH components

LIB = external_libraries
CORECP	= src:src.test:unittest:$(LIB)/alloy4.jar
SPECS = external_tools/JML/specs
JMLCP = $(LIB)/jmlruntime.jar:$(LIB)/jmljunitruntime.jar:$(LIB)/jml-release.jar:$(SPECS)
JUNITCP = $(LIB)/junit.jar
EXTCP = external_tools/coyledoyle/src:external_tools/stvcounter_src

# local variables for build process
javac ?= javac
jml ?= ./external_tools/bin/jml
jmlrac ?= ./external_tools/bin/jmlrac
jmlc ?= ./external_tools/bin/jmlc -G
jmldoc ?= ./external_tools/bin/jmldoc
jmlunit ?= ./external_tools/bin/jmlunit
version ?= 1.5
version4 ?= 1.4

basedocdir = doc
srcpath = src
testpath = unittest
specpath =$(SPECS)
buildpath =	build
jmlc_path =	jmlc_build
jmlunit_path =	jmlunit_src
jmlc_jmlunit_path =	jmlc_jmlunit_build

ESCPATH ?= ./external_tools/ESCJava2/ESCJava-2.0.5-04-11-08-binary
ESCJ_SIMPLIFY_DIR ?= $(ESCPATH)
JAVAFE_PATH ?= ./external_tools/ESCJava2/Javafe-2.0.11-26-04-10-binary
BCEL_PATH ?= ./external_tools/ESCJava2/bcel-5.2
escjava = $(ESCPATH)/escj -source $(version4) -vclimit 2500000 -warnUnsoundIncomplete
ESCJAVA2CP ?= $(ESCPATH)/esctools2.jar:$(JAVAFE_PATH)/Javafe2.0.11.jar:$(BCEL_PATH)/bcel-5.2.jar

# Various CLASSPATH constructions

BASE_CLASSPATH	= $(CORECP):$(JCECP):$(FOPCP):$(MISCCP):$(JUNITCP):$(JMLCP):$(EXTCP)
JAVAC_CLASSPATH	= $(buildpath):$(BASE_CLASSPATH)
JMLC_CLASSPATH	= $(jmlc_path):$(BASE_CLASSPATH)
JUNIT_CLASSPATH	= $(jmlc_jmlunit_path):$(CORECP):$(JCECP):$(FOPCP):$(MISCCP):$(JUNITCP):$(JMLCP):src.test/ie/votail/model/test:src.test/ie/votail/model/factory/test
ESCJAVA_CLASSPATH	= $(CORECP):$(JMLCP):$(ESCJAVA2CP):$(JCECP):$(FOPCP):$(MISCCP):$(JUNITCP)
UNIT_TEST_CLASSPATH	= $(jmlc_jmlunit_path):$(testpath):$(buildpath):$(JCECP):$(FOPCP):$(MISCCP):$(JUNITCP):$(JMLCP)
CHECKSTYLE_CLASSPATH	= $(CORECP):$(CHECKSTYLECP)

javapat	=	$(srcpath)/election/tally/*.java
javapat5	= $(srcpath)/ie/votail/model/*.java $(srcpath)/ie/votail/model/factory/*.java src.test/ie/votail/uilioch//UniversalTestRunner.java
javafiles =	$(wildcard $(srcpath)/election/tally/*.java $(srcpath)/ie/votail/model/*.java $(srcpath)/ie/votail/model/factory/*.java src.test/ie/votail/uilioch/UniversalTestRunner.java)
jmlunitpat =	$(jmlunit_path)/election/tally/*.java
jmlunitfiles =	$(wildcard $(jmlunit_path)/election/tally/*.java)
generated_jmlunitfiles	=	$(wildcard $(jmlunit_path)/election/tally/*_JML_Test.java)
classfiles =	$(foreach javafile,$(javafiles),\
		$(subst .java,.class,$(javafile)))
javadocflags =	-version -author -private -source $(version)
jmldocflags =	-version -author -private --source $(version)
javadocdir =	$(basedocdir)/javadocs
jmldocdir =	$(basedocdir)/jmldocs

main_memory_use =	-ms256M -mx256M
rac_memory_use =	-ms256M -mx320M
test_memory_use	=	-ms512M -mx10240M
generator_memory_use =  -ms1024M -mx102400M

copyright = "Votail<br />&copy; 2006-11 Dermot Cochran <br />All Rights Reserved"

# implicit rules for paper documentation generation

%.ps: %.gif
	giftopnm $< | pnmtops -noturn > $@
%.ps: %.fig
	fig2dev -L ps $< > $@
%.eps: %.fig
	fig2dev -L eps $< > $@
%.pdf: %.fig
	fig2dev -L pdf $< > $@
%.pdf: %.eps
	epstopdf $< > $@
.pdf_t: %.pstex_t
	sed 's/\.pstex/\.pdf/g' $< > $@
%.pdftex: %.tex
	sed 's/\.pstex_t/\.pdf_t/g' $< > $@
%.pstex: %.fig
	fig2dev -L pstex -m $(FIGSCALE) $< > $@
%.pstex_t: %.fig
	fig2dev -L pstex_t -m $(FIGSCALE) -p `basename $< .fig`.pstex $< > $@
%.ps: %.dvi
	dvips -D600 -Ppdf $< -o $@

%.aux: %.tex
	latex $*

%.dvi: %.tex
	latex $<
	if grep $(BIBWARN) $*.log >/dev/null; \
	then bibtex $(BIBTEXOPT) $*; latex $<; latex $<; fi
	RUNS=$(LATEXMAX); \
	while [ $$RUNS -gt 0 ] ; do \
		if grep $(REFWARN) $*.log > /dev/null; \
		then latex $< ; else break; fi; \
		RUNS=`expr $$RUNS - 1`; \
	done

%.pdf: %.ps
	ps2pdf $<

# identification of phony targets

.PHONY: all build escjava test ps pdf spellcheck \
	classes jmlc jmlc_jmlunit jmlunit jmlunit_classes \
	escjava2-typecheck escjava2 escjava2-current escjava2-core \
	main main-jmlrac jml-junit-tests jmlrac-tests \
	source_docs javadoc jmldoc checkstyle \
	clean clean_other_stamps clean_classes clean_jmlc \
	clean_jmlcjunit clean_jmlunit \
	clean_javadoc clean_jmldoc

# targets

default: classes

all:	build bonc escjava test

build:	classes jml jmlc jmlunit_classes

escjava:	escjava2-typecheck escjava2

test:	jml-junit-tests universal-rac-test

# paper documentation-related

ps:	$(BASE).ps

$(BASE).dvi:	$(BASE).tex\
		$(BASE).bbl

$(BASE).bbl:	$(BASE).aux\
		$(BASE).bib
		bibtex $(BIBTEXOPT) $(BASE)

$(BASE).ps:		$(BASE).dvi

$(BASE).pdf:	$(BASE).ps
		ps2pdf13 $(BASE).ps

pdf:		$(BASE).pdf

ps:		$(BASE).ps

spellcheck:
		aspell --lang=american --master=american -t -c $(BASE).tex

# targets related to building software

classes:	classes.stamp

classes.stamp:	$(javafiles)
	@mkdir -p $(buildpath)
	export CLASSPATH=$(JAVAC_CLASSPATH);\
	$(javac) -g -d $(buildpath) $(java_source_version) $(javapat) && \
	$(javac) -Xlint:unchecked -g -d $(buildpath) $(java_source_version5) $(javapat5) && \
	touch classes.stamp

jml:	jml.stamp

jml.stamp:	$(javafiles)
	export CLASSPATH=$(JMLC_CLASSPATH);\
	$(jml) --Quiet --source $(version) -G -A -a $(javapat) && \
	touch jml.stamp

jmlc:	jmlc.stamp

jmlc.stamp:	$(javafiles)
	@mkdir -p $(jmlc_path)
	export CLASSPATH=$(JMLC_CLASSPATH);\
	$(jmlc) --destination $(jmlc_path) \
		--Quiet --source $(version4) -A -a $(javapat) && \
	touch jmlc.stamp

jmlc_jmlunit: jmlc_jmlunit.stamp

jmlc_jmlunit.stamp:	$(javafiles)
	@mkdir -p $(jmlc_jmlunit_path)
	export CLASSPATH=$(JUNIT_CLASSPATH);\
	$(jmlc) --destination $(jmlc_jmlunit_path) \
		--Quiet --source $(version4) -A -a $(javapat) && \
	touch jmlc_jmlunit.stamp

jmlunit:	jmlc_jmlunit jmlunit.stamp

jmlunit.stamp:	$(javafiles)
	@mkdir -p $(jmlunit_path)
	export CLASSPATH=$(JAVAC_CLASSPATH);\
	$(jmlunit) --destination $(jmlunit_path) \
		--sourcepath $(specpath):$(srcpath):$(testpath) \
		--package --source $(version4) \
		--testLevel=2 $(srcpath)/election/tally && \
	touch jmlunit.stamp

jmlunit_classes:	jmlunit jmlunit_classes.stamp

jmlunit_classes.stamp:	$(jmlunitfiles)
	mkdir -p $(jmlc_jmlunit_path)
	export CLASSPATH=$(JUNIT_CLASSPATH);\
	javac -g -d $(jmlc_jmlunit_path) -source $(version4) $(jmlunitpat) && \
	touch jmlunit_classes.stamp

# targets related to checking software

escjava2-typecheck:	escjava2-typecheck.stamp

escjava2-typecheck.stamp:	$(javafiles)
	chmod a+x $(ESCPATH)/escj
	export VCSVER=0;\
	export ESC_CLASSPATH=$(ESCJAVA_CLASSPATH);\
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	export ESCTOOLS_ROOT=$(ESCPATH);\
		$(escjava) -typecheck $(javapat) && \
	touch escjava2-typecheck.stamp

escjava2:	escjava2.stamp

escjava2.stamp:	$(javafiles)
	export VCSVER=0;\
	export ESC_CLASSPATH=$(ESCJAVA_CLASSPATH);\
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	export ESCTOOLS_ROOT=$(ESCPATH);\
	export SIMPLY_DIR=$(ESCPATH);\
	$(escjava) -suggest -loopsafe $(javapat) && \
	$(escjava) -era $(javapat) && \
	touch escjava2.stamp

escjava2-current:
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	$(escjava) -bootclasspath $(BOOTCP) \
		election/tally/*.java

escjava2-core:
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	$(escjava) -bootclasspath $(BOOTCP) \
		election/tally/*.java

checkstyle.stamp:
	export CLASSPATH=$(CHECKSTYLE_CLASSPATH); \
	java com.puppycrawl.tools.checkstyle.Main \
		-c srg-group.xml $(core_javafiles)

checkstyle:	checkstyle.stamp

# executing the program

main: classes
	export CLASSPATH=$(JAVAC_CLASSPATH);\
	java $(main_memory_use) -version $(version) election.tally.*

main-jmlrac: jmlc
	export CLASSPATH=$(JMLC_CLASSPATH):$(testpath);\
	jmlrac $(rac_memory_use) election.tally.*

jml-junit-tests:	classes jmlunit_classes
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.Ballot_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.BallotCounting_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.Candidate_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.CandidateStatus_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.CountConfiguration_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.ElectionStatus_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.AbstractBallotCounting_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.BallotBox_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.AbstractCountStatus_JML_Test

generate-tests: tests-generated.stamp

tests-generated.stamp:	classes
	export CLASSPATH=$(JAVAC_CLASSPATH); \
	nice nohup java $(generator_memory_use) ie.votail.uilioch.UniversalTestGenerator
	touch tests-generated-stamp

universal-test:	 universal.stamp

universal.stamp:	classes
	export CLASSPATH=$(JAVAC_CLASSPATH); \
	java $(test_memory_use) ie.votail.uilioch.UniversalTestRunner; \
	touch universal.stamp

universal-rac-test:	universal-rac.stamp

universal-rac.stamp:	universal-test jml-junit-test escjava2
	export CLASSPATH=$(UNIT_TEST_CLASSPATH); \
	java $(test_memory_use) ie.votail.model.uilioch.UniversalTestRunner; \
	touch universal.stamp

# generating source-based documentation

source_docs:	javadoc jmldoc

javadoc:	javadoc.stamp

javadoc.stamp:	$(javafiles) $(srcpath)/election/tally/package.html $(basedocdir)/overview.html
	mkdir -p $(javadocdir); \
	export CLASSPATH=$(BASE_CLASSPATH);\
	$(javadoc) -d $(javadocdir) $(javadocflags) \
	-sourcepath .:$(srcpath):$(testpath):$(jdksrcpath) \
	-overview $(basedocdir)/overview.html \
	-doctitle "Votail" \
	-header $(copyright) \
	-footer $(copyright) \
	-subpackages election.tally; \
	touch javadoc.stamp

jmldoc:		jmldoc.stamp

jmldoc.stamp:	$(javafiles) $(srcpath)/election/tally/package.html $(basedocdir)/overview.html
	mkdir -p $(jmldocdir); \
	export CLASSPATH=$(BASE_CLASSPATH);\
	$(jmldoc) -d $(jmldocdir) $(jmldocflags) \
	-sourcepath .:$(srcpath):$(jdksrcpath) \
	-overview $(basedocdir)/overview.html \
	-doctitle "Votail" \
	-header $(copyright) \
	-footer $(copyright) \
	election.tally;
	touch jmldoc.stamp

usermanual:	usermanual.stamp

usermanual.stamp:	
	cd $(usermanual_dir); make pdf
	touch usermanual.stamp

# targets related to cleaning up

clean:	clean_javadoc clean_jmldoc clean_classes clean_jml clean_jmlc clean_jmlcjunit clean_other_stamps clean_distr clean_src_distr
	rm -f $(BASE).dvi $(BASE).ps $(BASE).pdf
	rm -f *.log *.bbl *.blg *.aux *.out
	rm -f *.pstex *.pstex_t *.pdf *.pdf_t *.pdftex
	rm -f *.bak
clean_other_stamps:
	rm -f escjava2-typecheck.stamp escjava2.stamp checkstyle.stamp *.stamp

clean_classes:
	rm -rf distr $(buildpath) classes.stamp jmlunit_classes.stamp

clean_jml:
	rm -rf jml.stamp

clean_jmlc:
	rm -rf $(jmlc_path) jmlc.stamp

clean_jmlcjunit:
	rm -rf $(jmlc_jmlunit_path)/*_JML_Test.java jmlc_jmlunit.stamp

clean_javadoc:
	rm -rf $(javadocdir)/*.html \
		$(javadocdir)/ie* \
		$(javadocdir)/com* \
		$(javadocdir)/images \
		$(javadocdir)/package-list \
		$(javadocdir)/stylesheet.css \
		javadoc.stamp

clean_jmldoc:
	rm -rf $(jmldocdir)/*.html \
		$(jmldocdir)/ie* \
		$(jmldocdir)/com* \
		$(jmldocdir)/images \
		$(jmldocdir)/package-list \
		$(jmldocdir)/stylesheet.css \
		jmldoc.stamp

clean_distr:
	rm -rf distr

clean_src_distr:
	rm -rf src_distr.stamp

bonc:
	external_tools/bonc/bonc -i --print=HTML -po=doc/bonc.html design/*.bon

release: clean
	mkdir -p release
	tar cvf release/Votail0.0.1b.tar --exclude .svn src design diagrams doc requirements license.txt read.me release.notes
	gzip release/Votail0.0.1b.tar

tech_report:
	make -C TechnicalReport
