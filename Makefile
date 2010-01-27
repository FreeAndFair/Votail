
RELEASE = v0.0.0
BASE	= proposal
BIBTEXOPT = 
BIBWARN = 'LaTeX Warning: Citation'
REFWARN = 'Rerun to get cross-references'
LATEXMAX = 6
FIGSCALE = 0.5

# CLASSPATH components

CORECP	= src:unittest
SPECS = external_tools/JML/specs
LIB = external_libraries
JMLCP = $(LIB)/jmlruntime.jar:$(LIB)/jmljunitruntime.jar:$(LIB)/jml-release.jar:$(SPECS)
JUNITCP = $(LIB)/junit.jar

# local variables for build process
javac ?= /usr/bin/javac
jml ?= ./external_tools/bin/jml
jmlrac ?= ./external_tools/bin/jmlrac
jmlc ?= ./external_tools/bin/jmlc
jmldoc ?= ./external_tools/bin/jmldoc
jmlunit ?= ./external_tools/bin/jmlunit

basedocdir = doc
srcpath = src
testpath = unittest
specpath =$(SPECS)
buildpath =	build
jmlc_path =	jmlc_build
jmlunit_path =	jmlunit_src
jmlc_jmlunit_path =	jmlc_jmlunit_build

ESCPATH ?= external_tools/ESCJava2/ESCJava2-2.0.5-04-11-08-binary
escjava = $(ESCPATH)/Escjava/escj -source 1.4 -vclimit 2500000 -warnUnsoundIncomplete
export ESCTOOLS_ROOT=$(ESCPATH)
export SIMPLIFY=$(ESCPATH)/Escjava/release/master/bin/Simplify-1.5.4.macosx

# Various CLASSPATH constructions

BASE_CLASSPATH	= $(CORECP):$(JCECP):$(FOPCP):$(MISCCP):$(JUNITCP):$(JMLCP)
JAVAC_CLASSPATH	= $(buildpath):$(BASE_CLASSPATH)
JMLC_CLASSPATH	= $(jmlc_path):$(BASE_CLASSPATH)
JUNIT_CLASSPATH	= $(jmlc_jmlunit_path):$(BASE_CLASSPATH)
ESCJAVA_CLASSPATH	= $(CORECP):$(JCECP):$(FOPCP):$(MISCCP):$(JUNITCP):$(JMLCP):$(ESCJAVA2CP)
UNIT_TEST_CLASSPATH	= $(jmlc_jmlunit_path):$(testpath):$(buildpath):$(JCECP):$(FOPCP):$(MISCCP):$(JUNITCP):$(JMLCP)
CHECKSTYLE_CLASSPATH	= $(CORECP):$(CHECKSTYLECP)

javapat	=	$(srcpath)/election/tally/*.java
javafiles =	$(wildcard $(srcpath)/election/tally/*.java)
jmlunitpat =	$(jmlunit_path)/election/tally/*.java
jmlunitfiles =	$(wildcard $(jmlunit_path)/election/tally/*.java)
generated_jmlunitfiles	=	$(wildcard $(jmlunit_path)/election/tally/*_JML_Test.java)
classfiles =	$(foreach javafile,$(javafiles),\
		$(subst .java,.class,$(javafile)))
javadocflags =	-version -author -private -source 1.4
jmldocflags =	-version -author -private --source 1.4
javadocdir =	$(basedocdir)/javadocs
jmldocdir =	$(basedocdir)/jmldocs

main_memory_use =	-ms256M -mx256M
rac_memory_use =	-ms256M -mx320M
test_memory_use	=	-ms256M -mx320M

copyright = "Votail<br />&copy; 2006-9 University College Dublin, Ireland <br />All Rights Reserved"

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

all:	build source_docs test escjava distr

build:	classes jml jmlc jmlunit_classes

escjava:	escjava2-typecheck escjava2

test:	jml-junit-tests

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
	$(javac) -g -d $(buildpath) -source 1.4 $(javapat) && \
	touch classes.stamp

jml:	jml.stamp

jml.stamp:	$(javafiles)
	export CLASSPATH=$(JMLC_CLASSPATH);\
	$(jml) --Quiet --source 1.4 -A -a $(javapat) && \
	touch jml.stamp

jmlc:	jmlc.stamp

jmlc.stamp:	$(javafiles)
	@mkdir -p $(jmlc_path)
	export CLASSPATH=$(JMLC_CLASSPATH);\
	$(jmlc) --destination $(jmlc_path) \
		--Quiet --source 1.4 -A -a $(javapat) && \
	touch jmlc.stamp

jmlc_jmlunit: jmlc_jmlunit.stamp

jmlc_jmlunit.stamp:	$(javafiles)
	@mkdir -p $(jmlc_jmlunit_path)
	export CLASSPATH=$(JUNIT_CLASSPATH);\
	$(jmlc) --destination $(jmlc_jmlunit_path) \
		--Quiet --source 1.4 -A -a $(javapat) && \
	touch jmlc_jmlunit.stamp

jmlunit:	jmlc_jmlunit jmlunit.stamp

jmlunit.stamp:	$(javafiles)
	@mkdir -p $(jmlunit_path)
	export CLASSPATH=$(JAVAC_CLASSPATH);\
	$(jmlunit) --destination $(jmlunit_path) \
		--sourcepath $(specpath):$(srcpath):$(testpath) \
		--package --source 1.4 \
		--testLevel=2 $(srcpath)/election/tally && \
	cp unittest/election/tally*_JML_TestData.java $(jmlunit_path)
	touch jmlunit.stamp

jmlunit_classes:	jmlunit jmlunit_classes.stamp

jmlunit_classes.stamp:	$(jmlunitfiles)
	mkdir -p $(jmlc_jmlunit_path)
	export CLASSPATH=$(JUNIT_CLASSPATH);\
	javac -g -d $(jmlc_jmlunit_path) -source 1.4 $(jmlunitpat) && \
	touch jmlunit_classes.stamp

# targets related to checking software

escjava2-typecheck:	escjava2-typecheck.stamp

escjava2-typecheck.stamp:	$(javafiles)
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	$(escjava) -typecheck $(javapat) && \
	touch escjava2-typecheck.stamp

escjava2:	escjava2.stamp

escjava2.stamp:	$(javafiles)
	export CLASSPATH=$(ESCJAVA_CLASSPATH);\
	$(escjava) $(javapat) && \
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
	java $(main_memory_use) election.tally.*

main-jmlrac: jmlc
	export CLASSPATH=$(JMLC_CLASSPATH):$(testpath);\
	jmlrac $(rac_memory_use) election.tally.*

jml-junit-tests:	classes jmlunit_classes
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.AbstractBallotCounting_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.AbstractCountStatus_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.Ballot_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.BallotBox_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.BallotCounting_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.Candidate_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.CandidateStatus_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.Constituency_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.CountConfiguration_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.Decision_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.DecisionStatus_JML_Test
	export CLASSPATH=$(UNIT_TEST_CLASSPATH);\
	java junit.textui.TestRunner $(test_memory_use) election.tally.ElectionStatus_JML_Test

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
	rm -f escjava2-typecheck.stamp escjava2.stamp checkstyle.stamp

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
