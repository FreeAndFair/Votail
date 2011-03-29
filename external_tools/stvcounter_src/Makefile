all: stvcounter.jar

clean:
	rm -rf build/* stvcounter.jar

SRCS = Ballot.java BallotList.java CandidateBallotMap.java Candidate.java \
       CandidatePreference.java Display.java EditorKit.java Election.java \
       InitParams.java ReadDataFromCSVFile.java Status.java \
       Surplus.java SwingWorker.java

stvcounter.jar: $(SRCS)
	rm -rf build/*
	javac -d build $(SRCS)
	cp *.gif build
	rm -f stvcounter.jar
	jar cvfm stvcounter.jar MANIFEST.MF -C build com -C build 1.gif -C build 2.gif -C build 3.gif
