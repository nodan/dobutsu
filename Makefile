dobutsu : dobutsu.cpp
	g++ -o $@ $<

debug :
	g++ -g -o dobutsu dobutsu.cpp

clean :
	rm -f dobutsu

.PHONY : clean debug
