dobutsu : dobutsu.cpp
	g++ -o $@ $<

clean :
	rm -f dobutsu

debug :
	g++ -g -o dobutsu dobutsu.cpp

pack :
	tar cfjS hashtable.tar.bz2 hashtable

unpack :
	tar xfjS hashtable.tar.bz2

.PHONY : clean debug pack unpack
