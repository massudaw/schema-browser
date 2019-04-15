# LIBDIR=/opt/pgsql-10/lib/#/usr/lib/postgresql/dimensional.so
INCLUDEDIR=/usr/include/postgresql/server/
all:
	gcc -I  $(INCLUDEDIR) -lpostgres -fpic -c dimensional.c
	gcc  -shared -o dimensional.so dimensional.o
install:
	cp dimensional.so  $(LIBDIR)/dimensional.so
