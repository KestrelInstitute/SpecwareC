all: coq theories/specware_c_plugin.cmxs

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

theories/specware_c_plugin.cmxs: coq
	ln -sf ../src/specware_c_plugin.cmxs theories/specware_c_plugin.cmxs

install: coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
