all: plugin theory

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin
	./clean_extraction.sh

Makefile.theories: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.theories

theory: plugin Makefile.theories
	mkdir -p -m 0755 _build
	$(MAKE) -f Makefile.theories

plugin: Makefile.plugin
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.plugin install
	$(MAKE) -f Makefile.theories install
	
uninstall: Makefile.theories Makefile.plugin
	$(MAKE) -f Makefile.plugin uninstall
	$(MAKE) -f Makefile.theories uninstall
	
clean: Makefile.theories Makefile.plugin
	make -f Makefile.theories clean
	make -f Makefile.plugin clean

mrproper:
	rm -f Makefile.plugin
	rm -f Makefile.theories

.merlin: Makefile.plugin
	make -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
