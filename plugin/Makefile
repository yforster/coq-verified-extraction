all: plugin

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin

plugin: Makefile.plugin
	mkdir -p -m 0755 _build
	$(MAKE) -f Makefile.plugin

install: plugin
	$(MAKE) -f Makefile.plugin install
	
uninstall: Makefile.plugin
	$(MAKE) -f Makefile.plugin uninstall
	
clean: Makefile.plugin
	make -f Makefile.plugin clean

mrproper:
	rm -f Makefile.plugin

.merlin: Makefile.plugin
	make -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
