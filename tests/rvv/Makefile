DIR = $(filter-out vsetvli01/,$(dir $(wildcard */Makefile)))

.PHONY : $(DIR)

build: $(DIR)

$(DIR):
	$(MAKE) -C $@
