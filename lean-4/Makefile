### Configuration

# The location of the lake executable (the Lean build system)
LAKE=lake
LOGLEVEL=30

.PHONY: build-lean clean-lean clean

all: build-lean

clean: clean-lean

clean-lean:
	$(LAKE) clean

build-lean:
	$(LAKE) build
