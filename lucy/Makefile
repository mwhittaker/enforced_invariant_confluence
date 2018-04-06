CC = clang
CXX = clang++
BIN = bin
CXXFLAGS = -std=c++14 -Wall -Wextra -Werror -g -I$(BIN) \
		   $(shell pkg-config protobuf) \
		   $(shell pkg-config libglog)
LDFLAGS = $(shell pkg-config --libs protobuf) \
          $(shell pkg-config --libs libglog)

PROTOS = $(wildcard *.proto)
PROTO_HEADERS = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.h))
PROTO_SOURCES = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.cc))
PROTO_OBJECTS = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.o))

BINARIES = two_ints_main echo_client echo_server
BINARY_SOURCES = $(addsuffix .cc, $(BINARIES))
SOURCES = $(filter-out $(BINARY_SOURCES), $(wildcard *.cc))
OBJECTS = $(addprefix $(BIN)/, $(SOURCES:%.cc=%.o)) $(PROTO_OBJECTS)

default: all
all: $(BIN) $(PROTO_HEADERS) $(OBJECTS) $(BINARIES)

$(BIN):
	mkdir -p $(BIN)

$(BIN)/%.pb.h: %.proto
	protoc --cpp_out=$(BIN) $<

$(BIN)/%.h: %.cc

$(BIN)/%.o: %.cc %.h
	$(CXX) $(CXXFLAGS) $< -c -o $@

$(BINARIES): %: %.cc $(OBJECTS)
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $^ -o $@

.PHONY: clean
clean:
	rm -rf $(BIN)
	rm -f $(BINARIES)

print-%:
	@echo '$*=$($*)'
