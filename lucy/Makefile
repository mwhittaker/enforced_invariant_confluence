CC = clang
CXX = clang++
BIN = bin
CXXFLAGS = -std=c++14 -Wall -Wextra -Werror -I$(BIN) $(shell pkg-config protobuf)
LDFLAGS = $(shell pkg-config --libs protobuf)

PROTOS = $(wildcard *.proto)
PROTO_HEADERS = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.h))
PROTO_SOURCES = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.cc))
PROTO_OBJECTS = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.o))
SOURCES = $(wildcard *.cc)
OBJECTS = $(addprefix $(BIN)/, $(SOURCES:%.cc=%.o)) $(PROTO_OBJECTS)
BINARIES = two_ints_main

default: all
all: $(PROTO_HEADERS) $(OBJECTS) $(BINARIES)

$(BIN):
	mkdir -p $(BIN)

$(BIN)/%.pb.h: %.proto $(BIN)
	protoc --cpp_out=$(BIN) $<

$(BIN)/%.h: %.cc $(BIN)

$(BIN)/%.o: %.cc $(BIN)
	$(CXX) $(CXXFLAGS) $< -c -o $@

two_ints_main: $(BIN)/two_ints_main.o
	$(CXX) $(LDFLAGS) $^ -o $@

.PHONY: clean
clean:
	rm -rf $(BIN)
