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

BINARIES = two_ints_main \
		   echo_client \
		   echo_server \
		   bank_account_client_main \
		   server_main
BINARY_SOURCES = $(addsuffix .cc, $(BINARIES))
BINARY_OBJECTS = $(addprefix $(BIN)/, $(addsuffix .o, $(BINARIES)))
SOURCES = $(wildcard *.cc)
OBJECTS = $(addprefix $(BIN)/, $(SOURCES:%.cc=%.o))
NON_BINARY_OBJECTS = $(filter-out $(BINARY_OBJECTS), $(OBJECTS))

default: all
all: $(BIN) $(PROTO_HEADERS) $(PROTO_OBJECTS) $(OBJECTS) $(BINARIES)

# See http://scottmcpeak.com/autodepend/autodepend.html.
-include $(PROTO_OBJECTS:.o=.d)
-include $(OBJECTS:.o=.d)

$(BIN):
	mkdir -p $(BIN)

$(BIN)/%.pb.h: %.proto
	protoc --cpp_out=$(BIN) $<

$(PROTO_OBJECTS): $(BIN)/%.o: $(BIN)/%.cc
	$(CXX) $(CXXFLAGS) $< -c -o $@
	$(CXX) $(CXXFLAGS) -MM $< -MP -MT $@ > $(BIN)/$*.d

$(OBJECTS): $(BIN)/%.o: %.cc
	$(CXX) $(CXXFLAGS) $< -c -o $@
	$(CXX) $(CXXFLAGS) -MM $< -MP -MT $@ > $(BIN)/$*.d

$(BINARIES): %: $(BIN)/%.o $(PROTO_OBJECTS) $(NON_BINARY_OBJECTS)
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $^ -o $@

.PHONY: clean
clean:
	rm -rf $(BIN)
	rm -f $(BINARIES)

print-%:
	@echo '$*=$($*)'
