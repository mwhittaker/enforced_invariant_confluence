CC = clang
CXX = clang++
BIN = bin
DEBUG=1
CXXFLAGS = -std=c++14 -Wall -Wextra -Werror -I$(BIN) \
		   $(shell pkg-config protobuf) \
		   $(shell pkg-config libglog)
LDFLAGS = $(shell pkg-config --libs protobuf) \
          $(shell pkg-config --libs libglog)

PROTOS = $(wildcard *.proto)
PROTO_HEADERS = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.h))
PROTO_SOURCES = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.cc))
PROTO_OBJECTS = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.o))

BINARIES = \
	bank_account_client_main \
	benchmark_client_main \
	benchmark_master_repl \
	benchmark_server_main \
	echo_client \
	echo_server \
	server_main \
	two_ints_main
BINARY_SOURCES = $(addsuffix .cc, $(BINARIES))
BINARY_OBJECTS = $(addprefix $(BIN)/, $(addsuffix .o, $(BINARIES)))
SOURCES = $(wildcard *.cc)
HEADERS = $(wildcard *.h)
OBJECTS = $(addprefix $(BIN)/, $(SOURCES:%.cc=%.o))
NON_BINARY_OBJECTS = $(filter-out $(BINARY_OBJECTS), $(OBJECTS))

ifeq ($(DEBUG), 1)
	CXXFLAGS += -g -O0
else
	CXXFLAGS += -O3
endif

default: all
all: $(BIN) \
	 $(PROTO_HEADERS) \
	 $(PROTO_OBJECTS) \
	 $(OBJECTS) \
	 $(BINARIES) \
	 tags \
	 .syntastic_cpp_config

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

tags: $(PROTOS) $(HEADERS) $(SOURCES)
	ctags --c++-kinds=+p --fields=+iaS --extra=+q --language-force=C++ -R .

.syntastic_cpp_config: Makefile
	echo "" > $@
	for flag in $(CXXFLAGS); do \
		echo "$$flag" >> $@; \
	done

.PHONY: clean
clean:
	rm -rf $(BIN)
	rm -f $(BINARIES)

print-%:
	@echo '$*=$($*)'
