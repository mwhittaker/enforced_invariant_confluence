# Flags.
CC = clang
CXX = clang++
BIN = bin
DEBUG=1
SANITIZERS=1
VERBOSE=0
CXXFLAGS = -std=c++14 -Wall -Wextra -Werror -I$(BIN) \
			$(shell pkg-config --cflags protobuf) \
			$(shell pkg-config --cflags libglog) \
			$(shell pkg-config --cflags libuv)
LDFLAGS = $(shell pkg-config --libs protobuf) \
			$(shell pkg-config --libs libglog) \
			$(shell pkg-config --libs libuv)

PROTOS = $(wildcard *.proto)
PROTO_HEADERS = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.h))
PROTO_SOURCES = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.cc))
PROTO_OBJECTS = $(addprefix $(BIN)/, $(PROTOS:%.proto=%.pb.o))

# Sources and binaries.
BINARIES = \
	bank_account_client_repl \
	benchmark_client_main \
	benchmark_master_main \
	benchmark_master_repl \
	benchmark_server_main \
	echo_client \
	echo_server \
	loop_echo_client \
	loop_echo_server \
	server_main \
	two_ints_client_repl \
	two_ints_main
BINARY_SOURCES = $(addsuffix .cc, $(BINARIES))
BINARY_OBJECTS = $(addprefix $(BIN)/, $(addsuffix .o, $(BINARIES)))
SOURCES = $(wildcard *.cc)
HEADERS = $(wildcard *.h)
OBJECTS = $(addprefix $(BIN)/, $(SOURCES:%.cc=%.o))
NON_BINARY_OBJECTS = $(filter-out $(BINARY_OBJECTS), $(OBJECTS))

# Conditional flags.
ifeq ($(DEBUG), 1)
	CXXFLAGS += -g -O0
	ifeq ($(CXX), clang++)
		ifeq ($(SANITIZERS), 1)
			CXXFLAGS += -fsanitize=address
			CXXFLAGS += -fsanitize=undefined
		endif
	endif
else
	CXXFLAGS += -O3
endif

ifeq ($(VERBOSE), 0)
	QUIET = @
else
	QUIET =
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
	$(QUIET)mkdir -p $(BIN)

$(BIN)/%.pb.h: %.proto
	@if [ "$(VERBOSE)" = 0 ]; then echo "[PROTOC] $<"; fi
	$(QUIET)protoc --cpp_out=$(BIN) $<

$(PROTO_OBJECTS): $(BIN)/%.o: $(BIN)/%.cc
	@if [ "$(VERBOSE)" = 0 ]; then echo "[CXX]    $<"; fi
	$(QUIET)$(CXX) $(CXXFLAGS) $< -c -o $@
	$(QUIET)$(CXX) $(CXXFLAGS) -MM $< -MP -MT $@ > $(BIN)/$*.d

$(OBJECTS): $(BIN)/%.o: %.cc
	@if [ "$(VERBOSE)" = 0 ]; then echo "[CXX]    $<"; fi
	$(QUIET)$(CXX) $(CXXFLAGS) $< -c -o $@
	$(QUIET)$(CXX) $(CXXFLAGS) -MM $< -MP -MT $@ > $(BIN)/$*.d

$(BINARIES): %: $(BIN)/%.o $(PROTO_OBJECTS) $(NON_BINARY_OBJECTS)
	@if [ "$(VERBOSE)" = 0 ]; then echo "[CXX]    $@"; fi
	$(QUIET)$(CXX) $(CXXFLAGS) $(LDFLAGS) $^ -o $@

tags: $(PROTOS) $(HEADERS) $(SOURCES)
	$(QUIET)ctags --c++-kinds=+p --fields=+iaS --extra=+q --language-force=C++ -R .

.syntastic_cpp_config: Makefile
	$(QUIET)echo "" > $@
	$(QUIET)for flag in $(CXXFLAGS); do \
		echo "$$flag" >> $@; \
	done

.PHONY: clean
clean:
	rm -rf $(BIN)
	rm -f $(BINARIES)

print-%:
	@echo '$*=$($*)'
