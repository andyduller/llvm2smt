SRC		= $(wildcard ../src/*.cc)
BIN_REP		= ../bin/
SRC_REP		= ../src/
OBJS		= $(subst $(SRC_REP),$(BIN_REP),$(SRC:.cc=.o))
CPPFLAGS	= -W -Wall -Wno-unused
LDFLAGS		=
EXEC		= llvm2smt

CPPFLAGS += $(shell llvm-config --cxxflags)

#LDFLAGS  += $(shell llvm-config --ldflags --libs jit bitreader bitwriter native)
LDFLAGS  += $(shell llvm-config --ldflags --libs)
LDFLAGS  += -ldl

all: $(EXEC)

$(EXEC) : $(OBJS)
	$(CXX) -o $@ $^ $(LDFLAGS)

${BIN_REP}%.o : %.cc *.h
	$(CXX) -o $@ -c $< $(CPPFLAGS)

.PHONY: clean realclean

clean:
	rm -rf $(BIN_REP)*.o

realclean: clean
	rm -rf $(EXEC)
