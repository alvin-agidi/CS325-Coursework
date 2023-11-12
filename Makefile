CXX=clang++ -std=c++17
CFLAGS= -g -O3 `llvm-config --cppflags --ldflags --system-libs --libs all` \
-Wno-unused-function -Wno-unknown-warning-option -fno-rtti

mccomp: mccomp.cpp
	$(CXX) mccomp.cpp $(CFLAGS) -o mccomp

# parser: parser.cpp
# 	$(CXX) parser.cpp $(CFLAGS) -o parser

# astnodes: mccomp.cpp
# 	$(CXX) astnodes.cpp $(CFLAGS) -o astnodes

clean:
	rm -rf mccomp 
