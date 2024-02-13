// Borrowed from pbbsbench
// https://github.com/cmuparlay/pbbsbench/blob/master/testData/sequenceData/trigrams.C
// with some modifications

#include <iostream>
#include <fstream>
#include <math.h>
#include <limits.h>
#include "parlay/random.h"
#include "parlay/primitives.h"

#define TRIGRAM_FILE "../../benchmarks/trigrams.txt"

struct nGramTable {
  int len;
  parlay::random r;

  struct tableEntry {
    char str[10];
    int len;
    char chars[27];
    float probs[27];
  };

  tableEntry S[27][27];

  int index(char c) {
    if (c=='_') return 26;
    else return (c-'a');
  }

  nGramTable() {
    std::ifstream ifile(TRIGRAM_FILE);
    if (!ifile.is_open()) {
      std::cout << "nGramTable: Unable to open trigram file" << std::endl;
      abort();
    } else {
      int i=0;
      while (! ifile.eof()) {
	tableEntry x;
	ifile >> x.str >> x.len;
	float probSum = 0.0;
	for (int j=0; j < x.len; j++) {
	  float prob;
	  ifile >> x.chars[j] >> prob;
	  probSum += prob;
	  if (j == x.len-1) x.probs[j] = 1.0;
	  else x.probs[j] = probSum;
	}
	int i0 = index(x.str[0]);
	int i1 = index(x.str[1]);
	if (i0 > 26 || i1 > 26) abort();
	S[i0][i1] = x;
	i++;
      }
      len = i;
    }
  }

  using uint = unsigned int;
  
  char next(char c0, char c1, int i) {
    int j=0;
    tableEntry E = S[index(c0)][index(c1)];
    uint ri = (uint) r.ith_rand(i);
    double x = ((double) ri)/((double) UINT_MAX);
    while (x > E.probs[j]) j++;
    return E.chars[j];
  }

  int word(int i, char* a, int maxLen) {
    a[0] = next('_','_',i);
    a[1] = next('_',a[0],i+1);
    int j = 1;
    while (a[j] != '_' && j < maxLen-1) {
      j++;
      a[j] = next(a[j-2],a[j-1],i+j);
    }
    //a[j] = 0;
    return j;
  }

  int wordLength(int i, int maxLen) {
    char a0 = next('_','_',i);
    char a1 = next('_',a0,i+1);
    int j = 1;
    while (a1 != '_' && j < maxLen-1) {
      j++;
      char tmp = next(a0,a1,i+j);
      a0 = a1; a1 = tmp;
    }
    return j;
  }

  char* word(int i) {
    int MAX_LEN = 100;
    char a[MAX_LEN+1];
    int l = word(i, a, MAX_LEN);
    char* out = new char[l];
    for(size_t j=0; j < l; j++) out[j] = a[j];
    return out;
  }

  char* string(size_t s, size_t e) {
    size_t n = e - s;
    char* a = new char[n+1];
    size_t j=0;
    while (j < n) {
      size_t l = word(j+s,a+j,n-j);
      a[j+l-1] = ' ';
      j += l;
    }
    a[n] = 0;
    return a;
  }
};

// allocates all words one after the other
template <class str_type>
parlay::sequence<std::string> trigramWords(long n) { 
  nGramTable T = nGramTable();
  return parlay::tabulate(n, [&] (size_t i) {
	   long j = 100 * i;
	   std::string x(T.wordLength(j, 100),' ');
	   T.word(j, x.data(), 100);
	   return x;});
}
