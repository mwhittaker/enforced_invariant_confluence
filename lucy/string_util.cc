#include "string_util.h"

#include <algorithm>
#include <iterator>
#include <sstream>

// https://stackoverflow.com/a/237280/3187068
std::vector<std::string> Split(const std::string& s) {
  std::istringstream iss(s);
  std::vector<std::string> words;
  std::copy(std::istream_iterator<std::string>(iss),
            std::istream_iterator<std::string>(), std::back_inserter(words));
  return words;
}
