#include "rand_util.h"

#include <random>

// https://cpppatterns.com/patterns/choose-random-element.html
int RandomInt(int low_inclusive, int high_exclusive) {
  std::random_device random_device;
  std::mt19937 engine{random_device()};
  std::uniform_int_distribution<int> dist(low_inclusive, high_exclusive - 1);
  return dist(engine);
}

bool RandomBool(double true_probability) {
  std::random_device random_device;
  std::mt19937 engine{random_device()};
  std::bernoulli_distribution dist(true_probability);
  return dist(engine);
}
