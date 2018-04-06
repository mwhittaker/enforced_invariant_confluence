#ifndef COMPARABLE_BY_KEY_H_
#define COMPARABLE_BY_KEY_H_

template <typename T, typename K>
class ComparableByKey {
 public:
  bool operator==(const ComparableByKey<T, K>& other) const {
    return Key() == other.Key();
  }
  bool operator!=(const ComparableByKey<T, K>& other) const {
    return Key() != other.Key();
  }
  bool operator<(const ComparableByKey<T, K>& other) const {
    return Key() < other.Key();
  }
  bool operator<=(const ComparableByKey<T, K>& other) const {
    return Key() <= other.Key();
  }
  bool operator>(const ComparableByKey<T, K>& other) const {
    return Key() > other.Key();
  }
  bool operator>=(const ComparableByKey<T, K>& other) const {
    return Key() >= other.Key();
  }

 protected:
  virtual K Key() const = 0;
};

#endif  //  COMPARABLE_BY_KEY_H_
