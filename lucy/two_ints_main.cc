#include <cstdlib>
#include <iostream>
#include <memory>

namespace {

std::string Usage() {
  return "./two_ints_main <cluster_file> <index> <paxos|segmented|gossip>";
}

}  // namespace

int main(int argc, char* argv[]) {
  if (argc != 4) {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }

  const std::string cluster_filename = argv[0];
  const int index = std::atoi(argv[1]);
  const std::string mode = argv[2];
  (void)cluster_filename;
  (void)index;
  (void)mode;
}
