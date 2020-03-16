#include <iostream>

int main()
{
  std::cout << "Printable ASCII:\n";
  for (char i = 32; i < 127; ++i) {
    std::cout << i << ' ';
    if (i % 16 == 15)
      std::cout << '\n';
  }
}
