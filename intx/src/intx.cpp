#include "intx.hpp"

extern "C" {
  struct uint256_t {
    uint64_t words[4];
  };

  struct div_result256 {
    uint256_t quot;
    uint256_t rem;
  };

  div_result256 intx_udivmod256(uint256_t *u, uint256_t *v) {
    union res {
      intx::div_result<intx::uint256> a;
      div_result256 b;
    
      res(intx::div_result<intx::uint256>&& a): a(a) {}
    } r(udivrem(*((intx::uint256*)u), *((intx::uint256*)v)));
    return r.b;
  }
}
