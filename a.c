#include <stdio.h>

typedef unsigned _BitInt(256) u256;

int main() {
    u256 a = 0x1234;
    u256 b = 255;
    printf("%d\n", a << b);
    printf("%d\n", a >> b);
    return 0;
}
