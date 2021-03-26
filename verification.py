a = 0xaaaa0;
b = 0x10000;

for i in range(1, 8):
    c = a * b
    print(c)
    b = c << i
    a = c * b
    print(a)

