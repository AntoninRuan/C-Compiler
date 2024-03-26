int main() {
    int x = 1;
    *&x = 2;

    int* y = &x;
    int* z = &*y;

    print(x);
    *z = 3;

    return x;
}