int f(int* z) {
    int x = 2;
    int* y = &x;

    *y = 3;
    *z = 2;

    return x;
}

int main() {
    int new_int = 0;
    int* push_stck = &new_int;

    int a = 1;
    int b = f(&a);

    print(*push_stck);
    print(a);
    return(b);
}