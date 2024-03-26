int main() {
    int x = 99;
    int* xP = &x;
    int** xPP = &xP;
    return **xPP;
}