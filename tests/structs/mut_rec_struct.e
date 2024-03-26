struct structA;

struct structB {
    struct structA* a;
    int n;
};

struct structA {
    struct structB b;
};


int main() {
    struct structB strB;
    strB.n = 1;

    struct structA strA;
    strA.b = strB;
    strB.a = & strA;

    return(strA.b.n);
}