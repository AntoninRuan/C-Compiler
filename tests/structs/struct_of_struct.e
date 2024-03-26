struct point {
    int x;
    int y;
};

struct ligne {
    struct point p1;
    struct point p2;
};

int main() {
    struct point p;
    
    p.x = 1;
    p.y = 2;

    struct ligne l;
    l.p1 = p;

    return l.p1.x;
}