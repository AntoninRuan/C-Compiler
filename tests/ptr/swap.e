void swap(int *x,int *y)
{
    int t;
     t   = *x;
    *x   = *y;
    *y   =  t;
}

int main()
{
    int num1 = 1;
    int num2 = 2;

    swap(&num1,&num2);

    print(num1);
    print(num2);

    return 0;
}