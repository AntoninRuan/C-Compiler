struct person
{
   int age;
};

int main()
{
    struct person *personPtr;
    struct person person1;
    personPtr = &person1;   

    personPtr->age = 10;

    return personPtr->age;
}