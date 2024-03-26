int main(){
  int x = 1;
  int *y = &x;
  int** z = &y;
  **z = 3;
  return x;
}
