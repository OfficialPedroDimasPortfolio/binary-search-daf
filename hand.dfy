
  function sorted(a:array<int>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }
  
method binarySearch(a:array<int>, n:int, e:int) returns (z:int)
  requires 0 < n <= a.Length
  requires sorted(a,n)
  //Z positivo
  ensures n > z >= 0 ==> a[z] == e
  //Z negativo
  ensures z < 0 ==> forall k :: 0 <= k < n ==> a[k] != e 

{
    var start := 0;
    var end := n;
    var mid := 0;

    while(start < end)
    decreases end-start;
    invariant 0 <= start <= end <= n && 0 <= mid;
    invariant forall j ::  0<= j < n && !(start <= j < end) ==> a[j] != e
    {
      mid := (start + end) / 2;     
      //verifica se e maior
      if e > a[mid]{start := mid +1;}
      //verifica se e menor
      else if e < a[mid]{end := mid;}
      //caso seja igual
      else{return mid;}
    }
    return -mid-1;
}


