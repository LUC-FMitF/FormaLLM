---- MODULE DieHarderWithMCCapacity ---
----------------------------------------
(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.  *)
**************************************************************************)

CONSTANTS Goal     = 4
          Jug      <- MCJug
          Capacity <- MCCapacity

VARIABLES
  d,
  n,
  x,
  y,
  z,
  t,
  w,
  m,
  q,
  o,
  s,
  u,
  f,
  g,
  h,
  i,
  j

Init ==
  /\ d \in 1 .. 10
  /\ n \in 1 .. 10
  /\ x \in 1 .. 10
  /\ y \in 1 .. 10
  /\ z \in 1 .. 10
  /\ t \in 1 .. 10
  /\ w \in 1 .. 10
  /\ m \in 1 .. 10
  /\ q \in 1 .. 10
  /\ o \in 1 .. 10
  /\ s \in 1 .. 10
  /\ u \in 1 .. 10
  /\ f \in 1 .. 10
  /\ g \in 1 .. 10
  /\ h \in 1 .. 10
  /\ i \in 1 .. 10
  /\ j \in 1 .. 10

Next ==
  \* The actions
  \/ \E d' \in 1 .. 10 : d' = d
  \/ \E n' \in 1 .. 10 : n' = n
  \/ \E x' \in 1 .. 10 : x' = x
  \/ \E y' \in 1 .. 10 : y' = y
  \/ \E z' \in 1 .. 10 : z' = z
  \/ \E t' \in 1 .. 10 : t' = t
  \/ \E w' \in 1 .. 10 : w' = w
  \/ \E m' \in 1 .. 10 : m' = m
  \/ \E q' \in 1 .. 10 : q' = q
  \/ \E o' \in 1 .. 10 : o' = o
  \/ \E s' \in 1 .. 10 : s' = s
  \/ \E u' \in 1 .. 10 : u' = u
  \/ \E f' \in 1 .. 10 : f' = f
  \/ \E g' \in 1 .. 10 : g' = g
  \/ \E h' \in 1 .. 10 : h' = h
  \/ \E i' \in 1 .. 10 : i' = i
  \/ \E j' \in 1 .. 10 : j' = j
  \/
    (* The transitions
       d' = d + 1
       n' = n + 1
       x' = x + 1
       y' = y + 1
       z' = z + 1
       t' = t + 1
       w' = w + 1
       m' = m + 1
       q' = q + 1
       o' = o + 1
       s' = s + 1
       u' = u + 1
       f' = f + 1
       g' = g + 1
       h' = h + 1
       i' = i + 1
       j' = j + 1
     *)
    d' = d + 1
    /\ n' = n + 1
    /\ x' = x + 1
    /\ y' = y + 1
    /\ z' = z + 1
    /\ t' = t + 1
    /\ w' = w + 1
    /\ m' = m + 1
    /\ q' = q + 1
    /\ o' = o + 1
    /\ s' = s + 1
    /\ u' = u + 1
    /\ f' = f + 1
    /\ g' = g + 1
    /\ h' = h + 1
    /\ i' = i + 1
    /\ j' = j + 1
  \/
    (* The transitions
       d' = d - 1
       n' = n - 1
       x' = x - 1
       y' = y - 1
       z' = z - 1
       t' = t - 1
       w' = w - 1
       m' = m - 1
       q' = q - 1
       o' = o - 1
       s' = s - 1
       u' = u - 1
       f' = f - 1
       g' = g - 1
       h' = h - 1
       i' = i - 1
       j' = j - 1
     *)
    d' = d - 1
    /\ n' = n - 1
    /\ x' = x - 1
    /\ y' = y - 1
    /\ z' = z - 1
    /\ t' = t - 1
    /\ w' = w - 1
    /\ m' = m - 1
    /\ q' = q - 1
    /\ o' = o - 1
    /\ s' = s - 1
    /\ u' = u - 1
    /\ f' = f - 1
    /\ g' = g - 1
    /\ h' = h - 1
    /\ i' = i - 1
    /\ j' = j - 1
  \/
    (* The transitions
       d' = d + n
       n' = n + 1
       x' = x + n
       y' = y + n
       z' = z + n
       t' = t + n
       w' = w + n
       m' = m + n
       q' = q + n
       o' = o + n
       s' = s + n
       u' = u + n
       f' = f + n
       g' = g + n
       h' = h + n
       i' = i + n
       j' = j + n
     *)
    d' = d + n
    /\ n' = n + 1
    /\ x' = x + n
    /\ y' = y + n
    /\ z' = z + n
    /\ t' = t + n
    /\ w' = w + n
    /\ m' = m + n
    /\ q' = q + n
    /\ o' = o + n
    /\ s' = s + n
    /\ u' = u + n
    /\ f' = f + n
    /\ g' = g + n
    /\ h' = h + n
    /\ i' = i + n
    /\ j' = j + n
  \/
    (* The transitions
       d' = d - n
       n' = n - 1
       x' = x - n
       y' = y - n
       z' = z - n
       t' = t - n
       w' = w - n
       m' = m - n
       q' = q - n
       o' = o - n
       s' = s - n
       u' = u - n
       f' = f - n
       g' = g - n
       h' = h - n
       i' = i - n
       j' = j - n
     *)
    d' = d - n
    /\ n' = n - 1
    /\ x' = x - n
    /\ y' = y - n
    /\ z' = z - n
    /\ t' = t - n
    /\ w' = w - n
    /\ m' = m - n
    /\ q' = q - n
    /\ o' = o - n
    /\ s' = s - n
    /\ u' = u - n
    /\ f' = f - n
    /\ g' = g - n
    /\ h' = h - n
    /\ i' = i - n
    /\ j' = j - n
  \/
    (* The transitions
       d' = d + n + x
       n' = n + 1
       x' = x + n + x
       y' = y + n + x
       z' = z + n + x
       t' = t + n + x
       w' = w + n + x
       m' = m + n + x
       q' = q + n + x
       o' = o + n + x
       s' = s + n + x
       u' = u + n + x
       f' = f + n + x
       g' = g + n + x
       h' = h + n + x
       i' = i + n + x
       j' = j + n + x
     *)
    d' = d + n + x
    /\ n' = n + 1
    /\ x' = x + n + x
    /\ y' = y + n + x
    /\ z' = z + n + x
    /\ t' = t + n + x
    /\ w' = w + n + x
    /\ m' = m + n + x
    /\ q' = q + n + x
    /\ o' = o + n + x
    /\ s' = s + n + x
    /\ u' = u + n + x
    /\ f' = f + n + x
    /\ g' = g + n + x
    /\ h' = h + n + x
    /\ i' = i + n + x
    /\ j' = j + n + x
  \/
    (* The transitions
       d' = d - n - x
       n' = n - 1
       x' = x - n - x
       y' = y - n - x
       z' = z - n - x
       t' = t - n - x
       w' = w - n - x
       m' = m - n - x
       q' = q - n - x
       o' = o - n - x
       s' = s - n - x
       u' = u - n - x
       f' = f - n - x
       g' = g - n - x
       h' = h - n - x
       i' = i - n - x
       j' = j - n - x
     *)
    d' = d - n - x
    /\ n' = n - 1
    /\ x' = x - n - x
    /\ y' = y - n - x
    /\ z' = z - n - x
    /\ t' = t - n - x
    /\ w' = w - n - x
    /\ m' = m - n - x
    /\ q' = q - n - x
    /\ o' = o - n - x
    /\ s' = s - n - x
    /\ u' = u - n - x
    /\ f' = f - n - x
    /\ g' = g - n - x
    /\ h' = h - n - x
    /\ i' = i - n - x
    /\ j' = j - n - x


(* Define a function to compute the Fibonacci sequence *)
fun fibonacci(n) =
  if n = 0
  then 0
  else if n = 1
  then 1
  else fibonacci(n-1) + fibonacci(n-2);

(* Test the function with different values of n *)
val test1 = fibonacci(0);
val test2 = fibonacci(1);
val test3 = fibonacci(2);
val test4 = fibonacci(3);
val test5 = fibonacci(4);
val test6 = fibonacci(5);

(* Print the results *)
Print[
  "fibonacci(0) = ", test1,
  "\nfibonacci(1) = ", test2,
  "\nfibonacci(2) = ", test3,
  "\nfibonacci(3) = ", test4,
  "\nfibonacci(4) = ", test5,
  "\nfibonacci(5) = ", test6
];

(* Define a function to compute the Fibonacci sequence using a while loop *)
fun fibonacci_while(n) =
  let
    var f0 = 0;
    var f1 = 1;
    var f2 = 1;
    while n > 0 do
      f2 = f0 + f1;
      f0 = f1;
      f1 = f2;
      n = n - 1;
    od;
    return f2;
  end;

(* Test the function with different values of n *)
val test1 = fibonacci_while(0);
val test2 = fibonacci_while(1);
val test3 = fibonacci_while(2);
val test4 = fibonacci_while(3);
val test5 = fibonacci_while(4);
val test6 = fibonacci_while(5);

(* Print the results *)
Print[
  "fibonacci_while(0) = ", test1,
  "\nfibonacci_while(1) = ", test2,
  "\nfibonacci_while(2) = ", test3,
  "\nfibonacci_while(3) = ", test4,
  "\nfibonacci_while(4) = ", test5,
  "\nfibonacci_while(5) = ", test6
];

(* Define a function to compute the Fibonacci sequence using a recursive function call *)
fun fibonacci_recursive(n) =
  if n = 0
  then 0
  else if n = 1
  then 1
  else fibonacci_recursive(n-1) + fibonacci_recursive(n-2);

(* Test the function with different values of n *)
val test1 = fibonacci_recursive(0);
val test2 = fibonacci_recursive(1);
val test3 = fibonacci_recursive(2);
val test4 = fibonacci_recursive(3);
val test5 = fibonacci_recursive(4);
val test6 = fibonacci_recursive(5);

(* Print the results *)
Print[
  "fibonacci_recursive(0) = ", test1,
  "\nfibonacci_recursive(1) = ", test2,
  "\nfibonacci_recursive(2) = ", test3,
  "\nfibonacci_recursive(3) = ", test4,
  "\nfibonacci_recursive(4) = ", test5,
  "\nfibonacci_recursive(5) = ", test6
];
====