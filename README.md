# List up superspecial genus-3 curves using isogeny graph

An implementation of the algorithm used in the paper "Computing Richelot isogeny graph of superspecial abelian threefolds" by Ryo Ohashi, Hiroshi Onuki, Momonari Kudo, Ryo Yoshizumi, and Koji Nuida.

This code allows you listing up superspecial genus-3 curves in characteristic $p \geq 11$. For example, if you want to do that for $p = 97$, please change the first line of file "main.m" to

```
p := 97;
```

and execute

```
load "main.m";
```

The outputs are displayed as the Shioda invariants of hyperelliptic genus-3 curves, and the Dixmier-Ohno invariants of smooth plane quartics.
If necessary, you can restore their explicit forms using built-in functions in Magma.
