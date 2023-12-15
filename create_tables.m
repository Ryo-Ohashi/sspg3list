/* ------------------------------------------------------------------ CHARACTERISTIC FUNCTIONS ------------------------------------------------------------------ */

// Return the d-bit binary representation of a given integer from the reverse.
function convert_to_binary(num,d)
    assert num lt 2^d;
    bin := IntegerToSequence(num,2);
    return bin cat [0: k in [#bin+1..d]];
end function;

// Return the charcteristic matrix corresponding to a given integer.
function integer_to_characteristic(g,num)
    bin := convert_to_binary(num,2*g);
    a := Matrix(1,g,[bin[j]: j in [g+1..2*g]]); b := Matrix(1,g,[bin[j]: j in [1..g]]);
    return BlockMatrix(2,1,[[a],[b]]);
end function;

// Return the integer corresponding to a given characteristic matrix.
function characteristic_to_integer(g,char)
    a := [char[1][j] mod 2: j in [1..g]]; b := [char[2][j] mod 2: j in [1..g]];
    return SequenceToInteger(b cat a,2);
end function;

// Return the set of characteristic matrices which are g-partitions of a given characteristic matrix.
function split_characteristic(g,char)
    assert Ncols(char) eq g;
    a := ElementToSequence(char[1]); b := ElementToSequence(char[2]);
    return [Matrix(2,1,[[a[j]],[b[j]]]): j in [1..g]];
end function;

// For a given sequence, return the set of indices which give zero entries.
function collect_zero(seq)
    set := {@ @};
    for j in [1..#seq] do if seq[j] eq 0 then set := set join {j-1}; end if; end for;
    return set;
end function;

// For a given sequence, return the set of indices which give even characteristics.
function collect_even(g)
    set := {@ @};
    for j1,j2 in [0..2^g-1] do
        a := Matrix([convert_to_binary(j1,g)]); b := Matrix([convert_to_binary(j2,g)]);
        if (a*Transpose(b))[1][1] mod 2 eq 1 then set := set join {characteristic_to_integer(g,BlockMatrix(2,1,[a,b]))}; end if;
    end for;
    return {@ j: j in [0..2^(2*g)-1] @} diff set;
end function;

/* ------------------------------------------------------------------ SYMPLECTIC FUNCTIONS ------------------------------------------------------------------ */

// For a given square matrix, return the row vector with its diagonal elements aligned.
function diagonal_element(P)
    assert Ncols(P) eq Nrows(P); g := Ncols(P);
    return Matrix(1,g,[P[k][k]: k in [1..g]]);
end function;

// For a given square matrix, return the block matrices that divides it into 2×2 partitions.
function parse_matrix(M)
    assert Ncols(M) eq Nrows(M); g := Integers()!(Ncols(M)/2);
    A := Submatrix(M,1,1,g,g);   B := Submatrix(M,1,g+1,g,g);
    C := Submatrix(M,g+1,1,g,g); D := Submatrix(M,g+1,g+1,g,g);
    return A,B,C,D;
end function;

// Return all symplectic matrices of dim = g corresponding to distinct (2^g)-isogenies.
function collect_symplectic_matrices(g)
    symp_set := {@ @};
    repeat
        M := RandomSymplecticMatrix(g,1); flag := true;
        for N in symp_set do
            A,B,C,D := parse_matrix(M*N^(-1));
            if ChangeRing(C,Integers(2)) eq ZeroMatrix(Integers(2),g) then flag := false; break; end if;
        end for;
        if flag eq true then symp_set := symp_set join {M}; end if;
    until #symp_set eq &*[2^k+1: k in [1..g]];
    return symp_set;
end function;

// Return a symplectic matrix of dim = 3 which induce the action null[0] -> null[index].
function generate_g3transmatrix(index)
    assert index in collect_even(3);
    A := IdentityMatrix(Integers(),3); D := IdentityMatrix(Integers(),3);
    if index eq 27 then
        B := Matrix(3,3,[[1,1,0],[1,1,0],[0,0,0]]);   C := Matrix(3,3,[[1,-1,0],[-1,1,0],[0,0,0]]);
    elif index eq 31 then
        B := Matrix(3,3,[[1,1,1],[1,1,1],[1,1,1]]);   C := Matrix(3,3,[[1,-1,0],[-1,1,0],[0,0,0]]);
    elif index eq 45 then
        B := Matrix(3,3,[[1,0,1],[0,0,0],[1,0,1]]);   C := Matrix(3,3,[[1,0,-1],[0,0,0],[-1,0,1]]);
    elif index eq 47 then
        B := Matrix(3,3,[[1,1,1],[1,1,1],[1,1,1]]);   C := Matrix(3,3,[[1,0,-1],[0,0,0],[-1,0,1]]);
    elif index eq 54 then
        B := Matrix(3,3,[[0,0,0],[0,1,1],[0,1,1]]);   C := Matrix(3,3,[[0,0,0],[0,1,-1],[0,-1,1]]);
    elif index eq 55 then
        B := Matrix(3,3,[[1,1,1],[1,1,1],[1,1,1]]);   C := Matrix(3,3,[[0,0,0],[0,1,-1],[0,-1,1]]);
    elif index eq 59 then
        B := Matrix(3,3,[[1,-1,0],[-1,1,0],[0,0,0]]); C := Matrix(3,3,[[1,1,1],[1,1,1],[1,1,1]]);
    elif index eq 61 then
        B := Matrix(3,3,[[1,0,-1],[0,0,0],[-1,0,1]]); C := Matrix(3,3,[[1,1,1],[1,1,1],[1,1,1]]);
    elif index eq 62 then
        B := Matrix(3,3,[[0,0,0],[0,1,-1],[0,-1,1]]); C := Matrix(3,3,[[1,1,1],[1,1,1],[1,1,1]]);
    else
        char := integer_to_characteristic(3,index);
        a := Matrix([ElementToSequence(char[1])]); b := Matrix([ElementToSequence(char[2])]);
        B := Matrix(3,3,[[b[1][1],0,0],[0,b[1][2],0],[0,0,b[1][3]]]); C := Matrix(3,3,[[a[1][1],0,0],[0,a[1][2],0],[0,0,a[1][3]]]);
    end if;
    return BlockMatrix(2,2,[[A,B],[C,D]]);
end function;

/* ------------------------------------------------------------------ THETA CALCULATE FUNCTIONS ------------------------------------------------------------------ */

// For a given symplectic matrix M and characteristics a,b, return M.a and M.b in theta transformation formula.
function trans_index(M,char)
    A,B,C,D := parse_matrix(M);
    a := Matrix([ElementToSequence(char[1])]); b := Matrix([ElementToSequence(char[2])]);
    Ma := a*Transpose(D) - b*Transpose(C) + diagonal_element(C*Transpose(D));
    Mb := b*Transpose(A) - a*Transpose(B) + diagonal_element(A*Transpose(B));
    return BlockMatrix(2,1,[[Ma],[Mb]]);
end function;

// For a given symplectic matrix M and characteristics a,b, return the value 4*k(M,a,b) in theta transformation formula.
function trans_coeff(M,char)
    A,B,C,D := parse_matrix(M);
    a := Matrix([ElementToSequence(char[1])]); b := Matrix([ElementToSequence(char[2])]);
    sign := a*Transpose(D) - b*Transpose(C);
    sign *:= Transpose(b*Transpose(A) - a*Transpose(B) + 2*diagonal_element(A*Transpose(B)));
    sign -:= a*Transpose(b);
    return sign[1][1] mod 4;
end function;

/* ------------------------------------------------------------------ TABLE CREATION FUNCTIONS ------------------------------------------------------------------ */

// Return two tables which will be used for transformations of theta null-points.
function create_symplectic_table(g)
    Sp2gMat := collect_symplectic_matrices(g); row := #Sp2gMat; col := 2^(2*g);
    index_table := ZeroMatrix(Integers(),row,col); signs_table := ZeroMatrix(Integers(),row,col);
    for j in [1..row] do
        M := Sp2gMat[j];
        for num in [0..col-1] do
            char := integer_to_characteristic(g,num);
            index_table[j][num+1] := characteristic_to_integer(g,trans_index(M,char));
            signs_table[j][num+1] := trans_coeff(M,char) mod 4;
        end for;
    end for;
    return [index_table,signs_table];
end function;

// Return two tables which will be used for computations of (2^g)-isogenies.
function create_isogeny_table(g)
    row := 2^g; col := 2^(2*g);
    index_table := ZeroMatrix(Integers(),row,col); signs_table := ZeroMatrix(Integers(),row,col);
    for num in [0..col-1] do
        char := integer_to_characteristic(g,num);
        a := Matrix([ElementToSequence(char[1])]); b := Matrix([ElementToSequence(char[2])]);
        for k in [0..row-1] do
            beta := Matrix([convert_to_binary(k,g)]);
            index_table[k+1][num+1] := characteristic_to_integer(g,BlockMatrix(2,1,[2*a,b+beta]));
            signs_table[k+1][num+1] := (a*Transpose(beta))[1][1] mod 2;
        end for;
    end for;
    return [index_table,signs_table];
end function;

// Return the tables which will be used for restoring genus-3 hyperelliptic equations.
function create_g3transform_table()
    index_table := ZeroMatrix(Integers(),64,64); signs_table := ZeroMatrix(Integers(),64,64);
    for index in collect_even(3) do
        M := generate_g3transmatrix(61)*generate_g3transmatrix(index)^(-1);
        for num in [0..63] do
            char := integer_to_characteristic(3,num);
            index_table[index+1][num+1] := characteristic_to_integer(3,trans_index(M,char));
            signs_table[index+1][num+1] := trans_coeff(M,char) mod 4;
        end for;
    end for;
    return [index_table,signs_table];
end function;
