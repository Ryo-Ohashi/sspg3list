/* ------------------------------------------------------------------ DIM = 1 FUNCTIONS ------------------------------------------------------------------ */

// For given 2-torsions P,Q and R = P+Q of an elliptic curve, return the theta null-point such that P,Q -> 1/2,tau/2.
function torsion_to_nullpoint(P,Q,R)
    a1 := P[1]; a2 := Q[1]; a3 := R[1];
    s1 := (a1-a3)*(a2-a3); s2 := (a3-a2)*(a1-a2); s3 := (a2-a1)*(a3-a1);
    r1 := Sqrt(-s2*s3); r2 := Sqrt(s3*s1); r3 := Sqrt(s1*s2);
    return [r1,r2,r3,0];
end function;

// Return the set of theta null-points corresponding to supersingular elliptic curves.
function collect_ssgellnulls()
    null_set := {@ @};
    for j in Roots(SupersingularPolynomial(p),K) do
        lam := Roots(256*(x^2-x+1)^3-j[1]*(x^2-x)^2,K)[1];
        E := EllipticCurve(x*(x-1)*(x-lam)); P := E![0,0]; Q := E![1,0]; R := E![lam,0];
        null := torsion_to_nullpoint(P,Q,R); null_set := null_set join {null};
    end for;
    return null_set;
end function;

// For given theta null-points on tau_j, return the theta null-point on Omega = diag(tau_1,…,tau_g).
function product_of_thetapoints(g,nulls)
    assert #nulls eq g;
    prod_null := [];
    for num in [0..2^(2*g)-1] do
        char_set := split_characteristic(g,integer_to_characteristic(g,num));
        value := &*[nulls[j][characteristic_to_integer(1,char_set[j])+1]: j in [1..g]]; prod_null := Append(prod_null,value);
    end for;
    return prod_null;
end function;

/* ------------------------------------------------------------------ DIM = 2 FUNCTIONS ------------------------------------------------------------------ */

// For a given theta null-point and lists corresonding to a symplectic matrix, return the transformed theta null-point by the matrix (for g=2 case).
function transform_g2nullpoint(null,index_list,signs_list)
    trans_null := [K!0: j in [1..16]];
    for num in g2evens do
        index := index_list[num+1]; sign := signs_list[num+1];
        if sign eq 0 then
            trans_null[index+1] :=    null[num+1];
        elif sign eq 1 then
            trans_null[index+1] :=  i*null[num+1];
        elif sign eq 2 then
            trans_null[index+1] :=   -null[num+1];
        else
            trans_null[index+1] := -i*null[num+1];
        end if;
    end for;
    return trans_null;
end function;

// For a given theta null-point of an abelian surface, return whether it is isomorphic to the product of two elliptic curves or not.
function is_g2split(null)
    even_set := collect_zero(null) meet g2evens;
    if #even_set eq 0 then
        return false;
    else
        assert #even_set eq 1;
        return true, even_set[1];
    end if;
end function;

// For a given theta null-point of an abelian surface corresponding to a genus-2 curve, return a Rosenhain invariant of it.
function restore_g2rosenhain(null)
    assert is_g2split(null) eq false;
    la := (null[1]*null[9])/(null[5]*null[13]);
    mu := (null[9]*null[3])/(null[13]*null[7]);
    nu := (null[3]*null[1])/(null[7]*null[5]);
    return la,mu,nu;
end function;

// For a given theta null-point on Omega/2, return the theta null-point on Omega (for g=2 case).
function compute_g2twoisogeny(full_null)
    non_zero := {@ 0,1,2,3 @} sdiff collect_zero([full_null[j]: j in [1..4]]);
    base := non_zero[1]; sqrt_null := [K!0: j in [1..8]];
    for k in non_zero do
        if k eq base then sqrt_null[k+1] := full_null[base+1]; else sqrt_null[k+1] := Sqrt(full_null[k+1]*full_null[base+1]); end if;
    end for;
    image_null := [K!0: j in [1..16]]; product_matrix := Matrix(4,4,[<j,k,sqrt_null[j]*sqrt_null[k]>: j in [1..k], k in [1..4]]);
    for num in g2evens do
        value := 0;
        for k in [1..4] do
            index := g2isogy[1][k][num+1]+1; min := Min(index,k); max := Max(index,k);
            if g2isogy[2][k][num+1] eq 0 then
                value +:= product_matrix[min][max];
            else
                value -:= product_matrix[min][max];
            end if;
        end for;
        image_null[num+1] := value;
    end for;
    return image_null;
end function;

/* ------------------------------------------------------------------ DIM = 3 FUNCTIONS ------------------------------------------------------------------ */

// For a given theta null-point and lists corresonding to a symplectic matrix, return the transformed theta null-point by the matrix (for g=3 case).
function transform_g3nullpoint(null,index_list,signs_list)
    trans_null := [K!0: j in [1..64]];
    for num in g3evens do
        index := index_list[num+1]; sign := signs_list[num+1];
        if sign eq 0 then
            trans_null[index+1] :=    null[num+1];
        elif sign eq 1 then
            trans_null[index+1] :=  i*null[num+1];
        elif sign eq 2 then
            trans_null[index+1] :=   -null[num+1];
        else
            trans_null[index+1] := -i*null[num+1];
        end if;
    end for;
    return trans_null;
end function;

// For a given theta null-point of an abelian 3-fold corresponding to a hyperelliptic genus-3 curve, return a Rosenhain invariant of it.
function restore_g3rosenhain(null)
    assert #collect_zero(null) eq 29;
    even_set := collect_zero(null) meet g3evens; index := even_set[1];
    index_list := [g3hyper[1][index+1][num+1]: num in [0..63]]; signs_list := [g3hyper[2][index+1][num+1]: num in [0..63]];
    trans_null := transform_g3nullpoint(null,index_list,signs_list);
    l1 := (trans_null[43]*trans_null[3])/(trans_null[6]*trans_null[46]);
    l2 := (trans_null[43]*trans_null[4])/(trans_null[5]*trans_null[46]);
    l3 := (trans_null[28]*trans_null[43])/(trans_null[46]*trans_null[29]);
    l4 := (trans_null[3]*trans_null[50])/(trans_null[55]*trans_null[6]);
    l5 := (trans_null[4]*trans_null[1])/(trans_null[8]*trans_null[5]);
    return l1,l2,l3,l4,l5;
end function;

// For a given theta null-point of an abelian 3-fold corresponding to a plane quartic, return it.
function restore_quartic(null)
    assert #collect_zero(null) eq 28;
    s11 := (null[13]*null[6])/(null[34]*null[41]);  s21 := (null[28]*null[6])/(null[55]*null[41]);  s31 := (null[13]*null[28])/(null[34]*null[55]);
    s12 := (null[22]*null[29])/(null[57]*null[50]); s22 := (null[3]*null[29])/(null[48]*null[50]);  s32 := (null[3]*null[22])/(null[48]*null[57]);
    s13 := (null[8]*null[15])/(null[43]*null[36]);  s23 := (null[17]*null[15])/(null[62]*null[36]); s33 := (null[17]*null[8])/(null[62]*null[43]);
    a11 := Sqrt(s11); a21 := Sqrt(s21); a31 := Sqrt(s31);
    a12 := (null[6]*null[22]*null[41]*null[57] + null[13]*null[29]*null[34]*null[50] - null[1]*null[17]*null[46]*null[62])/(2*a11*null[34]*null[41]*null[50]*null[57]);
    a22 := (null[6]*null[29]*null[41]*null[50] + null[3]*null[28]*null[48]*null[55] - null[13]*null[22]*null[34]*null[57])/(2*a21*null[41]*null[48]*null[50]*null[55]);
    a32 := (null[4]*null[21]*null[33]*null[56] - null[3]*null[22]*null[34]*null[55] - null[13]*null[28]*null[48]*null[57])/-(2*a31*null[34]*null[48]*null[55]*null[57]);
    a13 := (a11*null[34]*null[41] - a12*null[50]*null[57])/(null[36]*null[43]);
    a23 := (a22*null[48]*null[50] - a21*null[41]*null[55])/(null[36]*null[62]);
    a33 := (a32*null[48]*null[57] + a31*null[34]*null[55])/(null[43]*null[62]);
    row_vec := Matrix(3,1,[[K!-1],[K!-1],[K!-1]]);
    A := Matrix(3,3,[[1/a11,1/a21,1/a31],[1/a12,1/a22,1/a32],[1/a13,1/a23,1/a33]]);
    l1,l2,l3 := Explode(ElementToSequence(A^(-1)*row_vec));
    B := Matrix(3,3,[[l1*a11,l2*a21,l3*a31],[l1*a12,l2*a22,l3*a32],[l1*a13,l2*a23,l3*a33]]);
    k1,k2,k3 := Explode(ElementToSequence(B^(-1)*row_vec));
    V := Matrix(3,3,[[k1*a11,k2*a21,k3*a31],[k1*a12,k2*a22,k3*a32],[k1*a13,k2*a23,k3*a33]])*A^(-1);
    P2<X,Y,Z> := ProjectiveSpace(K,2);
    xi := [V[1][k]*X + V[2][k]*Y + V[3][k]*Z: k in [1,2,3]];
    return (xi[1]*X + xi[2]*Y - xi[3]*Z)^2 - 4*xi[1]*xi[2]*X*Y;
end function;

// For a given theta null-point on Omega/2, return the theta null-point on Omega (for g=3 case).
function compute_g3twoisogeny(full_null)
    non_zero := {@ 0,1,2,3,4,5,6,7 @} sdiff collect_zero([full_null[j]: j in [1..8]]);
    if #non_zero eq 8 then
        sqrt_null := [full_null[1]];
        for k in [2..7] do sqrt_null := Append(sqrt_null,Sqrt(full_null[1]*full_null[k])); end for;
        prod := &*[sqrt_null[k]: k in [2..7]];
        check := full_null[1]*full_null[2]*full_null[3]*full_null[4] + full_null[5]*full_null[6]*full_null[7]*full_null[8] - full_null[33]*full_null[34]*full_null[35]*full_null[36];
        sqrt_null := [2*prod*sqrt_null[k]: k in [1..7]]; sqrt_null[8] := full_null[1]^3*check;
    else
        base := non_zero[1]; sqrt_null := [K!0: j in [1..8]];
        for k in non_zero do
            if k eq base then sqrt_null[k+1] := full_null[base+1]; else sqrt_null[k+1] := Sqrt(full_null[k+1]*full_null[base+1]); end if;
        end for;
    end if;
    image_null := [K!0: j in [1..64]];
    product_matrix := Matrix(8,8,[<j,k,sqrt_null[j]*sqrt_null[k]>: j in [1..k], k in [1..8]]);
    for num in g3evens do
        value := 0;
        for k in [1..8] do
            index := g3isogy[1][k][num+1]+1; min := Min(index,k); max := Max(index,k);
            if g3isogy[2][k][num+1] eq 0 then
                value +:= product_matrix[min][max];
            else
                value -:= product_matrix[min][max];
            end if;
        end for;
        image_null[num+1] := value;
    end for;
    return image_null;
end function;

/* ------------------------------------------------------------------ LISTUP FUNCTIONS ------------------------------------------------------------------ */

// Return the number of isomorphism classes of superspecial genus-2 curves.
function number_of_sspg2curve()
    assert p gt 5;
    num := (p^3 + 24*p^2 + 141*p - 166)/2880;
    num -:= (1-LegendreSymbol(-1,p))/32;
    num +:= (1-LegendreSymbol(-2,p))/8;
    num +:= (1-LegendreSymbol(-3,p))/18;
    if p mod 5 eq 4 then
        num := num + 4/5;
    end if;
    return Integers()!num;
end function;

// Return the list of superspecial genus-2 curves.
function listup_sspg2curve(prod_set)
    null_set := prod_set; isom_set := AssociativeArray(); step := 0; limit := number_of_sspg2curve();
    repeat
        step := step + 1; full_null := null_set[step];
        for j in [1..15] do
            index_list := [g2trans[1][j][num+1]: num in [0..15]]; signs_list := [g2trans[2][j][num+1]: num in [0..15]];
            trans_null := transform_g2nullpoint(full_null,index_list,signs_list);
            image_null := compute_g2twoisogeny(trans_null);
            if is_g2split(image_null) eq false then
                la,mu,nu := restore_g2rosenhain(image_null);
                inv := AbsoluteInvariants(HyperellipticCurve(x*(x-1)*(x-la)*(x-mu)*(x-nu)));
                if IsDefined(isom_set,inv) ne true then
                    null_set := null_set join {image_null}; isom_set[inv] := step;
                end if;
            end if;
        end for;
    until #isom_set eq limit;
    return null_set diff prod_set;
end function;

// Return the number of isomorphism classes of superspecial genus-3 curves.
function number_of_sspg3curve()
    assert p gt 7;
    num := (p^6 - p^5 + 610*p^4 - 2410*p^3 + 67789*p^2 - 171109*p + 105120)/1451520;
    num +:= (p^2-4*p+87)*(1-LegendreSymbol(-1,p))/384;
    num +:= (p^2+2*p-35)*(1-LegendreSymbol(-3,p))/648;
    num +:= (1-LegendreSymbol(-1,p))*(1-LegendreSymbol(-2,p))/16;
    num +:= (1-LegendreSymbol(-1,p))*(1-LegendreSymbol(-3,p))/12;
    num +:= (1-LegendreSymbol(-7,p))/7;
    if p mod 7 eq 6 then
        num := num + 6/7;
    end if;
    if p mod 9 eq 8 then
        num := num + 2/3;
    end if;
    return Integers()!num;
end function;

// Return the lists of superspecial genus-3 hyperelliptic curves and superspecial plane quartics.
function listup_sspg3curve(prod_set)
    null_set := IndexedSetToSequence(prod_set); hyper_set := AssociativeArray(); quartic_set := AssociativeArray(); step := 0; limit := number_of_sspg3curve();
    repeat
        step := step + 1; full_null := null_set[step];
        for j in [1..135] do
            index_list := [g3trans[1][j][num+1]: num in [0..63]]; signs_list := [g3trans[2][j][num+1]: num in [0..63]];
            trans_null := transform_g3nullpoint(full_null,index_list,signs_list);
            image_null := compute_g3twoisogeny(trans_null);
            if #collect_zero(image_null) eq 28 then
                F := restore_quartic(image_null); C := Curve(ProjectiveSpace(K,2),F);
                inv := DixmierOhnoInvariants(C: normalize := true);
                if IsDefined(quartic_set,inv) ne true then
                    null_set := Append(null_set,image_null); quartic_set[inv] := step;
                end if;
            elif #collect_zero(image_null) eq 29 then
                l1,l2,l3,l4,l5 := restore_g3rosenhain(image_null); C := HyperellipticCurve(x*(x-1)*(x-l1)*(x-l2)*(x-l3)*(x-l4)*(x-l5));
                inv := ShiodaInvariants(C: normalize := true);
                if IsDefined(hyper_set,inv) ne true then
                    null_set := Append(null_set,image_null); hyper_set[inv] := step;
                end if;
            end if;
        end for;
        printf "[Step: %o/%o] > #Isom = %o\n", step, #prod_set + limit, #quartic_set + #hyper_set;
    until #hyper_set + #quartic_set eq limit;
    return hyper_set, quartic_set;
end function;
