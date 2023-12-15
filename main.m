p := 11;
K := GF(p^2);
R<x> := PolynomialRing(K);
i := Roots(x^2+1)[1][1];

load "create_tables.m";
g2evens := collect_even(2); g2trans := create_symplectic_table(2); g2isogy := create_isogeny_table(2);
g3evens := collect_even(3); g3trans := create_symplectic_table(3); g3isogy := create_isogeny_table(3); g3hyper := create_g3transform_table();

load "functions.m";

/* ------------------------------------------------------------------ MAIN FUNCTIONS ------------------------------------------------------------------ */

start := Realtime();
SSgEll := collect_ssgellnulls(); SSpSurf := {@ @}; SSp3fold := {@ @};
for j1 in [1..#SSgEll] do null1 := SSgEll[j1];
    for j2 in [j1..#SSgEll] do null2 := SSgEll[j2];
        prod_null2 := product_of_thetapoints(2,[null1,null2]); SSpSurf := SSpSurf join {prod_null2};
        for j3 in [j2..#SSgEll] do null3 := SSgEll[j3];
            prod_null3 := product_of_thetapoints(3,[null1,null2,null3]); SSp3fold := SSp3fold join {prod_null3};
        end for;
    end for;
end for;

SSpSurf := listup_sspg2curve(SSpSurf);
for j in [1..#SSgEll] do null1 := SSgEll[j];
    for k in [1..#SSpSurf] do null2 := SSpSurf[k]; prod_null3 := [];
        for num in [0..63] do
            char := integer_to_characteristic(3,num);
            a := ElementToSequence(char[1]); b := ElementToSequence(char[2]);
            index1 := characteristic_to_integer(1,Matrix(2,1,[[a[1]],[b[1]]])); index2 := characteristic_to_integer(2,Matrix(2,2,[[a[2],a[3]],[b[2],b[3]]]));
            prod_null3 := Append(prod_null3,null1[index1+1]*null2[index2+1]);
        end for;
        SSp3fold := SSp3fold join {prod_null3};
    end for;
end for;

hyper_set, quartic_set := listup_sspg3curve(SSp3fold);
printf "-------------------------------------------------------------------------------\n";
printf "Characteristic p = %o\n", p;
printf "There are superspecial %o quartics and %o hyperelliptic curves of genus 3.\n", #quartic_set, #hyper_set;
finish := Realtime();
printf "Total time: %o seconds.\n\n", finish-start;

Keys(hyper_set); Keys(quartic_set);
