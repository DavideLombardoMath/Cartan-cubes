solution := true;

/*
This script outputs true if and only if the main theorem of the accompanying paper is true.
More precisely, it outputs true if and only if for every j-invariant considered in the algorithm
described in section 6 an auxiliary prime q can be found that satisfies the properties described
in steps (2a) and (2c) of the algorithm.
*/

/*
We loop over all primes between 19 and 20400 lying in the residue classes 2 and 5 modulo 9.
By the results in the accompanying paper, these are the only primes we need to consider.
*/
total := 0;

for p in [ i : i in [19..20400] | IsPrime(i) and i mod 9 in {2,5} ] do
    "Checking p =", p;
    F:=FiniteField(p,2);    // the finite field F_{p^2}
    P<x>:=PolynomialRing(F);
    /*
    We loop over all the j-invariants allowed by the results in the paper
    In particular, we write j = \pm p^d * c^3 with d in {4,5} and c > 0;
    The bound |j| < 2 * e^39 leads to c < 2^(1/3) e^13 / p^(d/3).
    */
    for d in [4,5] do
        c:= 1;
        while (c lt 2^(1/3)*Exp(13)/(p^(d/3))) do
            for sgn in {-1,1} do
                j:= sgn * p^d * c^3;
		total := total+1;
                E:= IntegralModel(EllipticCurveWithjInvariant(j));
                /*
                We define an elliptic curve E with integral coefficients and j-invariant equal to j.
                */
                D := Discriminant(E);
                check := false;

                /*
                The variable "check" is set to true as soon as we find an auxiliary prime q
                that satisfies the requirements of the algorithm described in Section 6
                of the accompanying paper.
                */
                q:=2;
                while ((check eq false) and (q lt 200)) do
                    /*
                    We consider small primes q of good reduction for E (different from p) and check whether the eigenvalues of the Frobenius at q are cubes in F, updating the variable "check" if needed.
                    */
                    if Gcd(Integers() ! q , Integers() ! D) eq 1 and q ne p then  // Check if E has good reduction at q
                        /*
                        Next, we compute the L-polynomial of E over F_q. It is the inverse characteristic polynomial of Frobenius,
                        hence its roots are cubes if and only if the eigenvalues of Frobenius are
                        */
                        Emodq := ChangeRing(E,GF(q));
                        LPoly := LPolynomial(Emodq);
                        LPoly := ChangeRing(LPoly,F);
                        /*
                        We check if one (hence both) the roots of LPoly are cubes in F. If they are not, we set check to true.
                        */
                        r := Roots(LPoly)[1][1];
                        Ord:=Order(r);
			OrdCubes := Integers()!( (p^2-1)/ 3);
			OrdDividesOrdCubes := (OrdCubes mod Ord) eq 0;
			/*
			An element of F_{p^2}* is a cube if and only if its order
			divides the order of the subgroup F_{p^2}^{*3}, which is (p^2-1)/3
			*/
                        check:= check or ( not OrdDividesOrdCubes );
                    end if;
                    q := NextPrime(q); // Continue with the next prime
                end while;
                solution := solution and check;
                /*
                We update the variable solution, leaving it true if the curve E admits a prime q with the desired properties, and setting it to false otherwise.
                Note that, once the variable solution is set to false, it can never go back to being true.
                */
            end for;
            c := c+1; // Continue with the next j-invariant
        end while;
    end for;
end for;
"Number of pairs (curve, p) tested:", total;
"No such pair has Galois representation contained in G(p):", solution;

