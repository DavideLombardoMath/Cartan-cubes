load "FFT.m";
SetLogFile("AbelFFT-gamma.out");

// Global variables
// GlobalMax stores the maximum value witnessed so far for the ratio |D_\gamma(s)|/\sqrt{ps}
GlobalMax := 0;
// SRD stores the values of the function \sum_{d | m} 1/d
SRD := [Rationals()!0 : i in [1..110000]];
// C is the field of complex numbers with 16 digits of precision
C := ComplexField(16);

// As described in the paper, we loop over primes and compute D(s) for all s < p
for p in [ j : j in [3..110000] | IsPrime(j) and j mod 9 in {2,5} ] do
	"p =", p;
	MaxP := 0;        // the maximum ratio |D_\gamma(s)|/\sqrt{ps} witnessed so far for the prime p
	F2 := GF(p,2);    // the finite field F_{p^2}
    
	/*
	Find the smallest quadratic non-residue modulo p
	and let SqrEps be its square root in F_{p^2}
	*/
	testNonsquare := false;
	ep := 0;
	while not testNonsquare do
		ep := ep + 1;
		if not IsSquare(GF(p)!ep) then
			testNonsquare := true;
			_, SqrEps := IsSquare(F2!ep);
		end if;
	end while;

	// Find a non-cube in F_{p^2}
	testNotCube := false;
	while not testNotCube do
		nc := Random(F2);
		testNotCube := ( nc^( Integers()! ((p^2-1)/3) )) ne F2!1;
	end while;

	/* 
	Next we compute the set of a_2 \in F_p such that nc * (1 + a_2 * SqrEps)
	is a cube. Equivalently, the set of a_2 such that (1 + a_2 * SqrEps)
	lies in a specific non-trivial coset modulo cubes.
	The resulting value of D_\gamma(s) is independent of the choice of nc, up to
	complex conjugation (which does not change the absolute value of D_\gamma(s))
	*/
	time A1 := [ a2 : a2 in GF(p) | ( nc*(1+a2*SqrEps))^(Integers()!( (p^2-1)/3 ) ) eq 1 ];
	/*
	In general, the set F'(k) of a_2 such that nc * (k + a_2 * SqrEps) is a cube
	is simply given by {k*a : a in A1}
	*/

	/*
	We now construct the characteristic function of the
	set A1 = F(1), represented as an array of length p
	*/
	CharacteristicFunction := [C!0 : i in [1..p]];
	for a in A1 do
		CharacteristicFunction[Integers()!a+1] := 1;
	end for;

	/*
	We compute the (Fast) Fourier Transform of this characteristic
	function. By definition, the b-th coefficient of the Fourier transform
	is given by \sum_{a in A1} exp(2 pi i / p * a b)
	= \sum_{a in F'(b)} exp(2 pi i / p * a) = c_\gamma(b)
	*/
	time FourierCoeffs := RaderFFT(CharacteristicFunction);
	// We drop the zero-th Fourier coefficient, which is simply #F(1)
	FourierCoeffs := [FourierCoeffs[i] : i in [2..#FourierCoeffs]];

	/*
	We can now compute D(s) explicitly for all s < p
	D(s) is obtained from D(s-1) by adding a single summand
	*/
	PartialSum := 0;
	for s in [1..(p-1)] do
		/*
		Look up the value of \sum_{k | m} 1/k;
		if it has not been computed yet, we compute and store it
		*/
		if SRD[s] ne 0 then
			srd := SRD[s];
		else
			srd := &+[ 1/k : k in Divisors(s) ];
			SRD[s] := srd;
		end if;
		/*
		Compute the partial sum defining D_\gamma(s) and update the maximum
		ratio |D_\gamma(s)|/\sqrt{sp}, both for this single p and for all p
		tested so far
		*/
		PartialSum := PartialSum + FourierCoeffs[s] * srd;
		GlobalMax := Max( GlobalMax, Abs(PartialSum) / (Sqrt(p) * Sqrt(s)) );
		MaxP := Max( MaxP, Abs(PartialSum) / (Sqrt(p) * Sqrt(s)) );
	end for;
	"Maximum ratio |D_\gamma(s)|/(\sqrt{ps}) =", MaxP;    // print the optimal constant for p
	"Maximum ratio over all p =", GlobalMax;     // print the optimal constant for all primes up to p
end for;

quit;