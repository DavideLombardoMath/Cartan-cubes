/*
The next function takes as input a sequence of elements a and returns
a new sequence that is the "bit-reversed" version of a.

The "bit-reversed" sequence is obtained by reversing the order of bits in the
binary representation of the index of each element in the original sequence.
In other words, if the binary representation of the index of an element in the
original sequence is b_{k-1} b_{k-2} ... b_1 b_0, where b_i is either 0 or 1, 
then the corresponding index in the bit-reversed sequence is b_0 b_1 ... b_{k-2} b_{k-1}.
*/
function bitrev(a)
	// Determine the number of bits required to represent the largest index in the sequence
	p:=#(IntegerToSequence((#a)-1,2));

	// Create an empty sequence to hold the bit-reversed sequence
	b:=[];

	// Loop through each index in the original sequence
	for i :=1 to #a do
		// Convert the current index to binary and pad with zeros on the left to match the number of bits required
		d:=IntegerToSequence(i-1,2,p); 

		// Reverse the binary representation of the index and convert it back to an integer to get the bit-reversed index
		reversed_d := Reverse(d);
		bit_rev_index := SequenceToInteger(reversed_d,2);

		// Copy the element from the original sequence corresponding to the bit-reversed index to the new sequence
		b[i]:=a[bit_rev_index+1];
	end for;

	// Return the bit-reversed sequence
	return b;
end function;


/*
Function to compute the discrete Fourier transform (DFT) of a vector
of 2-power length using the Cooley-Tukey algorithm. 
*/
function fft2power(input_vector)
	// Get the base ring of the input vector
	base_ring := Parent(input_vector[1]);

	// Create variables to hold the imaginary unit and the constant pi for use in complex arithmetic
	imaginary_unit := base_ring.1;
	pi_constant := Pi(base_ring);

	// Create a local copy of the input vector
	vector_copy := input_vector;

	// Determine the length of the input vector
	vector_length := #vector_copy;

	// Compute the base-2 logarithm of the length of the input vector
	log_length := Ilog2(vector_length);

	// Perform bit-reversal on the input vector
	bit_reversed_vector := bitrev(vector_copy);

	// Perform the Cooley-Tukey FFT algorithm
	for sub_dft_size := 1 to log_length do 
		// Set the size of the sub-DFT being computed
		dft_size := 2^sub_dft_size;

		// Compute half the size of the sub-DFT
		half_dft_size := dft_size div 2;

		// Iterate over the sub-DFTs of size half_dft_size
		for j := 1 to half_dft_size do
			// Compute the twiddle factor for this sub-DFT
			twiddle_factor := Exp(-1 * imaginary_unit * 2 * pi_constant * (j - 1) / dft_size);

			// Iterate over the groups of size dft_size within the input vector
			for group_start_index := 0 to vector_length - dft_size by dft_size do
				// Extract the two elements of the sub-DFT
				first_element := bit_reversed_vector[group_start_index + j];
				second_element := bit_reversed_vector[group_start_index + j + half_dft_size] * twiddle_factor;

				// Perform the butterfly operation on the two elements
				bit_reversed_vector[group_start_index + j] := first_element + second_element;
				bit_reversed_vector[group_start_index + j + half_dft_size] := first_element - second_element;
			end for;
		end for;
	end for;

	// Store the output vector in the input vector
	output_vector := [bit_reversed_vector[i] : i in [1..vector_length]];

	// Return the output vector
	return output_vector;
end function;



/*
The next function pads a list S with zeros to a suitable power of 2, then returns the padded list
*/
function pad_list_to_power_of_two(S)
    // Get the length of the list
    N := #S;
    // Find the ceiling of log base 2 of N
    l := Ceiling(Log(2, N));
    // Calculate the new length of the list as a suitably large power of two
    new_length := 2^(l+1);
    // Pad the list with zeros to the new length and return it
    return S cat [0 : i in [1..new_length-N]];
end function;

/*
The next function calculates the convolution of two lists a and b using the FFT algorithm
*/
function FastConvolution(a, b)
    // Save the original length of a
    Norig := #a;
    // Pad a and b to the same length (power of 2)
    a := pad_list_to_power_of_two(a);
    b := pad_list_to_power_of_two(b);
    // Update the length of a to the padded length
    N := #a;
    // Make b periodic
    for i in [1..Norig] do
        b[N+1-i] := b[Norig+1-i];
    end for;
    // Compute the FFT of a and b
    a_fft := fft2power(a);
    b_fft := fft2power(b);
    // Multiply the FFTs element-wise to get the FFT of the convolution
    c_fft := [a_fft[i] * b_fft[i] : i in [1..#a]];
    // Compute the inverse FFT of c_fft
    c := fft2power(c_fft);
    // Normalize the result by dividing by the length of a
    c := [1/#a * c[i] : i in [1..#c]];
    // Reverse the order of the elements of c
    c := Reverse(c);
    // Shift the elements of c one position to the right, and set the first element to the last element
    c := [c[#c]] cat [c[i] : i in [1..#c-1]];
    // Return the first Norig elements of c as the convolution of a and b
    return [c[i] : i in [1..Norig]];
end function;

/*
The next function is an implementation of Rader's FFT algorithm
*/
function RaderFFT(x)
    // Get the base ring for the input sequence
    R := Parent(x[1]);

    // Initialize empty lists to hold the output and intermediate values
    X := [R!0 : i in [1..#x-1]];
    Y := [R!0 : i in [1..#x-1]];

    // The size of the input sequence is a prime p
    p := #x;

    // Find a primitive root modulo p
    g := PrimitiveRoot(p);

    // Convert the primitive root to the finite field F_p
    gp := GF(p)!g;

    // Compute a list of values a, where a[i] = x[1 + g^i (mod p)]
    a := [R!x[1 + Integers()!(gp^q)] : q in [0..p-2]];

    // Compute a list of values b, where b[q] = exp(-2*pi*I*g^(-q)/p)
    b := [R!Exp(-2*Pi(R)*R.1/p * Integers()!(gp^(-q))) : q in [0..p-2]];

    // Compute the circular convolution of a and b using the FastConvolution function
    c := FastConvolution(a,b);

    // Shift the resulting sequence to obtain the Rader algorithm output
    c := [x[1] + c[i] : i in [1..#c]];

    // Store the values of c in the output list X using the Rader permutation
    for q in [0..(p-2)] do
        X[Integers()!(gp^(p-1-q))] := c[1+q];
    end for;

    // Return the concatenation of the sum of the input sequence and the output list X
    return [&+x] cat X;
end function;
