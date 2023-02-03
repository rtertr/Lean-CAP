import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.log.deriv
import analysis.special_functions.sqrt
import analysis.calculus.cont_diff
import data.nat.log
import analysis.calculus.mean_value
import analysis.special_functions.trigonometric.arctan_deriv
import tactic
import analysis.special_functions.pow_deriv
import analysis.special_functions.trigonometric.inverse_deriv
import analysis.special_functions.log.base
open_locale topological_space
open_locale topological_space filter classical real

noncomputable theory

open set
open set filter
open real
namespace real

/- # This proof was our last, and there for quite messy and unfinished. -/
/- # Our main goal was to go from deriv c*log(a * y + b) to our system of 2 equations. This system is called system_a_2. -/
/- # Now, for our previous functions a, y, b, then we found deriv c*log(a * y + b) = x / y. -/
/- # This system can be rewritten as deriv c*log(a * y + b) = c* (a'*y+a*y'+b')/(a*y +b) in general. -/
/- # Then for a general a, y, and b, for deriv c*log(a * y + b) = x / y to hold, then c* (a'*y+a*y'+b')/(a*y +b) = x / y must hold. -/
/- # The easiest way to show this holds it to rewrite this to (a*y +b)*x = c*y*(a'*y + a*y' + b') =>  a*y*x + b*x - c*y*(a'*y + a*y') + c*y*b'= 0  -/
/- # We have the assumption that b is a polynomial of order 8, and than a = c*b'/x, thus the previous equation is reduced to b*x - c*y*(a'*y + a*y')= 0   -/
/- # To get rid for 1/x^2 b*x in a', we multiply by x^2, such that we get  x^2*(b*x - c*y*(a'*y + a*y'))= 0   -/
/- # Thus we have to show x^2*(b*x - c*y*(a'*y + a*y'))= 0, but this only holds under certain for the coeffiecient in y and b.   -/
/- # The relation between the coeffiecient in y and b is system_eleven. Thus if system_eleven holds iff x^2*(b*x - c*y*(a'*y + a*y'))= 0.   -/
/- # We only managed to show that system_eleven implies x^2*(b*x - c*y*(a'*y + a*y'))= 0, but if we had more we would have shown the other way as well.  -/

def fun_z_gen (x:ℝ) (e2:ℝ) (e3:ℝ) (e4:ℝ): ℝ := x^4+e2*x^2+e3*x+e4
def fun_b_gen (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ): ℝ 
:= -x^8+d7*x^7+d6*x^6+d5*x^5+d4*x^4+d3*x^3+d2*x^2+d1*x+d0 -- d_8 = - 1 as an assumption, could be better implemented.
def fun_a_gen (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) : ℝ 
:= (-1/8)*(-8*x^6+7*d7*x^5+6*d6*x^4+5*d5*x^3+4*d4*x^2+3*d3*x+2*d2+d1*x⁻¹)  -- this comes from the assumption c*b'/x, but again could be better implemented.
def deriv_fun_a_gen (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d1:ℝ) : ℝ 
:= -8*6*(-1/8)*x^5+7*5*(-1/8)*d7*x^4+6*4*(-1/8)*d6*x^3+5*3*(-1/8)*d5*x^2+4*2*(-1/8)*d4*x+3*(-1/8)*d3-(-1/8)*d1/(x)^2 -- done by hand due to time pressure.
def deriv_fun_z_gen (x:ℝ) (e2:ℝ) (e3:ℝ): ℝ := 4*x^3+2*e2*x+e3  -- done by hand due to time pressure.

def system_a_2 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ):= (100*e_4 + 71*e_2^2=0) ∧ (70*e_3^2 + 972*e_2*e_4+45*e_2^3=0) ∧ d_0 = -(e_2 ^ 4 / 128) - 83 * e_2 * e_3 ^ 2 / 720 - 3 * e_2 ^ 2 * e_4 / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210 * e_3 * (71 * e_2 ^ 2 + 100 * e_4)) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = -(4 / 3 * e_3) ∧ d_6 = -(2 * e_2) ∧ d_7 = 0
def system_eleven (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) := -((d_1*e_4)/64) = 0 ∧ -((d_1*e_3)/128) = 0 ∧ 1/64*(d_2*e_3 + 3*d_3*e_4) = 0 ∧ 1/128*(-128*d_0 + 4*d_2*e_2 + 9*d_3*e_3 + 16*d_4*e_4) = 0 ∧
1/64*(-63*d_1 + 6*d_3*e_2 + 10*d_4*e_3 + 15*d_5*e_4) = 0 ∧ 1/128*(-120*d_2 + 24*d_4*e_2 + 35*d_5*e_3 + 48*d_6*e_4) = 0 ∧ 1/64*(-55*d_3 + 20*d_5*e_2 + 27*d_6*e_3 + 35*d_7*e_4) = 0 ∧
1/128*(-96*d_4 + 60*d_6*e_2 + 77*d_7*e_3 - 96*e_4) = 0 ∧ 1/64*(-39*d_5 + 42*d_7*e_2 - 52*e_3) = 0 ∧ -(7/16)*(d_6 + 2*e_2) = 0 ∧ -((15*d_7)/64) = 0
def system_eleven_neg (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) := ((15/64)* d_7)=0 ∧ (7 / 16 * d_6 + 7 / 8 * e_2)=0 ∧ ((-1)/64* (-39 * d_5 + 42 * d_7 * e_2 - 52 * e_3))=0  ∧ ((-1)/128 * (-96* d_4 + 60 * d_6 * e_2 + 77 * d_7 * e_3 - 96 * e_4))=0 ∧ ((-1)/64 * (-55 * d_3 + 20 * d_5 * e_2 + 27 * d_6 * e_3 + 35 * d_7 * e_4))=0 ∧ ((-1)/128 * (-120 * d_2 + 24 * d_4 * e_2 + 35 * d_5 * e_3 + 48 * d_6 * e_4))=0 ∧ ((-1)/64*(-63 * d_1 + 6 * d_3 * e_2 + 10 * d_4 * e_3 + 15 * d_5 * e_4))=0 ∧ ((-1)/128 * (-128 * d_0 + 4 * d_2 * e_2 + 9 * d_3 * e_3 + 16 * d_4 * e_4))=0 ∧ ((-1)/64 * (d_2 * e_3 + 3 * d_3 * e_4))=0 ∧ ((d_1 * e_3)/128)=0 ∧ ((d_1 * e_4)/64)=0


/- # Needed system eleven with minus signs in front of it to match my other functions.  -/
lemma system_eleven_implies_system_eleven_neg (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
system_eleven e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7 → system_eleven_neg e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7:=
begin
  unfold system_eleven,
  unfold system_eleven_neg,
  intro h,
  cases h with h1 h2,
  cases h2 with h2 h3,
  cases h3 with h3 h4,
  cases h4 with h4 h5,
  cases h5 with h5 h6,
  cases h6 with h6 h7,
  cases h7 with h7 h8,
  cases h8 with h8 h9,
  cases h9 with h9 h10,
  cases h10 with h10 h11,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  linarith,
end

lemma system_eleven_neg_implies_system_eleven (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
system_eleven_neg e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7 → system_eleven e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7:=
begin
  unfold system_eleven,
  unfold system_eleven_neg,
  intro h,
  cases h with h1 h2,
  cases h2 with h2 h3,
  cases h3 with h3 h4,
  cases h4 with h4 h5,
  cases h5 with h5 h6,
  cases h6 with h6 h7,
  cases h7 with h7 h8,
  cases h8 with h8 h9,
  cases h9 with h9 h10,
  cases h10 with h10 h11,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  split,
  linarith,
  linarith,
end

lemma system_eleven_iff_system_eleven_neg (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
system_eleven e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7 ↔ system_eleven_neg e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7:=
begin
  split,
  apply system_eleven_implies_system_eleven_neg x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  apply system_eleven_neg_implies_system_eleven x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
end

lemma unfolding_polynomial_first_term (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ): 
x.fun_b_gen d7 d6 d5 d4 d3 d2 d1 d0 * x ^ 3= (-1) * x ^ 11 + d7 * x ^ 10 + d6 * x ^ 9 + d5 * x ^ 8 + d4 * x ^ 7 + d3 * x ^ 6 + d2 * x ^ 5 + d1 * x ^ 4 + d0 * x ^ 3:=
begin
  unfold fun_b_gen,
  repeat {conv_lhs {rw add_mul,}},
  ring_nf,
end

/- # Again, a better and more efficient way could have been used here, but due to time pressure this was not   -/
/- # Would have needed to add x≠0 to be with out sorrys, but due to time pressure, this has not been implemented.    -/
lemma unfolding_polynomial_second_term (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
1 / 8 * (x.deriv_fun_a_gen d7 d6 d5 d4 d3 d1 * x.fun_z_gen e2 e3 e4) * x ^ 2 = 3 / 4 * x ^ 11 + -(35 / 64 * d7 * x ^ 10) + 1 / 8 * (6 * e2 + -(3 * d6)) * x ^ 9 + 1 / 8 * (-(35 / 8 * d7 * e2) + 6 * e3 + -(15 / 8 * d5)) * x ^ 8 + 1 / 8 * (-(35 / 8 * d7 * e3) + -(3 * d6 * e2) + 6 * e4 + -d4) * x ^ 7 + 1 / 8 * (-(3 * d6 * e3) + -(35 / 8 * d7 * e4) + -(15 / 8 * d5 * e2) + -(3 / 8 * d3)) * x ^ 6 + 1 / 8 * (-(15 / 8 * d5 * e3) + -(3 * d6 * e4) + -(d4 * e2)) * x ^ 5 + 1 / 8 * (-(15 / 8 * d5 * e4) + -(d4 * e3) + -(3 / 8 * d3 * e2) + 1 / 8 * d1) * x ^ 4 + 1 / 8 * (-(d4 * e4) + -(3 / 8 * d3 * e3)) * x ^ 3 + 1 / 8 * (-(3 / 8 * d3 * e4) + 1 / 8 * d1 * e2) * x ^ 2 + 1 / 64 * d1 * e3 * x + 1 / 64 * d1 * e4:=
begin
  rw mul_assoc,
  rw mul_assoc,
  --unfold deriv_fun_a_gen,
  unfold fun_z_gen,
  repeat {conv_lhs {rw add_mul,}},
  have h1: x ^ 4 * x ^ 2 + e2 * x ^ 2 * x ^ 2 + e3 * x * x ^ 2 + e4 * x ^ 2 = x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2,
    ring_nf,
  rw h1,
  unfold deriv_fun_a_gen,
  rw sub_mul,
  repeat {conv_lhs {rw add_mul,}},
  have h2: (-8) * 6 * ((-1) / 8) * x ^ 5 * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2) = (6) * x ^ 11  + (6) * e2 * x ^ 9 + (6) * e3 * x ^ 8 + (6) * e4 * x ^ 7,
    ring_nf,
  rw h2,
  have h3: 7 * 5 * ((-1) / 8) * d7 * x ^ 4 * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2)= (-35/8) * d7 * x ^ 10 + (-35/8) * d7 * e2 * x ^ 8 + (-35/8) * d7 *e3 * x ^ 7 + (-35/8) * d7 *e4 * x ^ 6,
    ring_nf,
  rw h3,
  have h4: 6 * 4 * ((-1) / 8) * d6 * x ^ 3 * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2) = (-3) * d6 * x ^ 9  + (-3) * d6 *e2 * x ^ 7 + (-3) * d6 * e3 * x ^ 6 + (-3) * d6 * e4 * x ^ 5,
    ring_nf,
  rw h4, 
  have h5: 5 * 3 * ((-1) / 8) * d5 * x ^ 2 * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2) = (-15/8) * d5 * x ^ 8 + (-15/8) * d5 * e2 * x ^ 6 +(-15/8) * d5 * e3 * x ^ 5 + (-15/8) * d5 * e4 * x ^ 4,
    ring_nf,
  rw h5,
  --4 * 2 * ((-1) / 8) * d4 * x * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2) 
  have h6: 4 * 2 * ((-1) / 8) * d4 * x * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2)  = (-1) * d4 * x ^ 7 + (-1) * d4 *e2 * x ^ 5 + (-1) * d4 * e3 * x ^ 4 + (-1) * d4 *e4 * x ^ 3,
    ring_nf,
  rw h6,
  --3 * ((-1) / 8) * d3 * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2)
  have h7: 3 * ((-1) / 8) * d3 * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2) = (-3/8) * d3 * x ^ 6 + (-3/8) * d3 *e2 * x ^ 4 + (-3/8) * d3 *e3 * x ^ 3 + (-3/8) * d3 *e4 * x ^ 2,
    ring_nf,
  rw h7,
  -- (-1) / 8 * d1 / x ^ 2 * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2))
  have h8: (-1) / 8 * d1 / x ^ 2 * (x ^ 6 + e2 * x ^ 4 + e3 * x ^ 3 + e4 * x ^ 2) = (-1) / 8 * d1 * x ^ 4 + (-1) / 8 * d1 * e2 * x ^ 2 +  (-1) / 8 * d1 * e3 * x + (-1) / 8 * d1 * e4,
    ring_nf,
    sorry,
  rw h8,
  repeat {conv_lhs {rw sub_eq_add_neg,}},
  repeat {conv_lhs {rw ← add_assoc,}}, -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------d1 * x ^ 4 +  d1 * e2 * x ^ 2 +  d1 * e3 * x +  d1 * e4,
  have h9: (6) * x ^ 11 + (6) * e2 * x ^ 9 + (6) * e3 * x ^ 8 + (6) * e4 * x ^ 7 + (-35/8) * d7 * x ^ 10 + (-35/8) * d7 * e2 * x ^ 8 +(-35/8) * d7 * e3 * x ^ 7 +(-35/8) * d7 * e4 * x ^ 6 +(-3) * d6 * x ^ 9 +(-3) * d6 * e2 * x ^ 7 + (-3) * d6 * e3 * x ^ 6 + (-3) * d6 * e4 * x ^ 5 + (-15/8) * d5 * x ^ 8 + (-15/8) * d5 * e2 * x ^ 6 + (-15/8) * d5 * e3 * x ^ 5 + (-15/8)* d5 * e4 * x ^ 4 + (-1) * d4 * x ^ 7 + (-1) * d4 * e2 * x ^ 5 + (-1) * d4 * e3 * x ^ 4 + (-1) * d4 * e4 * x ^ 3 +(-3/8) * d3 * x ^ 6 + (-3/8) * d3 * e2 * x ^ 4 + (-3/8) * d3 * e3 * x ^ 3 + (-3/8) * d3 * e4 * x ^ 2    =    (6) * x ^ 11   + (-35/8) * d7 * x ^ 10  + ((6) * e2   + (-3) * d6) * x ^ 9+ ((-35/8) * d7 * e2 + (6) * e3   + (-15/8) * d5 ) * x ^ 8 + ((-35/8) * d7 * e3  + (-3) * d6 * e2 + (6) * e4 + (-1) * d4) * x ^ 7+ ((-3) * d6 * e3 + (-35/8) * d7 * e4 + (-15/8) * d5 * e2 +(-3/8) * d3) * x ^ 6   + ((-15/8) * d5 * e3 + (-3) * d6 * e4  + (-1) * d4 * e2) * x ^ 5   +((-15/8) * d5 * e4 + (-1) * d4 * e3 + (-3/8) * d3 * e2) * x ^ 4 +((-1) * d4 * e4 +  (-3/8) * d3 * e3) * x ^ 3 + (-3/8) * d3 * e4 * x ^ 2,
    ring_nf,
  rw h9,
  have h10: (-((-1) / 8 * d1 * x ^ 4 + (-1) / 8 * d1 * e2 * x ^ 2 + (-1) / 8 * d1 * e3 * x + (-1) / 8 * d1 * e4))= (-1)*((-1) / 8* d1 * x ^ 4 + (-1) / 8*d1 * e2 * x ^ 2 + (-1) / 8* d1 * e3 * x + (-1) / 8*d1 * e4),
    ring_nf,
  rw h10,
  rw mul_add (-1) ((-1) / 8 * d1 * x ^ 4 + (-1) / 8 * d1 * e2 * x ^ 2 + (-1) / 8 * d1 * e3 * x ) ((-1) / 8 * d1 * e4),
  rw mul_add (-1) ((-1) / 8 * d1 * x ^ 4 + (-1) / 8 * d1 * e2 * x ^ 2 ) ((-1) / 8 * d1 * e3 * x ),
  rw mul_add (-1) ((-1) / 8 * d1 * x ^ 4) ((-1) / 8 * d1 * e2 * x ^ 2 ),
  have h11: (6) * x ^ 11 + (-35/8) * d7 * x ^ 10 + ((6) * e2 + (-3) * d6) * x ^ 9 +((-35/8) * d7 * e2 + (6) * e3 + (-15/8) * d5) * x ^ 8 +((-35/8) * d7 * e3 + (-3) * d6 * e2 + (6) * e4 + (-1) * d4) * x ^ 7 +((-3) * d6 * e3 + (-35/8) * d7 * e4 + (-15/8) * d5 * e2 + (-3/8) * d3) * x ^ 6 +((-15/8) * d5 * e3 + (-3) * d6 * e4 + (-1) * d4 * e2) * x ^ 5 +((-15/8) * d5 * e4 + (-1) * d4 * e3 + (-3/8) * d3 * e2) * x ^ 4 +((-1) * d4 * e4 + (-3/8) * d3 * e3) * x ^ 3 + (-3/8) * d3 * e4 * x ^ 2 +((-1) * ( (-1) / 8 * d1 * x ^ 4) + (-1) * ((-1) / 8 *d1 * e2 * x ^ 2) + (-1) * ( (-1) / 8 *d1 * e3 * x) + (-1) * ((-1) / 8 * d1 * e4)) = (6) * x ^ 11 + (-35/8) * d7 * x ^ 10 + ((6) * e2 + (-3) * d6) * x ^ 9 +((-35/8) * d7 * e2 + (6) * e3 + (-15/8) * d5) * x ^ 8 +((-35/8) * d7 * e3 + (-3) * d6 * e2 + (6) * e4 + (-1) * d4) * x ^ 7 +((-3) * d6 * e3 + (-35/8) * d7 * e4 + (-15/8) * d5 * e2 + (-3/8) * d3) * x ^ 6 +((-15/8) * d5 * e3 + (-3) * d6 * e4 + (-1) * d4 * e2) * x ^ 5 +((-15/8) * d5 * e4 + (-1) * d4 * e3 + (-3/8) * d3 * e2 +(-1) * (-1) / 8 *d1) * x ^ 4 +((-1) * d4 * e4 + (-3/8) * d3 * e3) * x ^ 3 + ((-3/8) * d3 * e4+ (-1) * (-1) / 8 * d1 * e2)* x ^ 2  + ((-1) * (-1) / 8 * d1 * e3) * x + (-1) * (-1) / 8 *d1 * e4,
    ring_nf,
  rw h11,
  repeat {conv_lhs {rw mul_add,}},
  repeat {conv_lhs {rw ← mul_assoc,}},
  conv_lhs {norm_num,}
end 

lemma unfolding_polynomial_third_term (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
1 / 8 * (1 / 2 * x.fun_a_gen d7 d6 d5 d4 d3 d2 d1 * x.deriv_fun_z_gen e2 e3) * x ^ 2 = 1 / 4 * x ^ 11 + -(7 / 32) * d7 * x ^ 10 + -(1 / 128) * ((-16) * e2 + 24 * d6) * x ^ 9 + -(1 / 128) * ((-8) * e3 + 20 * d5 + 7 * d7 * 2 * e2) * x ^ 8 + -(1 / 128) * (16 * d4 + 6 * d6 * 2 * e2 + 7 * d7 * e3) * x ^ 7 + -(1 / 128) * (12 * d3 + 5 * d5 * 2 * e2 + 6 * d6 * e3) * x ^ 6 + -(1 / 128) * (8 * d2 + 4 * d4 * 2 * e2 + 5 * d5 * e3) * x ^ 5 + -(1 / 128) * (4 * d1 + 3 * d3 * 2 * e2 + 4 * d4 * e3) * x ^ 4 + -(1 / 128) * (2 * d2 * 2 * e2 + 3 * d3 * e3) * x ^ 3 + -(1 / 128) * (d1 * 2 * e2 + 2 * d2 * e3) * x ^ 2 + -(1 / 128) * d1 * e3 * x:=
begin
  rw mul_assoc,
  rw mul_assoc,
  --unfold fun_a_gen,
  unfold deriv_fun_z_gen,
  repeat {conv_lhs {rw add_mul,}},
  have h1: 4 * x ^ 3 * x ^ 2 + 2 * e2 * x * x ^ 2 + e3 * x ^ 2= 4 * x ^ 5  + 2 * e2 * x ^ 3 + e3 * x ^ 2,
    ring_nf,
  rw h1,
  unfold fun_a_gen,
  rw mul_assoc,
  repeat {conv_lhs {rw mul_add,}},
  have h2: 1 / 8 * (1 / 2 * (((-1) / 8 * ((-8) * x ^ 6) + (-1) / 8 * (7 * d7 * x ^ 5) + (-1) / 8 * (6 * d6 * x ^ 4) + (-1) / 8 * (5 * d5 * x ^ 3) + (-1) / 8 * (4 * d4 * x ^ 2) + (-1) / 8 * (3 * d3 * x) + (-1) / 8 * (2 * d2) + (-1) / 8 * (d1 * x⁻¹)) * (4 * x ^ 5))) = (-1) / 64 *(1 / 2 *(((-8) * 4* x ^ 11  + 7 * 4 * d7 * x ^ 10 + 6 *4 * d6 * x ^ 9 + 5 *4 * d5 * x ^ 8 + 4 * 4* d4 * x ^ 7 + 3 * 4 * d3 * x ^ 6 + 2 * 4* d2 * x ^5 + 4*d1*x⁻¹*x^5 ) )),
    ring_nf,
  have h2extra:  4*d1*x⁻¹*x^5= 4* d1 * x ^4,
      sorry,
  have h3: 1 / 8 * (1 / 2 * (((-1) / 8 * ((-8) * x ^ 6) + (-1) / 8 * (7 * d7 * x ^ 5) + (-1) / 8 * (6 * d6 * x ^ 4) + (-1) / 8 * (5 * d5 * x ^ 3) + (-1) / 8 * (4 * d4 * x ^ 2) + (-1) / 8 * (3 * d3 * x) + (-1) / 8 * (2 * d2) + (-1) / 8 * (d1 * x⁻¹)) * (4 * x ^ 5))) = (-1) / 64 *(1 / 2 *(((-8) * 4* x ^ 11  + 7 * 4 * d7 * x ^ 10 + 6 *4 * d6 * x ^ 9 + 5 *4 * d5 * x ^ 8 + 4 * 4* d4 * x ^ 7 + 3 * 4 * d3 * x ^ 6 + 2 * 4* d2 * x ^5 + 4*d1*x^4 ) )),
    rw h2,
    rw h2extra,
  rw h3,
  have h4: 1 / 8 * (1 / 2 * (((-1) / 8 * ((-8) * x ^ 6) + (-1) / 8 * (7 * d7 * x ^ 5) + (-1) / 8 * (6 * d6 * x ^ 4) + (-1) / 8 * (5 * d5 * x ^ 3) + (-1) / 8 * (4 * d4 * x ^ 2) + (-1) / 8 * (3 * d3 * x) + (-1) / 8 * (2 * d2) + (-1) / 8 * (d1 * x⁻¹)) * (2 * e2 * x ^ 3)))=(-1) / 64 *(1 / 2 *(((-8)  * 2 * e2 * x ^ 9 + 7 * d7 * 2 * e2 * x ^ 8 + 6 * d6 *  2 * e2 * x ^ 7 + 5 * d5 * 2 * e2 * x ^ 6 + 4 * d4 * 2 * e2 * x ^ 5 + 3 * d3 * 2 * e2 * x ^ 4 + 2 * d2 * 2 * e2 * x ^ 3 +d1 *  2 * e2 * x⁻¹ *x ^ 3) )),
    ring_nf,
  rw h4,
  have h5: 1 / 8 * (1 / 2 * (((-1) / 8 * ((-8) * x ^ 6) + (-1) / 8 * (7 * d7 * x ^ 5) + (-1) / 8 * (6 * d6 * x ^ 4) + (-1) / 8 * (5 * d5 * x ^ 3) + (-1) / 8 * (4 * d4 * x ^ 2) + (-1) / 8 * (3 * d3 * x) + (-1) / 8 * (2 * d2) + (-1) / 8 * (d1 * x⁻¹)) * (e3 * x ^ 2)))= (-1) / 64 *(1 / 2 *(((-8) * e3 * x ^ 8 + 7 * d7  * e3 * x ^ 7 + 6 * d6 * e3 * x ^ 6 + 5 * d5 * e3 * x ^ 5 + 4 * d4 * e3 * x ^ 4 + 3 * d3 * e3 * x ^ 3 + 2 * d2 *e3 * x ^ 2 + d1 * e3 * x ^ 2 * x⁻¹) )),
    ring_nf,
  rw h5,
  have h3extra: d1 * e3 * x ^ 2 * x⁻¹ = d1 * e3 * x,
    sorry,
  rw h3extra,
  have h4extra: d1 * 2 * e2 * x⁻¹ * x ^ 3 = d1 * 2 * e2 *  x ^ 2,
    sorry,
  rw h4extra,
  rw ← mul_add,
  rw ← mul_add,
  rw ← mul_add,
  rw ← mul_add,
  repeat {conv_lhs {rw ← add_assoc,}},
  have h5: (-8) * 4 * x ^ 11 + 7 * 4 * d7 * x ^ 10 + 6 * 4 * d6 * x ^ 9 + 5 * 4 * d5 * x ^ 8 + 4 * 4 * d4 * x ^ 7 + 3 * 4 * d3 * x ^ 6 + 2 * 4 * d2 * x ^ 5 + 4 * d1 * x ^ 4 + (-8) * 2 * e2 * x ^ 9 + 7 * d7 * 2 * e2 * x ^ 8 + 6 * d6 * 2 * e2 * x ^ 7 + 5 * d5 * 2 * e2 * x ^ 6 + 4 * d4 * 2 * e2 * x ^ 5 + 3 * d3 * 2 * e2 * x ^ 4 + 2 * d2 * 2 * e2 * x ^ 3 + d1 * 2 * e2 * x ^ 2 +(-8) * e3 * x ^ 8 + 7 * d7 * e3 * x ^ 7 + 6 * d6 * e3 * x ^ 6 +  5 * d5 * e3 * x ^ 5 + 4 * d4 * e3 * x ^ 4 +3 * d3 * e3 * x ^ 3 + 2 * d2 * e3 * x ^ 2 +d1 * e3 * x     =       (-8) * 4 * x ^ 11 + 7 * 4 * d7 * x ^ 10 + ((-8) * 2 * e2 + 6 * 4 * d6) * x ^ 9 + ( (-8) * e3  +5 * 4 * d5 + 7 * d7 * 2 * e2) * x ^ 8 + (4 * 4 * d4 + 6 * d6 * 2 * e2 + 7 * d7 * e3) * x ^ 7 + (3 * 4 * d3 + 5 * d5 * 2 * e2 + 6 * d6 * e3) * x ^ 6 + (2 * 4 * d2 + 4 * d4 * 2 * e2 +  5 * d5 * e3)* x ^ 5  + (4 * d1 + 3 * d3 * 2 * e2  + 4 * d4 * e3) * x ^ 4+ (2 * d2 * 2 * e2 +3 * d3 * e3) * x ^ 3 + (d1 * 2 * e2 + 2 * d2 * e3) * x ^ 2 + d1 * e3 * x, 
    ring_nf,
  rw h5,
  repeat {conv_lhs {rw mul_add,}},
  repeat {conv_lhs {rw ← mul_assoc,}},
  conv_lhs {norm_num,},
  repeat {conv_lhs {rw ← mul_assoc,}},
  repeat {conv_lhs {rw ← neg_mul,}},
end

lemma eq_11 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
d7 + -(35 / 64 * d7) + -(7 / 32 * d7)=(15/64)* d7:=
begin
  field_simp,
  ring_nf,
end

lemma eq_10 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(d6 + 1 / 8 * (6 * e2 + -(3 * d6)) + -(1 / 128 * (-(16 * e2) + 24 * d6)))=7 / 16 * d6 + 7 / 8 * e2:=
begin
  conv_lhs {simp,},
  conv_lhs {ring_nf,},
end

lemma eq_9 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(d5 + 1 / 8 * (-(35 / 8 * d7 * e2) + 6 * e3 + -(15 / 8 * d5)) + -(1 / 128 * (-(8 * e3) + 20 * d5 + 7 * d7 * 2 * e2)))=(-1)/64* (-39 * d5 + 42 * d7 * e2 - 52 * e3):=
begin
  simp,
  ring_nf,
end

lemma eq_8 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(d4 + -(1 / 128 * (16 * d4 + 6 * d6 * 2 * e2 + 7 * d7 * e3)) + 1 / 8 * (-(35 / 8 * d7 * e3) + -(3 * d6 * e2) + 6 * e4 + -d4))=(-1)/128 * (-96* d4 + 60 * d6 * e2 + 77 * d7 * e3 - 96 * e4):=
begin
  simp,
  ring_nf,
end

lemma eq_7 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(d3 + 1 / 8 * (-(3 * d6 * e3) + -(35 / 8 * d7 * e4) + -(15 / 8 * d5 * e2) + -(3 / 8 * d3)) + -(1 / 128 * (12 * d3 + 5 * d5 * 2 * e2 + 6 * d6 * e3)))=(-1)/64 * (-55 * d3 + 20 * d5 * e2 + 27 * d6 * e3 + 35 * d7 * e4):=
begin
  simp,
  ring_nf,
end

lemma eq_6 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(d2 + 1 / 8 * (-(15 / 8 * d5 * e3) + -(3 * d6 * e4) + -(d4 * e2)) + -(1 / 128 * (8 * d2 + 4 * d4 * 2 * e2 + 5 * d5 * e3))) =(-1)/128 * (-120 * d2 + 24 * d4 * e2 + 35 * d5 * e3 + 48 * d6 * e4):=
begin
  simp,
  ring_nf,
end

lemma eq_5 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(d1 + -(1 / 128 * (4 * d1 + 3 * d3 * 2 * e2 + 4 * d4 * e3)) + 1 / 8 * (-(15 / 8 * d5 * e4) + -(d4 * e3) + -(3 / 8 * d3 * e2) + 1 / 8 * d1))=(-1)/64*(-63 * d1 + 6 * d3 * e2 + 10 * d4 * e3 + 15 * d5 * e4):=
begin
  simp,
  ring_nf,
end

lemma eq_4 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(d0 + 1 / 8 * (-(d4 * e4) + -(3 / 8 * d3 * e3)) + -(1 / 128 * (2 * d2 * 2 * e2 + 3 * d3 * e3)))=(-1)/128 * (-128 * d0 + 4 * d2 * e2 + 9 * d3 * e3 + 16 * d4 * e4):=
begin
  simp,
  ring_nf,
end

lemma eq_3 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(1 / 8 * (-(3 / 8 * d3 * e4) + 1 / 8 * d1 * e2) + -(1 / 128 * (d1 * 2 * e2 + 2 * d2 * e3)))= (-1)/64 * (d2 * e3 + 3 * d3 * e4):=
begin
  simp,
  ring_nf,
end

lemma eq_2 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
(1 / 64 * d1 * e3 + -(1 / 128 * d1 * e3))=((d1 * e3)/128):=
begin
  simp,
  ring_nf,
end

lemma eq_1 (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
1 / 64 * d1 * e4=((d1 * e4)/64):=
begin
  simp,
  ring_nf,
end

/- # Again, a better and more efficient way could have been used here, but due to time pressure this was not   -/
lemma unfolding_polynomial (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ): 
((fun_b_gen x d7 d6 d5 d4 d3 d2 d1 d0)*x-(-1/8)*((deriv_fun_a_gen x d7 d6 d5 d4 d3 d1)*(fun_z_gen x e2 e3 e4)+(1/2)*(fun_a_gen x d7 d6 d5 d4 d3 d2 d1)*(deriv_fun_z_gen x e2 e3))) * x^2= (d7 + -(35 / 64 * d7) + -(7 / 32 * d7)) * x ^ 10 + (d6 + 1 / 8 * (6 * e2 + -(3 * d6)) + -(1 / 128 * (-(16 * e2) + 24 * d6))) * x ^ 9 + (d5 + 1 / 8 * (-(35 / 8 * d7 * e2) + 6 * e3 + -(15 / 8 * d5)) + -(1 / 128 * (-(8 * e3) + 20 * d5 + 7 * d7 * 2 * e2))) * x ^ 8 + (d4 + -(1 / 128 * (16 * d4 + 6 * d6 * 2 * e2 + 7 * d7 * e3)) + 1 / 8 * (-(35 / 8 * d7 * e3) + -(3 * d6 * e2) + 6 * e4 + -d4)) * x ^ 7 + (d3 + 1 / 8 * (-(3 * d6 * e3) + -(35 / 8 * d7 * e4) + -(15 / 8 * d5 * e2) + -(3 / 8 * d3)) + -(1 / 128 * (12 * d3 + 5 * d5 * 2 * e2 + 6 * d6 * e3))) * x ^ 6 + (d2 + 1 / 8 * (-(15 / 8 * d5 * e3) + -(3 * d6 * e4) + -(d4 * e2)) + -(1 / 128 * (8 * d2 + 4 * d4 * 2 * e2 + 5 * d5 * e3))) * x ^ 5 + (d1 + -(1 / 128 * (4 * d1 + 3 * d3 * 2 * e2 + 4 * d4 * e3)) + 1 / 8 * (-(15 / 8 * d5 * e4) + -(d4 * e3) + -(3 / 8 * d3 * e2) + 1 / 8 * d1)) * x ^ 4 + (d0 + 1 / 8 * (-(d4 * e4) + -(3 / 8 * d3 * e3)) + -(1 / 128 * (2 * d2 * 2 * e2 + 3 * d3 * e3))) * x ^ 3 + (1 / 8 * (-(3 / 8 * d3 * e4) + 1 / 8 * d1 * e2) + -(1 / 128 * (d1 * 2 * e2 + 2 * d2 * e3))) * x ^ 2 + (1 / 64 * d1 * e3 + -(1 / 128 * d1 * e3)) * x + 1 / 64 * d1 * e4:=
begin
  repeat {conv_lhs {rw sub_mul,}},
  conv_lhs {rw mul_assoc,},
  nth_rewrite 1 ← pow_one x,
  conv_lhs {rw ← pow_add,},
  conv_lhs {norm_num,},
  conv_lhs {rw mul_add,},
  conv_lhs {rw add_mul,},
  conv_lhs {rw unfolding_polynomial_first_term x d7 d6 d5 d4 d3 d2 d1 d0,},
  conv_lhs {rw unfolding_polynomial_second_term x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,},
  conv_lhs {rw unfolding_polynomial_third_term x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,},
  repeat {conv_lhs {rw ← add_assoc,}},
  have h: (-1) * x ^ 11 + d7 * x ^ 10 + d6 * x ^ 9 + d5 * x ^ 8 + d4 * x ^ 7 + d3 * x ^ 6 + d2 * x ^ 5 + d1 * x ^ 4 + d0 * x ^ 3 + 3 / 4 * x ^ 11 + -(35 / 64 * d7 * x ^ 10) + 1 / 8 * (6 * e2 + -(3 * d6)) * x ^ 9 + 1 / 8 * (-(35 / 8 * d7 * e2) + 6 * e3 + -(15 / 8 * d5)) * x ^ 8 + 1 / 8 * (-(35 / 8 * d7 * e3) + -(3 * d6 * e2) + 6 * e4 + -d4) * x ^ 7 + 1 / 8 * (-(3 * d6 * e3) + -(35 / 8 * d7 * e4) + -(15 / 8 * d5 * e2) + -(3 / 8 * d3)) * x ^ 6 + 1 / 8 * (-(15 / 8 * d5 * e3) + -(3 * d6 * e4) + -(d4 * e2)) * x ^ 5 + 1 / 8 * (-(15 / 8 * d5 * e4) + -(d4 * e3) + -(3 / 8 * d3 * e2) + 1 / 8 * d1) * x ^ 4 + 1 / 8 * (-(d4 * e4) + -(3 / 8 * d3 * e3)) * x ^ 3 + 1 / 8 * (-(3 / 8 * d3 * e4) + 1 / 8 * d1 * e2) * x ^ 2 + 1 / 64 * d1 * e3 * x + 1 / 64 * d1 * e4 + 1 / 4 * x ^ 11 + -(7 / 32) * d7 * x ^ 10 + -(1 / 128) * ((-16) * e2 + 24 * d6) * x ^ 9 + -(1 / 128) * ((-8) * e3 + 20 * d5 + 7 * d7 * 2 * e2) * x ^ 8 + -(1 / 128) * (16 * d4 + 6 * d6 * 2 * e2 + 7 * d7 * e3) * x ^ 7 + -(1 / 128) * (12 * d3 + 5 * d5 * 2 * e2 + 6 * d6 * e3) * x ^ 6 + -(1 / 128) * (8 * d2 + 4 * d4 * 2 * e2 + 5 * d5 * e3) * x ^ 5 + -(1 / 128) * (4 * d1 + 3 * d3 * 2 * e2 + 4 * d4 * e3) * x ^ 4 + -(1 / 128) * (2 * d2 * 2 * e2 + 3 * d3 * e3) * x ^ 3 + -(1 / 128) * (d1 * 2 * e2 + 2 * d2 * e3) * x ^ 2 + -(1 / 128) * d1 * e3 * x                             =                       (d7 + -(35 / 64 * d7) + -(7 / 32) * d7) * x ^ 10 + (d6+ 1 / 8 * (6 * e2 + -(3 * d6))  + -(1 / 128) * ((-16) * e2 + 24 * d6)) * x ^ 9 + (d5  + 1 / 8 * (-(35 / 8 * d7 * e2) + 6 * e3 + -(15 / 8 * d5))  + -(1 / 128) * ((-8) * e3 + 20 * d5 + 7 * d7 * 2 * e2)) * x ^ 8+ (d4 + -(1 / 128) * (16 * d4 + 6 * d6 * 2 * e2 + 7 * d7 * e3)   + 1 / 8 * (-(35 / 8 * d7 * e3) + -(3 * d6 * e2) + 6 * e4 + -d4)) * x ^ 7 + (d3  + 1 / 8 * (-(3 * d6 * e3) + -(35 / 8 * d7 * e4) + -(15 / 8 * d5 * e2) + -(3 / 8 * d3)) + -(1 / 128) * (12 * d3 + 5 * d5 * 2 * e2 + 6 * d6 * e3)) * x ^ 6 + (d2  + 1 / 8 * (-(15 / 8 * d5 * e3) + -(3 * d6 * e4) + -(d4 * e2))  + -(1 / 128) * (8 * d2 + 4 * d4 * 2 * e2 + 5 * d5 * e3)) * x ^ 5 + (d1  + -(1 / 128) * (4 * d1 + 3 * d3 * 2 * e2 + 4 * d4 * e3)  + 1 / 8 * (-(15 / 8 * d5 * e4) + -(d4 * e3) + -(3 / 8 * d3 * e2) + 1 / 8 * d1)) * x ^ 4+ (d0 + 1 / 8 * (-(d4 * e4) + -(3 / 8 * d3 * e3)) + -(1 / 128) * (2 * d2 * 2 * e2 + 3 * d3 * e3)) * x ^ 3 + (1 / 8 * (-(3 / 8 * d3 * e4) + 1 / 8 * d1 * e2) + -(1 / 128) * (d1 * 2 * e2 + 2 * d2 * e3)) * x ^ 2 + (1 / 64 * d1 * e3 + -(1 / 128) * d1 * e3) * x + 1 / 64 * d1 * e4 ,   
    ring_nf,
  rw h,
  norm_num,
end



lemma system_eleven_implies_polynomial_eq_zero (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ) (h: system_eleven e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7): 
system_eleven e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7 → ((fun_b_gen x d7 d6 d5 d4 d3 d2 d1 d0)*x-(-1/8)*((deriv_fun_a_gen x d7 d6 d5 d4 d3 d1)*(fun_z_gen x e2 e3 e4)+(1/2)*(fun_a_gen x d7 d6 d5 d4 d3 d2 d1)*(deriv_fun_z_gen x e2 e3))) * x^2= 0:=
begin
  intro h,
  rw system_eleven_iff_system_eleven_neg at h,
  cases h with h1 h2,
  cases h2 with h2 h3,
  cases h3 with h3 h4,
  cases h4 with h4 h5,
  cases h5 with h5 h6,
  cases h6 with h6 h7,
  cases h7 with h7 h8,
  cases h8 with h8 h9,
  cases h9 with h9 h10,
  cases h10 with h10 h11,
  rw unfolding_polynomial x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_1 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_2 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_3 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_4 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_5 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_6 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_7 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_8 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_9 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_10 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw eq_11 x d7 d6 d5 d4 d3 d2 d1 d0 e2 e3 e4,
  rw [h11,h10,h9,h8,h7,h6,h5,h4,h3,h2,h1],
  simp only [zero_mul, add_zero],
  exact x,
end

lemma polynomial_eq_zero_implies_system_eleven (x:ℝ) (d7:ℝ) (d6:ℝ) (d5:ℝ) (d4:ℝ) (d3:ℝ) (d2:ℝ) (d1:ℝ) (d0:ℝ)
(e2:ℝ) (e3:ℝ) (e4:ℝ) (h: system_eleven e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7): 
 ((fun_b_gen x d7 d6 d5 d4 d3 d2 d1 d0)*x-(-1/8)*((deriv_fun_a_gen x d7 d6 d5 d4 d3 d1)*(fun_z_gen x e2 e3 e4)+(1/2)*(fun_a_gen x d7 d6 d5 d4 d3 d2 d1)*(deriv_fun_z_gen x e2 e3))) * x^2= 0 →system_eleven e2 e3 e4 d0 d1 d2 d3 d4 d5 d6 d7 :=
begin
  sorry, --discussed this with Alain friday, unfortunately we could not make it work 
end

/- # Unfortunately, we did not have the time to fully connect the part above and the part below except for the lemma system_eleven_implies_polynomial_eq_zero   -/

lemma hd6 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : d_6 + 2 * e_2 = 0 ↔ d_6 = -(2 * e_2) :=
begin
  rw add_eq_zero_iff_eq_neg,
end

lemma hd5 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : -(39 * d_5) + 42 * d_7 * e_2 - 52 * e_3 = 0 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔ d_5 = -52 / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 :=
begin
  simp,
  intros hd6 hd7,
  simp[hd7],
  rw [sub_eq_zero, ← neg_mul, mul_comm, ← eq_div_iff],
  ring_nf,
  norm_num,
end

lemma hd4 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : -(96 * d_4) + 60 * d_6 * e_2 + 77 * d_7 * e_3 - 96 * e_4 = 0 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔
d_4 = -((5 * e_2^2) / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 :=
begin
  simp,
  intros hd5 hd6 hd7,
  simp[hd6, hd7],
  ring_nf,
  rw [add_eq_zero_iff_eq_neg, ← neg_mul, mul_comm, ← eq_div_iff],
  ring_nf,
  norm_num,
end

lemma hd3 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : -(55 * d_3) + 20 * d_5 * e_2 + 27 * d_6 * e_3 + 35 * d_7 * e_4 = 0 ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔
d_3 = -((22 * e_2 * e_3) / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 :=
begin
  simp,
  intros hd4 hd5 hd6 hd7,
  simp[hd5, hd6, hd7],
  rw [add_assoc, add_eq_zero_iff_eq_neg, ← neg_mul, mul_comm, ← eq_div_iff],
  ring_nf,
  norm_num,
end

lemma hd2 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : -(120 * d_2) + 24 * d_4 * e_2 + 35 * d_5 * e_3 + 48 * d_6 * e_4 = 0 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔
d_2 = -e_2 ^ 3 / 4 - (7 * e_3 ^ 2) / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 :=
begin
  simp,
  intros hd3 hd4 hd5 hd6 hd7,
  simp[hd4, hd5, hd6],
  rw [add_assoc, add_assoc, add_eq_zero_iff_eq_neg, ← neg_mul, mul_comm, ← eq_div_iff],
  ring_nf,
  norm_num,
end

lemma hd1 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : -(63 * d_1) + 6 * d_3 * e_2 + 10 * d_4 * e_3 + 15 * d_5 * e_4 = 0 ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔
d_1 = (-(1 / 210)) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 :=
begin 
  simp,
  intros hd2 hd3 hd4 hd5 hd6 hd7,
  simp[hd3, hd4, hd5],
  rw [add_assoc, add_assoc, add_eq_zero_iff_eq_neg, ← neg_mul, mul_comm, ← eq_div_iff],
  ring_nf,
  norm_num,
end

lemma hd0 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : -(128 * d_0) + 4 * d_2 * e_2 + 9 * d_3 * e_3 + 16 * d_4 * e_4 = 0 ∧ d_1 = -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔
d_0 = -(e_2 ^ 4 / 128) - (83 * e_2 * e_3 ^ 2) / 720 - (3 * e_2 ^ 2 * e_4) / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0:=
begin
  simp,
  intros hd1 hd2 hd3 hd4 hd5 hd6 hd7,
  simp[hd2, hd3, hd4],
  rw [add_assoc, add_assoc, add_eq_zero_iff_eq_neg, ← neg_mul, mul_comm, ← eq_div_iff],
  ring_nf,
  norm_num,
end

lemma hsys3 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : d_2 * e_3 + 3 * d_3 * e_4 = 0 ∧ d_0 = -(e_2 ^ 4 / 128) - 83 * e_2 * e_3 ^ 2 / 720 - 3 * e_2 ^ 2 * e_4 / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔
(-(1 / 180)) * e_3 * (45 * e_2 ^ 3 + 70 * e_3 ^ 2 + 972 * e_2 * e_4) = 0 ∧ d_0 = -(e_2 ^ 4 / 128) - 83 * e_2 * e_3 ^ 2 / 720 - 3 * e_2 ^ 2 * e_4 / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 :=
begin
  simp only [one_div, neg_mul, neg_eq_zero, inv_eq_zero, bit0_eq_zero, and.congr_left_iff, and_imp],
  intros hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7,
  rw [hd2, hd3],
  ring_nf,
  rw sub_eq_zero,
  rw add_eq_zero_iff_eq_neg,
  rw ← neg_neg ((1 / 4 * e_3 * e_2 ^ 2 + 27 / 5 * e_4 * e_3) * e_2),
  rw neg_inj,
  ring_nf,
end

lemma hsys2 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero : e_3 ≠ 0) : d_1 = 0 ∧ -(1 / 180) * e_3 * (45 * e_2 ^ 3 + 70 * e_3 ^ 2 + 972 * e_2 * e_4) = 0 ∧ d_0 = -(e_2 ^ 4 / 128) - 83 * e_2 * e_3 ^ 2 / 720 - 3 * e_2 ^ 2 * e_4 / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔
-(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) = 0 ∧ -(1 / 180) * e_3 * (45 * e_2 ^ 3 + 70 * e_3 ^ 2 + 972 * e_2 * e_4) = 0 ∧ d_0 = -(e_2 ^ 4 / 128) - 83 * e_2 * e_3 ^ 2 / 720 - 3 * e_2 ^ 2 * e_4 / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 :=
begin
  simp only [one_div, neg_mul, neg_eq_zero, inv_eq_zero, bit0_eq_zero, and.congr_left_iff, and_imp],
  intros hsys3 hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7,
  rw[hd1],
  simp,
end

lemma hsys1 (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero3 : e_3 ≠ 0) (hnotzero4 : e_4 ≠ 0) : (d_1 = 0 ∨ e_4 = 0) ∧ -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) = 0 ∧ -(1 / 180) * e_3 * (45 * e_2 ^ 3 + 70 * e_3 ^ 2 + 972 * e_2 * e_4) = 0 ∧ d_0 = -(e_2 ^ 4 / 128) - 83 * e_2 * e_3 ^ 2 / 720 - 3 * e_2 ^ 2 * e_4 / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 ↔
-(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) = 0 ∧ -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) = 0 ∧ -(1 / 180) * e_3 * (45 * e_2 ^ 3 + 70 * e_3 ^ 2 + 972 * e_2 * e_4) = 0 ∧ d_0 = -(e_2 ^ 4 / 128) - 83 * e_2 * e_3 ^ 2 / 720 - 3 * e_2 ^ 2 * e_4 / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210) * e_3 * (71 * e_2 ^ 2 + 100 * e_4) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = (-52) / 39 * e_3 ∧ d_6 = -(2 * e_2) ∧ d_7 = 0 :=
begin
  simp only [one_div, neg_mul, neg_eq_zero, inv_eq_zero, bit0_eq_zero, and.congr_left_iff, and_imp],
  intros hsys2 hsys3 hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7,
  rw[hd1],
  simp*,
end

lemma system_a_notzero (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero3 : e_3 ≠ 0) (h : system_a_2 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7) : e_4 ≠ 0 :=
begin
  unfold system_a_2 at h,
  cases h with h1 h,
  cases h with h2 h,
  by_contra,
  simp[h] at h1 h2,
  rw or_iff_right at h1,
  simp[h1] at h2,
  rw or_iff_right at h2,
  exact hnotzero3 h2,
  repeat {norm_num},
end

lemma system_a_iff_system_eleven (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero3 : e_3 ≠ 0) (hnotzero4 : e_4 ≠ 0) : system_eleven e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 ↔ system_a_2 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 :=
begin
  unfold system_a_2,
  unfold system_eleven,
  simp[hnotzero3],
  norm_num,
  rw hd6 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hd5 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hd4 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hd3 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hd2 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hd1 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hd0 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hsys3 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hsys2 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3,
  rw hsys1 e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 hnotzero3 hnotzero4,
  simp*,
  norm_num,
  ring_nf,
end

end real