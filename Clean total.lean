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

variables {f : ℝ → ℝ} {s : set ℝ} {f' x : ℝ}

/- ## Simple derivatives from Calculus: A Complete Course, first year calculus book ## -/

/- # Derivative x^a = a*x^(a-1) for integers -/
lemma deriv_zpow_ours (x : ℝ) (a : ℤ) : deriv (λ (x : ℝ), x ^ a) x = a * x ^ (a - 1) :=
begin
  simp only [deriv_zpow'],
end

/- # Derivative x^a = a*x^(a-1) for real numbers -/
lemma deriv_rpow_ours (x : ℝ) (a : ℝ) (h : x ≠ 0 ∨ 1 ≤ a) : deriv (λ (x : ℝ), x ^ a) x = a * x ^ (a - 1) :=
begin
  apply deriv_rpow_const,
  exact h,
end

/- # Derivative 1/x = -1/x^2 -/
lemma deriv_inv_ours  (x : ℝ) : deriv (λ (x : ℝ), 1 / x) x = -1 / x ^ 2 :=
begin
  simp only [one_div, deriv_inv'],
  ring,
end

/- # Derivative sqrt x= 1 / (2 * sqrt x) -/

lemma deriv_sqrt_ours (x : ℝ) (hx : x ≠ 0): deriv (λ (x : ℝ), sqrt x) x = 1 / (2 * sqrt x) :=
begin 
  have h: differentiable_at ℝ  (λ (x : ℝ), x) x,
    exact differentiable_at_id',
  convert deriv_sqrt h hx,
  simp,
end

/- # Derivative exp x = exp x -/

lemma deriv_exp_ours  (x : ℝ) : deriv (λ (x : ℝ), exp x) x = exp x :=
begin
  simp only [deriv_exp], 
end

/- # Derivative sin x = cos x -/

lemma deriv_sin_ours (x : ℝ) : deriv (λ (x : ℝ), sin x) x = cos x :=
begin
  simp only [deriv_sin],
end

/- # Derivative cos x = -sin x -/

lemma deriv_cos_ours (x : ℝ) : deriv (λ (x : ℝ), cos x) x = -sin x :=
begin
  simp only [deriv_cos],
end

/- # Derivative tan x = sec ^ 2 x -/

lemma deriv_tan_ours (x : ℝ) : deriv (λ (x : ℝ), tan x) x = 1 / cos x ^ 2 :=
begin
  simp only [deriv_tan],
end

/- # Derivative sec x = sec x tan x -/

lemma deriv_sec_ours (x : ℝ) (hx : cos x ≠ 0) : deriv (λ (x : ℝ), 1 / cos x) x = 1 / cos x * tan x :=
begin
  simp only [one_div], --rewrites 1 / cos x as (cos x)⁻¹
  rw deriv_inv'' differentiable_at_cos hx,
  /-applies the chain rule to (cos x)⁻¹,
  given that cos is differentiable and nonzero at x-/
  rw tan_eq_sin_div_cos, --rewrites tan x as sin x / cos x
  rw deriv_cos, --deals with the derivative of cos x
  rw [neg_neg, inv_eq_one_div, div_mul_div_comm, one_mul, sq],
  --manipulates the final equation to get an equality
end

/- # Derivative sec x = sec x tan x, alternative version -/ 

lemma deriv_sec_ours_extra (x : ℝ) (hx : cos x ≠ 0): deriv (λ (x : ℝ), (1 / cos x)) x = sin x / cos x ^ 2 :=
begin
  have hcos: differentiable_at ℝ (λ (x:ℝ), cos x) x,
    exact differentiable_at_cos,
  have hdiv := deriv_inv'' hcos hx,
  simp at hdiv,
  ring_nf,
  ring_nf at hdiv,
  exact hdiv,
end

/- # Derivative csc x = -csc x cot x -/

lemma deriv_csc_ours (x : ℝ) (hx : sin x ≠ 0): deriv (λ (x : ℝ), 1 / sin x) x = -((1 / sin x) * (1 / tan x)) :=
begin
  simp,
  have hd: differentiable_at ℝ  (λ (x : ℝ), sin x) x,
    exact differentiable_at_sin,
  have hdiv := deriv_inv'' hd hx,
  simp at hdiv,
  rw real.tan_eq_sin_div_cos,
  rw inv_eq_one_div,
  rw inv_eq_one_div,
  rw ← div_mul,
  rw ←  mul_assoc,
  rw one_div_mul_one_div_rev,
  rw one_div,
  rw inv_mul_eq_div,
  rw ← sq,
  convert hdiv,
  ring,
end

/- # Derivative cot x = - csc^2 x -/

lemma deriv_cot_ours (x : ℝ) (hx : sin x ≠ 0): deriv (λ (x : ℝ), cos x / sin x) x = -(1 / (sin x) ^ 2) :=
begin
  have hc: has_deriv_at (λ (x : ℝ), cos x) (-sin x) x ,
    have hcc: differentiable_at ℝ  (λ (x : ℝ), cos x) x,
      exact differentiable_at_cos,
    rw ← has_deriv_at_deriv_iff at hcc,
    simp at hcc,
    exact hcc,
  have hd: has_deriv_at (λ (x : ℝ), sin x) (cos x) x ,
    have hdd: differentiable_at ℝ  (λ (x : ℝ), sin x) x,
      exact differentiable_at_sin,
    rw ← has_deriv_at_deriv_iff at hdd,
    simp at hdd,
    exact hdd,
  have hdiv := has_deriv_at.div hc hd hx,
  simp at hdiv,
  rw ← sq at hdiv,
  rw ← sq at hdiv,
  rw neg_sub_left at hdiv,
  rw real.cos_sq_add_sin_sq at hdiv,
  apply has_deriv_at.deriv,
  convert hdiv,
  ring_nf,
end

/- # Derivative arcsin = 1/sqrt(1 - x^2) -/

lemma deriv_arcsin_ours (x : ℝ): deriv (λ (x : ℝ), arcsin x) x = 1 / sqrt (1 - x ^ 2) :=
begin
  simp only [real.deriv_arcsin]
end

/- # Derivative arccos = -1/sqrt(1 - x^2) -/

lemma deriv_arccos_ours (x : ℝ): deriv (λ (x : ℝ), arccos x) x = -(1 / sqrt (1 - x ^ 2)) :=
begin
  simp only [real.deriv_arccos]
end

/- # Derivative arctan = 1/(1 + x^2) -/

lemma deriv_arctan_ours (x : ℝ): deriv (λ (x : ℝ), arctan x) x = 1 / (1 + x ^ 2) :=
begin
  simp only [real.deriv_arctan]
end

/- # Derivative a^x = ln(a)*a^x, (a > 0) -/

lemma deriv_gen_exp_ours (x : ℝ) (a : ℝ) (h: 0 < a ∧ a ≠ 1): deriv (λ (x : ℝ), (a ^ x)) x = log a * a ^ x :=
begin
  simp only,
  have hf: has_deriv_at (λ (x : ℝ), a) (0: ℝ) x ,
    have ha: differentiable_at ℝ  (λ (x : ℝ), a) x,
      exact differentiable_at_const a,
    rw ← has_deriv_at_deriv_iff at ha,
    simp at ha,
    exact ha,
  have hg: has_deriv_at (λ (x : ℝ), x) (1: ℝ) x ,
    have ha: differentiable_at ℝ  (λ (x : ℝ), x) x,
      exact differentiable_at_id',
    rw ← has_deriv_at_deriv_iff at ha,
    simp at ha,
    exact ha,
  cases h with h1 h2,
  have hmain := has_deriv_at.rpow hf hg h1,
  simp at hmain,
  rw mul_comm (a^x) (log a) at hmain,
  apply has_deriv_at.deriv hmain,
end

/- # Derivative |x| = x / |x| -/

lemma deriv_abs_ours (x : ℝ) (h: (0 < x ∨ x < 0)): deriv (λ (x : ℝ), abs x) x = x / |x| :=
begin 
  cases h with hgre hles,
  rw abs_of_pos,
  simp [div_self, hgre.ne'],
  have hsg : ∀ (x : ℝ),  0 < x → abs x = x,
    intros y hx,
    rewrite abs_of_pos,
    exact hx,
  have hg : has_deriv_within_at (λ (x : ℝ), x) 1 {x | 0 < x} x,
    apply has_deriv_at.has_deriv_within_at,
    apply has_deriv_at_id,
  have hxg: abs x = x,
    rewrite abs_of_pos,
    exact hgre,
  have hwitgre: has_deriv_within_at (λ (x : ℝ), abs x) 1 {x | 0 < x} x,
    exact has_deriv_within_at.congr hg hsg hxg,
  rw has_deriv_at.deriv,
  apply has_deriv_within_at.has_deriv_at,
  apply hwitgre,
  apply Ioi_mem_nhds,
  exact hgre,
  exact hgre,
  rw abs_of_neg,
  simp [div_neg, hles],
  simp [div_self, hles.ne],
  have hsl : ∀ (x : ℝ), x<0 → abs x = -x,
    intros y hx,
    rewrite abs_of_neg,
    exact hx,
  have hl : has_deriv_within_at (λ (x : ℝ), -x) (-1) {x | x < 0} x,
    apply has_deriv_at.has_deriv_within_at,
    apply has_deriv_at.neg,
    apply has_deriv_at_id,
  have hxl: abs x = -x,
    rewrite abs_of_neg,
    exact hles,
  have hwitles: has_deriv_within_at (λ (x : ℝ), abs x) (-1) {x | x < 0} x,
    exact has_deriv_within_at.congr hl hsl hxl,
  rw has_deriv_at.deriv,
  apply has_deriv_within_at.has_deriv_at,
  apply hwitles,
  apply Iio_mem_nhds,
  exact hles,
  exact hles,
end

/- # Derivative ln(x) = 1 / x -/ 

lemma deriv_log_ours (x : ℝ) : deriv (λ (x : ℝ), log(x)) x = 1 / x :=
begin
  simp only [deriv_log', one_div],
end

/- ## Simple anti-derivatives ## -/

def has_antideriv (f': ℝ → ℝ) (f: ℝ → ℝ) := ∀ x, deriv f x = (f' x)
def has_antideriv_within (f': ℝ → ℝ) (f: ℝ → ℝ) (s: set ℝ) := ∀ x, x ∈ s → has_deriv_at f (f' x) x

/- # Anti derivative cos x = sin x -/

lemma antideriv_cos : has_antideriv (λ (x : ℝ), cos x) (λ (x : ℝ), sin x) :=
begin
  unfold has_antideriv,
  apply deriv_sin_ours,
end

/- # Anti derivative sin x = - cos x -/

lemma antideriv_sin : has_antideriv (λ (x : ℝ), sin x) (λ (x : ℝ), -cos x) :=
begin
  unfold has_antideriv,
  convert deriv_cos_ours,
  simp only [deriv.neg', deriv_cos_ours, neg_neg, neg_inj],
end

/- # Anti derivative sec^2 x = tan x -/

lemma antideriv_sec_sq : has_antideriv (λ (x : ℝ), 1 / cos x ^ 2) (λ (x : ℝ), tan x) :=
begin
  unfold has_antideriv,
  convert deriv_tan_ours,
end

/- # Anti derivative csc^2 x = -cot x -/

lemma antideriv_csc_sq: has_antideriv_within (λ (x : ℝ), (1 / sin x ^ 2)) (λ (x : ℝ), - (cos x / sin x))  {x | sin x ≠ 0} :=
begin
  unfold has_antideriv_within,
  intro x,
  intro hset,
  simp at hset,
  have h: differentiable_at ℝ (λ (x : ℝ), - (cos x / sin x)) x,
    simp,
    apply differentiable_at.div,
    exact differentiable_at_cos,
    exact differentiable_at_sin,
    intro h,
    apply hset h,
  have h1 := differentiable_at.has_deriv_at h,
  convert h1,
  have h2: 1 / sin x ^ 2 = deriv (λ (x : ℝ), - (cos x / sin x)) x,
    rw deriv.neg,
    rw deriv_cot_ours,
    simp,
    intro h3,
    apply hset h3,
  exact h2,  
end

/- # Anti derivative sec x tan x = -cot x -/

lemma antideriv_sec_tan : has_antideriv_within (λ (x : ℝ), (1 / cos x) * tan x) (λ (x : ℝ),  1 / cos x) {x | cos x ≠ 0} :=
begin
  unfold has_antideriv_within,
  intro x,
  intro hset,
  simp at hset,
  have h: differentiable_at ℝ (λ (x : ℝ), 1 / cos x) x,
    apply differentiable_at.div,
    exact differentiable_at_const 1,
    exact differentiable_at_cos,
    intro h,
    apply hset h,    
  have h1 := differentiable_at.has_deriv_at h,
  convert h1,
  have h2: (1 / cos x) * tan x = deriv (λ (x : ℝ), 1 / cos x) x,
    symmetry,
    apply deriv_sec_ours x hset,
  exact h2,
end

/- # Anti derivative x^a = 1/(a+1) * x^(a+1) for integers -/

lemma antideriv_zpow (a : ℤ) (h: a + 1 ≠ 0): has_antideriv (λ (x : ℝ), x ^ a) (λ (x : ℝ), 1 / (a + 1) * x ^ (a + 1)) :=
begin
  unfold has_antideriv, --unfolds the definition has_antiderivative
  intro x, --introduces an arbitrary x
  simp, --deals with the derivative
  rw [← one_div, ← mul_assoc _ _ (x^a), one_div_mul_cancel, one_mul],
  --rewrites (↑a + 1)⁻¹ * ((↑a + 1) * x ^ a) as (x ^ a), leaving the goal ↑a + 1 ≠ 0
  norm_cast, --moves ↑a in ℝ to a in ℤ
  exact h,
end

/- # Anti derivative x^a = 1/(a+1) * x^(a+1) for real numbers -/

lemma antideriv_rpow (a : ℤ) (h1: a + 1 ≠ 0) : has_antideriv_within (λ (x : ℝ), x ^ a) (λ (x : ℝ),  1 / (a + 1) * x ^ (a + 1)) {x : ℝ | x ≠ 0} :=
begin
  unfold has_antideriv_within,
  intro y,
  intro h3,
  have h4: differentiable_at ℝ (λ (x : ℝ), x ^ (a + 1)) y,
  { apply differentiable_at.zpow,
    exact differentiable_at_id, 
    left,
    assumption },
  have h5 := differentiable_at.has_deriv_at h4,
  convert has_deriv_at.const_mul (1 / (a + 1) : ℝ) (has_deriv_at.rpow_const (has_deriv_at_id _) (or.inl h3)),
  swap 3, exact a + 1,
  ext,
  simp,
  left,
  norm_cast,
  field_simp,
  rw mul_div_cancel_left,
  exact_mod_cast h1,
end

/- # Anti derivative 1/x = ln|x| -/

lemma antideriv_inv : has_antideriv (λ (x : ℝ), 1 / x) (λ (x : ℝ),  log (|x|)) :=
begin
  unfold has_antideriv,
  convert deriv_log_ours,
  simp,
end

/- # Anti derivative exp x = exp x -/

lemma antideriv_exp : has_antideriv (λ (x : ℝ), exp x) (λ (x : ℝ),  exp x) :=
begin
  unfold has_antideriv,
  convert deriv_exp_ours,
end

/- # Anti derivative a^x = 1 / log(a) * a^x -/

lemma antideriv_gen_exp (a : ℝ) (h: 0 < a ∧ a ≠ 1): has_antideriv (λ (x : ℝ), a ^ x) (λ (x : ℝ), 1 / log a * a ^ x) :=
begin
  unfold has_antideriv,
  intro x,
  rw deriv_const_mul,
  rw deriv_gen_exp_ours x a h,
  rw ←  mul_assoc (1 / log a) (log a) (a ^ x),
  rw one_div_mul_cancel,
  rw one_mul,
  cases h with h1 h2,
  apply log_ne_zero_of_pos_of_ne_one h1 h2,
  have h: differentiable_at ℝ (λ (x : ℝ), a ^ x) x,
    apply differentiable_at.rpow,
    exact differentiable_at_const a,
    exact differentiable_at_id,
    linarith,
  exact h,
end

/- # Anti derivative Example  x / sqrt(x^4)= ln(x) -/

example : has_antideriv (λ (x : ℝ), x / sqrt(x ^ 4)) (λ (x : ℝ), log(x)) :=
begin
  unfold has_antideriv,
  convert deriv_zpow_ours,
  simp,
  intro x,
  ring_nf,
  rw ((real.sqrt_eq_iff_sq_eq (pow_bit0_nonneg _ 2) (pow_bit0_nonneg x 1)).mpr _),
  ring_nf,
  by_cases h1: x = 0,
  { simp [h1] },
  { field_simp,
    ring },
  ring,
end

/- ## Elementary functions ## -/

/- # Definitions -/

inductive is_elementary : (ℝ → ℝ) → set ℝ → Prop 
| const : ∀ (a : ℝ), is_elementary (λ (x : ℝ), a) univ
| id : is_elementary id univ
| sin : is_elementary sin univ
| cos : is_elementary cos univ
| exp : is_elementary exp univ
| log : is_elementary log {x | 0 < x}
| add {f g s t} : is_elementary f s → is_elementary g t → is_elementary (f + g) (s ∩ t)
| sub {f g s t} : is_elementary f s → is_elementary g t → is_elementary (f - g) (s ∩ t)
| mul {f g s t} : is_elementary f s → is_elementary g t → is_elementary (f * g) (s ∩ t)
| div {f g s t} : is_elementary f s → is_elementary g t → is_elementary (f / g) (s ∩ t ∩ (g⁻¹' {0})ᶜ)
| comp {f g s t} : is_elementary f s → is_elementary g t → is_elementary (f ∘ g) (t ∩ g⁻¹' s)

def is_elementary_within (f : ℝ → ℝ) (s : set ℝ) := ∃ (g : ℝ → ℝ) (t : set ℝ), is_elementary g t ∧ ∀ (x ∈ s), f x = g x ∧ s ⊆ t

lemma is_elementary_within_def (f : ℝ → ℝ) (s : set ℝ) : is_elementary_within f s ↔ ∃ (g : ℝ → ℝ) (t : set ℝ), is_elementary g t ∧ ∀ (x ∈ s), f x = g x ∧ s ⊆ t :=
begin
  refl,
end

lemma is_elementary.is_elementary_within (f : ℝ → ℝ) (s : set ℝ) (hf : is_elementary f s) : is_elementary_within f s :=
begin
  use [f, s],
  simp[hf],
  intros x hx,
  refl,
end

lemma is_elementary_within.is_elementary_within_subset (f : ℝ → ℝ) (s t : set ℝ) (hs : s ⊆ t) (hf : is_elementary_within f t) : is_elementary_within f s :=
begin
  cases hf with g hf,
  cases hf with u hf,
  use [g, u],
  cases hf with hg hf,
  simp[hg],
  intros x hx,
  specialize hf x,
  have hxt : x ∈ t,
    exact hs hx,
  simp[hxt] at hf,
  cases hf with hf ht,
  simp[hf],
  apply subset.trans hs ht,
end

example (s t u : set ℝ) (hs : s ⊆ t) (ht : t ⊆ u) : s ⊆ u :=
begin
  exact subset.trans hs ht,
end

/- # Basic operations for is_elementary_within -/

lemma is_elementary_within.add (f g : ℝ → ℝ) (s t : set ℝ) (hf : is_elementary_within f s) (hg : is_elementary_within g t) : is_elementary_within (f + g) (s ∩ t):=
begin
  cases hf with F hF,
  cases hg with G hG,
  cases hF with S hF,
  cases hG with T hG,
  cases hF with hF1 hF2,
  cases hG with hG1 hG2,
  use [(F + G), (S ∩ T)],
  split,
  apply is_elementary.add hF1 hG1,
  intros x hx,
  specialize hF2 x,
  specialize hG2 x,
  simp at hx,
  simp at *,
  simp*,
  simp[hx] at hF2 hG2,
  cases hF2 with hF2 hS,
  cases hG2 with hG2 hT,
  rw ← set.subset_inter_iff,
  apply set.inter_subset_inter,
  exact hS,
  exact hT,
end

lemma is_elementary_within.sub (f g : ℝ → ℝ) (s t : set ℝ) (hf : is_elementary_within f s) (hg : is_elementary_within g t) : is_elementary_within (f - g) (s ∩ t) :=
begin
  cases hf with F hF,
  cases hg with G hG,
  cases hF with S hF,
  cases hG with T hG,
  cases hF with hF1 hF2,
  cases hG with hG1 hG2,
  use [(F - G), (S ∩ T)],
  split,
  apply is_elementary.sub hF1 hG1,
  intros x hx,
  specialize hF2 x,
  specialize hG2 x,
  simp at hx,
  simp at *,
  simp*,
  simp[hx] at hF2 hG2,
  cases hF2 with hF2 hS,
  cases hG2 with hG2 hT,
  rw ← set.subset_inter_iff,
  apply set.inter_subset_inter,
  exact hS,
  exact hT,
end

lemma is_elementary_within.mul (f g : ℝ → ℝ) (s t : set ℝ) (hf : is_elementary_within f s) (hg : is_elementary_within g t) : is_elementary_within (f * g) (s ∩ t) :=
begin
  cases hf with F hF,
  cases hg with G hG,
  cases hF with S hF,
  cases hG with T hG,
  cases hF with hF1 hF2,
  cases hG with hG1 hG2,
  use [(F * G), (S ∩ T)],
  split,
  apply is_elementary.mul hF1 hG1,
  intros x hx,
  specialize hF2 x,
  specialize hG2 x,
  simp at hx,
  simp at *,
  simp*,
  simp[hx] at hF2 hG2,
  cases hF2 with hF2 hS,
  cases hG2 with hG2 hT,
  rw ← set.subset_inter_iff,
  apply set.inter_subset_inter,
  exact hS,
  exact hT,
end

lemma is_elementary_within.div (f g : ℝ → ℝ) (s t : set ℝ) (hf : is_elementary_within f s) (hg : is_elementary_within g t) : is_elementary_within (f / g) (s ∩ t ∩ (g⁻¹' {0})ᶜ) :=
begin
  cases hf with F hF,
  cases hg with G hG,
  cases hF with S hF,
  cases hG with T hG,
  cases hF with hF1 hF2,
  cases hG with hG1 hG2,
  unfold is_elementary_within,
  use [(F / G), (S ∩ T ∩ (G⁻¹' {0})ᶜ)],
  split,
  apply is_elementary.div hF1 hG1,
  intros x hx,
  simp at hx,
  simp at *,
  simp*,
  rw ← set.subset_inter_iff,
  rw ← set.subset_inter_iff,
  unfold preimage,
  intros y hy,
  simp at *,
  specialize hF2 y,
  specialize hG2 y,
  cases hy with hyST hy,
  cases hyST with hyS hyT,
  simp[hyS, hyT] at hF2 hG2,
  simp[hG2] at hy,
  simp[hy],
  cases hG2 with hG2 hT,
  cases hF2 with hF2 hS,
  split,
  apply hS,
  exact hyS,
  apply hT,
  exact hyT,
end

lemma is_elementary_within.comp (f g : ℝ → ℝ) (s t : set ℝ) (hf : is_elementary_within f s) (hg : is_elementary_within g t) : is_elementary_within (f ∘ g) (t ∩ (g⁻¹' s)) :=
begin
  cases hf with F hF,
  cases hg with G hG,
  cases hF with S hF,
  cases hG with T hG,
  cases hF with hF1 hF2,
  cases hG with hG1 hG2,
  use [(F ∘ G), (T ∩ (G⁻¹' S))],
  split,
  apply is_elementary.comp hF1 hG1,
  intros x hx,
  split,
  specialize hG2 x,
  simp at hx,
  simp at *,
  simp*,
  simp[hx] at hF2 hG2,
  cases hx with hxt hxs,
  cases hG2 with hG2 hT,
  simp[hG2] at hxs,
  specialize hF2 (G x),
  simp[hxs] at hF2,
  cases hF2 with hF2 hS,
  exact hF2,
  intros y hy,
  rw set.mem_inter_iff at hy,
  cases hy with hyt hys,
  unfold preimage at *,
  specialize hG2 y,
  simp[hyt] at hG2,
  cases hG2 with hG2 hT,
  simp,
  split,
  apply hT,
  exact hyt,
  specialize hF2 (g y),
  simp at hys,
  simp[hys] at hF2,
  cases hF2 with hF2 hS,
  apply hS,
  rw ← hG2,
  exact hys,
end

/- # Basic lemmas for elementary functions -/

lemma is_elementary.neg (f : ℝ → ℝ) (h : is_elementary f s) : is_elementary (-f) s :=
begin
  rw [neg_eq_zero_sub, ← univ_inter s],
  exact is_elementary.sub (is_elementary.const 0) h,
end

lemma is_elementary_within.neg (f : ℝ → ℝ) (h : is_elementary_within f s) : is_elementary_within (-f) s :=
begin
  rw [neg_eq_zero_sub, ← univ_inter s],
  apply is_elementary_within.sub,
  use [(λ (x : ℝ), 0), univ],
  simp[is_elementary.const],
  exact h,
end

lemma is_elementary.one_div (f : ℝ → ℝ) (h : is_elementary f s) : is_elementary (1/f) (s ∩ (f⁻¹' {0})ᶜ) :=
begin
  rw ← univ_inter s,
  exact is_elementary.div (is_elementary.const 1) h,
end

lemma is_elementary_within.one_div (f : ℝ → ℝ) (h : is_elementary_within f s) : is_elementary_within (1/f) (s ∩ (f⁻¹' {0})ᶜ) :=
begin
  rw ← univ_inter s,
  apply is_elementary_within.div,
  use [(λ (x : ℝ), 1), univ],
  simp[is_elementary.const],
  exact h,
end

lemma is_elementary.add_const (a : ℝ) (f : ℝ → ℝ) (h : is_elementary f s) : is_elementary (λ (x : ℝ), f(x) + a) s :=
begin
  have hs : s = s ∩ univ,
    simp,
  rw hs,
  exact is_elementary.add h (is_elementary.const a),
end

lemma is_elementary.sub_const (a : ℝ) (f : ℝ → ℝ) (h : is_elementary f s) : is_elementary (λ (x : ℝ), f(x) - a) s :=
begin
  have hs : s = s ∩ univ,
    simp,
  rw hs,
  exact is_elementary.sub h (is_elementary.const (a)),
end

lemma is_elementary.const_mul (a : ℝ) (f : ℝ → ℝ) (h : is_elementary f s) : is_elementary (λ (x : ℝ), a * (f x)) s :=
begin
  have hs : s = univ ∩ s,
    simp,
  rw hs,
  exact is_elementary.mul (is_elementary.const a) h,
end

lemma is_elementary.const_mul_id (a : ℝ) : is_elementary (λ (x : ℝ), a * x) univ :=
begin
  exact is_elementary.const_mul _ _ is_elementary.id,
end

lemma is_elementary_within.add_const (a : ℝ) (f : ℝ → ℝ) (h : is_elementary_within f s) : is_elementary_within (λ (x : ℝ), f(x) + a) s :=
begin
  have hs : s = s ∩ univ,
    simp,
  rw hs,
  apply is_elementary_within.add,
  exact h,
  exact is_elementary.is_elementary_within _ _ (is_elementary.const a),
end

lemma is_elementary_within.sub_const (a : ℝ) (f : ℝ → ℝ) (h : is_elementary_within f s) : is_elementary_within (λ (x : ℝ), f(x) - a) s :=
begin
  have hs : s = s ∩ univ,
    simp,
  rw hs,
  apply is_elementary_within.sub,
  exact h,
  exact is_elementary.is_elementary_within _ _ (is_elementary.const a),
end

lemma is_elementary_within.const_mul (a : ℝ) (f : ℝ → ℝ) (h : is_elementary_within f s) : is_elementary_within (λ (x : ℝ), a * (f x)) s :=
begin
  have hs : s = univ ∩ s,
    simp,
  rw hs,
  apply is_elementary_within.mul,
  apply is_elementary.is_elementary_within,
  exact is_elementary.const a,
  exact h,
end

lemma is_elementary_wihtin.const_mul_id (a : ℝ) : is_elementary_within (λ (x : ℝ), a * x) univ :=
begin
  apply is_elementary_within.const_mul,
  exact is_elementary.is_elementary_within _ _ is_elementary.id,
end

/- # Showing functions are elementary -/

lemma is_elementary.npow (n : ℕ) : is_elementary (λ (x : ℝ), x^n) univ :=
begin
  induction n with n hn,
  {have h : (λ (x : ℝ), x ^ 0) = (λ (x : ℝ), 1),
    ext x,
    rw pow_zero,
  rw h,
  exact is_elementary.const 1},
  {have h : (λ (x : ℝ), x ^ n.succ) = (λ (x : ℝ), x^n * x),
    ext x,
    rw [nat.succ_eq_add_one, pow_add x n 1, pow_one],
  rw h,
  rw ← univ_inter univ,
  exact is_elementary.mul hn is_elementary.id}
end

lemma is_elementary.const_mul_npow (a : ℝ) (b : ℕ) : is_elementary (λ (x : ℝ), a*x^b) univ :=
begin
  exact is_elementary.const_mul _ _ (is_elementary.npow b),
end

lemma is_elementary_within.const_mul_npow (a : ℝ) (b : ℕ) : is_elementary_within (λ (x : ℝ), a*x^b) univ :=
begin
  apply is_elementary_within.const_mul,
  exact is_elementary.is_elementary_within _ _ (is_elementary.npow b),
end

lemma is_elementary_within.zpow (n : ℤ) : is_elementary_within (λ (x : ℝ), x^n) {x : ℝ | x ≠ 0} :=
begin
  cases n with n n,
  {use [(λ (x : ℝ), x ^n), univ],
  split,
  {exact is_elementary.npow n},
  {intros x hx,
  simp at *}},
  {use [(λ (x : ℝ), 1/x^(n+1)), univ ∩ univ ∩ ((λ (x : ℝ), x^(n+1))⁻¹' {0})ᶜ],
  split,
  {exact is_elementary.div (is_elementary.const 1) (is_elementary.npow (n+1))},
  {intros x hx,
  simp at *,
  have hs : ((λ (x : ℝ), x^(n+1))⁻¹' {0})ᶜ = {x : ℝ | x ≠ 0},
    unfold set.preimage,
    simp,
    refl,
  simp[hs]}},
end

lemma is_elementary_within.rpow (a : ℝ) : is_elementary_within (λ (x : ℝ), x^a) {x : ℝ | 0 < x} :=
begin
  use [(λ (x : ℝ), exp (a * log x)), ({x : ℝ | 0 < x} ∩ ((λ (x : ℝ), a*log x)⁻¹' univ))],
  split,
  {apply is_elementary.comp,
  exact is_elementary.exp,
  rw ← univ_inter {x : ℝ | 0 < x},
  exact is_elementary.mul (is_elementary.const a) is_elementary.log},
  intros x hx,
  split,
  {simp at *,
  rw ← log_rpow hx a,
  have hxa : 0 < x^a,
    exact rpow_pos_of_pos hx a,
  rw exp_log hxa},
  simp,
end

lemma is_elementary_within.sqrt : is_elementary_within sqrt {x : ℝ | 0 < x} :=
begin
  have h : sqrt = (λ (x : ℝ), x^(1/2 : ℝ)),
    ext x,
    rw sqrt_eq_rpow,
  rw h,
  simp[is_elementary_within.rpow],
end

lemma is_elementary_within.abs : is_elementary_within abs {x : ℝ | x ≠ 0} :=
begin
  have h : abs = (λ (x : ℝ), sqrt(x^2)),
    ext x,
    symmetry,
    revert x,
    exact sqrt_sq_eq_abs,
  rw h,
  have hpreim : (λ (x : ℝ), x^2)⁻¹' {x : ℝ | 0 < x} = {x : ℝ | x ≠ 0},
    simp[sq_pos_iff],
  rw ← univ_inter {x : ℝ | x ≠ 0},
  rw ← hpreim,
  apply is_elementary_within.comp,
  exact is_elementary_within.sqrt,
  apply is_elementary.is_elementary_within,
  exact is_elementary.npow 2,
end

lemma is_elementary.gen_exp (a : ℝ) (ha : 0 < a) : is_elementary (pow a) univ :=
begin
  have h : pow a = (λ (x : ℝ), exp(x * log(a))),
    ext x,
    rw [← log_rpow, exp_log],
    apply rpow_pos_of_pos ha,
    exact ha,
  rw [h, ← univ_inter univ],
  have hpreim : (λ (x : ℝ), x * log(a))⁻¹' univ = univ,
    simp,
  nth_rewrite 1 ← hpreim,
  apply is_elementary.comp is_elementary.exp,
  rw ← univ_inter univ,
  exact is_elementary.mul is_elementary.id (is_elementary.const (log a)),
end

lemma is_elementary.gen_log (b : ℝ) (hb : 0 < b) : is_elementary (logb b) ({x : ℝ | 0 < x} ∩ ((λ (x : ℝ), log b)⁻¹' {0})ᶜ) :=
begin
  have h : logb b = (λx, (log x)/(log b)),
    refl,
  rw h,
  have hs2 : {x : ℝ | 0 < x} ∩ ((λ (x : ℝ), log b)⁻¹' {0})ᶜ = {x : ℝ | 0 < x} ∩ univ ∩ ((λ (x : ℝ), log b)⁻¹' {0})ᶜ,
    simp,
  rw hs2,
  exact is_elementary.div is_elementary.log (is_elementary.const (log b)),
end

/- ## Elementary anti-derivatives ## -/

/- # Definitions -/

def is_elementary_anti (f' : ℝ → ℝ) (s : set ℝ) := ∃ (f : ℝ → ℝ), is_elementary f s ∧ has_antideriv f' f
def is_elementary_anti_within (f' : ℝ → ℝ) (s : set ℝ) := ∃ (f : ℝ → ℝ), is_elementary f s ∧ has_antideriv_within f' f s
def is_elementary_within_anti (f' : ℝ → ℝ) (s : set ℝ) := ∃ (f : ℝ → ℝ), is_elementary_within f s ∧ has_antideriv f' f
def is_elementary_within_anti_within (f' : ℝ → ℝ) (s : set ℝ) := ∃ (f : ℝ → ℝ), is_elementary_within f s ∧ has_antideriv_within f' f s

lemma is_elementary_within_anti_within.subset (f' : ℝ → ℝ) (s t : set ℝ) (hs : s ⊆ t) (hf : is_elementary_within_anti_within f t) : is_elementary_within_anti_within f s :=
begin
  cases hf with F hF,
  use F,
  split,
  apply is_elementary_within.is_elementary_within_subset F s t hs,
  simp[hF],
  cases hF with hF hf,
  unfold has_antideriv_within at *,
  intros x hx,
  specialize hf x,
  have hxt : x ∈ t,
    exact hs hx,
  simp[hxt] at hf,
  exact hf,
end

/- # Simple elementary anti-derivatives -/

lemma elementary_antideriv_cos : is_elementary_anti (λ (x : ℝ), cos x) univ :=
begin
  use (λ (x : ℝ), sin x),
  split,
  exact is_elementary.sin,
  exact antideriv_cos,
end

lemma elementary_antideriv_sin : is_elementary_anti (λ (x : ℝ), sin x) univ :=
begin
  use (λ (x : ℝ), -cos x),
  split,
  exact is_elementary.neg _ is_elementary.cos,
  exact antideriv_sin,
end

lemma elementary_antideriv_sec_sq : is_elementary_anti (λ (x : ℝ), 1 / cos x ^ 2) (cos⁻¹' {0})ᶜ :=
begin
  use (λ (x : ℝ), tan x),
  split,
  {have h : (λ (x : ℝ), tan x) = (λ (x : ℝ), sin x / cos x),
    ext x,
    revert x,
    exact tan_eq_sin_div_cos,
  rw h,
  have hs : (cos⁻¹' {0})ᶜ = univ ∩ univ ∩ (cos⁻¹' {0})ᶜ,
    simp,
  rw hs,
  exact is_elementary.div is_elementary.sin is_elementary.cos},
  exact antideriv_sec_sq,
end

lemma elementary_antideriv_csc_sq : is_elementary_anti_within (λ (x : ℝ), (1 / sin x ^ 2)) {x| sin x ≠ 0} :=
begin
  use (λ (x : ℝ), - (cos x / sin x)),
  split,
  {apply is_elementary.neg,
  rw ← univ_inter {x| sin x ≠ 0},
  rw ← univ_inter univ,
  exact is_elementary.div is_elementary.cos is_elementary.sin},
  exact antideriv_csc_sq,
end

lemma elementary_antideriv_sec_tan : is_elementary_anti_within (λ (x : ℝ), (1/cos x) * tan x) {x| cos x ≠ 0} :=
begin
  unfold is_elementary_anti_within,
  use (λ (x : ℝ),  1 / cos x),
  split,
  {rw ← univ_inter {x| cos x ≠ 0},
  exact is_elementary.one_div _ is_elementary.cos},
  exact antideriv_sec_tan,
end

lemma elementary_antideriv_npow (n : ℤ) (h: n + 1 ≠ 0) : is_elementary_within_anti (λ (x : ℝ), x^n) {x : ℝ | x ≠ 0} :=
begin
  use (λ (x : ℝ), 1/(n + 1) * x^(n + 1)),
  split,
  {rw ← univ_inter {x : ℝ | x ≠ 0},
  apply is_elementary_within.mul,
  exact is_elementary.is_elementary_within _ _ (is_elementary.const (1 / (n + 1))),
  exact is_elementary_within.zpow (n + 1)},
  exact antideriv_zpow n h,
end

lemma elementary_antideriv_inv : is_elementary_within_anti (λ (x : ℝ), 1 / x) {x : ℝ | x ≠ 0} :=
begin
  use (λ (x : ℝ), log(|x|)),
  split,
  {rw ← inter_self {x : ℝ | x ≠ 0},
  have h : {x : ℝ | x ≠ 0} = (λ (x : ℝ), |x|)⁻¹' {x : ℝ | 0 < x},
    simp,
  nth_rewrite 1 h,
  apply is_elementary_within.comp,
  exact is_elementary.is_elementary_within _ _ is_elementary.log,
  exact is_elementary_within.abs},
  exact antideriv_inv,
end

lemma elementary_antideriv_exp (a : ℝ) : is_elementary_anti (λ (x : ℝ), exp x) univ :=
begin
  use (λ (x : ℝ), exp x),
  split,
  exact is_elementary.exp,
  exact antideriv_exp,
end

lemma elementary_antideriv_gen_exp (x : ℝ) (a : ℝ) (h: 0 < a ∧ a ≠ 1) : is_elementary_anti (λ (x : ℝ), a^x) univ :=
begin
  use (λ (x : ℝ), 1 / log(a) * a^x),
  split,
  {rw ← univ_inter univ,
  apply is_elementary.mul,
  apply is_elementary.const (1 / log a),
  cases h with h1 h2,
  exact is_elementary.gen_exp a h1},
  exact antideriv_gen_exp a h,
end

/- ## Case study ## -/

/- # Function definitions and their derivatives -/

def fun_a (x:ℝ) : ℝ := x^6 + 15*x^4 - 80*x^3 + 27*x^2 - 528*x + 781
def fun_b (x:ℝ) : ℝ := -x^8-20*x^6+128*x^5-54*x^4+1408*x^3-3124*x^2-10001
def fun_y (x:ℝ) : ℝ := sqrt (x^4+10*x^2-96*x-71)
def fun_p (x:ℝ) : ℝ := x^4 + 10 * x^2 - 96 * x - 71
def fun_k (x:ℝ) : ℝ := 80008 * x + 24992 * x^3 - 11264 * x^4 + 432 * x^5 - 1024 * x^6 + 160 * x^7 + 8 * x^9
def fun_h (x:ℝ) : ℝ := -55451 - 37488 * x + 56581 * x^2 - 2192 * x^3 + 7666 * x^4 - 2768 * x^5 + 106 *x^6 - 176 * x^7 + 25 * x^8 + x^10

lemma deriv_a (x : ℝ): deriv fun_a x =  6*x^5 + 60*x^3 - 240*x^2 + 54*x - 528 :=
begin
  have h : fun_a = (λ (x : ℝ), x^6 + 15*x^4 - 80*x^3 + 27*x^2 - 528*x + 781),
    refl,
  rw h,
  simp,
  ring,
end

lemma deriv_b (x : ℝ): deriv fun_b x =  -8*x^7-120*x^5+640*x^4-216*x^3+4224*x^2-6248*x :=
begin
  have h : fun_b = (λ (x : ℝ), -x^8-20*x^6+128*x^5-54*x^4+1408*x^3-3124*x^2-10001),
    refl,
  rw h,
  simp,
  ring,
end

lemma deriv_y (x : ℝ) (hpos : 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71): deriv fun_y x =  (4*x^3+20*x-96) / (2*(sqrt (x^4 + 10*x^2-96*x-71))) :=
begin
  have h1 : fun_y = (λ (x : ℝ), sqrt (x^4+10*x^2-96*x-71)),
    refl,
  rw [h1, deriv_sqrt],
  simp,
  ring,
  simp,
  linarith,
end

lemma deriv_p (x : ℝ) : deriv fun_p x = 4*x^3+20*x-96 :=
begin
  have hz : fun_p = (λ (x : ℝ), x^4 + 10*x^2 - 96*x - 71),
    refl,
  rw hz,
  simp,
  ring,
end

/- # Showing f and F are elementary -/

lemma is_elementary_within_f_step : is_elementary_within fun_y {x : ℝ | 0 < x^4 + 10*x^2 - 96*x - 71} :=
begin
  unfold is_elementary_within,
  unfold fun_y,
  rw ← univ_inter {x : ℝ | x ^ 4 + 10 * x ^ 2 - 96 * x - 71 > 0},
  apply is_elementary_within.comp,
  {exact is_elementary_within.sqrt},
  apply is_elementary.is_elementary_within,
  rw ← univ_inter univ,
  nth_rewrite 0 ← univ_inter univ,
  nth_rewrite 0 ← univ_inter univ,
  repeat {apply is_elementary.add},
  {exact is_elementary.npow 4},
  {exact is_elementary.const_mul_npow 10 2},
  {apply is_elementary.neg,
  apply is_elementary.const_mul_id},
  exact is_elementary.const (-71),
end

lemma is_elementary_within_f : is_elementary_within (λ (x : ℝ), x / fun_y x) {x : ℝ | x^4 + 10*x^2 - 96*x - 71 > 0} :=
begin
  rw is_elementary_within_def,
  unfold fun_y,
  rw ← is_elementary_within_def,
  have hs : {x : ℝ | x^4 + 10*x^2 - 96*x - 71 > 0} = univ ∩ {x : ℝ | x^4 + 10*x^2 - 96*x - 71 > 0} ∩ {x : ℝ | x^4 + 10*x^2 - 96*x - 71 > 0},
    simp,
  rw hs,
  have hpreim : {x : ℝ | x^4 + 10*x^2 - 96*x - 71 > 0} = ((λ (x : ℝ), sqrt (x^4 + 10*x^2 - 96*x - 71))⁻¹' {0})ᶜ,
    unfold preimage,
    ext x,
    split,
    {intro hx,
    simp at *,
    rw [← ne, sqrt_ne_zero'],
    simp[hx]},
    {simp,
    intro hx,
    rw [← ne, sqrt_ne_zero'] at hx,
    simp at hx,
    exact hx},
  rw hpreim,
  apply is_elementary_within.div,
  exact is_elementary.is_elementary_within _ _ is_elementary.id,
  rw ← hpreim,
  exact is_elementary_within_f_step,
end

lemma is_elementary_within_F : is_elementary_within (λ (x : ℝ), -1/8 * log ((fun_a x) * (fun_y x) + (fun_b x))) {x : ℝ | 0 < x^4 + 10*x^2 - 96*x - 71 ∧ 0 < (x^6 + 15*x^4 - 80*x^3 + 27*x^2 - 528*x + 781) * sqrt(x^4 + 10*x^2 - 96*x - 71) + (-x^8 - 20*x^6 + 128*x^5 - 54*x^4 + 1408*x^3 - 3124*x^2 - 10001)} :=
begin
  rw is_elementary_within_def,
  unfold fun_a, unfold fun_y, unfold fun_b,
  rw ← is_elementary_within_def,
  rw ← univ_inter {x : ℝ | 0 < x^4 + 10*x^2 - 96*x - 71 ∧ 0 < (x^6 + 15*x^4 - 80*x^3 + 27*x^2 - 528*x + 781) * sqrt(x^4 + 10*x^2 - 96*x - 71) + (-x^8 - 20*x^6 + 128*x^5 - 54*x^4 + 1408*x^3 - 3124*x^2 - 10001)},
  apply is_elementary_within.mul,
  exact is_elementary.is_elementary_within _ _ (is_elementary.const ((-1)/8)),
  have hs : {x : ℝ | 0 < x^4 + 10*x^2 - 96*x - 71 ∧ 0 < (x^6 + 15*x^4 - 80*x^3 + 27*x^2 - 528*x + 781) * sqrt(x^4 + 10*x^2 - 96*x - 71) + (-x^8 - 20*x^6 + 128*x^5 - 54*x^4 + 1408*x^3 - 3124*x^2 - 10001)} = {x : ℝ | 0 < x^4 + 10*x^2 - 96*x - 71} ∩ {x : ℝ | 0 < (x^6 + 15*x^4 - 80*x^3 + 27*x^2 - 528*x + 781) * sqrt(x^4 + 10*x^2 - 96*x - 71) + (-x^8 - 20*x^6 + 128*x^5 - 54*x^4 + 1408*x^3 - 3124*x^2 - 10001)},
    rw inter_def,
    simp,
  rw hs,
  have hpreim : {x : ℝ | 0 < (x^6 + 15*x^4 - 80*x^3 + 27*x^2 - 528*x + 781) * sqrt(x^4 + 10*x^2 - 96*x - 71) + (-x^8 - 20*x^6 + 128*x^5 - 54*x^4 + 1408*x^3 - 3124*x^2 - 10001)} = (λ i, (i ^ 6 + 15 * i ^ 4 - 80 * i ^ 3 + 27 * i ^ 2 - 528 * i + 781) * sqrt (i ^ 4 + 10 * i ^ 2 - 96 * i - 71) + (-i ^ 8 - 20 * i ^ 6 + 128 * i ^ 5 - 54 * i ^ 4 + 1408 * i ^ 3 - 3124 * i ^ 2 - 10001))⁻¹' {x : ℝ | 0 < x},
    simp,
  rw hpreim,
  apply is_elementary_within.comp,
  exact is_elementary.is_elementary_within _ _ is_elementary.log,
  rw ← inter_univ {x : ℝ | 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71},
  apply is_elementary_within.add,
  {rw ← univ_inter {x : ℝ | 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71},
    apply is_elementary_within.mul,
    {apply is_elementary.is_elementary_within,
      apply is_elementary.add_const 781,
      nth_rewrite 0 ← univ_inter univ,
      nth_rewrite 0 ← univ_inter univ,
      nth_rewrite 0 ← univ_inter univ,
      nth_rewrite 0 ← univ_inter univ,
      {repeat {apply is_elementary.add},
        {exact is_elementary.npow 6},
        {exact is_elementary.const_mul_npow 15 4},
        {exact is_elementary.neg _ (is_elementary.const_mul_npow 80 3)},
        {exact is_elementary.const_mul_npow 27 2},
        {exact is_elementary.neg _ (is_elementary.const_mul_id _)}}},
  exact is_elementary_within_f_step},
  {apply is_elementary.is_elementary_within,
  apply is_elementary.sub_const 10001,
  nth_rewrite 0 ← univ_inter univ,
  nth_rewrite 0 ← univ_inter univ,
  nth_rewrite 0 ← univ_inter univ,
  nth_rewrite 0 ← univ_inter univ,
  nth_rewrite 0 ← univ_inter univ,
    {repeat {apply is_elementary.add},
      {exact is_elementary.neg _ (is_elementary.npow 8)},
      {exact is_elementary.neg _ (is_elementary.const_mul_npow 20 6)},
      {exact is_elementary.const_mul_npow 128 5},
      {exact is_elementary.neg _ (is_elementary.const_mul_npow 54 4)},
      {exact is_elementary.const_mul_npow 1408 3},
      {exact is_elementary.neg _ (is_elementary.const_mul_npow 3124 2)}}}
end

/- # Showing F' = f -/

lemma big_eq_is_eq (hpos : 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) : ((fun_h x)*(deriv fun_b x)*(fun_p x) - (fun_b x)*(fun_k x)*(fun_p x))/((fun_h x)^2-(fun_b x)^2*(fun_p x)) = -8*x :=
begin
  unfold fun_b,
  unfold fun_p,
  unfold fun_h,
  unfold fun_k,
  rw deriv_b,
  simp,
  ring_nf,
  repeat {rw inv_eq_one_div},
  simp[mul_add, mul_sub, sub_mul, add_mul],
  have h1 : 1146617856 * (-(143327232 * x ^ 2 * x * x) - 1433272320 * x * x + 13759414272 * x + 10176233472)⁻¹ * x ^ 2 * x * x * x = 1146617856 * (-(143327232 * x ^ 4) - 1433272320 * x^2 + 13759414272 * x + 10176233472)⁻¹ * x ^ 5,
    ring_nf,
  rw h1,
  have h2 : 11466178560 * (-(143327232 * x ^ 2 * x * x) - 1433272320 * x * x + 13759414272 * x + 10176233472)⁻¹ * x * x * x = 11466178560 * (-(143327232 * x ^ 4) - 1433272320 * x^2 + 13759414272 * x + 10176233472)⁻¹ * x^3,
    ring_nf,
  rw h2,
  have h3 : 110075314176 * (-(143327232 * x ^ 2 * x * x) - 1433272320 * x * x + 13759414272 * x + 10176233472)⁻¹ * x * x = 110075314176 * (-(143327232 * x ^ 4) - 1433272320 * x^2 + 13759414272 * x + 10176233472)⁻¹ * x^2,
    ring_nf,
  rw h3,
  have h4 : 81409867776 * (-(143327232 * x ^ 2 * x * x) - 1433272320 * x * x + 13759414272 * x + 10176233472)⁻¹ * x = 81409867776 * (-(143327232 * x ^ 4) - 1433272320 * x^2 + 13759414272 * x + 10176233472)⁻¹ * x,
    ring_nf,
  rw h4,
  have h5 : 1146617856 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x ^ 5 +
      11466178560 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x ^ 3 -
    110075314176 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x ^ 2 -
  81409867776 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x = (1146617856 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x ^ 4 +
      11466178560 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x ^ 2 -
    110075314176 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x -
  81409867776 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹) * x,
    ring,
  rw h5,
  have h6: -(8*x) = (-8)*x,
    ring,
  rw h6,
  have hmain : 1146617856 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x ^ 4 +
             11466178560 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x ^ 2 -
           110075314176 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ * x -
         81409867776 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹ = -8,
    begin
    rw mul_comm (1146617856 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹) (x^4),
    rw mul_comm (11466178560 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹) (x^2),
    rw mul_comm (110075314176 * (-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472)⁻¹) x,
    repeat {rw inv_eq_one_div},
    repeat {rw mul_div},
    repeat {rw mul_one},
    rw div_add_div_same,
    repeat {rw div_sub_div_same},
    have h7 : x ^ 4 * 1146617856 + x ^ 2 * 11466178560 - x * 110075314176 - 81409867776 = (-8)*(-(143327232 * x ^ 4) - 1433272320 * x ^ 2 + 13759414272 * x + 10176233472),
      ring,
    rw [h7, ← mul_div, div_self, mul_one],
    linarith,
    end,
  rw hmain,
end

lemma big_eq_is_zero_step : (fun_h x)*(fun_k x) - (deriv fun_b x)*(fun_b x)*(fun_p x) = 0 :=
begin
  unfold fun_h,
  unfold fun_k,
  unfold fun_b,
  unfold fun_p,
  rw deriv_b,
  simp,
  ring,
end

lemma big_eq_is_zero : ((fun_h x)*(fun_k x) - (deriv fun_b x)*(fun_b x)*(fun_p x))*(fun_y x)/((fun_h x)^2-(fun_b x)^2*(fun_p x)) = 0 :=
begin
  rw [big_eq_is_zero_step, zero_mul, zero_div],
end

lemma big_eq_decomposed_step (hpos : 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) (hnotneg : x.fun_h - x.fun_b * x.fun_y ≠ 0) : ((fun_k x) + (deriv fun_b x)*(fun_y x))/((fun_h x)/(fun_y x) + (fun_b x)) = ((fun_h x)*(deriv fun_b x)*(fun_p x) - (fun_b x)*(fun_k x)*(fun_p x))/((fun_h x)^2-(fun_b x)^2*(fun_p x)) + ((fun_h x)*(fun_k x) - (deriv fun_b x)*(fun_b x)*(fun_p x))*(fun_y x)/((fun_h x)^2-(fun_b x)^2*(fun_p x)) :=
begin
  have hyz : (fun_y x)^2 = fun_p x,
    unfold fun_y,
    rw sq_sqrt,
    refl,
    linarith,
  rw div_add_div_same,
  have h1 : x.fun_h ^ 2 - x.fun_b ^ 2 * x.fun_p = (x.fun_h + x.fun_b * x.fun_y)*(x.fun_h - x.fun_b * x.fun_y),
    ring_nf,
    rw hyz,
  rw h1,
  have h2 : x.fun_h * deriv fun_b x * x.fun_p - x.fun_b * x.fun_k * x.fun_p + (x.fun_h * x.fun_k - deriv fun_b x * x.fun_b * x.fun_p) * x.fun_y = (x.fun_k * x.fun_y + (deriv fun_b x) * x.fun_p) * (x.fun_h - x.fun_b * x.fun_y),
    ring_nf,
    rw hyz,
    ring,
  rw [h2, ← div_mul_div_comm, div_self, mul_one],
  have h3 : x.fun_k * x.fun_y + deriv fun_b x * x.fun_p = (x.fun_k + (deriv fun_b x) * x.fun_y)*(x.fun_y),
    ring_nf,
    rw hyz,
    ring,
  rw h3,
  have h4 : x.fun_h / x.fun_y + x.fun_b = (x.fun_h + x.fun_b * x.fun_y)/x.fun_y,
    rw ← div_add_div_same,
    simp,
    rw [← mul_div, div_self],
    simp,
    unfold fun_y,
    rw sqrt_ne_zero,
    linarith,
    linarith,
  rw [h4, ← div_mul],
  ring,
  exact hnotneg,
end

lemma big_eq_decomposed (hpos : 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) (hnotneg : x.fun_h - x.fun_b * x.fun_y ≠ 0) : ((fun_k x) + (deriv fun_b x)*(fun_y x))/((fun_h x)/(fun_y x) + (fun_b x)) = -8*x :=
begin
  rw [big_eq_decomposed_step hpos hnotneg, big_eq_is_eq hpos, big_eq_is_zero],
  simp,
end

lemma big_eq_to_k_h (hpos : 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) (hnotneg : x.fun_h - x.fun_b * x.fun_y ≠ 0) : ((deriv fun_a x) * (fun_y x) + (deriv fun_y x) * (fun_a x) + (deriv fun_b x))/((fun_a x)*(fun_y x)+(fun_b x)) = ((fun_k x) + (deriv fun_b x)*(fun_y x))/((fun_h x)/(fun_y x) + (fun_b x)) * (1/(fun_y x)) :=
begin
  have hynotzero : fun_y x ≠ 0,
    unfold fun_y,
    rw sqrt_ne_zero,
    linarith,
    linarith,
  have hh : (fun_h x) = (fun_a x)*(fun_p x),
    unfold fun_h,
    unfold fun_a,
    unfold fun_p,
    ring,
  have hk : (fun_k x) = (deriv fun_a x)*(fun_p x) + (fun_a x)*(deriv fun_p x)/2,
    unfold fun_a,
    unfold fun_p,
    unfold fun_k,
    rw [deriv_a, deriv_p],
    ring,
  rw [hh, hk],
  have hy'z : deriv fun_y x = (deriv fun_p x)/(2*(fun_y x)),
    rw [deriv_y _ hpos, deriv_p],
    refl,
  have hzy : (fun_p x) / (fun_y x) = fun_y x,
    unfold fun_y,
    unfold fun_p,
    rw div_sqrt,
  rw [hy'z, ← mul_div x.fun_a x.fun_p x.fun_y, mul_comm _ (1 / x.fun_y)],
  rw [mul_div, mul_comm (1 / x.fun_y)],
  repeat {rw add_mul},
  rw [mul_one_div, ← mul_div (deriv fun_a x) x.fun_p x.fun_y],
  rw [hzy, div_mul_div_comm, mul_one_div],
  simp[hynotzero],
  ring,
end

lemma big_eq_if (hpos : 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) (hnotneg : x.fun_h - x.fun_b * x.fun_y ≠ 0) : ((deriv fun_a x) * (fun_y x) + (deriv fun_y x) * (fun_a x) + (deriv fun_b x))/((fun_a x)*(fun_y x)+(fun_b x)) = -8*x / (sqrt (x^4+10*x^2-96*x-71)) → ((deriv fun_a x) * (fun_y x) + (deriv fun_y x) * (fun_a x) + (deriv fun_b x))/(-8*((fun_a x)*(fun_y x)+(fun_b x))) = x / (sqrt (x^4+10*x^2-96*x-71)) :=
begin
  intro h,
  rw [← mul_div, mul_comm (-8 : ℝ)] at h,
  have h1 : (-8:ℝ) ≠ 0,
    simp,
  symmetry' at h,
  rw [← eq_div_iff_mul_eq h1, div_div, mul_comm _ (-8:ℝ)] at h,
  rw h,
end

lemma big_eq (hpos : 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) (hnotneg : x.fun_h - x.fun_b * x.fun_y ≠ 0) : ((deriv fun_a x) * (fun_y x) + (deriv fun_y x) * (fun_a x) + (deriv fun_b x))/(-8*((fun_a x)*(fun_y x)+(fun_b x))) = x / (sqrt (x^4+10*x^2-96*x-71)) :=
begin
  apply big_eq_if hpos hnotneg,
  rw [big_eq_to_k_h hpos hnotneg, big_eq_decomposed hpos hnotneg],
  unfold fun_y,
  ring,
end

lemma deriv_our_function (x : ℝ) (a : ℝ → ℝ) (y : ℝ → ℝ) (b : ℝ → ℝ) (hnotzero : (a x) *(y x)+(b x) ≠ 0) (haindiff : differentiable_at ℝ (λ (x : ℝ), a x) x) (hyindiff : differentiable_at ℝ (λ (x : ℝ), y x) x) (hbindiff : differentiable_at ℝ (λ (x : ℝ), b x) x) 
: deriv (λ (x : ℝ), log((a x) *(y x)+(b x))) x = ((deriv (a)*y + a*deriv (y)+deriv (b)) x) / ((a x) *(y x)+(b x)) :=
begin
  have hayindiff : differentiable_at ℝ (λ (x : ℝ), (a*y) x) x,
    exact differentiable_at.mul haindiff hyindiff,
  have hmaindiff : differentiable_at ℝ (λ (x : ℝ), a x * y x + b x) x,
    exact differentiable_at.add hayindiff hbindiff,
  rw deriv.log hmaindiff hnotzero,
  simp*,
end

lemma deriv_F (hpos1 : 0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) (hpos2 : 0 < x.fun_a * x.fun_y + x.fun_b) : deriv (λ (x : ℝ), -1/8 * log((fun_a x) * (fun_y x) + (fun_b x))) x = ((deriv fun_a x) * (fun_y x) + (deriv fun_y x) * (fun_a x) + (deriv fun_b x))/(-8*((fun_a x)*(fun_y x)+(fun_b x))) :=
begin
  have hadiff : differentiable_at ℝ (λ (x : ℝ), fun_a x) x,
    unfold fun_a,
    simp,
  have hbdiff : differentiable_at ℝ (λ (x : ℝ), fun_b x) x,
    unfold fun_b,
    simp,
  have hydiff : differentiable_at ℝ (λ (x : ℝ), fun_y x) x,
    unfold fun_y,
    apply differentiable_at.sqrt,
    simp,
    linarith,
  have haydiff : differentiable_at ℝ (λ (x : ℝ), (fun_a x) * (fun_y x)) x,
    exact differentiable_at.mul hadiff hydiff,
  have hmaindiff : differentiable_at ℝ (λ (x : ℝ), (fun_a x) * (fun_y x) + (fun_b x)) x,
    exact differentiable_at.add haydiff hbdiff,
  have hlogmaindiff : differentiable_at ℝ (λ (x : ℝ), log((fun_a x) * (fun_y x) + (fun_b x))) x,
    apply differentiable_at.log hmaindiff,
    simp,
    linarith,
  rw [deriv_const_mul _ hlogmaindiff, deriv_our_function _ _ _ _ _ hadiff hydiff hbdiff],
  simp,
  rw [div_mul_div_comm, neg_one_mul, div_neg],
  ring,
  linarith,
end

/- # Showing F is the elementary anti-derivative of f -/

lemma has_antideriv_F : has_antideriv_within (λ (x : ℝ), ((deriv fun_a x) * (fun_y x) + (deriv fun_y x) * (fun_a x) + (deriv fun_b x))/(-8*((fun_a x)*(fun_y x)+(fun_b x)))) (λ (x : ℝ), -1/8 * log((fun_a x) * (fun_y x) + (fun_b x))) {x | (0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) ∧ 0 < x.fun_a * x.fun_y + x.fun_b} :=
begin
  unfold has_antideriv_within,
  intros y hy,
  cases hy with hpos1 hpos2,
  have h : differentiable_at ℝ (λ (x : ℝ), (-1) / 8 * log (x.fun_a * x.fun_y + x.fun_b)) y,
    apply differentiable_at.const_mul,
    apply differentiable_at.log,
    apply differentiable_at.add,
    apply differentiable_at.mul,
    {unfold fun_a,
    simp},
    {unfold fun_y,
    apply differentiable_at.sqrt,
    simp,
    linarith},
    {unfold fun_b,
    simp},
    {linarith},
  convert differentiable_at.has_deriv_at h,
  rw deriv_F hpos1 hpos2,
end

lemma elementary_antideriv_F : is_elementary_within_anti_within (λ (x : ℝ), ((deriv fun_a x) * (fun_y x) + (deriv fun_y x) * (fun_a x) + (deriv fun_b x))/(-8*((fun_a x)*(fun_y x)+(fun_b x)))) {x | (0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) ∧ 0 < x.fun_a * x.fun_y + x.fun_b} :=
begin
  unfold is_elementary_within_anti_within,
  use [(λ (x : ℝ), -1/8 * log((fun_a x) * (fun_y x) + (fun_b x)))],
  split,
  exact is_elementary_within_F,
  exact has_antideriv_F,
end

lemma elementary_antideriv_f_is_F : is_elementary_within_anti_within (λ (x : ℝ), x / (x.fun_y)) {x | (0 < x.fun_p) ∧ 0 < x.fun_a * x.fun_y + x.fun_b ∧ x.fun_h - x.fun_b * x.fun_y ≠ 0} :=
begin
  have h : is_elementary_within_anti_within (λ (x : ℝ), ((deriv fun_a x) * (fun_y x) + (deriv fun_y x) * (fun_a x) + (deriv fun_b x))/(-8*((fun_a x)*(fun_y x)+(fun_b x)))) {x | (0 < x ^ 4 + 10 * x ^ 2 - 96 * x - 71) ∧ 0 < x.fun_a * x.fun_y + x.fun_b ∧ x.fun_h - x.fun_b * x.fun_y ≠ 0} → is_elementary_within_anti_within (λ (x : ℝ), x / x.fun_y) {x : ℝ | 0 < x.fun_p ∧ 0 < x.fun_a * x.fun_y + x.fun_b ∧ x.fun_h - x.fun_b * x.fun_y ≠ 0} ,
    intro h1,
    unfold is_elementary_within_anti_within at *,
    cases h1 with f h1,
    use f,
    unfold fun_p,
    cases h1 with h1 h2,
    split,
    exact h1,
    unfold has_antideriv_within at *,
    intro x,
    specialize h2 x,
    simp at ⊢ h2,
    intros hx1 hx2 hx3,
    simp[hx1, hx2, hx3] at h2,
    unfold fun_y,
    rw ← big_eq,
    convert h2,
    ring,
    linarith,
    simp[hx3],
  apply h,
  have h1 : {x : ℝ | 0 < x.fun_p ∧ 0 < x.fun_a * x.fun_y + x.fun_b ∧ x.fun_h - x.fun_b * x.fun_y ≠ 0} ⊆ {x : ℝ | 0 < x.fun_p ∧ 0 < x.fun_a * x.fun_y + x.fun_b},
    simp,
    intros a ha1 ha2 ha3,
    simp[ha1, ha2],
  apply is_elementary_within_anti_within.subset (λ (x : ℝ), x / x.fun_y) _ _ h1,
  exact elementary_antideriv_F,
end

/- ## Showing systems are equivalent ## -/

def system_eleven_equations (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) := -((d_1*e_4)/64) = 0 ∧ -((d_1*e_3)/128) = 0 ∧ 1/64*(d_2*e_3 + 3*d_3*e_4) = 0 ∧ 1/128*(-128*d_0 + 4*d_2*e_2 + 9*d_3*e_3 + 16*d_4*e_4) = 0 ∧
1/64*(-63*d_1 + 6*d_3*e_2 + 10*d_4*e_3 + 15*d_5*e_4) = 0 ∧ 1/128*(-120*d_2 + 24*d_4*e_2 + 35*d_5*e_3 + 48*d_6*e_4) = 0 ∧ 1/64*(-55*d_3 + 20*d_5*e_2 + 27*d_6*e_3 + 35*d_7*e_4) = 0 ∧
1/128*(-96*d_4 + 60*d_6*e_2 + 77*d_7*e_3 - 96*e_4) = 0 ∧ 1/64*(-39*d_5 + 42*d_7*e_2 - 52*e_3) = 0 ∧ -(7/16)*(d_6 + 2*e_2) = 0 ∧ -((15*d_7)/64) = 0
def system_two_equations_with_d (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ):= (100*e_4 + 71*e_2^2=0) ∧ (70*e_3^2 + 972*e_2*e_4+45*e_2^3=0) ∧ d_0 = -(e_2 ^ 4 / 128) - 83 * e_2 * e_3 ^ 2 / 720 - 3 * e_2 ^ 2 * e_4 / 16 - e_4 ^ 2 / 8 ∧ d_1 = -(1 / 210 * e_3 * (71 * e_2 ^ 2 + 100 * e_4)) ∧ d_2 = -e_2 ^ 3 / 4 - 7 * e_3 ^ 2 / 18 - e_2 * e_4 ∧ d_3 = -(22 * e_2 * e_3 / 15) ∧ d_4 = -(5 * e_2 ^ 2 / 4) - e_4 ∧ d_5 = -(4 / 3 * e_3) ∧ d_6 = -(2 * e_2) ∧ d_7 = 0
def system_two_equations_without_d (e_2:ℝ) (e_3:ℝ) (e_4:ℝ):= (100*e_4 + 71*e_2^2=0) ∧ (70*e_3^2 + 972*e_2*e_4+45*e_2^3=0)
def system_three_equations (e_2:ℝ) (e_3:ℝ) (e_4:ℝ) (e_2_prime:ℝ) (e_3_prime:ℝ) (e_4_prime:ℝ) (k:ℝ):= (e_2_prime=e_2*k^2) ∧ (e_4_prime=e_4*k^4) ∧ (e_3_prime=e_3*k^3)

/- # Showing system_eleven_equations holds iff system_two_equations holds. -/

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

lemma system_two_iff_system_eleven (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero3 : e_3 ≠ 0) (hnotzero4 : e_4 ≠ 0) : system_eleven_equations e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 ↔ system_two_equations_with_d e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 :=
begin
  unfold system_two_equations_with_d,
  unfold system_eleven_equations,
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

lemma system_two_notzero (e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7 : ℝ) (hnotzero3 : e_3 ≠ 0) (h : system_two_equations_with_d e_2 e_3 e_4 d_0 d_1 d_2 d_3 d_4 d_5 d_6 d_7) : e_4 ≠ 0 :=
begin
  unfold system_two_equations_with_d at h,
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

/- # Showing system_two_equations holds iff system_three_equations holds -/

lemma system_two_iff_system_three (e_2:ℝ) (e_3:ℝ) (e_4:ℝ) (e_2_prime:ℝ) (e_3_prime:ℝ) (e_4_prime:ℝ) 
(k:ℝ) (hgtzero2: 0<k) (hrelation: e_2_prime = k^2*e_2) (hltzeroe3prime: 0>e_3_prime) (hltzeroe3: 0>e_3)
(ha1: 100*e_4 + 71*e_2^2=0) (ha2: 70*e_3^2 + 972*e_2*e_4+45*e_2^3=0)
(hnotzeroe2: e_2≠0) (hnotzeroe3: e_3≠0) (hnotzeroe4: e_4≠0) 
(hnotzeroe2prime: e_2_prime≠0) (hnotzeroe3prime: e_3_prime≠0) (hnotzeroe4prime: e_4_prime≠0):
system_two_equations_without_d (e_2_prime) (e_3_prime) (e_4_prime) ↔ system_three_equations (e_2) (e_3) (e_4) (e_2_prime) (e_3_prime) (e_4_prime) (k):=
begin
  unfold system_two_equations_without_d,
  unfold system_three_equations,
  split,
  {
    intro h,
    cases h with hsystem1 hsystem2,
    split,
    {simp[hrelation],
    ring},
    have hrelation4 : e_4_prime = e_4 * k ^ 4,
      rw add_eq_zero_iff_eq_neg at ha1 hsystem1,
      rw mul_comm (100 : ℝ) at ha1 hsystem1,
      rw ← eq_div_iff at ha1 hsystem1,
      rw hrelation at hsystem1,
      rw [ha1, hsystem1],
      ring,
      linarith,
      linarith,
    split,
    {exact hrelation4},
    {rw add_assoc at ha2 hsystem2,
      rw add_eq_zero_iff_eq_neg at ha2 hsystem2,
      rw mul_comm (70 : ℝ) at ha2 hsystem2,
      rw [hrelation, hrelation4] at hsystem2,
      have h : e_3_prime ^ 2 * 70 = k^6 * (e_3 ^ 2 * 70),
        rw [ha2, hsystem2],
        ring,
      rw ← mul_assoc at h,
      simp[mul_right_cancel_iff] at h,
      rw or_iff_left at h,
      have h1 : k ^ 6 * e_3 ^ 2 = (k^3*e_3)^2,
        ring,
      rw h1 at h,
      rw ← neg_sq at h,
      rw ← neg_sq (k ^ 3 * e_3) at h,
      rw sq_eq_sq at h,
      simp at h,
      rw h,
      ring,
      linarith,
      simp,
      have h3 : 0 < k^3,
        simp,
        linarith,
      have h4 : e_3 ≤ 0,
        linarith,
      exact linarith.mul_nonpos h4 h3,
      norm_num},
  },
  {
    intro hsystem,
    cases hsystem with hsystem1 hsystem,
    cases hsystem with hsystem2 hsystem3,
    rw [hsystem1, hsystem2, hsystem3],
    split,
    {have h1 : 100 * (e_4 * k ^ 4) + 71 * (e_2 * k ^ 2) ^ 2 = k ^ 4 * (100 * e_4 + 71 * e_2 ^ 2),
      ring,
    rw h1,
    rw ha1,
    simp},
    {have h1 : 70 * (e_3 * k ^ 3) ^ 2 + 972 * (e_2 * k ^ 2) * (e_4 * k ^ 4) + 45 * (e_2 * k ^ 2) ^ 3 = k ^ 6 * (70 * e_3 ^ 2 + 972 * e_2 * e_4 + 45 * e_2 ^ 3),
      ring,
    rw h1,
    rw ha2,
    simp,}
  },
end

/- # Showing there exist coefficients for which system_two_equations holds -/

def antideriv_exist (e_2:ℝ) (e_3:ℝ) (e_4:ℝ) (k:ℝ):= system_three_equations (e_2:ℝ) (e_3:ℝ) (e_4:ℝ) (10:ℝ) ((-96):ℝ) ((-71):ℝ) (k:ℝ)

lemma antideriv_exist_ (e_2:ℝ) (e_3:ℝ) (e_4:ℝ) 
(k:ℝ) (hgtzero2: 0<k) (hrelation: (10:ℝ) = k^2*e_2)
(ha1: 100*e_4 + 71*e_2^2=0) (ha2: 70*e_3^2 + 972*e_2*e_4+45*e_2^3=0)
(hnotzeroe2: e_2≠0) (hnotzeroe3: e_3≠0) (hnotzeroe4: e_4≠0) (hltzeroe3: 0>e_3):
system_three_equations (e_2) (e_3) (e_4) (10:ℝ) ((-96):ℝ) ((-71):ℝ) (k):=
begin 
  unfold system_three_equations,
  have h : 10 = e_2 * k ^ 2,
    rw hrelation,
    ring,
  split,
  {exact h},
  have h1 : e_2 = 10/(k^2),
    rw h,
    have h2 : k^2 ≠ 0,
      apply pow_ne_zero,
      linarith,
    simp[h2],
  have h2 : e_4 = -71 / (k^4),
    rw h1 at ha1,
    simp at ha1,
    rw ← pow_mul at ha1,
    rw add_eq_zero_iff_eq_neg at ha1,
    have h3 : 100 * e_4 = -(71 * (10 ^ 2 / k ^ (2 * 2))) ↔ e_4 = -(71 * (10 ^ 2 / k ^ (2 * 2)))/100,
      rw mul_comm (100 : ℝ),
      rw ← eq_div_iff,
      linarith,
    rw h3 at ha1,
    rw ha1,
    ring,
  split,
  {rw h2,
  have h4 : k^4 ≠ 0,
    apply pow_ne_zero,
    linarith,
  simp[h4]},
  simp[h2, h1, ← pow_mul] at ha2,
  rw add_assoc at ha2,
  rw add_eq_zero_iff_eq_neg at ha2,
  rw mul_comm (70 : ℝ) at ha2,
  rw ← eq_div_iff at ha2,
  simp at ha2,
  have h3 : (-(45 * (10 ^ 3 / k ^ (2 * 3))) + -(972 * (10 / k ^ 2) * ((-71) / k ^ 4))) / 70 = (9216)/(k^6),
    norm_num,
    ring_nf,
    repeat {rw inv_eq_one_div},
    rw mul_assoc,
    nth_rewrite 1 div_mul_div_comm,
    rw ← pow_add,
    ring,
  rw h3 at ha2,
  have h4 : (9216) / k ^ 6 = (96 / k ^ 3)^2,
    simp,
    ring_nf,
  rw h4 at ha2,
  rw ← neg_sq at ha2,
  rw sq_eq_sq at ha2,
  rw neg_eq_iff_neg_eq at ha2,
  rw ← ha2,
  have hk3notzero : k^3 ≠ 0,
    apply pow_ne_zero,
    linarith,
  simp[hk3notzero],
  linarith,
  have hk3pos : 0 ≤ k^3,
    apply pow_nonneg,
    linarith,
  apply div_nonneg _ hk3pos,
  norm_num,
  norm_num,
end

/- ## Further research ## -/

def fun_A (x:ℝ) : ℝ := 52*x^4 + 92*x^3 + 30*x^2 -22*x - 11
def fun_B (x:ℝ) : ℝ := 112*x^6 + 360*x^5 + 624*x^4 + 772*x^3 + 612*x^2 + 258*x + 43
def fun_Y (x:ℝ) : ℝ := sqrt (4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1)
def fun_Z (x:ℝ) : ℝ := 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1

lemma deriv_Y (x : ℝ) (h : 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1 ≠ 0)
(hnotzeroinsidey: 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1 ≠ 0): 
deriv fun_Y x =  (deriv fun_Z x) / (2*(fun_Y x)) :=
begin
  have h1 : fun_Y = (λ (x : ℝ), sqrt (4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1)),
    refl,
  rw [h1,deriv_sqrt],
   have h3 : fun_Z = (λ (x : ℝ), 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1),
    refl,
  rw h3,
  simp only [differentiable_at.add, differentiable_at.mul, differentiable_at_const, differentiable_at.pow, differentiable_at_id'],
  simp only [ne.def],
  exact hnotzeroinsidey,
end

lemma fun_Z_eq_fun_Y_sq (x : ℝ) (h: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1):  
(fun_Z x = fun_Y x ^2 ):=
begin 
  unfold fun_Z,
  unfold fun_Y,
  rw sq_sqrt,
  exact h,
end

lemma deriv_sub (x : ℝ) (g : ℝ → ℝ) (h : ℝ → ℝ) 
(hxdiff : differentiable_at ℝ (λ x, x) x)
(hgdiff : differentiable_at ℝ (λ x, g x) x) 
(hhdiff : differentiable_at ℝ (λ x, h x) x): 
deriv (λ (x : ℝ), (g x)-(h x)) x = (deriv (g) -deriv (h) ) x :=
begin
  apply deriv_sub (hgdiff) (hhdiff),
end


lemma factors_sq_equal (x : ℝ):  
(fun_Z x) * (x*(fun_A x) + fun_B x - (1/6)*(x+1)*(deriv fun_B x))^2 = ((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x)+((fun_A x)*(deriv fun_Z x)/2))-x*(fun_B x)-(fun_A x)*(fun_Z x))^2:=
begin
  have h1 : fun_A = (λ (x : ℝ), 52*x^4 + 92*x^3 + 30*x^2 -22*x - 11),
    refl,
  have h2 : fun_B = (λ (x : ℝ), 112*x^6 + 360*x^5 + 624*x^4 + 772*x^3 + 612*x^2 + 258*x + 43),
    refl,
  have h3 : fun_Z = (λ (x : ℝ), 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1),
    refl,
  rw [h1,h2,h3],
  simp,
  ring_nf,
end

lemma factors_equal (x : ℝ) (h: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1):  
(fun_Y x) * (x*(fun_A x) + fun_B x - (1/6)*(x+1)*(deriv fun_B x)) = ((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x)+((fun_A x)*(deriv fun_Z x)/2))-x*(fun_B x)-(fun_A x)*(fun_Z x)):=
begin
  have h1 : fun_A = (λ (x : ℝ), 52*x^4 + 92*x^3 + 30*x^2 -22*x - 11),
    refl,
  have h2 : fun_B = (λ (x : ℝ), 112*x^6 + 360*x^5 + 624*x^4 + 772*x^3 + 612*x^2 + 258*x + 43),
    refl,
  have h3 : fun_Y = (λ (x : ℝ), sqrt (4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1)),
    refl,
  have h4 : fun_Z = (λ (x : ℝ), 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1),
    refl,
  have h5:  (fun_Z x) * (x*(fun_A x) + fun_B x - (1/6)*(x+1)*(deriv fun_B x))^2 = ((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x)+((fun_A x)*(deriv fun_Z x)/2))-x*(fun_B x)-(fun_A x)*(fun_Z x))^2,
    exact factors_sq_equal x,
  have h: (fun_Z x) * (x*(fun_A x) + fun_B x - (1/6)*(x+1)*(deriv fun_B x))^2 = 0,
    rw [h1,h2,h4],
    simp,
    ring_nf,
    right,
    norm_num,
  rw h at h5,
  symmetry' at h5,
  rw sq_eq_zero_iff at h5, 
  rw [h5,h1,h2,h3],
  simp,
  ring_nf,
  right,
  norm_num,
end

lemma expanding_factors_add_equal (x : ℝ) (hgtzero: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1):  
x*(fun_A x)*(fun_Y x)+x*(fun_B x) + (fun_A x)*(fun_Z x) + (fun_B x)*(fun_Y x) = (1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)) + (1/6)*(x+1)*(deriv fun_B x)*(fun_Y x) :=
begin
  have h:  (fun_Y x) * (x*(fun_A x) + fun_B x - (1/6)*(x+1)*(deriv fun_B x)) = ((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x)+((fun_A x)*(deriv fun_Z x)/2))-x*(fun_B x)-(fun_A x)*(fun_Z x)),
    exact factors_equal x hgtzero,
  have h1:  (fun_Y x) * (x*(fun_A x) + fun_B x - (1/6)*(x+1)*(deriv fun_B x)) =(fun_Y x) * (x*(fun_A x)) + (fun_Y x) *(fun_B x) - (fun_Y x) * (1/6)*(x+1)*(deriv fun_B x),
      unfold fun_A,
      unfold fun_B,
      unfold fun_Y,
      simp,
      ring,
  rw [h1,sub_eq_add_neg] at h,
  rw add_comm (x.fun_Y * (x * x.fun_A) + x.fun_Y * x.fun_B) (-(x.fun_Y * (1 / 6) * (x + 1) * deriv fun_B x)) at h,
  rw [neg_add_eq_iff_eq_add,sub_eq_add_neg,← add_assoc,← add_neg_eq_iff_eq_add] at h,
  rw sub_eq_add_neg (1 / 6 * (x + 1) * (deriv fun_A x * x.fun_Z + x.fun_A * deriv fun_Z x / 2))  (x * x.fun_B) at h,
  rw [← add_assoc,← add_neg_eq_iff_eq_add,neg_neg,neg_neg] at h,
  have h2: x.fun_Y * (x * x.fun_A) + x.fun_Y * x.fun_B + x.fun_A * x.fun_Z + x * x.fun_B = x * x.fun_A * x.fun_Y + x * x.fun_B + x.fun_A * x.fun_Z + x.fun_B * x.fun_Y,
    ring,
  have h3: x.fun_Y * (1 / 6) * (x + 1) * deriv fun_B x + 1 / 6 * (x + 1) * (deriv fun_A x * x.fun_Z + x.fun_A * deriv fun_Z x / 2) = 1 / 6 * (x + 1) * (deriv fun_A x * x.fun_Z + x.fun_A * deriv fun_Z x / 2) + 1 / 6 * (x + 1) * deriv fun_B x * x.fun_Y,
    ring,
  rw [h2,h3] at h,
  exact h,
end

lemma factoring_equal (x : ℝ) (hgtzero: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1):  
(x+ fun_Y x)*((fun_A x)*(fun_Y x)+fun_B x) = (1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)+ (deriv fun_B x)*(fun_Y x))  :=
begin
  have h:   x*(fun_A x)*(fun_Y x)+x*(fun_B x) + (fun_A x)*(fun_Z x) + (fun_B x)*(fun_Y x) = (1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)) + (1/6)*(x+1)*(deriv fun_B x)*(fun_Y x) ,
    exact expanding_factors_add_equal x hgtzero,
  have h1: x*(fun_A x)*(fun_Y x)+x*(fun_B x) + (fun_A x)*(fun_Z x) + (fun_B x)*(fun_Y x) = (x+ fun_Y x)*((fun_A x)*(fun_Y x)+fun_B x),
    ring_nf,
    rw ← fun_Z_eq_fun_Y_sq,
    exact hgtzero,
  rw h1 at h,
  have h2:  (1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)+ (deriv fun_B x)*(fun_Y x)) = (1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)) + (1/6)*(x+1)*(deriv fun_B x)*(fun_Y x) ,
    ring_nf,
  rw ← h2 at h,
  exact h,
end

lemma division_equal (x : ℝ) (hgtzero: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1)
(hnotzeroden : (fun_A x) *(fun_Y x)+(fun_B x) ≠ 0) :  
(x+ fun_Y x)= ((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)+ (deriv fun_B x)*(fun_Y x)))/((fun_A x)*(fun_Y x)+fun_B x)  :=
begin
  have h:   (x+ fun_Y x)*((fun_A x)*(fun_Y x)+fun_B x) = (1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)+ (deriv fun_B x)*(fun_Y x)),
    exact factoring_equal x hgtzero,
  symmetry' at h,
  rw ←  div_eq_iff hnotzeroden at h,
  symmetry' at h,
  exact h,
end

lemma add_equal (x : ℝ) (hgtzero: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1)
(hnotzeroden : (fun_A x) *(fun_Y x)+(fun_B x) ≠ 0) :  
x= ((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)+ (deriv fun_B x)*(fun_Y x)))/((fun_A x)*(fun_Y x)+fun_B x) + (- fun_Y x ):=
begin
  have h:   (x+ fun_Y x)= ((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)+ (deriv fun_B x)*(fun_Y x)))/((fun_A x)*(fun_Y x)+fun_B x),
    exact division_equal x hgtzero hnotzeroden,
  rw ← eq_add_neg_iff_add_eq at h,
  exact h,
end

lemma mul_Y_equal (x : ℝ)  (hgtzero: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1)
(hnotzeroinsidey: 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1 ≠ 0) :  
((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)+ (deriv fun_B x)*(fun_Y x)))/((fun_A x)*(fun_Y x)+fun_B x)= (1/6)*(x+1)*(fun_Y x)*(((deriv fun_A x)*(fun_Y x) + ((fun_A x)*(deriv fun_Z x)/(2*(fun_Y x)))+ (deriv fun_B x))/((fun_A x)*(fun_Y x)+fun_B x)):=
begin
  have h: deriv fun_A x * x.fun_Z + x.fun_A * deriv fun_Z x / 2 + deriv fun_B x * x.fun_Y = (x.fun_Y)* (deriv fun_A x * x.fun_Y + (x.fun_A) *(deriv fun_Z x) / (2*(fun_Y x)) + deriv fun_B x),
    rw [fun_Z_eq_fun_Y_sq,mul_add,mul_add,← mul_div_assoc],
    rw ←  mul_assoc (x.fun_Y) (x.fun_A) (deriv fun_Z x),
    rw mul_comm (x.fun_Y) (x.fun_A),
    rw mul_assoc (x.fun_A) (x.fun_Y) (deriv fun_Z x),
    rw mul_comm (x.fun_Y) (deriv fun_Z x),
    rw ← mul_assoc (x.fun_A) (deriv fun_Z x) (x.fun_Y),
    rw mul_div_assoc (x.fun_A * deriv fun_Z x),
    rw mul_comm (2) (x.fun_Y),
    rw div_mul_eq_div_mul_one_div (x.fun_Y) (x.fun_Y) (2),
    have hnotzero: x.fun_Y≠ 0,
      unfold fun_Y,
      rw sqrt_ne_zero,
      exact hnotzeroinsidey,
      exact hgtzero,
    rw [div_self hnotzero,one_mul,← mul_div_assoc (x.fun_A * deriv fun_Z x),mul_one],
    ring_nf,
  exact hgtzero,
  rw [h,mul_div_assoc,mul_div_assoc,mul_assoc (1 / 6 * (x + 1))],
end

lemma divide_by_x_plus_1_mul_Y (x : ℝ) (hgtzero: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1) (hnotzeroden : (fun_A x) *(fun_Y x)+(fun_B x) ≠ 0)
(hnotzeroinsidey: 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1 ≠ 0) (hnotzeroxplus1 : x+1 ≠ 0) :  
x/((x+1)*(fun_Y x))=(1/6)*(((deriv fun_A x)*(fun_Y x) + ((fun_A x)*(deriv fun_Z x)/(2*(fun_Y x)))+ (deriv fun_B x))/((fun_A x)*(fun_Y x)+fun_B x)) + (- (1/(x+1))):=
begin
  have h: x= ((1/6)*(x+1)*((deriv fun_A x)*(fun_Z x) + ((fun_A x)*(deriv fun_Z x)/2)+ (deriv fun_B x)*(fun_Y x)))/((fun_A x)*(fun_Y x)+fun_B x) + (- fun_Y x ),
    exact add_equal x hgtzero hnotzeroden,
  rw [mul_Y_equal x,← one_mul (-x.fun_Y)] at h,
  have hnotzero: (x+1)≠0,
    exact hnotzeroxplus1,
  nth_rewrite 4 ← div_self hnotzero at h,
  rw [div_mul_eq_mul_div (x + 1),mul_assoc (1 / 6) (x + 1) (x.fun_Y),mul_comm (1 / 6) ((x + 1) * x.fun_Y)] at h,
  have h2: (x + 1) * -x.fun_Y = (x + 1) * (x.fun_Y) * (-1),
    ring_nf,
  rw [h2,mul_div_assoc ((x + 1) * x.fun_Y),mul_assoc,← mul_add] at h,
  have hnotzeroy: x.fun_Y ≠ 0,
    unfold fun_Y,
    rw sqrt_ne_zero,
    exact hnotzeroinsidey,
    exact hgtzero,
  have h3: (x + 1) * x.fun_Y ≠ 0,
    apply mul_ne_zero hnotzeroxplus1 hnotzeroy,
  rw [mul_comm ((x + 1) * x.fun_Y),←  div_eq_iff h3,neg_div] at h,
  exact h,
  exact hgtzero,
  exact hnotzeroinsidey,
end

lemma simplify_our_expression (x : ℝ) (hgtzero: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1) (hnotzeroden : (fun_A x) *(fun_Y x)+(fun_B x) ≠ 0)
(hnotzeroinsidey: 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1 ≠ 0)  (hnotzeroxplus1 : x+1 ≠ 0):  
x/((x+1)*(fun_Y x))=(1/6)*(((deriv fun_A x)*(fun_Y x) + ((fun_A x)*(deriv fun_Y x))+ (deriv fun_B x))/((fun_A x)*(fun_Y x)+fun_B x)) + (- (1/(x+1))):=
begin
  have h: x/((x+1)*(fun_Y x))=(1/6)*(((deriv fun_A x)*(fun_Y x) + ((fun_A x)*(deriv fun_Z x)/(2*(fun_Y x)))+ (deriv fun_B x))/((fun_A x)*(fun_Y x)+fun_B x)) + (- (1/(x+1))),
    exact divide_by_x_plus_1_mul_Y x hgtzero hnotzeroden hnotzeroinsidey hnotzeroxplus1,
  rw deriv_Y x hnotzeroinsidey,
  rw mul_div_assoc at h,
  exact h,
  exact hnotzeroinsidey,
end

lemma deriv_log_x_plus_1 (x : ℝ) (hnotzero: x+1 ≠ 0): deriv (λ (x : ℝ), real.log(x+1)) x = 1/(x+1) :=
begin
  rw [deriv.comp,real.deriv_log,div_eq_mul_inv,mul_comm],
  simp only [deriv_add_const', deriv_id''],
  simp only [differentiable_at_log_iff, ne.def],
  exact hnotzero,
  simp only [differentiable_at_add_const_iff, differentiable_at_id'],
end

lemma deriv_alternative_function (x : ℝ) (a : ℝ → ℝ) (y : ℝ → ℝ) (b : ℝ → ℝ) 
(hnotzeroden : (a x) *(y x)+(b x) ≠ 0) (hnotzeroxplus1 : x+1 ≠ 0) 
(hadiff : differentiable_at ℝ (λ x, (a) x) x)
(hydiff : differentiable_at ℝ (λ x, (y) x) x)
(hbdiff : differentiable_at ℝ (λ x, b x) x): 
deriv (λ (x : ℝ), (1/6)*real.log((a x) *(y x)+(b x)) - real.log(x+1)) x = (1/6)*((deriv (a)*y + a*deriv (y)+deriv (b) ) x) / ((a x) *(y x)+(b x) )  - 1 /(1+x):=
begin
  rw [deriv_sub,pi.sub_apply,deriv_const_mul,deriv_our_function],
  simp only [one_div, pi.add_apply, pi.mul_apply],
  rw deriv_log_x_plus_1,
  simp only [one_div],
  rw [mul_div_assoc,add_comm (1) (x)],
  exact hnotzeroxplus1,
  exact hnotzeroden,
  exact hadiff,
  exact hydiff,
  exact hbdiff,
  apply differentiable_at.log,
  apply differentiable_at.add,
  apply differentiable_at.mul,
  exact hadiff,
  exact hydiff,
  exact hbdiff,
  exact hnotzeroden,
  exact differentiable_at_id,
  apply differentiable_at.const_mul,
  apply differentiable_at.log,
  apply differentiable_at.add,
  apply differentiable_at.mul,
  exact hadiff,
  exact hydiff,
  exact hbdiff,
  exact hnotzeroden,
  apply differentiable_at.log,
  simp only [differentiable_at_add_const_iff, differentiable_at_id'],
  exact hnotzeroxplus1,
end

lemma deriv_alt_function_w_simps (x : ℝ)  (hgtzero: 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1) (hnotzeroden : (fun_A x) *(fun_Y x)+(fun_B x) ≠ 0)
(hnotzeroinsidey: 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1 ≠ 0)  (hnotzeroxplus1 : x+1 ≠ 0)
(hadiff : differentiable_at ℝ (λ x, (fun_A) x) x)
(hydiff : differentiable_at ℝ (λ x, (fun_Y) x) x)
(hbdiff : differentiable_at ℝ (λ x, (fun_B) x) x): 
deriv (λ (x : ℝ), (1/6)*real.log((fun_A x) *(fun_Y x)+(fun_B x)) - real.log(x+1)) x = x/ ((1+x)*(fun_Y x)):=
begin
  rw deriv_alternative_function,
  have h1: (1/6)*(((deriv fun_A x)*(fun_Y x) + ((fun_A x)*(deriv fun_Y x))+ (deriv fun_B x))/((fun_A x)*(fun_Y x)+fun_B x)) = 1 / 6 * ((deriv (λ (x : ℝ), x.fun_A) * λ (x : ℝ), x.fun_Y) + (λ (x : ℝ), x.fun_A) * deriv (λ (x : ℝ), x.fun_Y) + deriv (λ (x : ℝ), x.fun_B)) x / (x.fun_A * x.fun_Y + x.fun_B),
    simp,
    rw mul_div_assoc,
  rw [←  h1,sub_eq_add_neg,add_comm (1) (x),←  simplify_our_expression x hgtzero hnotzeroden hnotzeroinsidey hnotzeroxplus1],
  exact hnotzeroden,
  exact hnotzeroxplus1,
  exact hadiff,
  exact hydiff,
  exact hbdiff,
end

lemma antideriv_alt_function_within : has_antideriv_within (λ (x : ℝ), x/ ((1+x)*(fun_Y x))) (λ x,  (1/6)*real.log((fun_A x) *(fun_Y x)+(fun_B x))- real.log(x+1)) {x| (fun_A x) *(fun_Y x)+(fun_B x) ≠ 0 ∧ x+1 ≠ 0 ∧ 4*x^4 + 8*x^3 + 12*x^2 + 8*x + 1 ≠ 0 ∧ 0 ≤ 4 * x ^ 4 + 8 * x ^ 3 + 12 * x ^ 2 + 8 * x + 1} :=
begin
  unfold has_antideriv_within,
  intro x,
  intro hset,
  have h: differentiable_at ℝ (λ x,  (1/6)*real.log((fun_A x) *(fun_Y x)+(fun_B x)) - real.log(x+1)) x,
    apply differentiable_at.sub,
    apply differentiable_at.const_mul,
    apply differentiable_at.log,
    unfold fun_A,
    unfold fun_B,
    have hy: differentiable_at ℝ (λ x,  fun_Y x) x,
      apply differentiable_at.sqrt,
      simp only [differentiable_at.add, differentiable_at.mul, differentiable_at_const, differentiable_at.pow, differentiable_at_id'],
      cases hset with hset1 hset2,
      cases hset2 with hset2 hset3,
      cases hset3 with hset3 hset4,
      exact hset3,
    apply differentiable_at.add,
    apply differentiable_at.mul,
    simp only [differentiable_at.sub, differentiable_at.add, differentiable_at.mul, differentiable_at_const, differentiable_at.pow,
  differentiable_at_id'],
    exact hy,
    simp only [differentiable_at.add, differentiable_at.mul, differentiable_at_const, differentiable_at.pow, differentiable_at_id'],
    cases hset with hset1 hset2,
    exact hset1,
    apply differentiable_at.comp,
    apply differentiable_at.log,
    apply differentiable_at_id,
    cases hset with hset1 hset2,
    cases hset2 with hset2 hset3,
    exact hset2,
    simp only [differentiable_at_add_const_iff, differentiable_at_id'], 
  have h1:= differentiable_at.has_deriv_at h,
  convert h1,
  have h2:   x/ ((1+x)*(fun_Y x)) = deriv (λ (x : ℝ), (1/6)*real.log((fun_A x) *(fun_Y x)+(fun_B x)) - real.log(x+1)) x ,
    symmetry,
    cases hset with hset1 hset2,
    cases hset2 with hset2 hset3,
    cases hset3 with hset3 hset4,
    apply deriv_alt_function_w_simps x hset4 hset1 hset3 hset2,
  unfold fun_A,
  simp only [differentiable_at.sub, differentiable_at.add, differentiable_at.mul, differentiable_at_const, differentiable_at.pow,
  differentiable_at_id'],
  unfold fun_Y,
  apply differentiable_at.sqrt,
  simp only [differentiable_at.add, differentiable_at.mul, differentiable_at_const, differentiable_at.pow, differentiable_at_id'],
  exact hset3,
  unfold fun_B,
  simp only [differentiable_at.add, differentiable_at.mul, differentiable_at_const, differentiable_at.pow, differentiable_at_id'],
  exact h2,
end



end real

/- !!!RENAME THINGS!!! -/