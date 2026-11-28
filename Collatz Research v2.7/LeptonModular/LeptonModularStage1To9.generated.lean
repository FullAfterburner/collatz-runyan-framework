import Mathlib

/-! Algebraic tests for the minimal modular A4 texture.
The modular-form relation is a hypothesis, not a formalized modular-form theorem.
No empirical measurements or physical identifications are axiomatized. -/
namespace CollatzRunyan.LeptonSpectral

section Texture
variable {R : Type*} [CommRing R]

def texture (x y z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![2*x, -z, -y; -z, 2*y, -x; -y, -x, 2*z]

def tm1 (x y z l : R) : Prop :=
  4*x + y + z = 2*l ∧ x - 2*y - 2*z = -l

theorem texture_tm1_components (x y z : R) :
    (texture x y z).mulVec ![2, -1, -1] =
      ![4*x+y+z, x-2*y-2*z, x-2*y-2*z] := by
  funext i
  fin_cases i <;> simp [texture, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem trace_product (x y z u v w : R) :
    Matrix.trace (texture u v w * texture x y z) = 6*(u*x+v*y+w*z) := by
  simp [Matrix.trace, Matrix.mul_apply, texture, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 0 in
theorem trace_product_square (x y z u v w : R) :
    Matrix.trace ((texture u v w * texture x y z) *
      (texture u v w * texture x y z)) = 18*(u*x+v*y+w*z)^2 := by
  simp [Matrix.trace, Matrix.mul_apply, texture, Fin.sum_univ_succ] <;> ring

theorem trace_rigidity (x y z u v w : R) :
    Matrix.trace (texture u v w * texture x y z)^2 =
      2 * Matrix.trace ((texture u v w * texture x y z) *
        (texture u v w * texture x y z)) := by
  rw [trace_product, trace_product_square]
  ring

end Texture

-- TM1 and the level-three modular relation (explicit hypotheses).
theorem tm1_linear {x y z l : ℂ} (h : tm1 x y z l) : y+z=2*x := by
  rcases h with ⟨h1,h2⟩
  linear_combination (-1/3 : ℂ)*h1 - (2/3 : ℂ)*h2

theorem tm1_modular_quadratic {x y z l : ℂ}
    (h : tm1 x y z l) (hm : y^2+2*x*z=0) : (y-x)^2+3*x^2=0 := by
  have hz : z=2*x-y := by linear_combination (tm1_linear h)
  rw [hz] at hm
  linear_combination hm

theorem tm1_real_zero {x y z l : ℝ} (h : tm1 x y z l)
    (hm : y^2+2*x*z=0) : x=0 ∧ y=0 ∧ z=0 := by
  rcases h with ⟨h1,h2⟩
  have hz : z=2*x-y := by linarith
  rw [hz] at hm
  have hq : (y-x)^2+3*x^2=0 := by linear_combination hm
  have hx2 : x^2=0 := by nlinarith [sq_nonneg (y-x), sq_nonneg x]
  have hx : x=0 := by
    rcases mul_eq_zero.mp (show x*x=0 by simpa [pow_two] using hx2) with hh | hh <;> exact hh
  have hy2 : y^2=0 := by simpa [hx] using hq
  have hy : y=0 := by
    rcases mul_eq_zero.mp (show y*y=0 by simpa [pow_two] using hy2) with hh | hh <;> exact hh
  exact ⟨hx,hy,by linarith⟩

theorem tm1_complex_nonzero_first {x y z l : ℂ} (h : tm1 x y z l)
    (hm : y^2+2*x*z=0) (hn : x≠0 ∨ y≠0 ∨ z≠0) : x≠0 := by
  intro hx
  have hy2 : y^2=0 := by simpa [hx] using hm
  have hy : y=0 := by
    rcases mul_eq_zero.mp (show y*y=0 by simpa [pow_two] using hy2) with hh | hh <;> exact hh
  have hz : z=0 := by simpa [hx,hy] using tm1_linear h
  simp [hx,hy,hz] at hn

theorem tm1_complex_projective {x y z l : ℂ} (h : tm1 x y z l)
    (hm : y^2+2*x*z=0) (hx : x≠0) : ((y-x)/x)^2 = -3 := by
  have hq := tm1_modular_quadratic h hm
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hx)]
  linear_combination hq

-- These are scalar spectral consequences. The two moment identities below
-- follow from the trace theorem when a unitary singular-value decomposition
-- is supplied. The SVD-to-trace bridge itself is not formalized in this file.
theorem heron_factor (a b c : ℝ) :
    (a^2+b^2+c^2)^2-2*(a^4+b^4+c^4) =
      (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c) := by ring

theorem ordered_mass_sum_rule {a b c : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h : (a^2+b^2+c^2)^2=2*(a^4+b^4+c^4)) : c=a+b := by
  have hp : (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c)=0 := by
    rw [← heron_factor]
    rw [h]
    ring
  rcases mul_eq_zero.mp hp with h123 | h4
  · rcases mul_eq_zero.mp h123 with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2 <;> linarith
    · linarith
  · linarith

theorem spectral_moments_imply_sum {a b c q : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : a^2+b^2+c^2=6*q) (h2 : a^4+b^4+c^4=18*q^2) : c=a+b := by
  apply ordered_mass_sum_rule ha hab hbc
  rw [h1,h2]
  ring

theorem sum_rule_atmospheric_identity {a b c : ℝ} (h : c=a+b) :
    c^2-a^2 = b^2+2*a*b := by rw [h]; ring

theorem sum_rule_ratio_bound {a b c : ℝ} (ha : 0 < a)
    (hr : 4*a < b) (hs : c=a+b) :
    c^2-a^2 < 2*(b^2-a^2) := by
  rw [hs]
  have h1 : 0 < b-4*a := by linarith
  have h2 : 0 < b+2*a := by linarith
  nlinarith [mul_pos h1 h2, mul_pos ha ha]

theorem inverse_sum_rule_ratio_bound {a b c : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (h : 1/a=1/b+1/c) : b ≤ 2*a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hh := h
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc] at hh
  by_contra! hn
  have hp : 0 < (b-2*a)*c := mul_pos (by linarith) hc
  have hp2 : 0 ≤ a*(c-b) := mul_nonneg (le_of_lt ha) (by linarith)
  nlinarith

-- Exact scalar invariants of the original two-dimensional arithmetic ansatz.
theorem arithmetic_coefficients (s : ℝ) (hs : s^2=26) :
    (3*s-10)*(3*s+10)=134 ∧
    (3*s+10)^2-(3*s-10)^2=120*s := by
  constructor
  · linear_combination 9*hs
  · ring

theorem arithmetic_ratio_gt_four (s : ℝ) (hs : s^2=26) (hp : 0 ≤ s) :
    0 < 3*s-10 ∧ 4*(3*s-10)<3*s+10 := by
  have hlo : 5 < s := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ 5-s by linarith) (show 0 ≤ 5+s by linarith)]
  have hhi : s < 11/2 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ s-11/2 by linarith) (show 0 ≤ s+11/2 by linarith)]
  constructor <;> linarith

theorem arithmetic_ratio_forces_gt_four (s a b : ℝ)
    (hs : s^2=26) (hp : 0 ≤ s) (hm : 0 < a)
    (hr : (3*s-10)*b=(3*s+10)*a) : 4*a < b := by
  obtain ⟨hpos,hgt⟩ := arithmetic_ratio_gt_four s hs hp
  have hba : 4*a < b := by
    by_contra! hn
    have hh := mul_le_mul_of_nonneg_left hn (le_of_lt hpos)
    nlinarith [mul_pos (show 0 < (3*s+10)-4*(3*s-10) by linarith) hm]
  exact hba

theorem arithmetic_ratio_excludes_direct_sum_rule (s a b c : ℝ)
    (hs : s^2=26) (hp : 0 ≤ s) (hm : 0 < a)
    (hr : (3*s-10)*b=(3*s+10)*a) (hc : c=a+b) :
    c^2-a^2 < 2*(b^2-a^2) := by
  exact sum_rule_ratio_bound hm (arithmetic_ratio_forces_gt_four s a b hs hp hm hr) hc

-- Necessary triangle-inequality condition for the twin modular S4 inverse
-- mass rule (King-Zhou, Phys. Rev. D 101, 015001, eq. 51).
-- u and v stand for magnitudes of the two complex coefficients, each ≤ 2.
-- Clearing positive denominators gives b*c ≤ a*(u*c+v*b).
theorem bounded_inverse_rule_excluded {a b c u v : ℝ}
    (ha : 0 < a) (hr : 4*a < b) (hbc : b ≤ c)
    (hu : u ≤ 2) (hv : v ≤ 2) : a*(u*c+v*b) < b*c := by
  have hb : 0 < b := by linarith
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hsum : u*c+v*b ≤ 4*c := by
    linarith [mul_le_mul_of_nonneg_right hu (le_of_lt hc),
      mul_le_mul_of_nonneg_right hv (le_of_lt hb)]
  have hup := mul_le_mul_of_nonneg_left hsum (le_of_lt ha)
  have hlt := mul_lt_mul_of_pos_right hr hc
  nlinarith

theorem arithmetic_ratio_excludes_bounded_inverse_rule (s a b c u v : ℝ)
    (hs : s^2=26) (hp : 0 ≤ s) (ha : 0 < a)
    (hr : (3*s-10)*b=(3*s+10)*a) (hbc : b ≤ c)
    (hu : u ≤ 2) (hv : v ≤ 2) : ¬ b*c ≤ a*(u*c+v*b) := by
  exact not_le.mpr (bounded_inverse_rule_excluded ha
    (arithmetic_ratio_forces_gt_four s a b hs hp ha hr) hbc hu hv)

-- Normalized TM1 special case: one mass is 3 and the squared masses sum to 54.
-- The analytic SVD argument supplies these hypotheses, rather than axioms.
theorem normalized_tm1_degenerate {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hs : c=a+b) (h1 : a^2+b^2+c^2=54)
    (hthree : a=3 ∨ b=3 ∨ c=3) : a=3 ∧ b=3 ∧ c=6 := by
  rcases hthree with ha3 | hb3 | hc3
  · subst a
    rw [hs] at h1
    have hz : (b-3)*(b+6)=0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · exact ⟨rfl, by linarith, by linarith⟩
    · exfalso; linarith
  · subst b
    rw [hs] at h1
    have hz : (a-3)*(a+6)=0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · exact ⟨by linarith, rfl, by linarith⟩
    · exfalso; linarith
  · have hb0 : 0 ≤ b := le_trans ha hab
    have ha3 : a ≤ 3 := by linarith
    have hb3 : b ≤ 3 := by linarith
    exfalso
    nlinarith [mul_nonneg (show 0 ≤ 3-a by linarith) (show 0 ≤ 3+a by linarith),
      mul_nonneg (show 0 ≤ 3-b by linarith) (show 0 ≤ 3+b by linarith)]

theorem juno_central_ratio_gt_two : (2:ℚ)*(7388/100) < 2509 := by norm_num

#print axioms texture_tm1_components
#print axioms trace_product
#print axioms trace_product_square
#print axioms trace_rigidity
#print axioms tm1_linear
#print axioms tm1_modular_quadratic
#print axioms tm1_real_zero
#print axioms tm1_complex_nonzero_first
#print axioms tm1_complex_projective
#print axioms heron_factor
#print axioms ordered_mass_sum_rule
#print axioms spectral_moments_imply_sum
#print axioms sum_rule_atmospheric_identity
#print axioms sum_rule_ratio_bound
#print axioms inverse_sum_rule_ratio_bound
#print axioms arithmetic_coefficients
#print axioms arithmetic_ratio_gt_four
#print axioms arithmetic_ratio_forces_gt_four
#print axioms arithmetic_ratio_excludes_direct_sum_rule
#print axioms bounded_inverse_rule_excluded
#print axioms arithmetic_ratio_excludes_bounded_inverse_rule
#print axioms normalized_tm1_degenerate
#print axioms juno_central_ratio_gt_two

end CollatzRunyan.LeptonSpectral

/-! Stage 2: algebraic consequences only. Compile the combined Stage1To2 file.
No modular-form existence, vacuum dynamics, or empirical physical law assumed. -/
namespace CollatzRunyan.LeptonSpectral

section TraceBridge
variable {R : Type*} [CommRing R]
def stage2_diag (a b c : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a,0,0;0,b,0;0,0,c]

theorem stage2_trace_cycle (A B : Matrix (Fin 3) (Fin 3) R) :
    Matrix.trace (A*B) = Matrix.trace (B*A) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem stage2_trace_similarity (Q D U : Matrix (Fin 3) (Fin 3) R)
    (h : U*Q=1) : Matrix.trace (Q*D*U)=Matrix.trace D := by
  calc
    Matrix.trace (Q*D*U) = Matrix.trace (U*(Q*D)) := stage2_trace_cycle _ _
    _ = Matrix.trace ((U*Q)*D) := by rw [mul_assoc]
    _ = Matrix.trace D := by rw [h, one_mul]

theorem stage2_square_similarity (Q D U : Matrix (Fin 3) (Fin 3) R)
    (h : U*Q=1) : (Q*D*U)*(Q*D*U)=Q*(D*D)*U := by
  calc
    (Q*D*U)*(Q*D*U)=Q*D*(U*Q)*D*U := by simp only [mul_assoc]
    _=Q*(D*D)*U := by rw [h, mul_one, mul_assoc Q D D]

theorem stage2_diag_trace (a b c : R) :
    Matrix.trace (stage2_diag a b c)=a+b+c := by
  simp [stage2_diag, Matrix.trace, Fin.sum_univ_succ] <;> ring

theorem stage2_diag_square_trace (a b c : R) :
    Matrix.trace (stage2_diag a b c * stage2_diag a b c)=a^2+b^2+c^2 := by
  simp [stage2_diag, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem stage2_similarity_moments (H Q U : Matrix (Fin 3) (Fin 3) R)
    (a b c : R) (h : U*Q=1) (hd : H=Q*stage2_diag a b c*U) :
    Matrix.trace H=a+b+c ∧ Matrix.trace (H*H)=a^2+b^2+c^2 := by
  constructor
  · rw [hd, stage2_trace_similarity _ _ _ h, stage2_diag_trace]
  · rw [hd, stage2_square_similarity _ _ _ h, stage2_trace_similarity _ _ _ h,
      stage2_diag_square_trace]
end TraceBridge

-- A supplied similarity diagonalization of the texture product closes the
-- trace-to-ordered-mass algebra. Existence of an SVD is not asserted here.
theorem stage2_texture_spectral_sum (x y z u v w : ℂ)
    (Q U : Matrix (Fin 3) (Fin 3) ℂ) (a b c : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (h : U*Q=1)
    (hd : texture u v w * texture x y z =
      Q*stage2_diag ((a:ℂ)^2) ((b:ℂ)^2) ((c:ℂ)^2)*U) : c=a+b := by
  obtain ⟨h1,h2⟩ := stage2_similarity_moments _ Q U ((a:ℂ)^2) ((b:ℂ)^2) ((c:ℂ)^2) h hd
  have hr := trace_rigidity x y z u v w
  rw [h1,h2] at hr
  have hc : ((a:ℂ)^2+(b:ℂ)^2+(c:ℂ)^2)^2 =
      2*((a:ℂ)^4+(b:ℂ)^4+(c:ℂ)^4) := by
    calc
      _ = 2*(((a:ℂ)^2)^2+((b:ℂ)^2)^2+((c:ℂ)^2)^2) := hr
      _ = _ := by ring
  have hreal : (a^2+b^2+c^2)^2=2*(a^4+b^4+c^4) := by exact_mod_cast hc
  exact ordered_mass_sum_rule ha hab hbc hreal

section Modular
variable {K : Type*} [Field K] [CharZero K]

def stage2_p (t : K) := 1+t^3/2
def stage2_q (t : K) := t^4/4-t
def stage2_r (t : K) := 3*t^2/2

theorem stage2_weight4_factor (t : K) :
    4*(stage2_q t+stage2_r t-2*stage2_p t)=
      (t^2-2*t-2)*(t^2-2*t+4) := by
  unfold stage2_p stage2_q stage2_r
  ring

theorem stage2_weight4_branches (t : K)
    (h : stage2_q t+stage2_r t=2*stage2_p t) :
    (t-1)^2=3 ∨ (t-1)^2= -3 := by
  have hp := stage2_weight4_factor t
  have hz : (t^2-2*t-2)*(t^2-2*t+4)=0 := by rw [← hp, h]; ring
  rcases mul_eq_zero.mp hz with hh | hh
  · left; linear_combination hh
  · right; linear_combination hh

theorem stage2_weight4_real_branch_equal (t : K) (h : (t-1)^2=3) :
    stage2_p t=stage2_q t ∧ stage2_q t=stage2_r t := by
  unfold stage2_p stage2_q stage2_r
  constructor
  · linear_combination (-(t^2)/4-1/2)*h
  · linear_combination (t^2/4+t/2)*h

theorem stage2_weight4_complex_branch (t : K) (h : (t-1)^2= -3) :
    stage2_q t-stage2_r t=2*(t-1)*stage2_p t := by
  unfold stage2_p stage2_q stage2_r
  linear_combination (-(3*t^2)/4-t/2+1/2)*h

-- Component equations for the three-singlet texture acting on (2,-1,-1).
def stage2_texture (p q r u v w : K) : Matrix (Fin 3) (Fin 3) K :=
  !![2*p+u,-r+w,-q+v; -r+w,2*q+v,-p+u; -q+v,-p+u,2*r+w]

theorem stage2_texture_components (p q r u v w : K) :
    (stage2_texture p q r u v w).mulVec ![2,-1,-1] =
      ![4*p+2*u+r+q-v-w, p-u-2*q-2*r-v+2*w,
        p-u-2*q-2*r+2*v-w] := by
  funext i
  fin_cases i <;> simp [stage2_texture, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem stage2_three_singlet_tm1 (p q r u v w l : K)
    (h1 : 4*p+2*u+r+q-v-w=2*l)
    (h2 : p-u-2*q-2*r-v+2*w= -l)
    (h3 : p-u-2*q-2*r+2*v-w= -l) : v=w ∧ q+r=2*p := by
  constructor
  · linear_combination (1/3:K)*h3-(1/3:K)*h2
  · linear_combination (-1/3:K)*h1+(-1/3:K)*h2+(-1/3:K)*h3

theorem stage2_two_singlet_tm1 (p q r u v l : K)
    (h1 : 4*p+2*u+r+q-v=2*l)
    (h2 : p-u-2*q-2*r-v= -l)
    (h3 : p-u-2*q-2*r+2*v= -l) : v=0 ∧ q+r=2*p := by
  apply stage2_three_singlet_tm1 p q r u v 0 l
  · simpa using h1
  · simpa using h2
  · simpa using h3

theorem stage2_weight8_projective (t A B : K)
    (h : A*stage2_q t+B*stage2_p t+(A*stage2_r t+B*stage2_q t)=
      2*(A*stage2_p t+B*stage2_r t)) :
    (t-1)*(A*stage2_q t+B*stage2_p t-(A*stage2_r t+B*stage2_q t)) =
      (t^2-2*t-2)*(A*stage2_p t+B*stage2_r t) := by
  unfold stage2_p stage2_q stage2_r at *
  linear_combination (-t-1)*h

theorem stage2_discriminant (t : K) :
    (1-t^3)^3-(1+(5/2)*t^3-t^6/8)^2 = -t^3*(t^3+8)^3/64 := by ring

-- Denominator-cleared j-invariance, including at algebraic poles.
theorem stage2_j_involution_polynomial (t : K) :
    ((t+2)^3-(t-1)^3)^3 * t^3 * (t^3+8)^3 * (t-1)^3 =
      (t^3-1)^3 * (t+2)^3 * ((t+2)^3+8*(t-1)^3)^3 := by ring
end Modular

-- Real coordinates for the complex projective circle. The nonzero real
-- part condition selects the two off-axis roots, not the other branch.
theorem stage2_projective_circle (x y R : ℝ)
    (hx : x ≠ 0) (h1 : x^2-y^2+R*y-3=0) (h2 : x*(2*y-R)=0) :
    x^2+y^2=3 := by
  have hy : 2*y-R=0 := (mul_eq_zero.mp h2).resolve_left hx
  have hyy : R=2*y := by linarith
  rw [hyy] at h1
  nlinarith

theorem stage2_circle_involution (t u : ℂ) (ht : t≠1)
    (h : (t-1)*(u-1)=3) : (t+2)/(t-1)=u := by
  apply (div_eq_iff (sub_ne_zero.mpr ht)).2
  linear_combination -h

section Orientation

theorem stage2_rank_one_det (a b g x y : ℝ) :
    (a+g*x^2-a)*(b+g*y^2-a)-(g*x*y)^2=g*x^2*(b-a) := by ring

theorem stage2_rank_one_no_mixing (a b g x y : ℝ) (hab : b≠a)
    (h : (a+g*x^2-a)*(b+g*y^2-a)-(g*x*y)^2=0) : g*x*y=0 := by
  rw [stage2_rank_one_det] at h
  have hba : b-a ≠ 0 := sub_ne_zero.mpr hab
  have hgx : g*x^2=0 := (mul_eq_zero.mp h).resolve_right hba
  rcases mul_eq_zero.mp hgx with hg | hx
  · simp [hg]
  · have hx0 : x=0 := by
      rcases mul_eq_zero.mp (show x*x=0 by simpa [pow_two] using hx) with hh | hh <;> exact hh
    simp [hx0]

-- c and s denote cos(phi) and sin(phi), respectively.
def stage2_dx (a d s : ℝ) := (d-a)*s^2
def stage2_dy (a d c s : ℝ) := (d-a)*s*c
def stage2_dz (a b d c : ℝ) := a-b+(d-a)*c^2

theorem stage2_update_trace (a b d c s : ℝ) (h : c^2+s^2=1) :
    stage2_dx a d s+stage2_dz a b d c=d-b := by
  unfold stage2_dx stage2_dz
  linear_combination (d-a)*h

theorem stage2_update_det (a b d c s : ℝ) :
    stage2_dx a d s*stage2_dz a b d c-(stage2_dy a d c s)^2 =
      -(b-a)*(d-a)*s^2 := by
  unfold stage2_dx stage2_dy stage2_dz
  ring

theorem stage2_update_indefinite_det (a b d c s : ℝ)
    (hg : 0 < (b-a)*(d-a)) (hs : s≠0) :
    stage2_dx a d s*stage2_dz a b d c-(stage2_dy a d c s)^2 < 0 := by
  rw [stage2_update_det]
  have hp : 0 < s^2 := by positivity
  nlinarith [mul_pos hg hp]

theorem stage2_update_not_rank_one (a b d c s : ℝ)
    (hg : 0 < (b-a)*(d-a)) (hs : s≠0) :
    ¬ stage2_dx a d s*stage2_dz a b d c=(stage2_dy a d c s)^2 := by
  intro h
  have hh := stage2_update_indefinite_det a b d c s hg hs
  rw [h, sub_self] at hh
  exact (lt_irrefl 0) hh

theorem stage2_opposite_update_eigenvalues (x y : ℝ) (h : x*y<0) :
    (x<0 ∧ 0<y) ∨ (y<0 ∧ 0<x) := by
  by_cases hx : x < 0
  · left
    refine ⟨hx, ?_⟩
    by_contra! hy
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos (le_of_lt hx) hy)) h
  · right
    have hx0 : 0 ≤ x := le_of_not_gt hx
    have hy : y < 0 := by
      by_contra! hy
      exact (not_lt_of_ge (mul_nonneg hx0 hy)) h
    refine ⟨hy, ?_⟩
    by_contra! hh
    exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hh (le_of_lt hy))) h

theorem stage2_orientation_block_square (R : Type*) [CommRing R] :
    (!![0,0,0;0,0,1;0,1,0] : Matrix (Fin 3) (Fin 3) R) *
      !![0,0,0;0,0,1;0,1,0] = !![0,0,0;0,1,0;0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem stage2_axis_overlap (s t : ℝ) (hs : s^2=1/3) (ht : t^2=1/2) :
    (2*s*t)^2=2/3 := by
  calc
    (2*s*t)^2=4*s^2*t^2 := by ring
    _=2/3 := by rw [hs,ht]; norm_num

theorem stage2_orientation_reactor (D beta c s : ℝ)
    (h : c^2+s^2=1) (hb : beta=D*s*c) :
    beta^2=D^2*(3*(s^2/3))*(1-3*(s^2/3)) := by
  rw [hb]
  linear_combination D^2*s^2*h

theorem stage2_orientation_bound (c s : ℝ) (h : c^2+s^2=1) : s*c ≤ 1/2 := by
  nlinarith [sq_nonneg (c-s)]

theorem stage2_jarlskog_polynomial (D beta J c s : ℝ)
    (hb : beta=D*s*c) (hJ : 54*J^2=(s*c)^2) :
    54*D^2*J^2=beta^2 := by
  rw [hb]
  linear_combination D^2*hJ

theorem stage2_universal_coupling_obstruction (mu tau z : ℝ)
    (hm : 0 < mu) (ht : 3*mu^2 < tau^2) (hz : z ≤ 1/2) :
    (tau^2-mu^2)/(tau^2+mu^2) ≠ z := by
  have hp : 0 < tau^2+mu^2 := by positivity
  intro h
  have hh := (div_eq_iff (ne_of_gt hp)).mp h
  have hb := mul_le_mul_of_nonneg_right hz (le_of_lt hp)
  nlinarith

end Orientation

#print axioms stage2_trace_cycle
#print axioms stage2_trace_similarity
#print axioms stage2_square_similarity
#print axioms stage2_diag_trace
#print axioms stage2_diag_square_trace
#print axioms stage2_similarity_moments
#print axioms stage2_texture_spectral_sum
#print axioms stage2_weight4_factor
#print axioms stage2_weight4_branches
#print axioms stage2_weight4_real_branch_equal
#print axioms stage2_weight4_complex_branch
#print axioms stage2_texture_components
#print axioms stage2_three_singlet_tm1
#print axioms stage2_two_singlet_tm1
#print axioms stage2_weight8_projective
#print axioms stage2_discriminant
#print axioms stage2_j_involution_polynomial
#print axioms stage2_projective_circle
#print axioms stage2_circle_involution
#print axioms stage2_rank_one_det
#print axioms stage2_rank_one_no_mixing
#print axioms stage2_update_trace
#print axioms stage2_update_det
#print axioms stage2_update_indefinite_det
#print axioms stage2_update_not_rank_one
#print axioms stage2_opposite_update_eigenvalues
#print axioms stage2_orientation_block_square
#print axioms stage2_axis_overlap
#print axioms stage2_orientation_reactor
#print axioms stage2_orientation_bound
#print axioms stage2_jarlskog_polynomial
#print axioms stage2_universal_coupling_obstruction

end CollatzRunyan.LeptonSpectral

/-! Stage 3: two-channel geometry, kinetic normalization, and spectral rigidity.
All mass interpretations and kinetic choices remain hypotheses. The scalar
coordinates c,s and their normalization are supplied, not inferred from data.
Compile the cumulative generated source, not this fragment. -/
namespace CollatzRunyan.LeptonSpectral

section Frame

-- Unnormalized channel outer product in the u,v basis.
def stage3_projector (x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x^2,x*y;x*y,y^2]

theorem stage3_frame_sum (x y : ℝ) :
    stage3_projector x y + stage3_projector x (-y) =
      !![2*x^2,0;0,2*y^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stage3_projector] <;> ring

theorem stage3_projector_square (x y : ℝ) (h : x^2+y^2=1) :
    stage3_projector x y * stage3_projector x y = stage3_projector x y := by
  have hxx : x^2*x^2+(x*y)*(x*y)=x^2 := by
    linear_combination x^2*h
  have hxy : x^2*(x*y)+(x*y)*y^2=x*y := by
    linear_combination (x*y)*h
  have hyx : (x*y)*x^2+y^2*(x*y)=x*y := by
    linear_combination (x*y)*h
  have hyy : (x*y)*(x*y)+y^2*y^2=y^2 := by
    linear_combination y^2*h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage3_projector, Matrix.mul_apply, Fin.sum_univ_succ, hxx, hxy, hyx, hyy]

theorem stage3_channel_overlap (x y : ℝ) (h : x^2+y^2=1) :
    (x^2-y^2)^2=1-4*x^2*y^2 := by
  linear_combination (x^2+y^2+1)*h

-- Coordinate squares of the frame-weighted normalized channels.
theorem stage3_frame_refinement (x y : ℝ) (hx : x^2=2/3) (hy : y^2=1/3) :
    (2*x^2*x^2)/(2*x^2*x^2+2*y^2*y^2)=4/5 ∧
    (2*y^2*y^2)/(2*x^2*x^2+2*y^2*y^2)=1/5 := by
  rw [hx,hy]
  norm_num

theorem stage3_original_overlap (x y : ℝ) (hx : x^2=2/3) (hy : y^2=1/3) :
    (x^2-y^2)^2=1/9 := by rw [hx,hy]; norm_num

theorem stage3_refined_overlap (x y : ℝ) (hx : x^2=4/5) (hy : y^2=1/5) :
    (x^2-y^2)^2=9/25 := by rw [hx,hy]; norm_num

theorem stage3_whitened_overlap (x y : ℝ) (hx : x^2=1/2) (hy : y^2=1/2) :
    x^2-y^2=0 := by rw [hx,hy]; ring

theorem stage3_frame_power_step (x y : ℝ) (hx : x ≠ 0) :
    (y/(2*x))^2=(y/x)^2/4 := by
  have hmul : y / x * x = y :=
    ((div_eq_iff hx).mp (show y / x = y / x from rfl)).symm
  have hden : (2 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx
  have hdiv : y / (2*x) = (y/x)/2 := by
    apply (div_eq_iff hden).2
    calc
      y = (y/x)*x := hmul.symm
      _ = ((y/x)/2)*(2*x) := by ring
  rw [hdiv]
  ring

-- K proportional to Q^-1, with the common overall factor removed.
def stage3_kinetic (R : Type*) [Field R] : Matrix (Fin 2) (Fin 2) R :=
  !![1/2,0;0,1]

def stage3_stretch (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![r,0;0,1]

theorem stage3_kinetic_canonical (r : ℝ) (hr : r^2=2) :
    stage3_stretch r * stage3_kinetic ℝ * stage3_stretch r = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage3_stretch, stage3_kinetic, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
    nlinarith [hr]

-- Congruence of the entire raw mass block, not just its correction.
theorem stage3_stretch_block (r a b c : ℝ) :
    stage3_stretch r * !![a,c;c,b] * stage3_stretch r =
      !![r^2*a,r*c;r*c,b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage3_stretch, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring


-- Full inverse frame metric Q^-1, not just its rescaled form.
noncomputable def stage3_full_kinetic : Matrix (Fin 2) (Fin 2) ℝ := !![3/4,0;0,3/2]

def stage3_full_stretch (r t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![r,0;0,t]

theorem stage3_full_metric_canonical (r t : ℝ) (hr : r^2=4/3) (ht : t^2=2/3) :
    stage3_full_stretch r t * stage3_full_kinetic * stage3_full_stretch r t =
      !![1,0;0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage3_full_stretch,stage3_full_kinetic,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    nlinarith [hr,ht]

theorem stage3_full_mass_congruence (r t a b c : ℝ) :
    stage3_full_stretch r t * !![a,c;c,b] * stage3_full_stretch r t =
      !![r^2*a,r*t*c;r*t*c,t^2*b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage3_full_stretch,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem stage3_raw_compensation (r t a b : ℝ) (hr : r^2=4/3) (ht : t^2=2/3) :
    stage3_full_stretch r t * !![3*a/4,0;0,3*b/2] * stage3_full_stretch r t =
      !![a,0;0,b] := by
  rw [stage3_full_mass_congruence,hr,ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end Frame

section Channel

-- Component formulas for gp P+ - gm P-; x,y are normalized coordinates.
def stage3_x (x gp gm : ℝ) := x^2*(gp-gm)
def stage3_y (x y gp gm : ℝ) := x*y*(gp+gm)
def stage3_z (y gp gm : ℝ) := y^2*(gp-gm)

theorem stage3_channel_trace (x y gp gm : ℝ) (h : x^2+y^2=1) :
    stage3_x x gp gm+stage3_z y gp gm=gp-gm := by
  unfold stage3_x stage3_z
  linear_combination (gp-gm)*h

theorem stage3_channel_det (x y gp gm : ℝ) :
    stage3_x x gp gm*stage3_z y gp gm-(stage3_y x y gp gm)^2 =
      -4*x^2*y^2*gp*gm := by
  unfold stage3_x stage3_y stage3_z
  ring

theorem stage3_channel_indefinite (x y gp gm : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hp : 0 < gp) (hm : 0 < gm) :
    stage3_x x gp gm*stage3_z y gp gm-(stage3_y x y gp gm)^2 < 0 := by
  rw [stage3_channel_det]
  have h : 0 < 4*x^2*y^2*gp*gm := by positivity
  nlinarith

theorem stage3_channel_ratio (x y k gp gm : ℝ) (h : y^2=k*x^2) :
    stage3_z y gp gm=k*stage3_x x gp gm := by
  unfold stage3_x stage3_z
  linear_combination (gp-gm)*h

theorem stage3_third_relation (a b d c s k : ℝ) (hcs : c^2+s^2=1)
    (h : stage2_dz a b d c=k*stage2_dx a d s) :
    (d-a)*(1-(1+k)*s^2)=b-a := by
  unfold stage2_dx stage2_dz at h
  linear_combination h-(d-a)*hcs

theorem stage3_third_formula (a b d z k : ℝ)
    (h : (d-a)*(1-(1+k)*z)=b-a) (hn : 1-(1+k)*z ≠ 0) :
    d=a+(b-a)/(1-(1+k)*z) := by
  have hh := (eq_div_iff hn).2 h
  linarith

theorem stage3_fixed_original (a b d r : ℝ)
    (h : (d-a)*(1-(1+1/2)*(2-r)/4)=b-a) :
    (d-a)*(2+3*r)=8*(b-a) := by
  linear_combination 8*h

theorem stage3_fixed_refined (a b d r : ℝ)
    (h : (d-a)*(1-(1+1/4)*(2-r)/4)=b-a) :
    (d-a)*(6+5*r)=16*(b-a) := by
  linear_combination 16*h

theorem stage3_inverse_geometry (a b d z k : ℝ)
    (h : (d-a)*(1-(1+k)*z)=b-a) (hn : (d-a)*z ≠ 0) :
    k=(d-b)/((d-a)*z)-1 := by
  have hh : (1+k)*((d-a)*z)=d-b := by linear_combination -h
  have hq := (eq_div_iff hn).2 hh
  linarith

-- Equal strengths make the update traceless, so the third eigenvalue
-- cannot shift if the solar eigenvalue remains fixed.
theorem stage3_equal_strength_no_shift (a b d c s x y g : ℝ)
    (hcs : c^2+s^2=1) (hx : stage2_dx a d s=stage3_x x g g)
    (hz : stage2_dz a b d c=stage3_z y g g) : d=b := by
  have ht := stage2_update_trace a b d c s hcs
  rw [hx,hz] at ht
  simp [stage3_x,stage3_z] at ht
  linarith

theorem stage3_equal_strength_no_rotation (a b d c s x y g : ℝ)
    (hcs : c^2+s^2=1) (hab : b ≠ a)
    (hx : stage2_dx a d s=stage3_x x g g)
    (hz : stage2_dz a b d c=stage3_z y g g) : s=0 := by
  have hd := stage3_equal_strength_no_shift a b d c s x y g hcs hx hz
  rw [hd] at hx
  have hzero : (b-a)*s^2=0 := by
    simpa only [stage2_dx,stage3_x,sub_self,mul_zero] using hx
  have hba : b-a ≠ 0 := sub_ne_zero.mpr hab
  have hs : s^2=0 := (mul_eq_zero.mp hzero).resolve_left hba
  nlinarith

-- If the difference of the strengths is positive, both are positive iff
-- the sum exceeds the difference. The next theorem gives the geometric test.
theorem stage3_positive_strengths (gp gm : ℝ) (h : 0 < gp-gm) :
    (0 < gp ∧ 0 < gm) ↔ gp-gm < gp+gm := by
  constructor
  · intro hh; linarith [hh.2]
  · intro hh; constructor <;> linarith

theorem stage3_positive_geometry (gp gm r s c : ℝ)
    (hd : 0 < gp-gm) (hrs : 0 < r*s)
    (h : (gp+gm)*(r*s)=(gp-gm)*c) :
    (0 < gp ∧ 0 < gm) ↔ r*s < c := by
  rw [stage3_positive_strengths gp gm hd]
  constructor
  · intro hh
    have hm := mul_lt_mul_of_pos_right hh hrs
    rw [h] at hm
    by_contra! hbad
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left hbad (le_of_lt hd))) hm
  · intro hh
    have hm := mul_lt_mul_of_pos_left hh hd
    rw [← h] at hm
    by_contra! hbad
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right hbad (le_of_lt hrs))) hm

-- For positive sine and cosine, r*s<c is equivalent to k*tan^2(phi)<1
-- when r^2=k. No trigonometric or measured-angle premise is required.
theorem stage3_squared_geometry (r s c k : ℝ) (hrs : 0 < r*s)
    (hc : 0 < c) (hk : r^2=k) :
    r*s<c ↔ k*s^2<c^2 := by
  have hh : (r*s)^2=k*s^2 := by rw [mul_pow,hk]
  constructor
  · intro h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < c+r*s by linarith)
    nlinarith
  · intro h
    by_contra! hn
    have hp := mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ r*s+c by linarith)
    nlinarith

-- With 0<h<1 the matched negative parity branch has greater magnitude
-- than the positive branch, provided the latter is positive.
theorem stage3_parity_gap (a b dp dn h : ℝ)
    (ha : 0 < a) (hh : 0 < h) (h1 : h<1) (hp : 0 < dp)
    (ep : (dp-a)*h=b-a) (en : (dn-a)*h= -b-a) : dp < -dn := by
  have he : (dp+dn)*h=2*a*(h-1) := by linear_combination ep+en
  have hn : 2*a*(h-1)<0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hz : (dp+dn)*h<0 := by rw [he]; exact hn
  have hs : dp+dn<0 := by
    by_contra! hbad
    exact (not_lt_of_ge (mul_nonneg hbad (le_of_lt hh))) hz
  linarith

-- Scale independence as a denominator-cleared identity, valid even when
-- a zero scale would prevent forming the actual quotient.
theorem stage3_scale_independent (m a b c : ℝ) :
    ((m*b)^2-(m*c)^2)*(a^2-c^2)=
      ((m*a)^2-(m*c)^2)*(b^2-c^2) := by ring

-- An affine reactor relation R=R0+R1*z allows z to be inferred, not fitted
-- independently of R. This is a conditional algebraic identity.
theorem stage3_reactor_inverse (R R0 R1 z : ℝ) (h : R=R0+R1*z)
    (hn : R1 ≠ 0) : z=(R-R0)/R1 := by
  apply (eq_div_iff hn).2
  linear_combination -h


-- Refined channels: r=1/2, cot(phi)=2+sqrt(3). The supplied t is sqrt(3)
-- in the numerical model, but the identity holds without that hypothesis.
theorem stage3_refined_coupling_ratio (gp gm t : ℝ)
    (h : (gp+gm)/2=(gp-gm)*(2+t)) :
    (3+2*t)*gp=(5+2*t)*gm := by
  linear_combination -2*h

-- If g+=q/M+ and g-=q/M-, equal Dirac column squared norms q imply
-- M-/M+=g+/g-. Use a denominator-cleared identity.
theorem stage3_equal_dirac_norm (gp gm Mp Mm q : ℝ)
    (hp : gp*Mp=q) (hm : gm*Mm=q) : gp*Mp=gm*Mm := by
  rw [hp,hm]

end Channel

section Seesaw

-- A heavy-field coordinate change and its inverse cancel exactly. This
-- generic associative algebra identity applies to square matrices, given
-- the two inverse-pair hypotheses. It does not assert a physical seesaw.
theorem stage3_heavy_basis_cancel {A : Type*} [Monoid A]
    (D S T R V U E : A) (hST : S*T=1) (hVU : V*U=1) :
    (D*S)*(T*R*V)*(U*E)=D*R*E := by
  calc
    (D*S)*(T*R*V)*(U*E)=D*(S*T)*R*(V*U)*E := by simp only [mul_assoc]
    _=D*R*E := by rw [hST,hVU,mul_one,mul_one]

-- Scalar complex phase identity for the signed channel contribution.
theorem stage3_seesaw_phase (M q : ℂ) :
    -(Complex.I*q)^2/M=q^2/M := by
  have hI : Complex.I^2 = -1 := Complex.I_sq
  rw [mul_pow,hI]
  ring

end Seesaw


#print axioms stage3_frame_sum
#print axioms stage3_projector_square
#print axioms stage3_channel_overlap
#print axioms stage3_frame_refinement
#print axioms stage3_original_overlap
#print axioms stage3_refined_overlap
#print axioms stage3_whitened_overlap
#print axioms stage3_frame_power_step
#print axioms stage3_kinetic_canonical
#print axioms stage3_stretch_block
#print axioms stage3_full_metric_canonical
#print axioms stage3_full_mass_congruence
#print axioms stage3_raw_compensation
#print axioms stage3_channel_trace
#print axioms stage3_channel_det
#print axioms stage3_channel_indefinite
#print axioms stage3_channel_ratio
#print axioms stage3_third_relation
#print axioms stage3_third_formula
#print axioms stage3_fixed_original
#print axioms stage3_fixed_refined
#print axioms stage3_inverse_geometry
#print axioms stage3_equal_strength_no_shift
#print axioms stage3_equal_strength_no_rotation
#print axioms stage3_positive_strengths
#print axioms stage3_positive_geometry
#print axioms stage3_squared_geometry
#print axioms stage3_parity_gap
#print axioms stage3_scale_independent
#print axioms stage3_reactor_inverse
#print axioms stage3_refined_coupling_ratio
#print axioms stage3_equal_dirac_norm
#print axioms stage3_heavy_basis_cancel
#print axioms stage3_seesaw_phase

end CollatzRunyan.LeptonSpectral

/-! Stage 4: vacuum alignment, competing drivers, and correlated mediator rigidity.
The finite-dimensional real signed mass model and the potential are hypotheses.
No claims about ultraviolet completion, measured masses, or quantum stability.
Compile the cumulative generated source, not this fragment. -/
namespace CollatzRunyan.LeptonSpectral

section Vacuum

-- Denominator-cleared traceless doublet coordinates (s^2 = 3).
theorem stage4_tensor_invariants (x y s : ℝ) (hs : s^2 = 3) :
    (-x+s*y)+(-x-s*y)+2*x=0 ∧
    (-x+s*y)^2+(-x-s*y)^2+(2*x)^2=6*(x^2+y^2) ∧
    (-x+s*y)*(-x-s*y)*(2*x)=2*x*(x^2-3*y^2) := by
  refine ⟨by ring, ?_, ?_⟩
  · linear_combination (2*y^2)*hs
  · linear_combination (-2*x*y^2)*hs

-- First two components of N are 1/sqrt(2); the cross product has one component.
theorem stage4_cross_driver_factor (d e : ℝ) :
    (d*e^2-e*d^2)/2=d*e*((e-d)/2) := by ring

theorem stage4_tensor_gram_identity (x y s : ℝ) (hs : s^2=3) :
    ((-x+s*y)*(-x-s*y)*(-2*s*y))^2 =
      12*y^2*(x^2-3*y^2)^2 := by
  have h : (-x+s*y)*(-x-s*y)=x^2-3*y^2 := by
    linear_combination -y^2*hs
  rw [h]
  linear_combination (4*y^2*(x^2-3*y^2)^2)*hs

noncomputable def stage4_vacuum (l k b v x y : ℝ) : ℝ :=
  l*(x^2+y^2-v^2)^2+(k*x^2+b*y^2)*(x^2-3*y^2)^2

theorem stage4_vacuum_nonnegative (l k b v x y : ℝ)
    (hl : 0 ≤ l) (hk : 0 ≤ k) (hb : 0 ≤ b) :
    0 ≤ stage4_vacuum l k b v x y := by
  unfold stage4_vacuum
  positivity

theorem stage4_vacuum_zero_set (l k b v x y : ℝ)
    (hl : 0 < l) (hk : 0 < k) (hb : 0 < b) (hv : 0 < v) :
    stage4_vacuum l k b v x y=0 ↔ x^2+y^2=v^2 ∧ x^2=3*y^2 := by
  constructor
  · intro h
    unfold stage4_vacuum at h
    have h1 : 0 ≤ l*(x^2+y^2-v^2)^2 := by positivity
    have h2 : 0 ≤ (k*x^2+b*y^2)*(x^2-3*y^2)^2 := by positivity
    have h3 : l*(x^2+y^2-v^2)^2=0 := by linarith
    have h4 : (k*x^2+b*y^2)*(x^2-3*y^2)^2=0 := by linarith
    have h5 : (x^2+y^2-v^2)^2=0 := (mul_eq_zero.mp h3).resolve_left (ne_of_gt hl)
    have hrad : x^2+y^2=v^2 := by
      have h6 : x^2+y^2-v^2=0 := by
        rcases mul_eq_zero.mp (show (x^2+y^2-v^2)*(x^2+y^2-v^2)=0 by simpa [pow_two] using h5) with hh | hh <;> exact hh
      linarith
    have hpos : 0 < k*x^2+b*y^2 := by
      by_cases hx : x=0
      · have hy : y ≠ 0 := by
          intro hy
          rw [hx,hy] at hrad
          have hv2 : 0 < v^2 := by positivity
          nlinarith
        rw [hx]
        positivity
      · have hp : 0 < k*x^2 := by positivity
        have hq : 0 ≤ b*y^2 := by positivity
        linarith
    have hh : (x^2-3*y^2)^2=0 := (mul_eq_zero.mp h4).resolve_left (ne_of_gt hpos)
    have hz : x^2-3*y^2=0 := by
      rcases mul_eq_zero.mp (show (x^2-3*y^2)*(x^2-3*y^2)=0 by simpa [pow_two] using hh) with h0 | h0 <;> exact h0
    exact ⟨hrad, by linarith⟩
  · rintro ⟨hr,ha⟩
    unfold stage4_vacuum
    rw [hr,ha]
    ring

theorem stage4_vacuum_components (v x y : ℝ)
    (hr : x^2+y^2=v^2) (ha : x^2=3*y^2) :
    4*x^2=3*v^2 ∧ 4*y^2=v^2 := by
  constructor <;> linarith

theorem stage4_vertical_excluded (v x y : ℝ) (hv : 0 < v)
    (hr : x^2+y^2=v^2) (ha : x^2=3*y^2) : x ≠ 0 := by
  intro hx
  rw [hx] at hr ha
  have hv2 : 0 < v^2 := by positivity
  nlinarith

theorem stage4_angular_square (p delta : ℝ) :
    (4*p-3)^2+delta*p = 16*(p-(3/4-delta/32))^2+3*delta/4-delta^2/64 := by ring

theorem stage4_angular_minimum (p delta : ℝ) :
    (4*(3/4-delta/32)-3)^2+delta*(3/4-delta/32) ≤ (4*p-3)^2+delta*p := by
  calc
    _ = 3*delta/4-delta^2/64 := by ring
    _ ≤ _ := by
      rw [stage4_angular_square]
      nlinarith [sq_nonneg (p-(3/4-delta/32))]

-- Joint polynomial constraints, with the positive square-root branch supplied.
theorem stage4_joint_constraint (R X Y a b s : ℝ)
    (hs : s^2=3) (hspos : 0 < s) (hR : 0 < R) (hX : 0 < X)
    (hr : R^2=X^2+Y^2) (ha : X^2=3*Y^2) (hg : 3*R+5*X=8*(b-a)) :
    R*(6+5*s)=16*(b-a) := by
  have hh : (2*X)^2=(s*R)^2 := by
    linear_combination -R^2*hs-3*hr+ha
  have hp : 0 < 2*X+s*R := by positivity
  have hf : (2*X-s*R)*(2*X+s*R)=0 := by linear_combination hh
  have he := (mul_eq_zero.mp hf).resolve_right (ne_of_gt hp)
  linear_combination 2*hg-5*he

end Vacuum

section Drivers

-- Equal additive charges follow in any abelian group, including finite ones.
theorem stage4_driving_charge_obstruction {G : Type*} [AddCommGroup G]
    (c d n xi : G) (h1 : c+d+d+n=0) (h2 : c+xi+d+n=0) :
    c+xi+xi+n=0 := by
  have h : c+xi+xi+n=(c+xi+d+n)+(c+xi+d+n)-(c+d+d+n) := by abel
  rw [h,h1,h2]
  simp

theorem stage4_distinct_tensor_entries (d e f : ℝ)
    (ht : d+e+f=0) (hd : d*e*f=0) (hn : 0 < d^2+e^2+f^2) : d ≠ e := by
  intro h
  subst e
  rcases mul_eq_zero.mp hd with h1 | h2
  · have hz : d=0 := (mul_eq_zero.mp h1).elim id id
    have hf : f=0 := by linarith
    rw [hz,hf] at hn
    norm_num at hn
  · have hz : d=0 := by linarith
    rw [hz,h2] at hn
    norm_num at hn

theorem stage4_competing_driving_no_solution (d e f xi c : ℝ)
    (ht : d+e+f=0) (hd : d*e*f=0) (hn : 0 < d^2+e^2+f^2)
    (hc : c ≠ 0) (h1 : d^2-xi*d+c*xi^2=0) (h2 : e^2-xi*e+c*xi^2=0) : False := by
  have hne := stage4_distinct_tensor_entries d e f ht hd hn
  have hh : (d-e)*(d+e-xi)=0 := by linear_combination h1-h2
  have he := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)
  have hp : d*e=c*xi^2 := by linear_combination -h1+d*he
  have hf : f = -xi := by linarith
  have hz : c*xi^2*(-xi)=0 := by
    rw [← hp,← hf]
    exact hd
  have hxi : xi=0 := by
    rcases mul_eq_zero.mp hz with h | h
    · have hsq := (mul_eq_zero.mp h).resolve_left hc
      rcases mul_eq_zero.mp (show xi*xi=0 by simpa [pow_two] using hsq) with h0 | h0 <;> exact h0
    · linarith
  rw [hxi] at h1 h2 hf
  have hd0 : d=0 := by
    have hh : d*d=0 := by nlinarith
    exact (mul_eq_zero.mp hh).elim id id
  have he0 : e=0 := by
    have hh : e*e=0 := by nlinarith
    exact (mul_eq_zero.mp hh).elim id id
  rw [hd0,he0,hf] at hn
  norm_num at hn

theorem stage4_cross_driver_rigidity (d e f eps v : ℝ)
    (ht : d+e+f=0) (hd : d*e*f=0) (hn : d^2+e^2+f^2=v^2)
    (hv : v ≠ 0) (h : d*e+eps*v^2=0) : eps=0 ∨ eps=1/2 := by
  rcases mul_eq_zero.mp hd with hz | hf
  · left
    have hh : eps*v^2=0 := by linarith
    exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero 2 hv)
  · right
    have hh : 2*(d*e) = -v^2 := by
      have hsum : d+e=0 := by linarith
      linear_combination (d+e)*hsum-hn+f*hf
    have hh2 : (2*eps-1)*v^2=0 := by linear_combination 2*h-hh
    have he := (mul_eq_zero.mp hh2).resolve_right (pow_ne_zero 2 hv)
    linarith

end Drivers

section Mediator

-- Characteristic determinant expanded for the full real symmetric 3x3 system.
theorem stage4_one_mediator_char (a M x y z : ℝ) :
    (a-z)*((a-z)*(M-z)-y^2)-x^2*(a-z)=
    (a-z)*((a-z)*(M-z)-x^2-y^2) := by ring

theorem stage4_one_mediator_eigenvector (a M x y : ℝ) :
    a*(-y)+0*x+x*0=a*(-y) ∧
    0*(-y)+a*x+y*0=a*x ∧ x*(-y)+y*x+M*0=a*0 := by
  constructor
  · ring
  constructor <;> ring

theorem stage4_one_mediator_matrix_eigenvector (a M x y : ℝ) :
    (!![a,0,x;0,a,y;x,y,M] : Matrix (Fin 3) (Fin 3) ℝ).mulVec ![-y,x,0] =
      ![-a*y,a*x,0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

-- Exact Schur resolvent identity with denominators cleared.
theorem stage4_resolvent_remainder (M z : ℝ) :
    M^2=(M-z)*(M+z)+z^2 := by ring

theorem stage4_correlated_coefficient (a M : ℝ) (hM : M ≠ 0) :
    -1/M-a/M^2=-(M+a)/M^2 := by
  have hm : M^2 ≠ 0 := pow_ne_zero 2 hM
  apply (eq_div_iff hm).2
  have h : (-1/M)*M = -1 := ((div_eq_iff hM).mp (show -1/M = -1/M from rfl)).symm
  have ha : (a/M^2)*M^2=a := ((div_eq_iff hm).mp (show a/M^2=a/M^2 from rfl)).symm
  calc
    (-1/M-a/M^2)*M^2=((-1/M)*M)*M-(a/M^2)*M^2 := by ring
    _=-(M+a) := by rw [h,ha]; ring

-- Component form of H_raw = a K + g w w^T, with g supplied.
theorem stage4_correlated_mass_components (a x y k m g : ℝ) (h : m=a*k+g) :
    a+m*x^2=a*(1+k*x^2)+g*x^2 ∧
    m*x*y=a*(k*x*y)+g*x*y ∧
    a+m*y^2=a*(1+k*y^2)+g*y^2 := by
  subst m
  exact ⟨by ring,by ring,by ring⟩

-- General symmetric K, no matrix square-root existence assumption needed.
-- det(H_raw - z K) = (a-z)[(a-z)det K + g w^T adj(K) w].
theorem stage4_metric_char (a z p q r g x y : ℝ) :
    ((a-z)*p+g*x^2)*((a-z)*r+g*y^2)-((a-z)*q+g*x*y)^2 =
    (a-z)*((a-z)*(p*r-q^2)+g*(r*x^2-2*q*x*y+p*y^2)) := by ring

theorem stage4_metric_protected_root (p q r g x y : ℝ) :
    (g*x^2)*(g*y^2)-(g*x*y)^2=0 := by ring

theorem stage4_metric_second_root (a z p q r g x y : ℝ)
    (hd : p*r-q^2 ≠ 0) (hz : z ≠ a)
    (h : ((a-z)*p+g*x^2)*((a-z)*r+g*y^2)-((a-z)*q+g*x*y)^2=0) :
    z=a+g*(r*x^2-2*q*x*y+p*y^2)/(p*r-q^2) := by
  rw [stage4_metric_char] at h
  have hh := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hz))
  have hmul : (z-a)*(p*r-q^2)=g*(r*x^2-2*q*x*y+p*y^2) := by linear_combination -hh
  have he := (eq_div_iff hd).2 hmul
  linarith

-- Two opposite signed heavy offsets about a, equal real couplings t.
theorem stage4_balanced_pair_char (e M t : ℝ) :
    (-e)*(M-e)*(-M-e)-t^2*(-M-e)-t^2*(M-e) =
      -e*(e^2-M^2-2*t^2) := by ring

theorem stage4_balanced_pair_eigenvector (M t : ℝ) :
    (0*M+t*(-t)+t*t=0) ∧ (t*M+M*(-t)+0*t=0) ∧
      (t*M+0*(-t)-M*t=0) := by exact ⟨by ring,by ring,by ring⟩

theorem stage4_balanced_pair_matrix_kernel (M t : ℝ) :
    (!![0,t,t;t,M,0;t,0,-M] : Matrix (Fin 3) (Fin 3) ℝ).mulVec ![M,-t,t]=
      ![0,0,0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

-- Opposite offsets cancel the centered mass contribution but not the metric.
theorem stage4_balanced_mass_cancel (M t : ℝ) :
    t^2/M+t^2/(-M)=0 := by rw [div_neg] <;> ring

theorem stage4_balanced_metric_add (M t : ℝ) :
    t^2/M^2+t^2/(-M)^2=2*t^2/M^2 := by rw [neg_sq] <;> ring

theorem stage4_balanced_norm (M t : ℝ) : M^2+(-t)^2+t^2=M^2+2*t^2 := by ring

theorem stage4_balanced_half_active (M t : ℝ) (hM : M ≠ 0) (h : 2*t^2=M^2) :
    M^2/(M^2+2*t^2)=1/2 := by
  rw [h]
  have hp : M^2+M^2 ≠ 0 := by positivity
  apply (div_eq_iff hp).2
  ring

-- Metric eigenvalues produced by canonical light fields plus positive mixing.
-- If k2/k1=2, k2>=2, so inverse metric weight <=1/2.
theorem stage4_metric_anisotropy_bound (k1 k2 : ℝ)
    (h1 : 1 ≤ k1) (h2 : k2=2*k1) : 2 ≤ k2 := by linarith

theorem stage4_metric_active_weight_bound (k1 k2 p : ℝ)
    (h1 : 1 ≤ k1) (h2 : k2=2*k1) (hp : 0 ≤ p) (hw : p*k2=1) : p ≤ 1/2 := by
  have hk := stage4_metric_anisotropy_bound k1 k2 h1 h2
  have hh := mul_nonneg hp (sub_nonneg.mpr hk)
  nlinarith

-- An upward signed light eigenvalue cannot come from a heavier positive
-- signed state in this real symmetric one-mediator model.
theorem stage4_positive_heavy_obstruction (a d M x y : ℝ)
    (had : a < d) (hdM : d < M)
    (h : (a-d)*(M-d)=x^2+y^2) : False := by
  have hn : (a-d)*(M-d)<0 := mul_neg_of_neg_of_pos (sub_neg.mpr had) (sub_pos.mpr hdM)
  nlinarith [sq_nonneg x,sq_nonneg y]

-- Inverting the exact eigenvalue equation gives a continuum of couplings.
theorem stage4_mediator_inverse_norm (a d M x y : ℝ)
    (h : (a-d)*(M-d)=x^2+y^2) : x^2+y^2=(d-a)*(d-M) := by
  linear_combination -h

-- Two light directions coupled to one mediator: choose the orthogonal
-- eigenvector. A nonzero coupling implies the proposed eigenvector is nonzero.
theorem stage4_protected_vector_nonzero (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    -y ≠ 0 ∨ x ≠ 0 := by
  rcases h with hx | hy
  · exact Or.inr hx
  · left
    intro hz
    apply hy
    linarith

end Mediator


#print axioms stage4_tensor_invariants
#print axioms stage4_cross_driver_factor
#print axioms stage4_tensor_gram_identity
#print axioms stage4_vacuum_nonnegative
#print axioms stage4_vacuum_zero_set
#print axioms stage4_vacuum_components
#print axioms stage4_vertical_excluded
#print axioms stage4_angular_square
#print axioms stage4_angular_minimum
#print axioms stage4_joint_constraint
#print axioms stage4_driving_charge_obstruction
#print axioms stage4_distinct_tensor_entries
#print axioms stage4_competing_driving_no_solution
#print axioms stage4_cross_driver_rigidity
#print axioms stage4_one_mediator_char
#print axioms stage4_one_mediator_eigenvector
#print axioms stage4_one_mediator_matrix_eigenvector
#print axioms stage4_resolvent_remainder
#print axioms stage4_correlated_coefficient
#print axioms stage4_correlated_mass_components
#print axioms stage4_metric_char
#print axioms stage4_metric_protected_root
#print axioms stage4_metric_second_root
#print axioms stage4_balanced_pair_char
#print axioms stage4_balanced_pair_eigenvector
#print axioms stage4_balanced_pair_matrix_kernel
#print axioms stage4_balanced_mass_cancel
#print axioms stage4_balanced_metric_add
#print axioms stage4_balanced_norm
#print axioms stage4_balanced_half_active
#print axioms stage4_metric_anisotropy_bound
#print axioms stage4_metric_active_weight_bound
#print axioms stage4_positive_heavy_obstruction
#print axioms stage4_mediator_inverse_norm
#print axioms stage4_protected_vector_nonzero

end CollatzRunyan.LeptonSpectral

/-! Stage 5: independent scalar response, messenger symmetry, and exact
rank-deficiency protection. Algebraic hypotheses only; no gauge-invariant
UV completion, experimental validation or quantum RG derivation is claimed.
Compile the cumulative generated source, not this fragment. -/
namespace CollatzRunyan.LeptonSpectral

section ScalarResponse

-- Component form of B^2 = Q for a real symmetric two-by-two tensor.
theorem stage5_scalar_square_commutes (r s t p q : ℝ)
    (h1 : r^2+s^2=p) (h2 : s^2+t^2=q) (h3 : s*(r+t)=0)
    (hpq : p ≠ q) : s=0 := by
  rcases mul_eq_zero.mp h3 with hs | hrt
  · exact hs
  · exfalso
    apply hpq
    linear_combination -h1+h2+(r-t)*hrt

theorem stage5_scalar_vacuum_diagonal (r s t : ℝ)
    (h1 : r^2+s^2=4/3) (h2 : s^2+t^2=2/3) (h3 : s*(r+t)=0) :
    s=0 ∧ r^2=4/3 ∧ t^2=2/3 := by
  have hs := stage5_scalar_square_commutes r s t (4/3) (2/3) h1 h2 h3 (by norm_num)
  refine ⟨hs, ?_, ?_⟩
  · simpa [hs] using h1
  · simpa [hs] using h2

-- Ratio of squared channel coordinates after scalar refinement.
theorem stage5_scalar_refinement (r t : ℝ) (hr : r^2=4/3) (ht : t^2=2/3) :
    4*t^2=2*r^2 := by linarith

theorem stage5_scalar_perturbation (r s t e : ℝ)
    (h1 : r^2+s^2=4/3-e) (h2 : s^2+t^2=2/3-e) (h3 : s*(r+t)=0) :
    s=0 ∧ r^2=4/3-e ∧ t^2=2/3-e := by
  have hh : (4/3-e : ℝ) ≠ 2/3-e := by intro h; linarith
  have hs := stage5_scalar_square_commutes r s t (4/3-e) (2/3-e) h1 h2 h3 hh
  refine ⟨hs, ?_, ?_⟩
  · simpa [hs] using h1
  · simpa [hs] using h2

theorem stage5_scalar_geometry_rigidity (e : ℝ) (he : e < 2/3) :
    (1/2)*(2/3-e)/(4/3-e)=1/4 ↔ e=0 := by
  have hd : (4/3-e : ℝ) ≠ 0 := by linarith
  constructor
  · intro h
    have hh := (div_eq_iff hd).1 h
    linarith
  · intro h
    subst e
    norm_num

theorem stage5_channel_overlap (k : ℝ) (hk : 0 < k) :
    (1-k)/(1+k)=0 ↔ k=1 := by
  have hd : (1+k : ℝ) ≠ 0 := by linarith
  constructor
  · intro h
    have hh := (div_eq_iff hd).1 h
    linarith
  · intro h
    subst k
    norm_num

theorem stage5_refined_overlap : ((1-(1/4 : ℝ))/(1+1/4))^2=9/25 := by norm_num

-- Dimensionless scaling identities, with a supplied positive heavy-scale multiplier.
theorem stage5_seesaw_scaling (q M t : ℝ) (hM : M ≠ 0) (ht : t ≠ 0) :
    (t*q)/(t*M)=q/M := by
  field_simp [hM,ht] <;> ring

theorem stage5_mixing_suppression (q M t : ℝ) (hM : M ≠ 0) (ht : t ≠ 0) :
    (t*q)/(t*M)^2=(q/M^2)/t := by
  field_simp [hM,ht] <;> ring

end ScalarResponse

section Messenger

-- Here s^2=3, and the two real directions are (1,s)/2 and (-s,1)/2.
theorem stage5_messenger_diagonal_weights (x y s : ℝ) (hs : s^2=3) :
    (x+s^2*y)/4=(x+3*y)/4 ∧ (s^2*x+y)/4=(3*x+y)/4 := by
  rw [hs]
  exact ⟨rfl,rfl⟩

theorem stage5_reflection_average (p j m : ℝ) :
    (1/2 : ℝ) • ((!![p,j;j,m] : Matrix (Fin 2) (Fin 2) ℝ)+!![p,-j;-j,m]) =
      !![p,0;0,m] := by
  ext i j'
  fin_cases i <;> fin_cases j' <;> simp <;> ring

theorem stage5_heavy_diagonal_ratio (s : ℝ) (hs : s^2=3) (hp : 0<s) :
    (3*s+1)/(s+3)=(4*s)/3-1 := by
  have hd : s+3 ≠ 0 := by linarith
  apply (div_eq_iff hd).2
  linear_combination -(4/3)*hs

theorem stage5_direct_mass_asymmetry (s : ℝ) (hs : s^2=3) (hp : 0<s) :
    (s-1)/(2*(s+1))=(2-s)/2 := by
  have hd : 2*(s+1) ≠ 0 := by positivity
  apply (div_eq_iff hd).2
  linear_combination hs

-- A scalar form of unitary character rigidity: invariance of the inner
-- product forces identical eigenphases when the overlap is nonzero.
theorem stage5_nonorthogonal_character_rigidity (p q c : ℂ)
    (hc : c ≠ 0) (h : p*c=q*c) : p=q := by
  have hz : (p-q)*c=0 := by rw [sub_mul,h,sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hc)

theorem stage5_unitary_parity_obstruction (c : ℂ) (hc : c ≠ 0)
    (h : c = -c) : False := by
  apply hc
  linear_combination (1/2 : ℂ)*h

-- In a fixed Majorana CP basis, opposite parities force z = -conj(z).
theorem stage5_cp_offdiagonal (z : ℂ) (h : z = -star z) : z.re=0 := by
  have hr := congrArg Complex.re h
  simp at hr
  linarith

-- Component calculation of the CP-compatible inverse-seesaw numerator.
-- s is the signed sqrt(k); normalized columns (1,s), (1,-s).
theorem stage5_cp_seesaw_numerator (p m j s : ℝ) :
    ((!![Complex.I,1; (s:ℂ)*Complex.I,-(s:ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) *
      !![(m:ℂ),-Complex.I*(j:ℂ);-Complex.I*(j:ℂ),(p:ℂ)] *
      !![Complex.I,(s:ℂ)*Complex.I;1,-(s:ℂ)]) =
      !![((p:ℂ)-(m:ℂ)+2*(j:ℂ)),-(s:ℂ)*((p:ℂ)+(m:ℂ));
         -(s:ℂ)*((p:ℂ)+(m:ℂ)),(s:ℂ)^2*((p:ℂ)-(m:ℂ)-2*(j:ℂ))] := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

-- Algebra of the supplied one-loop RGE, not a proof of quantum field theory.
theorem stage5_radiative_offdiagonal (p m q c : ℝ) :
    ((q:ℂ)^2*(c:ℂ)*Complex.I)*(m:ℂ) +
      (p:ℂ)*(-(q:ℂ)^2*(c:ℂ)*Complex.I) =
      (q:ℂ)^2*(c:ℂ)*Complex.I*((m:ℂ)-(p:ℂ)) := by ring

theorem stage5_radiative_ratio_stationary (p m q : ℝ) :
    (2*q^2*m)*p-m*(2*q^2*p)=0 := by ring

end Messenger

section ExactProtection

-- A and G are the rotated Dirac couplings, with G^2=k*A^2.
-- First-row determinant expansion of the centered four-state matrix.
theorem stage5_centered_determinant_expansion (A B G d J : ℝ) :
    A*(0*(0*d-G*0)-B*(A*d-G*0)+0*(A*0-0*0)+G*(A*G-B*0)) =
      -A^2*(B*d-G^2) := by ring

-- Actual finite-matrix determinant (in addition to the expanded polynomial).
theorem stage5_centered_matrix_det (A B G d J : ℝ) :
    Matrix.det (!![0,0,A,0;0,B,0,G;A,0,d,-J;0,G,-J,d] : Matrix (Fin 4) (Fin 4) ℝ) =
      -A^2*(B*d-G^2) := by
  have hidx : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := by decide
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,hidx] <;> ring

-- An explicit four-state kernel when the rank-one condition holds.
theorem stage5_four_state_kernel (A B G d J : ℝ) (h : B*d=G^2) :
    (!![0,0,A,0;0,B,0,G;A,0,d,-J;0,G,-J,d] : Matrix (Fin 4) (Fin 4) ℝ).mulVec
      ![J*B,-A*G,0,A*B]=0 := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> nlinarith [congrArg (fun z : ℝ => A*z) h]

-- Exact elimination of the additional mediator, expressed in the v,t rows.
theorem stage5_schur_mediator_rows (g h L v t chi : ℝ) (hL : L ≠ 0)
    (hc : L*chi=g*v+h*t) :
    g*chi=(g^2*v+g*h*t)/L ∧ h*chi=(g*h*v+h^2*t)/L := by
  constructor
  · apply (eq_div_iff hL).2
    linear_combination g*hc
  · apply (eq_div_iff hL).2
    linear_combination h*hc

-- Equivalent exact scalar determinant-zero condition.
theorem stage5_rank_one_constraint_iff (A B G d : ℝ) (hA : A ≠ 0) :
    -A^2*(B*d-G^2)=0 ↔ B*d=G^2 := by
  constructor
  · intro h
    have hna : -A^2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hA)
    have hh := (mul_eq_zero.mp h).resolve_left hna
    linarith
  · intro h
    rw [h]
    ring

-- Exact Schur relation, denominator-cleared, including the shift by a.
theorem stage5_exact_schur_protection (k B q p m a : ℝ)
    (hk : k ≠ 0) (h : 4*k*q=(1+k)*B*(m-p-2*a)) :
    q=(1+k)*B*(m-p-2*a)/(4*k) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hk)).2
  linear_combination h

theorem stage5_exact_dirac_refined (B q p m a : ℝ)
    (h : 4*(1/4 : ℝ)*q=(1+1/4)*B*(m-p-2*a)) :
    q=5/4*B*(m-p-2*a) := by nlinarith

theorem stage5_common_mediator_factor (g h L : ℝ) :
    (g^2/L)*(h^2/L)=(g*h/L)^2 := by ring

theorem stage5_common_mediator_constraint (g h L B G d : ℝ)
    (hB : B=g^2/L) (hG : G=g*h/L) (hd : d=h^2/L) : B*d=G^2 := by
  rw [hB,hG,hd]
  exact stage5_common_mediator_factor g h L

-- Full five-state centered matrix, not an effective approximation.
noncomputable def stage5_five_matrix (A g h T J L : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,0,A,0,0;0,0,0,0,g;A,0,T,-J,0;0,0,-J,0,h;0,g,0,h,-L]

noncomputable def stage5_five_vector (A g h J : ℝ) : Fin 5 → ℝ := ![J*g,-A*h,0,A*g,0]

theorem stage5_five_state_matrix_kernel (A g h T J L : ℝ) :
    (stage5_five_matrix A g h T J L).mulVec (stage5_five_vector A g h J)=0 := by
  ext i
  fin_cases i <;> simp [stage5_five_matrix,stage5_five_vector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem stage5_protected_vector_nonzero (A g h J : ℝ) (hA : A ≠ 0) (hg : g ≠ 0) :
    stage5_five_vector A g h J ≠ 0 := by
  intro he
  have hh := congrFun he (3 : Fin 5)
  have hz : A*g=0 := by simpa [stage5_five_vector] using hh
  exact (mul_ne_zero hA hg) hz

-- Exact shifted eigenvalue identity using the full matrix entries.
theorem stage5_five_state_shifted_eigenvector (a A g h T J L : ℝ) :
    (!![a,0,A,0,0;0,a,0,0,g;A,0,a+T,-J,0;0,0,-J,a,h;0,g,0,h,a-L] : Matrix (Fin 5) (Fin 5) ℝ).mulVec
      (stage5_five_vector A g h J)=![a*(J*g),a*(-A*h),0,a*(A*g),0] := by
  ext i
  fin_cases i <;> simp [stage5_five_vector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

-- More general 3+2 rectangular block: cross product of the two columns.
theorem stage5_rectangular_kernel_lift (p q r s t u c d e : ℝ) :
    (!![0,0,0,p,q;0,0,0,r,s;0,0,0,t,u;p,r,t,c,d;q,s,u,d,e] : Matrix (Fin 5) (Fin 5) ℝ).mulVec
       ![r*u-t*s,t*q-p*u,p*s-r*q,0,0]=0 := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem stage5_rectangular_cross_nonzero (p q r s t u : ℝ)
    (h : r*u-t*s ≠ 0 ∨ t*q-p*u ≠ 0 ∨ p*s-r*q ≠ 0) :
    (![r*u-t*s,t*q-p*u,p*s-r*q,0,0] : Fin 5 → ℝ) ≠ 0 := by
  intro he
  rcases h with h0 | h1 | h2
  · apply h0
    simpa using congrFun he (0 : Fin 5)
  · apply h1
    simpa using congrFun he (1 : Fin 5)
  · apply h2
    simpa using congrFun he (2 : Fin 5)

-- General finite-dimensional rank-nullity bound for the rectangular map.
-- The block lift itself is verified separately above and below.
theorem stage5_rank_nullity_protection {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (L : V →ₗ[ℝ] W) :
    Module.finrank ℝ V - Module.finrank ℝ W ≤ Module.finrank ℝ (LinearMap.ker L) := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  have hr : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ W :=
    Submodule.finrank_le (LinearMap.range L)
  omega

-- Abstract block action, so the lifting property is dimension independent.
theorem stage5_general_block_kernel {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : W →ₗ[ℝ] V) (R : V →ₗ[ℝ] W)
    (C : W →ₗ[ℝ] W) (v : V) (hv : R v=0) :
    (L 0, R v+C 0)=(0,0) := by simp [hv]

theorem stage5_protected_norm (A g h J : ℝ) :
    (J*g)^2+(-A*h)^2+(A*g)^2=J^2*g^2+A^2*h^2+A^2*g^2 := by ring

theorem stage5_protected_weight_sum (A g h J : ℝ) (hA : A ≠ 0) (hg : g ≠ 0) :
    (J^2*g^2+A^2*h^2)/(J^2*g^2+A^2*h^2+A^2*g^2)+
    (A^2*g^2)/(J^2*g^2+A^2*h^2+A^2*g^2)=1 := by
  have hp : 0 < A^2*g^2 := by positivity
  have h1 : 0 ≤ J^2*g^2 := by positivity
  have h2 : 0 ≤ A^2*h^2 := by positivity
  have hd : J^2*g^2+A^2*h^2+A^2*g^2 ≠ 0 := by linarith
  rw [← add_div]
  exact div_self hd

-- Angle relation, first in denominator-cleared form.
theorem stage5_mediator_angle_relation (A g h d r G L : ℝ)
    (hG : G=r*A) (hc : G*L=g*h) (hd : d*L=h^2) (hL : L ≠ 0) :
    r*A*h=d*g := by
  have hh : (r*A*h-d*g)*L=0 := by
    linear_combination -h*L*hG+h*hc-g*hd
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hL)

-- A generic algebraic kernel transport for an invertible congruence.
-- S,T are supplied inverse maps in the indicated direction; no existence
-- claim about a metric square root is made here.
theorem stage5_metric_kernel_transport {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S T C : V →ₗ[ℝ] V) (v : V) (hv : C v=0) (hST : S (T v)=v) :
    S (C (S (T v)))=0 := by rw [hST,hv,map_zero]

theorem stage5_metric_kernel_transport_nonzero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S T : V →ₗ[ℝ] V) (v : V) (hv : v ≠ 0) (hST : S (T v)=v) :
    T v ≠ 0 := by
  intro h
  apply hv
  simpa [h] using hST.symm

-- Perturbing one entry of the zero block gives a nonzero residual
-- on the old eigenvector when its corresponding component is nonzero.
theorem stage5_zero_block_perturbation (A g h T J L e : ℝ) :
    (!![e,0,A,0,0;0,0,0,0,g;A,0,T,-J,0;0,0,-J,0,h;0,g,0,h,-L] : Matrix (Fin 5) (Fin 5) ℝ).mulVec
      (stage5_five_vector A g h J)=![e*J*g,0,0,0,0] := by
  ext i
  fin_cases i <;> simp [stage5_five_vector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

end ExactProtection

#print axioms stage5_scalar_square_commutes
#print axioms stage5_scalar_vacuum_diagonal
#print axioms stage5_scalar_refinement
#print axioms stage5_scalar_perturbation
#print axioms stage5_scalar_geometry_rigidity
#print axioms stage5_channel_overlap
#print axioms stage5_refined_overlap
#print axioms stage5_seesaw_scaling
#print axioms stage5_mixing_suppression
#print axioms stage5_messenger_diagonal_weights
#print axioms stage5_reflection_average
#print axioms stage5_heavy_diagonal_ratio
#print axioms stage5_direct_mass_asymmetry
#print axioms stage5_nonorthogonal_character_rigidity
#print axioms stage5_unitary_parity_obstruction
#print axioms stage5_cp_offdiagonal
#print axioms stage5_cp_seesaw_numerator
#print axioms stage5_radiative_offdiagonal
#print axioms stage5_radiative_ratio_stationary
#print axioms stage5_centered_determinant_expansion
#print axioms stage5_centered_matrix_det
#print axioms stage5_four_state_kernel
#print axioms stage5_schur_mediator_rows
#print axioms stage5_rank_one_constraint_iff
#print axioms stage5_exact_schur_protection
#print axioms stage5_exact_dirac_refined
#print axioms stage5_common_mediator_factor
#print axioms stage5_common_mediator_constraint
#print axioms stage5_five_state_matrix_kernel
#print axioms stage5_protected_vector_nonzero
#print axioms stage5_five_state_shifted_eigenvector
#print axioms stage5_rectangular_kernel_lift
#print axioms stage5_rectangular_cross_nonzero
#print axioms stage5_rank_nullity_protection
#print axioms stage5_general_block_kernel
#print axioms stage5_protected_norm
#print axioms stage5_protected_weight_sum
#print axioms stage5_mediator_angle_relation
#print axioms stage5_metric_kernel_transport
#print axioms stage5_metric_kernel_transport_nonzero
#print axioms stage5_zero_block_perturbation

end CollatzRunyan.LeptonSpectral

/-! Stage 6: gauge-sector algebra, arithmetic interaction geometry, and
forward-adjoint Collatz word obstructions. All statements are mathematical.
The general finite-field splitting and characteristic-polynomial reduction
arguments are not formalized in this file. Compile the cumulative source. -/
namespace CollatzRunyan.LeptonSpectral

section AffineWords
variable {R : Type*} [CommRing R]

def stage6_affine (a b d : R) : Matrix (Fin 2) (Fin 2) R := !![a,b;0,d]

theorem stage6_affine_compose (a b d e f g : R) :
    stage6_affine a b d * stage6_affine e f g =
      stage6_affine (a*e) (a*f+b*g) (d*g) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage6_affine, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem stage6_affine_det (a b d : R) :
    (stage6_affine a b d).det=a*d := by
  simp [stage6_affine, Matrix.det_fin_two]

theorem stage6_affine_gram (a b d : R) :
    (stage6_affine a b d).transpose * stage6_affine a b d =
      !![a^2,a*b;a*b,b^2+d^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage6_affine, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] <;> ring

theorem stage6_affine_gram_trace (a b d : R) :
    Matrix.trace ((stage6_affine a b d).transpose * stage6_affine a b d) =
      a^2+b^2+d^2 := by
  rw [stage6_affine_gram]
  simp [Matrix.trace, Fin.sum_univ_succ] <;> ring

theorem stage6_affine_gram_det (a b d : R) :
    Matrix.det ((stage6_affine a b d).transpose * stage6_affine a b d) =
      (a*d)^2 := by
  rw [stage6_affine_gram]
  simp [Matrix.det_fin_two] <;> ring

def stage6_branch (b : Bool) : Matrix (Fin 2) (Fin 2) ℤ :=
  if b then stage6_affine 3 1 2 else stage6_affine 1 0 2

def stage6_word : List Bool → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | b::w => stage6_word w * stage6_branch b

def stage6_oddCount : List Bool → ℕ
  | [] => 0
  | b::w => if b then stage6_oddCount w+1 else stage6_oddCount w

theorem stage6_word_det (w : List Bool) :
    (stage6_word w).det = (2:ℤ)^w.length * 3^stage6_oddCount w := by
  induction w with
  | nil => simp [stage6_word, stage6_oddCount]
  | cons b w ih =>
    cases b <;>
      simp [stage6_word, stage6_branch, stage6_oddCount, Matrix.det_mul,
        stage6_affine_det, ih, pow_succ] <;> ring

-- The complete triangular form, including an existential integer correction.
theorem stage6_word_affine (w : List Bool) :
    ∃ c : ℤ, stage6_word w =
      stage6_affine (3^stage6_oddCount w) c (2^w.length) := by
  induction w with
  | nil =>
    refine ⟨0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [stage6_word, stage6_oddCount, stage6_affine, Matrix.one_apply]
  | cons b w ih =>
    obtain ⟨c,hc⟩ := ih
    cases b
    · refine ⟨2*c, ?_⟩
      simp [stage6_word, stage6_branch, hc, stage6_affine_compose, stage6_oddCount, pow_succ, mul_comm]
    · refine ⟨3^stage6_oddCount w+2*c, ?_⟩
      simp [stage6_word, stage6_branch, hc, stage6_affine_compose, stage6_oddCount, pow_succ, mul_comm]

-- The factor 67 cannot occur in a determinant made from 2 and 3.
theorem stage6_word_det_mod67 (w : List Bool) :
    ((stage6_word w).det : ZMod 67) ≠ 0 := by
  letI : Fact (Nat.Prime 67) := ⟨by decide⟩
  rw [stage6_word_det]
  push_cast
  exact mul_ne_zero (pow_ne_zero _ (by decide : (2 : ZMod 67) ≠ 0))
    (pow_ne_zero _ (by decide : (3 : ZMod 67) ≠ 0))

theorem stage6_prime67_trace_det_obstruction (t d : ℤ)
    (hd : (d : ZMod 67) ≠ 0) : 67*t ≠ 334*d := by
  letI : Fact (Nat.Prime 67) := ⟨by decide⟩
  intro h
  have hh := congrArg (fun z : ℤ => (z : ZMod 67)) h
  push_cast at hh
  simp only [show (67 : ZMod 67) = 0 by decide, zero_mul] at hh
  exact (mul_ne_zero (by decide : (334 : ZMod 67) ≠ 0) hd) hh.symm

theorem stage6_word_gram_exclusion (w : List Bool) :
    67*Matrix.trace ((stage6_word w).transpose * stage6_word w) ≠
      334*(stage6_word w).det :=
  stage6_prime67_trace_det_obstruction _ _ (stage6_word_det_mod67 w)

-- Scale cancellation: if the squared singular values matched the target,
-- the trace and positive determinant would have these common factors.
theorem stage6_scaled_target_exclusion (w : List Bool) (r : ℝ) :
    ¬ (((Matrix.trace ((stage6_word w).transpose * stage6_word w) : ℤ) : ℝ)=668*r ∧
      ((stage6_word w).det : ℝ)=134*r) := by
  rintro ⟨ht,hd⟩
  have hh : (67:ℝ)*((Matrix.trace ((stage6_word w).transpose * stage6_word w) : ℤ) : ℝ)=
      334*((stage6_word w).det : ℝ) := by linarith only [ht, hd]
  apply stage6_word_gram_exclusion w
  exact_mod_cast hh

-- Extension to a rational metric: cleared trace t/v has denominator v
-- prime to 67. The determinant d is still prime to 67.
theorem stage6_localized_trace_exclusion (t v d : ℤ)
    (hv : (v : ZMod 67) ≠ 0) (hd : (d : ZMod 67) ≠ 0) :
    67*t ≠ 334*(v*d) := by
  letI : Fact (Nat.Prime 67) := ⟨by decide⟩
  apply stage6_prime67_trace_det_obstruction
  push_cast
  exact mul_ne_zero hv hd

end AffineWords

section CollectiveOperators

-- Unweighted sum of denominator-cleared even and odd matrices.
def stage6_sumBranch : Matrix (Fin 2) (Fin 2) ℚ := stage6_affine 4 1 4

theorem stage6_sum_branch_identity :
    (stage6_affine (1:ℚ) 0 2 + stage6_affine 3 1 2)=stage6_sumBranch := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [stage6_affine, stage6_sumBranch]

theorem stage6_sum_power (k : ℕ) :
    stage6_sumBranch^k = stage6_affine ((4:ℚ)^k) ((k:ℚ)*4^k/4) (4^k) := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [stage6_affine, Matrix.one_apply]
  | succ k ih =>
    calc
      stage6_sumBranch^(k+1) = stage6_sumBranch^k*stage6_sumBranch := pow_succ _ _
      _ = stage6_affine ((4:ℚ)^k*4) ((4:ℚ)^k+((k:ℚ)*4^k/4)*4) (4^k*4) := by
        rw [ih, stage6_sumBranch, stage6_affine_compose] <;> simp
      _ = stage6_affine ((4:ℚ)^(k+1)) (((k+1:ℕ):ℚ)*4^(k+1)/4) (4^(k+1)) := by
        push_cast
        simp only [pow_succ] <;> congr 1 <;> ring

theorem stage6_sum_normalized_gram_trace (k : ℕ) :
    Matrix.trace ((stage6_affine (1:ℚ) ((k:ℚ)/4) 1).transpose *
      stage6_affine 1 ((k:ℚ)/4) 1) = 2+(k:ℚ)^2/16 := by
  rw [stage6_affine_gram_trace]
  ring

theorem stage6_sum_ratio_integer_exclusion (k : ℕ) :
    67*k^2 ≠ 3200 := by omega

theorem stage6_sum_ratio_exclusion (k : ℕ) :
    (2:ℚ)+(k:ℚ)^2/16 ≠ 334/67 := by
  intro h
  have hq : (67:ℚ)*(k:ℚ)^2=3200 := by linarith
  apply stage6_sum_ratio_integer_exclusion k
  exact_mod_cast hq

-- Even diagonal entries in the integral symmetrization exclude the
-- target trace/determinant pair, since 234 is 2 modulo 4.
theorem stage6_integer_symmetrization_exclusion (a b d : ℤ) :
    ¬ (2*a+2*d=20 ∧ 4*a*d-b^2 = -134) := by
  rintro ⟨ht,hd⟩
  have hsq : b^2 = 4*(a*d)+134 := by nlinarith [hd]
  have hb : b^2 % 4 = 2 := by omega
  have hr : b%4=0 ∨ b%4=1 ∨ b%4=2 ∨ b%4=3 := by omega
  have hs : b^2 % 4 = (b%4)^2 % 4 := by
    simpa only [pow_two] using Int.mul_emod b b 4
  rcases hr with h|h|h|h <;> rw [h] at hs <;> norm_num at hs <;> omega

-- Adjoining the transpose generates a rational symmetric realization.
-- This is deliberately target-built, not a derivation of the coefficients.
theorem stage6_target_symmetric_trace :
    Matrix.trace (!![(13:ℤ),15;15,7] : Matrix (Fin 2) (Fin 2) ℤ)=20 := by
  norm_num [Matrix.trace, Fin.sum_univ_succ]

theorem stage6_target_symmetric_det :
    Matrix.det (!![(13:ℤ),15;15,7] : Matrix (Fin 2) (Fin 2) ℤ)= -134 := by
  norm_num [Matrix.det_fin_two]

theorem stage6_arithmetic_centered_square :
    (!![(-7:ℝ),Real.sqrt 185;Real.sqrt 185,7] : Matrix (Fin 2) (Fin 2) ℝ)^2 =
      !![234,0;0,234] := by
  have hs : (Real.sqrt 185)^2=185 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith

theorem stage6_target_invariants (s : ℝ) (hs : s^2=234) :
    (10+s)*(10-s)= -134 ∧ (10+s)^2+(10-s)^2=668 := by
  constructor <;> nlinarith

theorem stage6_affine_commutator :
    (stage6_affine (1/2:ℚ) 0 1 * stage6_affine (3/2) (1/2) 1) -
      (stage6_affine (3/2:ℚ) (1/2) 1 * stage6_affine (1/2) 0 1) =
      !![0,-1/4;0,0] := by
  rw [stage6_affine_compose, stage6_affine_compose]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [stage6_affine]

end CollectiveOperators

section GaugeSector

def stage6_perturbed (A g h T J L e : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,0,A,0,0;0,0,0,0,g;A,0,T,-J,0;0,0,-J,e,h;0,g,0,h,-L]

-- Stronger than a residual on the old vector: every kernel vector vanishes.
theorem stage6_sterile_perturbation_kernel (A g h T J L e : ℝ)
    (hA : A ≠ 0) (hg : g ≠ 0) (he : e ≠ 0)
    (v : Fin 5 → ℝ) (hv : (stage6_perturbed A g h T J L e).mulVec v=0) : v=0 := by
  have h0 := congrFun hv (0 : Fin 5)
  have h1 := congrFun hv (1 : Fin 5)
  have h2 := congrFun hv (2 : Fin 5)
  have h3 := congrFun hv (3 : Fin 5)
  have h4 := congrFun hv (4 : Fin 5)
  have p2 : A*v 2=0 := by
    simpa [stage6_perturbed,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using h0
  have p4 : g*v 4=0 := by
    simpa [stage6_perturbed,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using h1
  have z2 := (mul_eq_zero.mp p2).resolve_left hA
  have z4 := (mul_eq_zero.mp p4).resolve_left hg
  have p3 : e*v 3=0 := by
    simpa [stage6_perturbed,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,z2,z4] using h3
  have z3 := (mul_eq_zero.mp p3).resolve_left he
  have p0 : A*v 0=0 := by
    simpa [stage6_perturbed,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,z2,z3] using h2
  have p1 : g*v 1=0 := by
    simpa [stage6_perturbed,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,z3,z4] using h4
  have z0 := (mul_eq_zero.mp p0).resolve_left hA
  have z1 := (mul_eq_zero.mp p1).resolve_left hg
  funext i
  fin_cases i <;> assumption

def stage6_hybrid (c a q M : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![c,0,0,0;0,a,0,0;0,0,a,q;0,0,q,-M]

theorem stage6_hybrid_first_eigenvector (c a q M : ℝ) :
    (stage6_hybrid c a q M).mulVec ![1,0,0,0] = ![c,0,0,0] := by
  ext i
  fin_cases i <;> simp [stage6_hybrid,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem stage6_hybrid_solar_eigenvector (c a q M : ℝ) :
    (stage6_hybrid c a q M).mulVec ![0,1,0,0] = ![0,a,0,0] := by
  ext i
  fin_cases i <;> simp [stage6_hybrid,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem stage6_hybrid_atmospheric_eigenvector (c a q M d : ℝ)
    (hq : q^2=(d-a)*(d+M)) :
    (stage6_hybrid c a q M).mulVec ![0,0,d+M,q] = ![0,0,d*(d+M),d*q] := by
  ext i
  fin_cases i <;> simp [stage6_hybrid,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> nlinarith

theorem stage6_hybrid_root_factor (a q M d z : ℝ)
    (hq : q^2=(d-a)*(d+M)) :
    (a-z)*(-M-z)-q^2=(d-z)*(a-M-d-z) := by
  rw [hq]
  ring

theorem stage6_hybrid_sterile_weight (a q M d : ℝ)
    (hq : q^2=(d-a)*(d+M)) (hM : d+M ≠ 0) (hh : M+2*d-a ≠ 0) :
    q^2/((d+M)^2+q^2)=(d-a)/(M+2*d-a) := by
  rw [hq]
  have h : (d+M)^2+(d-a)*(d+M)=(d+M)*(M+2*d-a) := by ring
  rw [h]
  field_simp [hM,hh] <;> ring

-- Component form of the distinct-diagonal commutant obstruction.
theorem stage6_distinct_diagonal_commutant (di dj : ℝ) (s : ℂ)
    (hd : (di:ℂ) ≠ (dj:ℂ)) (hc : (di:ℂ)*s=s*(dj:ℂ)) : s=0 := by
  have h : ((di:ℂ)-(dj:ℂ))*s=0 := by linear_combination hc
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hd)

theorem stage6_projector_commutant_rigidity (si sj fi fj : ℂ)
    (hi : fi ≠ 0) (hj : fj ≠ 0) (hc : si*(fi*fj)=(fi*fj)*sj) : si=sj := by
  have h : (si-sj)*(fi*fj)=0 := by linear_combination hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (mul_ne_zero hi hj))

theorem stage6_radiative_ratio_identity (u v a x y : ℝ)
    (hu : u=a-3*x) (hv : v=a-3*y) : v-u= -3*(y-x) := by linarith

end GaugeSector

section ArithmeticResidues

-- Only the integer counting constraints, not a graph existence theorem.
theorem stage6_graph_minimum_order (x y ex : ℕ)
    (hx : 0<x) (hb : 37*x=5*y) (hp : 3*x=2*ex) : 84≤x+y := by omega

theorem stage6_graph_minimum_counts (x y ex : ℕ)
    (hx : 0<x) (hb : 37*x=5*y) (hp : 3*x=2*ex) (hn : x+y=84) : x=10 ∧ y=74 := by omega

theorem stage6_target_mod_seven_no_root :
    ∀ z : ZMod 7, z^2-20*z-134 ≠ 0 := by decide

-- Counterexample to extending the irreducibility argument to p=3.
-- Integer-weighted affine maps: 11 id, 17 (-r), 4 (1-r), 2 (r+1).
def stage6_affine_mod3_example : Matrix (Fin 3) (Fin 3) ℤ :=
  !![28,6,0;4,11,19;2,17,15]

theorem stage6_affine_mod3_row_sum :
    stage6_affine_mod3_example.mulVec ![1,1,1]=![34,34,34] := by
  ext i
  fin_cases i <;> norm_num [stage6_affine_mod3_example,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem stage6_affine_mod3_characteristic (z : ℤ) :
    Matrix.det (!![z-28,-6,0;-4,z-11,-19;-2,-17,z-15] : Matrix (Fin 3) (Fin 3) ℤ)=
      (z-34)*(z^2-20*z-134) := by
  simp [Matrix.det_fin_three] <;> ring

-- Affine-word action and the exact intertwining on one shift.
def stage6_applyWord {X : Type*} (F : Bool → X → X) : List Bool → X → X
  | [],r => r
  | b::w,r => stage6_applyWord F w (F b r)

theorem stage6_applyWord_append {X : Type*} (F : Bool → X → X)
    (w v : List Bool) (r : X) :
    stage6_applyWord F (w++v) r = stage6_applyWord F v (stage6_applyWord F w r) := by
  induction w generalizing r with
  | nil => rfl
  | cons b w ih => simp [stage6_applyWord, ih]

theorem stage6_residue_intertwining {X : Type*} (F : Bool → X → X)
    (g : X → ℝ) (a b : ℝ) (c : Bool) (w : List Bool) (r : X) :
    a*g (stage6_applyWord F (w++[false]) (F c r))+
      b*g (stage6_applyWord F (w++[true]) (F c r)) =
    a*g (F false (stage6_applyWord F (c::w) r))+
      b*g (F true (stage6_applyWord F (c::w) r)) := by
  simp [stage6_applyWord_append, stage6_applyWord]

theorem stage6_residue_embedding_injective {X : Type*} (F : Bool → X → X)
    (w : List Bool) (hs : Function.Surjective (stage6_applyWord F w))
    (g h : X → ℝ) (he : ∀ v r, g (stage6_applyWord F v r)=h (stage6_applyWord F v r)) : g=h := by
  funext x
  obtain ⟨r,hr⟩ := hs x
  simpa [hr] using he w r

end ArithmeticResidues

#print axioms stage6_affine_compose
#print axioms stage6_affine_det
#print axioms stage6_affine_gram
#print axioms stage6_affine_gram_trace
#print axioms stage6_affine_gram_det
#print axioms stage6_word_det
#print axioms stage6_word_affine
#print axioms stage6_word_det_mod67
#print axioms stage6_prime67_trace_det_obstruction
#print axioms stage6_word_gram_exclusion
#print axioms stage6_scaled_target_exclusion
#print axioms stage6_localized_trace_exclusion
#print axioms stage6_sum_branch_identity
#print axioms stage6_sum_power
#print axioms stage6_sum_normalized_gram_trace
#print axioms stage6_sum_ratio_integer_exclusion
#print axioms stage6_sum_ratio_exclusion
#print axioms stage6_integer_symmetrization_exclusion
#print axioms stage6_target_symmetric_trace
#print axioms stage6_target_symmetric_det
#print axioms stage6_arithmetic_centered_square
#print axioms stage6_target_invariants
#print axioms stage6_affine_commutator
#print axioms stage6_sterile_perturbation_kernel
#print axioms stage6_hybrid_first_eigenvector
#print axioms stage6_hybrid_solar_eigenvector
#print axioms stage6_hybrid_atmospheric_eigenvector
#print axioms stage6_hybrid_root_factor
#print axioms stage6_hybrid_sterile_weight
#print axioms stage6_distinct_diagonal_commutant
#print axioms stage6_projector_commutant_rigidity
#print axioms stage6_radiative_ratio_identity
#print axioms stage6_graph_minimum_order
#print axioms stage6_graph_minimum_counts
#print axioms stage6_target_mod_seven_no_root
#print axioms stage6_affine_mod3_row_sum
#print axioms stage6_affine_mod3_characteristic
#print axioms stage6_applyWord_append
#print axioms stage6_residue_intertwining
#print axioms stage6_residue_embedding_injective

end CollatzRunyan.LeptonSpectral

/-! Stage 7: integer spectral rigidity, Gram ensembles, arithmetic moments,
conditioned parity amplitudes. All spectral statements concern mathematical
operators, not a derivation of physical neutrino masses. -/
namespace CollatzRunyan.LeptonSpectral

section IntegerRigidity

theorem stage7_target_circle (a b d : ℤ) (ht : a+d=20)
    (hd : a*d-b^2 = -134) : (a-10)^2+b^2=234 := by
  have hh : d=20-a := by omega
  rw [hh] at hd
  nlinarith [hd]

theorem stage7_mod_three_rigidity (x y : ℤ) (h : x^2+y^2=234) :
    x%3=0 ∧ y%3=0 := by
  have hx : x%3=0 ∨ x%3=1 ∨ x%3=2 := by omega
  have hy : y%3=0 ∨ y%3=1 ∨ y%3=2 := by omega
  have hs : ((x%3)^2+(y%3)^2)%3=0 := by
    have h1 : x^2%3=(x%3)^2%3 := by
      simpa only [pow_two] using Int.mul_emod x x 3
    have h2 : y^2%3=(y%3)^2%3 := by
      simpa only [pow_two] using Int.mul_emod y y 3
    have h3 := Int.add_emod (x^2) (y^2) 3
    rw [h,h1,h2] at h3
    have h4 := Int.add_emod ((x%3)^2) ((y%3)^2) 3
    exact h4.trans (h3.symm.trans (by decide : (234:ℤ)%3=0))
  rcases hx with hx|hx|hx <;> rcases hy with hy|hy|hy <;>
    rw [hx,hy] at hs <;> norm_num at hs <;> omega

set_option maxHeartbeats 2000000 in
theorem stage7_sum_squares_classification (x y : ℤ) (h : x^2+y^2=26) :
    (x^2=1 ∧ y^2=25) ∨ (x^2=25 ∧ y^2=1) := by
  have hx0 : -5 ≤ x := by
    by_contra hn
    have hh : x≤ -6 := by omega
    nlinarith [sq_nonneg y,mul_nonneg (show 0≤ -x-6 by omega) (show 0≤ -x+6 by omega)]
  have hx1 : x ≤ 5 := by
    by_contra hn
    have hh : 6≤x := by omega
    nlinarith [sq_nonneg y,mul_nonneg (show 0≤x-6 by omega) (show 0≤x+6 by omega)]
  have hy0 : -5 ≤ y := by
    by_contra hn
    have hh : y≤ -6 := by omega
    nlinarith [sq_nonneg x,mul_nonneg (show 0≤ -y-6 by omega) (show 0≤ -y+6 by omega)]
  have hy1 : y ≤ 5 := by
    by_contra hn
    have hh : 6≤y := by omega
    nlinarith [sq_nonneg x,mul_nonneg (show 0≤y-6 by omega) (show 0≤y+6 by omega)]
  interval_cases x <;> interval_cases y <;> norm_num at h ⊢

theorem stage7_symmetric_integer_classification (a b d : ℤ)
    (ht : a+d=20) (hd : a*d-b^2 = -134) :
    ((a-10)^2=9 ∧ b^2=225) ∨ ((a-10)^2=225 ∧ b^2=9) := by
  have hc := stage7_target_circle a b d ht hd
  obtain ⟨hx,hy⟩ := stage7_mod_three_rigidity (a-10) b hc
  have hxx : a-10=3*((a-10)/3) := by omega
  have hyy : b=3*(b/3) := by omega
  have hh : ((a-10)/3)^2+(b/3)^2=26 := by
    have hsum : 9*(((a-10)/3)^2+(b/3)^2)=234 := by
      calc
        9*(((a-10)/3)^2+(b/3)^2) = (3*((a-10)/3))^2+(3*(b/3))^2 := by ring
        _ = 234 := by rw [← hxx, ← hyy, hc]
    nlinarith only [hsum]
  rcases stage7_sum_squares_classification _ _ hh with h|h
  · left; constructor <;> nlinarith [h.1,h.2,congrArg (fun z : ℤ => z^2) hxx,congrArg (fun z : ℤ => z^2) hyy]
  · right; constructor <;> nlinarith [h.1,h.2,congrArg (fun z : ℤ => z^2) hxx,congrArg (fun z : ℤ => z^2) hyy]

theorem stage7_nonnegative_target_rigidity (a b d : ℤ)
    (ha : 0≤a) (hb : 0≤b) (hdd : 0≤d) (ht : a+d=20)
    (hd : a*d-b^2 = -134) : b=15 := by
  rcases stage7_symmetric_integer_classification a b d ht hd with h|h
  · have he : (b-15)*(b+15)=0 := by nlinarith [h.2]
    rcases mul_eq_zero.mp he with h0|h0 <;> omega
  · have had : a*d= -125 := by nlinarith [h.2,hd]
    nlinarith [mul_nonneg ha hdd]

theorem stage7_gram_spectral_circle (a b d t x : ℤ)
    (ha : a=167*t+x) (hd : d=167*t-x)
    (hdet : a*d-b^2=4489*t^2) : x^2+b^2=23400*t^2 := by
  rw [ha,hd] at hdet
  nlinarith

theorem stage7_gram_scale_identity (a b d t : ℤ) (htr : a+d=334*t)
    (h : 67^2*(a+d)^2=334^2*(a*d-b^2)) : a*d-b^2=4489*t^2 := by
  rw [htr] at h
  nlinarith

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem stage7_gram_trace_divisibility (a b d : ℤ)
    (h : 67^2*(a+d)^2=334^2*(a*d-b^2)) : (a+d)%334=0 := by
  have hc : ∀ z : ZMod 334, (67 : ZMod 334)^2*z^2=0 → z=0 := by decide
  have hh := congrArg (fun z : ℤ => (z : ZMod 334)) h
  push_cast at hh
  -- push_cast may evaluate numeral powers before rewriting modulo 334.
  have hL : (67 : ZMod 334)^2 = (4489 : ZMod 334) := by decide
  have hRpow : (334 : ZMod 334)^2 = (111556 : ZMod 334) := by decide
  have hR : (111556 : ZMod 334) = 0 := by decide
  have hcast : (4489 : ZMod 334)*((a : ZMod 334)+(d : ZMod 334))^2 =
      (111556 : ZMod 334)*((a : ZMod 334)*(d : ZMod 334)-(b : ZMod 334)^2) := by
    simpa only [hL, hRpow] using hh
  rw [hR, zero_mul] at hcast
  have hz : (67 : ZMod 334)^2*((a+d : ℤ) : ZMod 334)^2=0 := by
    rw [hL]
    simpa only [Int.cast_add] using hcast
  have hdvd : (334:ℤ) ∣ a+d :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hc _ hz)
  omega

-- Primitive congruence certificates, not the full valuation induction.
theorem stage7_mod_three_square_zero :
    ∀ x y : ZMod 3, x^2+y^2=0 → x=0 ∧ y=0 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem stage7_mod_sixteen_square_eight :
    ∀ x y : ZMod 16, x^2+y^2=8 → x^2=4 ∧ y^2=4 := by decide

theorem stage7_positive_polynomial_final_obstruction (a b d : ℤ)
    (ha : 0≤a) (hb : 0≤b) (hd : 0≤d) (ht : a+d=20)
    (hbound : 17*(2*b)≤10*(a+d)) : a*d-b^2 ≠ -134 := by
  intro he
  have hh := stage7_nonnegative_target_rigidity a b d ha hb hd ht he
  omega

end IntegerRigidity

section GramEnsemble

def stage7_gramStep (q : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  (10*q.1,3*q.1+8*q.2.1,q.1+4*q.2.1+8*q.2.2)

def stage7_gramEnsemble : ℕ → ℚ × ℚ × ℚ
  | 0 => (1,0,1)
  | k+1 => stage7_gramStep (stage7_gramEnsemble k)

def stage7_gramClosed (k : ℕ) : ℚ × ℚ × ℚ :=
  (10^k, (3/2)*(10^k-8^k), (7/2)*10^k-(10+3*(k:ℚ))/4*8^k)

theorem stage7_gram_matrix_step (a b d : ℚ) :
    (stage6_affine (1:ℚ) 0 2).transpose * !![a,b;b,d] * stage6_affine 1 0 2 +
    (stage6_affine (3:ℚ) 1 2).transpose * !![a,b;b,d] * stage6_affine 3 1 2 =
      !![10*a,3*a+8*b;3*a+8*b,a+4*b+8*d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stage6_affine, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;> ring

theorem stage7_gram_closed_step (k : ℕ) :
    stage7_gramStep (stage7_gramClosed k)=stage7_gramClosed (k+1) := by
  apply Prod.ext
  · simp [stage7_gramStep,stage7_gramClosed,pow_succ] <;> ring
  · apply Prod.ext <;>
      simp [stage7_gramStep,stage7_gramClosed,pow_succ] <;> push_cast <;> ring

theorem stage7_gram_closed_form (k : ℕ) : stage7_gramEnsemble k=stage7_gramClosed k := by
  induction k with
  | zero => norm_num [stage7_gramEnsemble,stage7_gramClosed]
  | succ k ih => rw [stage7_gramEnsemble,ih,stage7_gram_closed_step]

theorem stage7_gram_normalized_trace (x k : ℚ) :
    x+(7/2*x-(10+3*k)/4)=(18*x-10-3*k)/4 := by ring

theorem stage7_gram_normalized_det (x k : ℚ) :
    x*(7/2*x-(10+3*k)/4)-(3/2*(x-1))^2 =
      (5*x^2+(8-3*k)*x-9)/4 := by ring

theorem stage7_gram_difference (x k : ℚ) :
    16*(20*((5*x^2+(8-3*k)*x-9)/4)-((18*x-10-3*k)/4)^2)=
    76*x^2+(1000-132*k)*x-720-(10+3*k)^2 := by ring

theorem stage7_exponential_linear_bound (k : ℕ) (hk : 16≤k) :
    2*(k:ℚ)≤(5/4:ℚ)^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 16≤k
    · have hi := ih h
      have h4 : (4:ℚ)≤k := by exact_mod_cast (show 4≤k by omega)
      rw [pow_succ]
      push_cast
      linarith
    · have he : k+1=16 := by omega
      rw [he]
      norm_num

theorem stage7_gram_tail_positive (x k : ℚ) (hk : 16≤k) (hx : 2*k≤x) :
    0<76*x^2+(1000-132*k)*x-720-(10+3*k)^2 := by
  have hx0 : 0≤x := by linarith
  have h1 := mul_nonneg hx0 (show 0≤x-2*k by linarith)
  have h2 := mul_nonneg (show 0≤x+2*k by linarith) (show 0≤x-2*k by linarith)
  have h3 := mul_nonneg (show 0≤k by linarith) (show 0≤x-2*k by linarith)
  nlinarith [sq_nonneg k]

theorem stage7_gram_uniform_difference (k : ℕ) :
    0<76*((5/4:ℚ)^k)^2+(1000-132*(k:ℚ))*(5/4)^k-720-(10+3*(k:ℚ))^2 := by
  by_cases h : 16≤k
  · exact stage7_gram_tail_positive _ _ (by exact_mod_cast h) (stage7_exponential_linear_bound k h)
  · have hk : k≤15 := by omega
    interval_cases k <;> norm_num

theorem stage7_gram_uniform_bound (k : ℕ) :
    let x : ℚ := (5/4)^k
    ((18*x-10-3*(k:ℚ))/4)^2 < 20*((5*x^2+(8-3*(k:ℚ))*x-9)/4) := by
  dsimp
  have h := stage7_gram_uniform_difference k
  rw [← stage7_gram_difference ((5/4:ℚ)^k) (k:ℚ)] at h
  linarith

theorem stage7_ensemble_target_exclusion (k : ℕ) :
    let x : ℚ := (5/4)^k
    67^2*((18*x-10-3*(k:ℚ))/4)^2 ≠ 334^2*((5*x^2+(8-3*(k:ℚ))*x-9)/4) := by
  dsimp
  have h := stage7_gram_uniform_bound k
  dsimp at h
  intro he
  have hd : 0<((5*((5/4:ℚ)^k)^2+(8-3*(k:ℚ))*(5/4)^k-9)/4) := by
    nlinarith [sq_nonneg ((18*(5/4:ℚ)^k-10-3*(k:ℚ))/4)]
  linarith

theorem stage7_gram_closed_normalization (k : ℕ) :
    let x : ℚ := (5/4)^k
    stage7_gramClosed k = (8^k*x,8^k*(3/2*(x-1)),8^k*(7/2*x-(10+3*(k:ℚ))/4)) := by
  dsimp [stage7_gramClosed]
  have h : (8:ℚ)^k*(5/4)^k=10^k := by rw [← mul_pow] <;> norm_num
  apply Prod.ext
  · exact h.symm
  · apply Prod.ext <;> dsimp <;> nlinarith only [h]

theorem stage7_gram_actual_uniform_bound (k : ℕ) :
    let q := stage7_gramEnsemble k
    (q.1+q.2.2)^2 < 20*(q.1*q.2.2-q.2.1^2) := by
  dsimp
  rw [stage7_gram_closed_form,stage7_gram_closed_normalization]
  dsimp
  let x : ℚ := (5/4)^k
  have h := stage7_gram_uniform_bound k
  change ((18*x-10-3*(k:ℚ))/4)^2 < 20*((5*x^2+(8-3*(k:ℚ))*x-9)/4) at h
  have hp : 0<((8:ℚ)^k)^2 := by positivity
  have hm := mul_lt_mul_of_pos_left h hp
  change ((8:ℚ)^k*x+8^k*(7/2*x-(10+3*(k:ℚ))/4))^2 <
    20*(8^k*x*(8^k*(7/2*x-(10+3*(k:ℚ))/4))-(8^k*(3/2*(x-1)))^2)
  nlinarith only [hm]

theorem stage7_limiting_trace : Matrix.trace (!![(1:ℚ),3/2;3/2,7/2] : Matrix (Fin 2) (Fin 2) ℚ)=9/2 := by
  norm_num [Matrix.trace,Fin.sum_univ_succ]

theorem stage7_limiting_det : Matrix.det (!![(1:ℚ),3/2;3/2,7/2] : Matrix (Fin 2) (Fin 2) ℚ)=5/4 := by
  norm_num [Matrix.det_fin_two]

theorem stage7_limiting_root (r : ℝ) (hr : r^2=61) :
    ((9+r)/4)^2-(9/2)*((9+r)/4)+5/4=0 := by nlinarith

end GramEnsemble

section ArithmeticMoments

theorem stage7_descent_threshold (a c d n : ℝ) (hd : 0<d) :
    (a*n+c)/d<n ↔ c<(d-a)*n := by
  rw [div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem stage7_moment_odd_extension (N U V d : ℤ) :
    (9*V+6*d*U+d^2*N)*N-(3*U+d*N)^2=9*(N*V-U^2) := by ring

theorem stage7_aggregate_gram_det (N U V a d : ℤ) :
    (N*a^2)*(V+N*d^2)-(a*U)^2=a^2*(N^2*d^2+N*V-U^2) := by ring

theorem stage7_dispersion_pair (x y : ℤ) : 2*(x^2+y^2)-(x+y)^2=(x-y)^2 := by ring

theorem stage7_dispersion_mod_four (N U V r u v : ℤ)
    (hu : U=N*r+4*u) (hv : V=N*r^2+8*r*u+16*v) :
    N*V-U^2=16*(N*v-u^2) := by rw [hu,hv]; ring

theorem stage7_first_count_unique (k s t : ℕ)
    (hs : (2:ℕ)^k≤2*3^s ∧ 3^s<2^k)
    (ht : (2:ℕ)^k≤2*3^t ∧ 3^t<2^k) : s=t := by
  by_contra h
  rcases lt_or_gt_of_ne h with hst|hts
  · have hpow : (3:ℕ)^(s+1)≤3^t := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hpow
    omega
  · have hpow : (3:ℕ)^(t+1)≤3^s := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hpow
    omega

theorem stage7_endpoint_ratio_tail (A B D : ℝ) (hA : 0<A) (hD : 0<D)
    (h : 25*A<D) : (A+D)^2>25*(A*D-B^2) := by
  have hh := mul_pos hD (sub_pos.mpr h)
  nlinarith [sq_nonneg A,sq_nonneg B,mul_pos hA hD]

theorem stage7_endpoint_decay_certificate : (2:ℚ)*(29/30)^116<1/25 := by norm_num

end ArithmeticMoments

section ConditionedAmplitudes

theorem stage7_fixed_count_conditioning (p q z w : ℝ)
    (hz : z≠0) (hw : w≠0) (hq : q=w*p) : q/(w*z)=p/z := by
  rw [hq]
  field_simp <;> ring

theorem stage7_branch_probability_norm : (1/4:ℚ)+3/4=1 := by norm_num

theorem stage7_likelihood_ratio_identity (k s : ℕ) :
    ((3:ℚ)^s/4^k)/(1/2^k)=3^s/2^k := by
  have h2 : (2:ℚ)^k≠0 := pow_ne_zero _ (by norm_num)
  have h4 : (4:ℚ)^k=(2:ℚ)^k*(2:ℚ)^k := by rw [← mul_pow] <;> norm_num
  rw [h4]
  field_simp <;> ring

theorem stage7_fractional_overlap_square :
    ((1+Real.sqrt 3)/(2*Real.sqrt 2))^2=(2+Real.sqrt 3)/4 := by
  have h2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have h3 := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hn : Real.sqrt 2≠0 := by positivity
  rw [div_pow, mul_pow, h2]
  nlinarith

theorem stage7_conditioned_numerator_square (x y : ℝ) :
    (x+y*Real.sqrt 3)^2=x^2+3*y^2+2*x*y*Real.sqrt 3 := by
  have h := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  calc
    (x+y*Real.sqrt 3)^2=x^2+y^2*(Real.sqrt 3)^2+2*x*y*Real.sqrt 3 := by ring
    _ = _ := by rw [h]; ring

theorem stage7_sqrt_three_irrational : Irrational (Real.sqrt 3) := by
  simpa using (show Nat.Prime 3 by decide).irrational_sqrt

theorem stage7_mixed_overlap_exclusion (x y n z : ℚ)
    (hx : x≠0) (hy : y≠0) (hn : n≠0) :
    ((x:ℝ)+(y:ℝ)*Real.sqrt 3)^2/(n:ℝ) ≠ (z:ℝ) := by
  intro h
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn
  have hxy : (2:ℚ)*x*y≠0 := mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
  have hrr : (2:ℝ)*(x:ℝ)*(y:ℝ)≠0 := by exact_mod_cast hxy
  have he := (div_eq_iff hnr).mp h
  rw [stage7_conditioned_numerator_square] at he
  have hq : (((z*n-x^2-3*y^2)/(2*x*y):ℚ):ℝ)=Real.sqrt 3 := by
    push_cast
    apply (div_eq_iff hrr).2
    nlinarith only [he]
  exact stage7_sqrt_three_irrational ⟨_,hq⟩

theorem stage7_projector_invariant_exclusion (x y n a b : ℚ)
    (hx : x≠0) (hy : y≠0) (hn : n≠0) (ha : a≠0) (hb : b≠0) :
    4489*((a:ℝ)+(b:ℝ))^2 ≠
      111556*(a:ℝ)*(b:ℝ)*(1-((x:ℝ)+(y:ℝ)*Real.sqrt 3)^2/(n:ℝ)) := by
  intro h
  have hq : (111556:ℚ)*a*b≠0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
  have hr : (111556:ℝ)*(a:ℝ)*(b:ℝ)≠0 := by exact_mod_cast hq
  apply stage7_mixed_overlap_exclusion x y n (1-4489*(a+b)^2/(111556*a*b)) hx hy hn
  push_cast
  have he : 4489*((a:ℝ)+(b:ℝ))^2/(111556*(a:ℝ)*(b:ℝ)) =
      1-((x:ℝ)+(y:ℝ)*Real.sqrt 3)^2/(n:ℝ) := by
    apply (div_eq_iff hr).2
    rw [h] <;> ring
  linarith

theorem stage7_projector_span_invariants (a b c : ℝ) :
    (a+b*c^2)*(b*(1-c^2))-(b*c)^2*(1-c^2)=a*b*(1-c^2) := by ring

theorem stage7_equal_projector_rank_one (a b : ℝ) :
    Matrix.det (!![a+b,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ)=0 := by
  simp [Matrix.det_fin_two]

theorem stage7_target_overlap_square (c : ℚ) (h : 4489*4=111556*(1-c)) :
    c=23400/27889 := by linarith

end ConditionedAmplitudes

#print axioms stage7_target_circle
#print axioms stage7_mod_three_rigidity
#print axioms stage7_sum_squares_classification
#print axioms stage7_symmetric_integer_classification
#print axioms stage7_nonnegative_target_rigidity
#print axioms stage7_gram_spectral_circle
#print axioms stage7_gram_scale_identity
#print axioms stage7_gram_trace_divisibility
#print axioms stage7_mod_three_square_zero
#print axioms stage7_mod_sixteen_square_eight
#print axioms stage7_positive_polynomial_final_obstruction
#print axioms stage7_gram_matrix_step
#print axioms stage7_gram_closed_step
#print axioms stage7_gram_closed_form
#print axioms stage7_gram_normalized_trace
#print axioms stage7_gram_normalized_det
#print axioms stage7_gram_difference
#print axioms stage7_exponential_linear_bound
#print axioms stage7_gram_tail_positive
#print axioms stage7_gram_uniform_difference
#print axioms stage7_gram_uniform_bound
#print axioms stage7_ensemble_target_exclusion
#print axioms stage7_gram_closed_normalization
#print axioms stage7_gram_actual_uniform_bound
#print axioms stage7_limiting_trace
#print axioms stage7_limiting_det
#print axioms stage7_limiting_root
#print axioms stage7_descent_threshold
#print axioms stage7_moment_odd_extension
#print axioms stage7_aggregate_gram_det
#print axioms stage7_dispersion_pair
#print axioms stage7_dispersion_mod_four
#print axioms stage7_first_count_unique
#print axioms stage7_endpoint_ratio_tail
#print axioms stage7_endpoint_decay_certificate
#print axioms stage7_fixed_count_conditioning
#print axioms stage7_branch_probability_norm
#print axioms stage7_likelihood_ratio_identity
#print axioms stage7_fractional_overlap_square
#print axioms stage7_conditioned_numerator_square
#print axioms stage7_sqrt_three_irrational
#print axioms stage7_mixed_overlap_exclusion
#print axioms stage7_projector_invariant_exclusion
#print axioms stage7_projector_span_invariants
#print axioms stage7_equal_projector_rank_one
#print axioms stage7_target_overlap_square

end CollatzRunyan.LeptonSpectral

/-! Stage 8: finite forward and inverse affine moments, covariance determinants,
prime-square obstructions and normalized correction identities.
Analytic probability and Mellin results are not claimed as formalized here. -/
namespace CollatzRunyan.LeptonSpectral

section MomentTransport

-- Pointwise weighted identities: taking expectations gives moment transport.
theorem stage8_forward_mean_a (a : ℚ) :
    (a/2+3*a/2)/2=a := by ring

theorem stage8_forward_mean_b (b : ℚ) :
    (b/2+(3*b/2+1/2))/2=b+1/4 := by ring

theorem stage8_forward_second_a (a : ℚ) :
    ((a/2)^2+(3*a/2)^2)/2=5/4*a^2 := by ring

theorem stage8_forward_second_ab (a b : ℚ) :
    ((a/2)*(b/2)+(3*a/2)*(3*b/2+1/2))/2=5/4*a*b+3/8*a := by ring

theorem stage8_forward_second_b (b : ℚ) :
    ((b/2)^2+(3*b/2+1/2)^2)/2=5/4*b^2+3/4*b+1/8 := by ring

theorem stage8_inverse_mean_r (r : ℚ) :
    1/4*(2*r)+3/4*(2*r/3)=r := by ring

theorem stage8_inverse_mean_z (r z : ℚ) :
    1/4*z+3/4*(z+r/3)=z+r/4 := by ring

theorem stage8_inverse_second_r (r : ℚ) :
    1/4*(2*r)^2+3/4*(2*r/3)^2=4/3*r^2 := by ring

theorem stage8_inverse_second_rz (r z : ℚ) :
    1/4*(2*r)*z+3/4*(2*r/3)*(z+r/3)=r*z+r^2/6 := by ring

theorem stage8_inverse_second_z (r z : ℚ) :
    1/4*z^2+3/4*(z+r/3)^2=z^2+r*z/2+r^2/12 := by ring

-- Common first-moment recursion, once the first coordinate mean is 1.
def stage8_mean : ℕ → ℚ × ℚ
  | 0 => (1,0)
  | k+1 => ((stage8_mean k).1,(stage8_mean k).2+(stage8_mean k).1/4)

theorem stage8_mean_closed (k : ℕ) : stage8_mean k=(1,(k:ℚ)/4) := by
  induction k with
  | zero => norm_num [stage8_mean]
  | succ k ih =>
    rw [stage8_mean,ih]
    apply Prod.ext
    · rfl
    · simp <;> ring

def stage8_forwardStep (k : ℕ) (q : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  (5/4*q.1,5/4*q.2.1+3/8,5/4*q.2.2+3*(k:ℚ)/16+1/8)

def stage8_forwardMoments : ℕ → ℚ × ℚ × ℚ
  | 0 => (1,0,0)
  | k+1 => stage8_forwardStep k (stage8_forwardMoments k)

def stage8_forwardClosed (k : ℕ) : ℚ × ℚ × ℚ :=
  ((5/4)^k,3/2*((5/4)^k-1),7/2*((5/4)^k-1)-3*(k:ℚ)/4)

theorem stage8_forward_closed_step (k : ℕ) :
    stage8_forwardStep k (stage8_forwardClosed k)=stage8_forwardClosed (k+1) := by
  apply Prod.ext
  · simp [stage8_forwardStep,stage8_forwardClosed,pow_succ] <;> ring
  · apply Prod.ext <;>
      simp [stage8_forwardStep,stage8_forwardClosed,pow_succ] <;> push_cast <;> ring

theorem stage8_forward_moments_closed (k : ℕ) :
    stage8_forwardMoments k=stage8_forwardClosed k := by
  induction k with
  | zero => norm_num [stage8_forwardMoments,stage8_forwardClosed]
  | succ k ih => rw [stage8_forwardMoments,ih,stage8_forward_closed_step]

def stage8_inverseStep (q : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  (4/3*q.1,q.2.1+q.1/6,q.2.2+q.2.1/2+q.1/12)

def stage8_inverseMoments : ℕ → ℚ × ℚ × ℚ
  | 0 => (1,0,0)
  | k+1 => stage8_inverseStep (stage8_inverseMoments k)

def stage8_inverseClosed (k : ℕ) : ℚ × ℚ × ℚ :=
  ((4/3)^k,((4/3)^k-1)/2,(4/3)^k-1-(k:ℚ)/4)

theorem stage8_inverse_closed_step (k : ℕ) :
    stage8_inverseStep (stage8_inverseClosed k)=stage8_inverseClosed (k+1) := by
  apply Prod.ext
  · simp [stage8_inverseStep,stage8_inverseClosed,pow_succ] <;> ring
  · apply Prod.ext <;>
      simp [stage8_inverseStep,stage8_inverseClosed,pow_succ] <;> push_cast <;> ring

theorem stage8_inverse_moments_closed (k : ℕ) :
    stage8_inverseMoments k=stage8_inverseClosed k := by
  induction k with
  | zero => norm_num [stage8_inverseMoments,stage8_inverseClosed]
  | succ k ih => rw [stage8_inverseMoments,ih,stage8_inverse_closed_step]

end MomentTransport

section Covariance

def stage8_center (q : ℚ × ℚ × ℚ) (k : ℕ) : ℚ × ℚ × ℚ :=
  (q.1-1,q.2.1-(k:ℚ)/4,q.2.2-((k:ℚ)/4)^2)

def stage8_forwardCov (k : ℕ) := stage8_center (stage8_forwardMoments k) k

def stage8_inverseCov (k : ℕ) := stage8_center (stage8_inverseMoments k) k

theorem stage8_forward_cov_closed (k : ℕ) :
    let x : ℚ := (5/4)^k
    stage8_forwardCov k=(x-1,3/2*(x-1)-(k:ℚ)/4,
      7/2*(x-1)-3*(k:ℚ)/4-(k:ℚ)^2/16) := by
  dsimp [stage8_forwardCov]
  rw [stage8_forward_moments_closed]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> simp [stage8_center,stage8_forwardClosed] <;> ring

theorem stage8_inverse_cov_closed (k : ℕ) :
    let x : ℚ := (4/3)^k
    stage8_inverseCov k=(x-1,(x-1)/2-(k:ℚ)/4,
      x-1-(k:ℚ)/4-(k:ℚ)^2/16) := by
  dsimp [stage8_inverseCov]
  rw [stage8_inverse_moments_closed]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> simp [stage8_center,stage8_inverseClosed] <;> ring

theorem stage8_forward_trace (x k : ℚ) :
    (x-1)+(7/2*(x-1)-3*k/4-k^2/16)=9/2*(x-1)-3*k/4-k^2/16 := by ring

theorem stage8_inverse_trace (x k : ℚ) :
    (x-1)+(x-1-k/4-k^2/16)=2*(x-1)-k/4-k^2/16 := by ring

theorem stage8_forward_cov_det (x k : ℚ) :
    (x-1)*(7/2*(x-1)-3*k/4-k^2/16)-(3/2*(x-1)-k/4)^2=
      5/4*(x-1)^2-k^2*x/16 := by ring

theorem stage8_inverse_cov_det (x k : ℚ) :
    (x-1)*(x-1-k/4-k^2/16)-((x-1)/2-k/4)^2=
      3/4*(x-1)^2-k^2*x/16 := by ring

-- Integral numerator matrices, scaled by 16 times the denominator power.
def stage8_forwardInt (k : ℕ) : ℤ × ℤ × ℤ :=
  let p : ℤ := 5^k; let q : ℤ := 4^k
  (16*(p-q),24*(p-q)-4*(k:ℤ)*q,56*(p-q)-12*(k:ℤ)*q-(k:ℤ)^2*q)

def stage8_inverseInt (k : ℕ) : ℤ × ℤ × ℤ :=
  let p : ℤ := 4^k; let q : ℤ := 3^k
  (16*(p-q),8*(p-q)-4*(k:ℤ)*q,16*(p-q)-4*(k:ℤ)*q-(k:ℤ)^2*q)

def stage8_forwardIntDet (k : ℕ) : ℤ :=
  320*((5:ℤ)^k-4^k)^2-16*(k:ℤ)^2*5^k*4^k

def stage8_inverseIntDet (k : ℕ) : ℤ :=
  192*((4:ℤ)^k-3^k)^2-16*(k:ℤ)^2*4^k*3^k

theorem stage8_forward_int_det (k : ℕ) :
    let q := stage8_forwardInt k
    q.1*q.2.2-q.2.1^2=stage8_forwardIntDet k := by
  dsimp [stage8_forwardInt,stage8_forwardIntDet]
  ring

theorem stage8_inverse_int_det (k : ℕ) :
    let q := stage8_inverseInt k
    q.1*q.2.2-q.2.1^2=stage8_inverseIntDet k := by
  dsimp [stage8_inverseInt,stage8_inverseIntDet]
  ring

-- Generic scale transport, with p=q*x proved below for each horizon.
theorem stage8_forward_scaled_components (p q x k : ℚ) (h : p=q*x) :
    (16*(p-q),24*(p-q)-4*k*q,56*(p-q)-12*k*q-k^2*q) =
    (16*q*(x-1),16*q*(3/2*(x-1)-k/4),16*q*(7/2*(x-1)-3*k/4-k^2/16)) := by
  rw [h]
  apply Prod.ext
  · ring
  · apply Prod.ext <;> ring

theorem stage8_inverse_scaled_components (p q x k : ℚ) (h : p=q*x) :
    (16*(p-q),8*(p-q)-4*k*q,16*(p-q)-4*k*q-k^2*q) =
    (16*q*(x-1),16*q*((x-1)/2-k/4),16*q*(x-1-k/4-k^2/16)) := by
  rw [h]
  apply Prod.ext
  · ring
  · apply Prod.ext <;> ring

theorem stage8_forward_power_scale (k : ℕ) : (4:ℚ)^k*(5/4)^k=5^k := by
  rw [← mul_pow] <;> norm_num

theorem stage8_inverse_power_scale (k : ℕ) : (3:ℚ)^k*(4/3)^k=4^k := by
  rw [← mul_pow] <;> norm_num

theorem stage8_forward_det_scale (k : ℕ) :
    ((stage8_forwardIntDet k : ℤ) : ℚ) =
      (16*(4:ℚ)^k)^2*(5/4*((5/4:ℚ)^k-1)^2-(k:ℚ)^2*(5/4)^k/16) := by
  unfold stage8_forwardIntDet
  push_cast
  have h := stage8_forward_power_scale k
  rw [← h]
  ring

theorem stage8_inverse_det_scale (k : ℕ) :
    ((stage8_inverseIntDet k : ℤ) : ℚ) =
      (16*(3:ℚ)^k)^2*(3/4*((4/3:ℚ)^k-1)^2-(k:ℚ)^2*(4/3)^k/16) := by
  unfold stage8_inverseIntDet
  push_cast
  have h := stage8_inverse_power_scale k
  rw [← h]
  ring

end Covariance

section ModularExclusion

-- Explicit modular numerals avoid reliance on prime typeclass synthesis.
theorem stage8_forward_residue_power (k : ℕ) :
    (320:ZMod 25)*((4:ZMod 25)^k)^2=20 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ (4 : ZMod 25) k]
    calc
      (320:ZMod 25)*(4^k*4)^2 = (320*((4:ZMod 25)^k)^2)*4^2 := by ring
      _ = 20 := by rw [ih] <;> decide

theorem stage8_inverse_residue_power (k : ℕ) :
    (192:ZMod 9)*((4:ZMod 9)^k)^2=3 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ (4 : ZMod 9) k]
    calc
      (192:ZMod 9)*(4^k*4)^2 = (192*((4:ZMod 9)^k)^2)*4^2 := by ring
      _ = 3 := by rw [ih] <;> decide

theorem stage8_forward_det_mod25 (k : ℕ) (hk : 2≤k) :
    ((stage8_forwardIntDet k : ℤ) : ZMod 25)=20 := by
  have he : k=(k-2)+2 := by omega
  have hz : (5:ZMod 25)^k=0 := by
    rw [he,pow_add,show (5:ZMod 25)^2=0 by decide,mul_zero]
  unfold stage8_forwardIntDet
  push_cast
  change (320:ZMod 25)*(5^k-4^k)^2-16*(k:ZMod 25)^2*5^k*4^k=20
  rw [hz]
  simp only [zero_sub,neg_sq,mul_zero,zero_mul,sub_zero]
  exact stage8_forward_residue_power k

theorem stage8_inverse_det_mod9 (k : ℕ) (hk : 2≤k) :
    ((stage8_inverseIntDet k : ℤ) : ZMod 9)=3 := by
  have he : k=(k-2)+2 := by omega
  have hz : (3:ZMod 9)^k=0 := by
    rw [he,pow_add,show (3:ZMod 9)^2=0 by decide,mul_zero]
  unfold stage8_inverseIntDet
  push_cast
  change (192:ZMod 9)*(4^k-3^k)^2-16*(k:ZMod 9)^2*4^k*3^k=3
  rw [hz]
  simp only [sub_zero,mul_zero]
  exact stage8_inverse_residue_power k

theorem stage8_forward_square_certificate : ∀ t : ZMod 25, t^2≠20 := by decide

theorem stage8_inverse_square_certificate : ∀ t : ZMod 9, t^2≠3 := by decide

theorem stage8_forward_det_nonsquare (k : ℕ) (hk : 2≤k) (t : ℤ) :
    t^2≠stage8_forwardIntDet k := by
  intro h
  have hh : ((t^2 : ℤ) : ZMod 25) = (stage8_forwardIntDet k : ZMod 25) :=
    congrArg (fun z : ℤ => (z : ZMod 25)) h
  push_cast at hh
  rw [stage8_forward_det_mod25 k hk] at hh
  exact stage8_forward_square_certificate _ hh

theorem stage8_inverse_det_nonsquare (k : ℕ) (hk : 2≤k) (t : ℤ) :
    t^2≠stage8_inverseIntDet k := by
  intro h
  have hh : ((t^2 : ℤ) : ZMod 9) = (stage8_inverseIntDet k : ZMod 9) :=
    congrArg (fun z : ℤ => (z : ZMod 9)) h
  push_cast at hh
  rw [stage8_inverse_det_mod9 k hk] at hh
  exact stage8_inverse_square_certificate _ hh

theorem stage8_forward_target_certificate :
    ∀ t : ZMod 25, (4489:ZMod 25)*t^2≠111556*20 := by decide

theorem stage8_inverse_target_certificate :
    ∀ t : ZMod 9, (4489:ZMod 9)*t^2≠111556*3 := by decide

theorem stage8_forward_target_exclusion (k : ℕ) (hk : 2≤k) (t : ℤ) :
    4489*t^2≠111556*stage8_forwardIntDet k := by
  intro h
  have hh := congrArg (fun z : ℤ => (z : ZMod 25)) h
  push_cast at hh
  rw [stage8_forward_det_mod25 k hk] at hh
  exact stage8_forward_target_certificate _ hh

theorem stage8_inverse_target_exclusion (k : ℕ) (hk : 2≤k) (t : ℤ) :
    4489*t^2≠111556*stage8_inverseIntDet k := by
  intro h
  have hh := congrArg (fun z : ℤ => (z : ZMod 9)) h
  push_cast at hh
  rw [stage8_inverse_det_mod9 k hk] at hh
  exact stage8_inverse_target_certificate _ hh

theorem stage8_forward_integer_cov_exclusion (k : ℕ) (hk : 2≤k) :
    let q := stage8_forwardInt k
    4489*(q.1+q.2.2)^2≠111556*(q.1*q.2.2-q.2.1^2) := by
  change 4489*((stage8_forwardInt k).1+(stage8_forwardInt k).2.2)^2 ≠
    111556*((stage8_forwardInt k).1*(stage8_forwardInt k).2.2-(stage8_forwardInt k).2.1^2)
  rw [show (stage8_forwardInt k).1*(stage8_forwardInt k).2.2-(stage8_forwardInt k).2.1^2 =
    stage8_forwardIntDet k from stage8_forward_int_det k]
  exact stage8_forward_target_exclusion k hk _

theorem stage8_inverse_integer_cov_exclusion (k : ℕ) (hk : 2≤k) :
    let q := stage8_inverseInt k
    4489*(q.1+q.2.2)^2≠111556*(q.1*q.2.2-q.2.1^2) := by
  change 4489*((stage8_inverseInt k).1+(stage8_inverseInt k).2.2)^2 ≠
    111556*((stage8_inverseInt k).1*(stage8_inverseInt k).2.2-(stage8_inverseInt k).2.1^2)
  rw [show (stage8_inverseInt k).1*(stage8_inverseInt k).2.2-(stage8_inverseInt k).2.1^2 =
    stage8_inverseIntDet k from stage8_inverse_int_det k]
  exact stage8_inverse_target_exclusion k hk _

end ModularExclusion

section AffineCorrection

def stage8_invBranch (odd : Bool) (p : ℚ × ℚ) : ℚ × ℚ :=
  if odd then (2*p.1/3,p.2+p.1/3) else (2*p.1,p.2)

def stage8_invWord : List Bool → ℚ × ℚ
  | [] => (1,0)
  | b::w => stage8_invBranch b (stage8_invWord w)

-- The word recursion adds the head after the tail. Reversing lists gives
-- chronological order; the invariant holds for either convention.
theorem stage8_correction_branch_pos (b : Bool) (p : ℚ × ℚ)
    (hr : 0<p.1) (hz : 0≤p.2) :
    0<(stage8_invBranch b p).1 ∧ 0≤(stage8_invBranch b p).2 := by
  cases b with
  | false =>
    change 0<2*p.1 ∧ 0≤p.2
    constructor <;> linarith
  | true =>
    change 0<2*p.1/3 ∧ 0≤p.2+p.1/3
    constructor <;> linarith

theorem stage8_correction_branch_sum (b : Bool) (p : ℚ × ℚ)
    (hr : 0≤p.1) : p.1+p.2≤(stage8_invBranch b p).1+(stage8_invBranch b p).2 := by
  cases b with
  | false =>
    change p.1+p.2≤2*p.1+p.2
    linarith
  | true =>
    change p.1+p.2≤2*p.1/3+(p.2+p.1/3)
    linarith

theorem stage8_correction_word_invariant (w : List Bool) :
    0<(stage8_invWord w).1 ∧ 0≤(stage8_invWord w).2 ∧
      1≤(stage8_invWord w).1+(stage8_invWord w).2 := by
  induction w with
  | nil => norm_num [stage8_invWord]
  | cons b w ih =>
    rw [stage8_invWord]
    have hp := stage8_correction_branch_pos b (stage8_invWord w) ih.1 ih.2.1
    exact ⟨hp.1,hp.2,le_trans ih.2.2 (stage8_correction_branch_sum b _ (le_of_lt ih.1))⟩

theorem stage8_normalized_even (a b : ℚ) (ha : a≠0) :
    (1/(a/2),(b/2)/(a/2))=(2/a,b/a) := by
  apply Prod.ext <;> dsimp <;> field_simp [ha] <;> ring

theorem stage8_normalized_odd (a b : ℚ) (ha : a≠0) :
    (1/(3*a/2),(3*b/2+1/2)/(3*a/2))=(2/(3*a),b/a+1/(3*a)) := by
  apply Prod.ext <;> dsimp <;> field_simp [ha] <;> ring

theorem stage8_shifted_perpetuity_even (z : ℚ) : 2*(z+1)-1=1+2*z := by ring

theorem stage8_shifted_perpetuity_odd (z : ℚ) : (1+2*(z+1))/3-1=2*z/3 := by ring

theorem stage8_branch_moment_zero : (1/4:ℚ)*2^0+3/4*(2/3)^0=1 := by norm_num

theorem stage8_branch_moment_one : (1/4:ℚ)*2+3/4*(2/3)=1 := by norm_num

theorem stage8_branch_moment_two : (1/4:ℚ)*2^2+3/4*(2/3)^2=4/3 := by norm_num

-- Pure algebraic duality: positive square roots of the branch multipliers.
theorem stage8_fractional_duality (u v : ℝ) :
    (u/2+v/2)/2=u/4+3/4*(v/3) := by ring

theorem stage8_fractional_duality_square (u v : ℝ) (hu : u^2=2) (hv : v^2=6)
    (huv : u*v=2*Real.sqrt 3) : ((u+v)/4)^2=(2+Real.sqrt 3)/4 := by
  nlinarith only [hu,hv,huv]

theorem stage8_affine_residue_certificate (n c a d y : ℤ)
    (h : d*y=a*n+c) : d ∣ a*n+c := ⟨y,h.symm⟩

-- Matrix invariants for the two limiting matrices; no limit theorem here.
theorem stage8_forward_limit_invariants :
    (1:ℚ)+7/2=9/2 ∧ (1:ℚ)*(7/2)-(3/2)^2=5/4 := by norm_num

theorem stage8_inverse_limit_invariants :
    (1:ℚ)+1=2 ∧ (1:ℚ)*1-(1/2)^2=3/4 := by norm_num

theorem stage8_inverse_limit_roots (z : ℚ) :
    z^2-2*z+3/4=(z-3/2)*(z-1/2) := by ring

theorem stage8_congruence_det (L G : Matrix (Fin 2) (Fin 2) ℚ) :
    (L*G*L.transpose).det=L.det^2*G.det := by
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  ring

end AffineCorrection

#print axioms stage8_forward_mean_a
#print axioms stage8_forward_mean_b
#print axioms stage8_forward_second_a
#print axioms stage8_forward_second_ab
#print axioms stage8_forward_second_b
#print axioms stage8_inverse_mean_r
#print axioms stage8_inverse_mean_z
#print axioms stage8_inverse_second_r
#print axioms stage8_inverse_second_rz
#print axioms stage8_inverse_second_z
#print axioms stage8_mean_closed
#print axioms stage8_forward_closed_step
#print axioms stage8_forward_moments_closed
#print axioms stage8_inverse_closed_step
#print axioms stage8_inverse_moments_closed
#print axioms stage8_forward_cov_closed
#print axioms stage8_inverse_cov_closed
#print axioms stage8_forward_trace
#print axioms stage8_inverse_trace
#print axioms stage8_forward_cov_det
#print axioms stage8_inverse_cov_det
#print axioms stage8_forward_int_det
#print axioms stage8_inverse_int_det
#print axioms stage8_forward_scaled_components
#print axioms stage8_inverse_scaled_components
#print axioms stage8_forward_power_scale
#print axioms stage8_inverse_power_scale
#print axioms stage8_forward_det_scale
#print axioms stage8_inverse_det_scale
#print axioms stage8_forward_residue_power
#print axioms stage8_inverse_residue_power
#print axioms stage8_forward_det_mod25
#print axioms stage8_inverse_det_mod9
#print axioms stage8_forward_square_certificate
#print axioms stage8_inverse_square_certificate
#print axioms stage8_forward_det_nonsquare
#print axioms stage8_inverse_det_nonsquare
#print axioms stage8_forward_target_certificate
#print axioms stage8_inverse_target_certificate
#print axioms stage8_forward_target_exclusion
#print axioms stage8_inverse_target_exclusion
#print axioms stage8_forward_integer_cov_exclusion
#print axioms stage8_inverse_integer_cov_exclusion
#print axioms stage8_correction_branch_pos
#print axioms stage8_correction_branch_sum
#print axioms stage8_correction_word_invariant
#print axioms stage8_normalized_even
#print axioms stage8_normalized_odd
#print axioms stage8_shifted_perpetuity_even
#print axioms stage8_shifted_perpetuity_odd
#print axioms stage8_branch_moment_zero
#print axioms stage8_branch_moment_one
#print axioms stage8_branch_moment_two
#print axioms stage8_fractional_duality
#print axioms stage8_fractional_duality_square
#print axioms stage8_affine_residue_certificate
#print axioms stage8_forward_limit_invariants
#print axioms stage8_inverse_limit_invariants
#print axioms stage8_inverse_limit_roots
#print axioms stage8_congruence_det

end CollatzRunyan.LeptonSpectral

/-! Stage 9: invariant coefficients, positive Dirichlet defects, Basel sum
reformulation, binary cylinders, and normalized affine residue certificates.
The shortcut and cylinder algebra are adapted from the earlier verified
Geometric Spectral Stage 1; these are overlapping research results, not a
claim of additional independent discoveries. -/
namespace CollatzRunyan.LeptonSpectral

section ZetaAdelic
open scoped BigOperators

def stage9_step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3*n+1)/2

def stage9_orbit : ℕ → ℕ → ℕ
  | 0, n => n
  | k+1, n => stage9_orbit k (stage9_step n)

def stage9_parity (n : ℕ) : ℕ := n % 2

def stage9_count : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, n => stage9_count k (stage9_step n) + stage9_parity n

def stage9_basin (n : ℕ) : Prop := ∃ k, stage9_orbit k n = 1

def stage9_converges : Prop := ∀ n : ℕ, 0 < n → stage9_basin n

theorem stage9_step_even (j : ℕ) : stage9_step (2*j) = j := by
  have h : (2*j)%2=0 := by omega
  simp only [stage9_step, if_pos h]
  omega

theorem stage9_step_odd (j : ℕ) : stage9_step (2*j+1) = 3*j+2 := by
  have h : (2*j+1)%2≠0 := by omega
  simp only [stage9_step, if_neg h]
  omega

theorem stage9_step_pos (n : ℕ) (hn : 0<n) : 0<stage9_step n := by
  unfold stage9_step
  split <;> omega

theorem stage9_step_one : stage9_step 1 = 2 := by decide

theorem stage9_step_two : stage9_step 2 = 1 := by decide

theorem stage9_orbit_pos (k n : ℕ) (hn : 0<n) : 0<stage9_orbit k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih _ (stage9_step_pos n hn)

theorem stage9_orbit_add (k l n : ℕ) :
    stage9_orbit (k+l) n = stage9_orbit l (stage9_orbit k n) := by
  induction k generalizing n with
  | zero => simp [stage9_orbit]
  | succ k ih =>
    rw [Nat.succ_add]
    change stage9_orbit (k+l) (stage9_step n) = stage9_orbit l (stage9_orbit k (stage9_step n))
    exact ih (stage9_step n)

theorem stage9_basin_step (n : ℕ) : stage9_basin (stage9_step n) ↔ stage9_basin n := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k+1,hk⟩
  · rintro ⟨k,hk⟩
    cases k with
    | zero =>
      change n=1 at hk
      subst n
      exact ⟨1, by decide⟩
    | succ k => exact ⟨k,hk⟩

theorem stage9_basin_orbit (k n : ℕ) :
    stage9_basin (stage9_orbit k n) ↔ stage9_basin n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => exact (ih (stage9_step n)).trans (stage9_basin_step n)

theorem stage9_basin_one : stage9_basin 1 := ⟨0,rfl⟩

-- Coefficient fixed points of composition by the shortcut map.
def stage9_fixed {K : Type*} (f : ℕ → K) : Prop :=
  ∀ n, 0<n → f (stage9_step n) = f n

theorem stage9_fixed_orbit {K : Type*} (f : ℕ → K) (hf : stage9_fixed f)
    (k n : ℕ) (hn : 0<n) : f (stage9_orbit k n) = f n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => exact (ih _ (stage9_step_pos n hn)).trans (hf n hn)

theorem stage9_fixed_on_basin {K : Type*} (f : ℕ → K) (hf : stage9_fixed f)
    (n : ℕ) (hn : 0<n) (hb : stage9_basin n) : f n = f 1 := by
  obtain ⟨k,hk⟩ := hb
  have h := stage9_fixed_orbit f hf k n hn
  rw [hk] at h
  exact h.symm

noncomputable def stage9_indicator (n : ℕ) : ℝ := by
  classical
  exact if stage9_basin n then 0 else 1

theorem stage9_indicator_fixed : stage9_fixed stage9_indicator := by
  classical
  intro n _
  by_cases h : stage9_basin n
  · have h' := (stage9_basin_step n).2 h
    simp [stage9_indicator,h,h']
  · have h' : ¬ stage9_basin (stage9_step n) := fun hh => h ((stage9_basin_step n).1 hh)
    simp [stage9_indicator,h,h']

theorem stage9_indicator_bounds (n : ℕ) : 0 ≤ stage9_indicator n ∧ stage9_indicator n ≤ 1 := by
  classical
  by_cases h : stage9_basin n <;> simp [stage9_indicator,h]

theorem stage9_indicator_zero (n : ℕ) : stage9_indicator n = 0 ↔ stage9_basin n := by
  classical
  by_cases h : stage9_basin n <;> simp [stage9_indicator,h]

theorem stage9_fixed_unique_iff : stage9_converges ↔
    (∀ f : ℕ → ℝ, stage9_fixed f → (∀ n, 0≤f n ∧ f n≤1) →
      ∀ n, 0<n → f n=f 1) := by
  constructor
  · intro h f hf _ n hn
    exact stage9_fixed_on_basin f hf n hn (h n hn)
  · intro h n hn
    have he := h stage9_indicator stage9_indicator_fixed stage9_indicator_bounds n hn
    rw [(stage9_indicator_zero 1).2 stage9_basin_one] at he
    exact (stage9_indicator_zero n).1 he

-- A positive summable weight, zero at the unused index 0.
noncomputable def stage9_basinWeight (w : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if stage9_basin n then w n else 0

noncomputable def stage9_missingWeight (w : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if stage9_basin n then 0 else w n

theorem stage9_weight_partition (w : ℕ → ℝ) (n : ℕ) :
    stage9_basinWeight w n + stage9_missingWeight w n = w n := by
  classical
  by_cases h : stage9_basin n <;> simp [stage9_basinWeight,stage9_missingWeight,h]

theorem stage9_basin_weight_bounds (w : ℕ → ℝ) (hw : ∀ n, 0≤w n) (n : ℕ) :
    0≤stage9_basinWeight w n ∧ stage9_basinWeight w n≤w n := by
  classical
  by_cases h : stage9_basin n <;> simp [stage9_basinWeight,h,hw n]

theorem stage9_missing_weight_bounds (w : ℕ → ℝ) (hw : ∀ n, 0≤w n) (n : ℕ) :
    0≤stage9_missingWeight w n ∧ stage9_missingWeight w n≤w n := by
  classical
  by_cases h : stage9_basin n <;> simp [stage9_missingWeight,h,hw n]

theorem stage9_basin_summable (w : ℕ → ℝ) (hw : ∀ n, 0≤w n) (hs : Summable w) :
    Summable (stage9_basinWeight w) :=
  Summable.of_nonneg_of_le (fun n => (stage9_basin_weight_bounds w hw n).1)
    (fun n => (stage9_basin_weight_bounds w hw n).2) hs

theorem stage9_missing_summable (w : ℕ → ℝ) (hw : ∀ n, 0≤w n) (hs : Summable w) :
    Summable (stage9_missingWeight w) :=
  Summable.of_nonneg_of_le (fun n => (stage9_missing_weight_bounds w hw n).1)
    (fun n => (stage9_missing_weight_bounds w hw n).2) hs

theorem stage9_tsum_partition (w : ℕ → ℝ) (hw : ∀ n, 0≤w n) (hs : Summable w) :
    (∑' n, w n) = (∑' n, stage9_basinWeight w n) + (∑' n, stage9_missingWeight w n) := by
  calc
    (∑' n, w n) = ∑' n, (stage9_basinWeight w n + stage9_missingWeight w n) := by
      apply tsum_congr
      intro n
      exact (stage9_weight_partition w n).symm
    _ = _ := (stage9_basin_summable w hw hs).tsum_add (stage9_missing_summable w hw hs)

theorem stage9_defect_zero_iff (w : ℕ → ℝ) (h0 : w 0=0)
    (hp : ∀ n, 0<n → 0<w n) (hs : Summable w) :
    stage9_converges ↔ (∑' n, stage9_missingWeight w n)=0 := by
  classical
  have hw : ∀ n, 0≤w n := by
    intro n
    by_cases h : n=0
    · simp [h,h0]
    · exact (hp n (by omega)).le
  constructor
  · intro h
    have he : ∀ n, stage9_missingWeight w n=0 := by
      intro n
      by_cases hn : n=0
      · subst n
        by_cases hb : stage9_basin 0 <;> simp [stage9_missingWeight,hb,h0]
      · simp [stage9_missingWeight,h n (by omega : 0<n)]
    calc
      (∑' n, stage9_missingWeight w n) = ∑' _ : ℕ, (0:ℝ) := tsum_congr he
      _ = 0 := tsum_zero
  · intro h n hn
    have hm := stage9_missing_summable w hw hs
    have hle := hm.le_tsum n (fun i _ => (stage9_missing_weight_bounds w hw i).1)
    rw [h] at hle
    by_contra hb
    simp only [stage9_missingWeight,if_neg hb] at hle
    exact (not_le_of_gt (hp n hn)) hle

theorem stage9_basin_mass_iff (w : ℕ → ℝ) (h0 : w 0=0)
    (hp : ∀ n, 0<n → 0<w n) (hs : Summable w) :
    stage9_converges ↔ (∑' n, stage9_basinWeight w n)=(∑' n, w n) := by
  have hw : ∀ n, 0≤w n := by
    intro n
    by_cases h : n=0
    · simp [h,h0]
    · exact (hp n (by omega)).le
  have ht := stage9_tsum_partition w hw hs
  rw [stage9_defect_zero_iff w h0 hp hs]
  constructor <;> intro h <;> linarith

noncomputable def stage9_zetaTwoWeight (n : ℕ) : ℝ := 1 / (n : ℝ)^2

theorem stage9_zeta_two_zero : stage9_zetaTwoWeight 0=0 := by norm_num [stage9_zetaTwoWeight]

theorem stage9_zeta_two_positive (n : ℕ) (hn : 0<n) : 0<stage9_zetaTwoWeight n := by
  have h : 0<(n:ℝ) := by exact_mod_cast hn
  unfold stage9_zetaTwoWeight
  positivity

theorem stage9_zeta_two_hasSum : HasSum stage9_zetaTwoWeight (Real.pi^2/6) := by
  exact hasSum_zeta_two

theorem stage9_zeta_two_total : (∑' n, stage9_zetaTwoWeight n)=Real.pi^2/6 :=
  stage9_zeta_two_hasSum.tsum_eq

theorem stage9_basel_iff : stage9_converges ↔
    (∑' n, stage9_basinWeight stage9_zetaTwoWeight n)=Real.pi^2/6 := by
  have h := stage9_basin_mass_iff _ stage9_zeta_two_zero stage9_zeta_two_positive
    stage9_zeta_two_hasSum.summable
  rw [stage9_zeta_two_total] at h
  exact h

-- Missing a single positive seed forces a positive quantitative Basel defect.
theorem stage9_basel_gap (n : ℕ) (hn : 0<n) (hb : ¬ stage9_basin n) :
    stage9_zetaTwoWeight n ≤ Real.pi^2/6 - (∑' i, stage9_basinWeight stage9_zetaTwoWeight i) := by
  classical
  have hw : ∀ i, 0≤stage9_zetaTwoWeight i := by
    intro i
    unfold stage9_zetaTwoWeight
    positivity
  have hm := stage9_missing_summable _ hw stage9_zeta_two_hasSum.summable
  have ht := stage9_tsum_partition _ hw stage9_zeta_two_hasSum.summable
  rw [stage9_zeta_two_total] at ht
  have hle := hm.le_tsum n (fun i _ => (stage9_missing_weight_bounds _ hw i).1)
  simp only [stage9_missingWeight,if_neg hb] at hle
  change stage9_zetaTwoWeight n ≤ (∑' i, stage9_missingWeight stage9_zetaTwoWeight i) at hle
  linarith only [ht, hle]

theorem stage9_basin_double (n : ℕ) : stage9_basin (2*n) ↔ stage9_basin n := by
  have h := stage9_basin_step (2*n)
  rw [stage9_step_even] at h
  exact h.symm

theorem stage9_basin_power_two (k n : ℕ) : stage9_basin (2^k*n) ↔ stage9_basin n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (2:ℕ)^(k+1)*n=2*(2^k*n) by rw [pow_succ]; ring,stage9_basin_double]
    exact ih

-- A complete finite sum over the first 2*N positive starting values.
theorem stage9_one_step_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (2*N), f (stage9_step (i+1))) =
    ∑ j ∈ Finset.range N, (f (3*j+2)+f (j+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega]
    simp only [Finset.sum_range_succ]
    rw [ih,stage9_step_odd,show 2*N+1+1=2*(N+1) by omega,stage9_step_even] <;> ring

-- Cylinder arithmetic (adapted from earlier Geometric Spectral Stage 1).
theorem stage9_parity_shift (r t : ℕ) : stage9_parity (r+2*t)=stage9_parity r := by
  unfold stage9_parity
  omega

theorem stage9_step_shift (r t : ℕ) :
    stage9_step (r+2*t)=stage9_step r+3^stage9_parity r*t := by
  have hmod : (r+2*t)%2=r%2 := by omega
  by_cases h : r%2=0
  · have hp : stage9_parity r=0 := h
    simp only [stage9_step,hmod,if_pos h,hp,pow_zero,one_mul]
    omega
  · have hp : stage9_parity r=1 := by unfold stage9_parity; omega
    simp only [stage9_step,hmod,if_neg h,hp,pow_one]
    omega

theorem stage9_cylinder_affine (k r q : ℕ) :
    stage9_orbit k (r+2^k*q)=stage9_orbit k r+3^stage9_count k r*q ∧
    stage9_count k (r+2^k*q)=stage9_count k r := by
  induction k generalizing r q with
  | zero => simp [stage9_orbit,stage9_count]
  | succ k ih =>
    have ha : r+2^(k+1)*q=r+2*(2^k*q) := by rw [pow_succ]; ring
    have hs : stage9_step (r+2^(k+1)*q)=stage9_step r+2^k*(3^stage9_parity r*q) := by
      rw [ha,stage9_step_shift]
      ring
    have hp : stage9_parity (r+2^(k+1)*q)=stage9_parity r := by rw [ha,stage9_parity_shift]
    have hi := ih (stage9_step r) (3^stage9_parity r*q)
    simp only [stage9_orbit,stage9_count,hs,hp]
    constructor
    · rw [hi.1,pow_add]; ring
    · rw [hi.2]

theorem stage9_cylinder_basin (k r q : ℕ) : stage9_basin (r+2^k*q) ↔
    stage9_basin (stage9_orbit k r+3^stage9_count k r*q) := by
  have h := stage9_basin_orbit k (r+2^k*q)
  rw [(stage9_cylinder_affine k r q).1] at h
  exact h.symm

-- Finite cylinder decomposition for any real-valued test kernel.
-- This is the discrete prerequisite of the Hurwitz-zeta representation.
theorem stage9_cylinder_kernel (f : ℕ → ℝ) (k N : ℕ) :
    (∑ q ∈ Finset.range N, ∑ r ∈ Finset.range (2^k),
      f (stage9_orbit k (r+1+2^k*q))) =
    ∑ q ∈ Finset.range N, ∑ r ∈ Finset.range (2^k),
      f (stage9_orbit k (r+1)+3^stage9_count k (r+1)*q) := by
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  rw [(stage9_cylinder_affine k (r+1) q).1]

-- Exact additive correction along the actual shortcut orbit.
def stage9_correction : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, n => 3^stage9_count k (stage9_step n)*stage9_parity n +
      2*stage9_correction k (stage9_step n)

theorem stage9_step_affine (n : ℕ) :
    2*stage9_step n=3^stage9_parity n*n+stage9_parity n := by
  by_cases h : n%2=0
  · have hp : stage9_parity n=0 := h
    simp only [stage9_step,if_pos h,hp,pow_zero,one_mul,add_zero]
    omega
  · have hp : stage9_parity n=1 := by unfold stage9_parity; omega
    simp only [stage9_step,if_neg h,hp,pow_one]
    omega

theorem stage9_orbit_affine (k n : ℕ) :
    2^k*stage9_orbit k n=3^stage9_count k n*n+stage9_correction k n := by
  induction k generalizing n with
  | zero => simp [stage9_orbit,stage9_count,stage9_correction]
  | succ k ih =>
    simp only [stage9_orbit,stage9_count,stage9_correction]
    rw [pow_succ,pow_add]
    calc
      2^k*2*stage9_orbit k (stage9_step n) = 2*(2^k*stage9_orbit k (stage9_step n)) := by ring
      _ = 2*(3^stage9_count k (stage9_step n)*stage9_step n+stage9_correction k (stage9_step n)) := by rw [ih]
      _ = 3^stage9_count k (stage9_step n)*(2*stage9_step n)+2*stage9_correction k (stage9_step n) := by ring
      _ = _ := by rw [stage9_step_affine]; ring

theorem stage9_orbit_divisibility (k n : ℕ) :
    (2:ℕ)^k ∣ 3^stage9_count k n*n+stage9_correction k n :=
  ⟨stage9_orbit k n,(stage9_orbit_affine k n).symm⟩

theorem stage9_orbit_affine_int (k n : ℕ) :
    (2:ℤ)^k*(stage9_orbit k n:ℤ)=3^stage9_count k n*(n:ℤ)+(stage9_correction k n:ℤ) := by
  exact_mod_cast (stage9_orbit_affine k n)

-- Explicit inverse witness: u is the inverse of the odd multiplier modulo d.
theorem stage9_inverse_residue (a c d n y u v : ℤ)
    (h : d*y=a*n+c) (hi : a*u=1+d*v) : d ∣ n+u*c := by
  refine ⟨u*y-v*n,?_⟩
  linear_combination -u*h-n*hi

theorem stage9_normalized_residue (k n : ℕ) (u v : ℤ)
    (hi : (3:ℤ)^stage9_count k n*u=1+2^k*v) :
    (2:ℤ)^k ∣ (n:ℤ)+u*(stage9_correction k n:ℤ) := by
  exact stage9_inverse_residue _ _ _ _ _ _ _ (stage9_orbit_affine_int k n) hi

theorem stage9_cycle_balance (k n : ℕ) (h : stage9_orbit k n=n) :
    (stage9_correction k n:ℤ)=((2:ℤ)^k-3^stage9_count k n)*(n:ℤ) := by
  have he := stage9_orbit_affine_int k n
  rw [h] at he
  linear_combination -he

-- Local pole residue algebra; the complex analytic limits are not asserted here.
theorem stage9_mellin_first_residue (d c : ℝ) (hd : d≠0) (h : d*c=1/4) :
    c=1/(4*d) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num : (4:ℝ)≠0) hd)).2
  calc
    c*(4*d)=4*(d*c) := by ring
    _ = 1 := by rw [h]; norm_num

theorem stage9_mellin_second_residue (r1 r2 : ℝ) (h : (-1/3)*r2=(1/3)*r1) :
    r2 = -r1 := by linarith

end ZetaAdelic

#print axioms stage9_step_even
#print axioms stage9_step_odd
#print axioms stage9_step_pos
#print axioms stage9_step_one
#print axioms stage9_step_two
#print axioms stage9_orbit_pos
#print axioms stage9_orbit_add
#print axioms stage9_basin_step
#print axioms stage9_basin_orbit
#print axioms stage9_basin_one
#print axioms stage9_fixed_orbit
#print axioms stage9_fixed_on_basin
#print axioms stage9_indicator_fixed
#print axioms stage9_indicator_bounds
#print axioms stage9_indicator_zero
#print axioms stage9_fixed_unique_iff
#print axioms stage9_weight_partition
#print axioms stage9_basin_weight_bounds
#print axioms stage9_missing_weight_bounds
#print axioms stage9_basin_summable
#print axioms stage9_missing_summable
#print axioms stage9_tsum_partition
#print axioms stage9_defect_zero_iff
#print axioms stage9_basin_mass_iff
#print axioms stage9_zeta_two_zero
#print axioms stage9_zeta_two_positive
#print axioms stage9_zeta_two_hasSum
#print axioms stage9_zeta_two_total
#print axioms stage9_basel_iff
#print axioms stage9_basel_gap
#print axioms stage9_basin_double
#print axioms stage9_basin_power_two
#print axioms stage9_one_step_sum
#print axioms stage9_parity_shift
#print axioms stage9_step_shift
#print axioms stage9_cylinder_affine
#print axioms stage9_cylinder_basin
#print axioms stage9_cylinder_kernel
#print axioms stage9_step_affine
#print axioms stage9_orbit_affine
#print axioms stage9_orbit_divisibility
#print axioms stage9_orbit_affine_int
#print axioms stage9_inverse_residue
#print axioms stage9_normalized_residue
#print axioms stage9_cycle_balance
#print axioms stage9_mellin_first_residue
#print axioms stage9_mellin_second_residue

end CollatzRunyan.LeptonSpectral
