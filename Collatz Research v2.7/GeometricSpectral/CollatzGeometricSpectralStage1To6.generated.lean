import Mathlib

/-! Experimental Collatz–Runyan geometric spectral extension.
    Original (unaccelerated) Collatz map. The additional sign coordinate is
    an imposed orientation cocycle, not an intrinsic topology theorem. -/

namespace CollatzRunyan.GeometricSpectral

set_option autoImplicit false

def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

def orbit : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => orbit k (step n)

def parity (n : ℕ) : ℕ := n % 2

def oddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => oddCount k (step n) + parity n

def liftStep (p : ℕ × ℤ) : ℕ × ℤ :=
  (step p.1, (-1 : ℤ) ^ parity p.1 * p.2)

def liftOrbit : ℕ → (ℕ × ℤ) → (ℕ × ℤ)
  | 0, p => p
  | k + 1, p => liftOrbit k (liftStep p)

theorem step_double (n : ℕ) : step (2 * n) = n := by
  have h : (2 * n) % 2 = 0 := by omega
  simp only [step, if_pos h]
  omega

theorem step_odd (n : ℕ) (h : n % 2 = 1) : step n = 3 * n + 1 := by
  have h' : n % 2 ≠ 0 := by omega
  simp [step, h']

theorem step_pos (n : ℕ) (h : 0 < n) : 0 < step n := by
  by_cases he : n % 2 = 0
  · simp only [step, if_pos he]
    omega
  · simp only [step, if_neg he]
    omega

theorem orbit_add (k l n : ℕ) : orbit (k + l) n = orbit l (orbit k n) := by
  induction k generalizing n with
  | zero => simp [orbit]
  | succ k ih =>
    rw [show k + 1 + l = (k + l) + 1 by omega]
    simp only [orbit]
    exact ih (step n)

theorem liftOrbit_formula (k n : ℕ) (u : ℤ) :
    liftOrbit k (n, u) = (orbit k n, (-1 : ℤ) ^ oddCount k n * u) := by
  induction k generalizing n u with
  | zero => simp [liftOrbit, orbit, oddCount]
  | succ k ih =>
    simp only [liftOrbit, liftStep, orbit, oddCount, ih, pow_add, mul_assoc]

theorem cycle4 : orbit 3 4 = 4 := by decide

theorem cycle4_oddCount : oddCount 3 4 = 1 := by decide

theorem cycle4_twist (u : ℤ) : liftOrbit 3 (4, u) = (4, -u) := by
  rw [liftOrbit_formula, cycle4, cycle4_oddCount]
  simp

theorem cycle4_double_return (u : ℤ) : liftOrbit 6 (4, u) = (4, u) := by
  have h : orbit 6 4 = 4 := by decide
  have hm : oddCount 6 4 = 2 := by decide
  rw [liftOrbit_formula, h, hm]
  norm_num

theorem even_cycle_orientation (k n m : ℕ) (u : ℤ)
    (hc : orbit k n = n) (hm : oddCount k n = 2 * m) :
    liftOrbit k (n, u) = (n, u) := by
  rw [liftOrbit_formula, hc, hm, pow_mul]
  norm_num

theorem odd_cycle_orientation (k n m : ℕ) (u : ℤ)
    (hc : orbit k n = n) (hm : oddCount k n = 2 * m + 1) :
    liftOrbit k (n, u) = (n, -u) := by
  rw [liftOrbit_formula, hc, hm, pow_succ, pow_mul]
  norm_num

/-- Eventual hitting of one. Universal convergence quantifies only n > 0. -/
def Basin (n : ℕ) : Prop := ∃ k : ℕ, orbit k n = 1

def Missing (n : ℕ) : Prop := ¬ Basin n

def Converges : Prop := ∀ n : ℕ, 0 < n → Basin n

theorem basin_one : Basin 1 := ⟨0, rfl⟩

theorem basin_step_iff (n : ℕ) : Basin (step n) ↔ Basin n := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, hk⟩
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      change n = 1 at hk
      subst n
      exact ⟨2, by decide⟩
    | succ k => exact ⟨k, hk⟩

theorem basin_orbit_iff (k n : ℕ) : Basin (orbit k n) ↔ Basin n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    change Basin (orbit k (step n)) ↔ Basin n
    exact (ih (step n)).trans (basin_step_iff n)

theorem missing_orbit_iff (k n : ℕ) : Missing (orbit k n) ↔ Missing n :=
  not_congr (basin_orbit_iff k n)

theorem basin_double_iff (n : ℕ) : Basin (2 * n) ↔ Basin n := by
  have h := basin_step_iff (2 * n)
  rw [step_double] at h
  exact h.symm

theorem missing_double_iff (n : ℕ) : Missing (2 * n) ↔ Missing n :=
  not_congr (basin_double_iff n)

theorem basin_odd_branch_iff (n : ℕ) (h : n % 2 = 1) :
    Basin (3 * n + 1) ↔ Basin n := by
  have hh := basin_step_iff n
  rw [step_odd n h] at hh
  exact hh

theorem missing_pow_two_iff (k n : ℕ) : Missing (2 ^ k * n) ↔ Missing n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    rw [show 2 ^ k * 2 * n = 2 * (2 ^ k * n) by ring]
    exact (missing_double_iff (2 ^ k * n)).trans ih

theorem missing_unbounded (n : ℕ) (hn : 0 < n) (hm : Missing n) :
    ∀ M : ℕ, ∃ m : ℕ, M < m ∧ Missing m := by
  intro M
  have hpow : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  have hmul : 2 ^ (M + 1) ≤ 2 ^ (M + 1) * n := by
    calc
      2 ^ (M + 1) = 2 ^ (M + 1) * 1 := by simp
      _ ≤ 2 ^ (M + 1) * n := Nat.mul_le_mul_left _ hn
  refine ⟨2 ^ (M + 1) * n, ?_, (missing_pow_two_iff (M + 1) n).2 hm⟩
  have hh := hpow (M + 1)
  omega

theorem converges_iff_no_positive_missing :
    Converges ↔ ∀ n : ℕ, 0 < n → ¬ Missing n := by
  classical
  constructor
  · intro h n hn hm
    exact hm (h n hn)
  · intro h n hn
    by_contra hm
    exact h n hn hm

#print axioms step_double
#print axioms step_odd
#print axioms step_pos
#print axioms orbit_add
#print axioms liftOrbit_formula
#print axioms cycle4
#print axioms cycle4_oddCount
#print axioms cycle4_twist
#print axioms cycle4_double_return
#print axioms even_cycle_orientation
#print axioms odd_cycle_orientation
#print axioms basin_one
#print axioms basin_step_iff
#print axioms basin_orbit_iff
#print axioms missing_orbit_iff
#print axioms basin_double_iff
#print axioms missing_double_iff
#print axioms basin_odd_branch_iff
#print axioms missing_pow_two_iff
#print axioms missing_unbounded
#print axioms converges_iff_no_positive_missing

end CollatzRunyan.GeometricSpectral

namespace CollatzRunyan.GeometricSpectral

set_option autoImplicit false

/-! Shortcut map and exact binary-cylinder lifting. -/
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def shortcutOrbit : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => shortcutOrbit k (shortcut n)

def shortcutOddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => shortcutOddCount k (shortcut n) + parity n

theorem shortcut_basin_iff (n : ℕ) : Basin (shortcut n) ↔ Basin n := by
  by_cases h : n % 2 = 0
  · have he : shortcut n = step n := by simp [shortcut, step, h]
    rw [he]
    exact basin_step_iff n
  · have he : (3 * n + 1) % 2 = 0 := by omega
    have hs : shortcut n = step (step n) := by
      simp only [shortcut, step, if_neg h, if_pos he]
    rw [hs]
    exact (basin_step_iff (step n)).trans (basin_step_iff n)

theorem shortcut_orbit_basin_iff (k n : ℕ) : Basin (shortcutOrbit k n) ↔ Basin n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    change Basin (shortcutOrbit k (shortcut n)) ↔ Basin n
    exact (ih (shortcut n)).trans (shortcut_basin_iff n)

theorem parity_add_even (r t : ℕ) : parity (r + 2 * t) = parity r := by
  unfold parity
  omega

theorem shortcut_add_even (r t : ℕ) :
    shortcut (r + 2 * t) = shortcut r + 3 ^ parity r * t := by
  have hmod : (r + 2 * t) % 2 = r % 2 := by omega
  by_cases h : r % 2 = 0
  · have hp : parity r = 0 := h
    simp only [shortcut, hmod, if_pos h, hp, pow_zero, one_mul]
    omega
  · have hp : parity r = 1 := by unfold parity; omega
    simp only [shortcut, hmod, if_neg h, hp, pow_one]
    omega

theorem binary_cylinder_affine (k r q : ℕ) :
    shortcutOrbit k (r + 2 ^ k * q) =
        shortcutOrbit k r + 3 ^ shortcutOddCount k r * q ∧
    shortcutOddCount k (r + 2 ^ k * q) = shortcutOddCount k r := by
  induction k generalizing r q with
  | zero => simp [shortcutOrbit, shortcutOddCount]
  | succ k ih =>
    have ha : r + 2 ^ (k + 1) * q = r + 2 * (2 ^ k * q) := by
      rw [pow_succ]
      ring
    have hs : shortcut (r + 2 ^ (k + 1) * q) =
        shortcut r + 2 ^ k * (3 ^ parity r * q) := by
      rw [ha, shortcut_add_even]
      ring
    have hp : parity (r + 2 ^ (k + 1) * q) = parity r := by
      rw [ha, parity_add_even]
    have hi := ih (shortcut r) (3 ^ parity r * q)
    simp only [shortcutOrbit, shortcutOddCount, hs, hp]
    constructor
    · rw [hi.1, pow_add]
      ring
    · rw [hi.2]

theorem binary_cylinder_basin_iff (k r q : ℕ) :
    Basin (r + 2 ^ k * q) ↔
      Basin (shortcutOrbit k r + 3 ^ shortcutOddCount k r * q) := by
  have h := shortcut_orbit_basin_iff k (r + 2 ^ k * q)
  rw [(binary_cylinder_affine k r q).1] at h
  exact h.symm

/-- Conditional lifting: the congruence equation is supplied as an exact
    equality. Existence of its solutions in all cylinders is a separate task. -/
theorem binary_cylinder_lift (k r q j a : ℕ)
    (h : shortcutOrbit k r + 3 ^ shortcutOddCount k r * q = 2 ^ j * a) :
    Missing (r + 2 ^ k * q) ↔ Missing a := by
  have hb := binary_cylinder_basin_iff k r q
  rw [h] at hb
  exact (not_congr hb).trans (missing_pow_two_iff j a)

#print axioms shortcut_basin_iff
#print axioms shortcut_orbit_basin_iff
#print axioms parity_add_even
#print axioms shortcut_add_even
#print axioms binary_cylinder_affine
#print axioms binary_cylinder_basin_iff
#print axioms binary_cylinder_lift

/-! Reflection geometry in real coordinates. No claim about zero confinement. -/
theorem reflection_fixed_iff (x : ℝ) : 1 - x = x ↔ x = 1 / 2 := by
  constructor <;> intro h <;> linarith

theorem mobius_radius_sq_iff (x y : ℝ) (h : x ^ 2 + y ^ 2 ≠ 0) :
    ((x - 1) ^ 2 + y ^ 2) / (x ^ 2 + y ^ 2) = 1 ↔ x = 1 / 2 := by
  constructor
  · intro he
    have hh := (div_eq_iff h).mp he
    nlinarith
  · intro hx
    apply (div_eq_iff h).2
    rw [hx]
    ring

noncomputable def symmetricPolynomial (x : ℝ) : ℝ := (x - 1 / 2) ^ 2 - 1 / 16

theorem symmetricPolynomial_reflect (x : ℝ) :
    symmetricPolynomial (1 - x) = symmetricPolynomial x := by
  unfold symmetricPolynomial
  ring

theorem symmetry_not_zero_confinement :
    ∃ x : ℝ, symmetricPolynomial x = 0 ∧ x ≠ 1 / 2 := by
  refine ⟨1 / 4, ?_, ?_⟩ <;> norm_num [symmetricPolynomial]

#print axioms reflection_fixed_iff
#print axioms mobius_radius_sq_iff
#print axioms symmetricPolynomial_reflect
#print axioms symmetry_not_zero_confinement

/-! Positive missing-weight series. Index n+1 avoids the zero integer.
    Explicit summability is essential: the totalized infinite sum is zero
    for a nonsummable series in Lean's usual real tsum convention. -/
noncomputable def missingWeight (w : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if Basin (n + 1) then 0 else w (n + 1)

theorem missingWeight_nonneg (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 0 < n → 0 ≤ w n) (i : ℕ) :
    0 ≤ missingWeight w i := by
  classical
  by_cases h : Basin (i + 1)
  · simp [missingWeight, h]
  · simpa [missingWeight, h] using hw (i + 1) (by omega)

theorem positive_missing_series_iff (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 0 < n → 0 < w n)
    (hs : Summable (missingWeight w)) :
    Converges ↔ (∑' n : ℕ, missingWeight w n) = 0 := by
  classical
  constructor
  · intro hc
    have hz : missingWeight w = (fun _ : ℕ => (0 : ℝ)) := by
      funext i
      simp [missingWeight, hc (i + 1) (by omega)]
    rw [hz]
    simp
  · intro hz n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
    by_contra hb
    have hle := hs.le_tsum k
      (fun i _ => missingWeight_nonneg w (fun j hj => (hw j hj).le) i)
    rw [hz] at hle
    simp only [missingWeight, if_neg hb] at hle
    exact (not_le_of_gt (hw (k + 1) (by omega))) hle

/-- The actual scalar weight in the single-point weight-four Fricke defect. -/
noncomputable def frickeKernel (n : ℕ) : ℝ :=
  Real.exp (-(2 * Real.pi * (n : ℝ)) / 3) -
    9 * Real.exp (-(2 * Real.pi * (n : ℝ)))

theorem frickeKernel_pos (n : ℕ) (hn : 0 < n) : 0 < frickeKernel n := by
  have h2 : (3 : ℝ) ≤ Real.exp 2 := by
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have h4 : (9 : ℝ) ≤ Real.exp 4 := by
    calc
      (9 : ℝ) = 3 * 3 := by norm_num
      _ ≤ Real.exp 2 * Real.exp 2 :=
        mul_le_mul h2 h2 (by norm_num) (Real.exp_pos _).le
      _ = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : 4 < 4 * Real.pi * (n : ℝ) / 3 := by
    have hpi := Real.pi_gt_three
    have hh := mul_nonneg (show 0 ≤ Real.pi by positivity) (sub_nonneg.mpr hn')
    nlinarith
  have he : (9 : ℝ) < Real.exp (4 * Real.pi * (n : ℝ) / 3) :=
    lt_of_le_of_lt h4 (Real.exp_lt_exp.mpr hp)
  have heq : Real.exp (4 * Real.pi * (n : ℝ) / 3) *
      Real.exp (-(2 * Real.pi * (n : ℝ))) =
      Real.exp (-(2 * Real.pi * (n : ℝ)) / 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh := mul_lt_mul_of_pos_right he (Real.exp_pos (-(2 * Real.pi * (n : ℝ))))
  rw [heq] at hh
  unfold frickeKernel
  exact sub_pos.mpr hh

/-- This is the positivity stage of the Fricke criterion. It assumes the
    coefficient positivity and summability; it does not assert modularity. -/
theorem fricke_missing_series_iff (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, 0 < n → 0 < r n)
    (hs : Summable (missingWeight (fun n => r n * frickeKernel n))) :
    Converges ↔ (∑' n : ℕ, missingWeight (fun j => r j * frickeKernel j) n) = 0 := by
  exact positive_missing_series_iff _ (fun n hn => mul_pos (hr n hn) (frickeKernel_pos n hn)) hs

/-- Transfer to an independently established Fricke identity. The equality
    relating delta to the missing series must be proved separately. -/
theorem fricke_defect_iff_of_identity (r : ℕ → ℝ) (delta : ℝ)
    (hr : ∀ n : ℕ, 0 < n → 0 < r n)
    (hs : Summable (missingWeight (fun n => r n * frickeKernel n)))
    (hd : delta = ∑' n : ℕ, missingWeight (fun j => r j * frickeKernel j) n) :
    Converges ↔ delta = 0 := by
  rw [hd]
  exact fricke_missing_series_iff r hr hs

#print axioms missingWeight_nonneg
#print axioms positive_missing_series_iff
#print axioms frickeKernel_pos
#print axioms fricke_missing_series_iff
#print axioms fricke_defect_iff_of_identity

end CollatzRunyan.GeometricSpectral

namespace CollatzRunyan.GeometricSpectral

set_option autoImplicit false

/-! Elementary algebraic stage of the Hasse–Weil comparison. The L-value
    is an explicit nonzero parameter, not a claim about BSD. -/
theorem positive_product_ratio_eq_iff (a b c d L : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbd : b ≤ d)
    (hL : L ≠ 0) :
    a * b / L = c * d / L ↔ a = c ∧ b = d := by
  constructor
  · intro he
    have hp : a * b = c * d := by
      calc
        a * b = (a * b / L) * L := by field_simp
        _ = (c * d / L) * L := by rw [he]
        _ = c * d := by field_simp
    have hc : 0 < c := lt_of_lt_of_le ha hac
    have hca : a = c := by
      by_contra hn
      have hlt : a < c := lt_of_le_of_ne hac hn
      have h1 : a * b < c * b := mul_lt_mul_of_pos_right hlt hb
      have h2 : c * b ≤ c * d := mul_le_mul_of_nonneg_left hbd hc.le
      exact (ne_of_lt (lt_of_lt_of_le h1 h2)) hp
    have hdb : b = d := by
      by_contra hn
      have hlt : b < d := lt_of_le_of_ne hbd hn
      have h1 : c * b < c * d := mul_lt_mul_of_pos_left hlt hc
      rw [hca] at hp
      exact (ne_of_lt h1) hp
    exact ⟨hca, hdb⟩
  · rintro ⟨rfl, rfl⟩
    rfl

#print axioms positive_product_ratio_eq_iff

end CollatzRunyan.GeometricSpectral

/-! Stage 2: arithmetic prerequisites, Gaussian summability, and theta defect.
The classical theta inversion identity remains an explicit hypothesis.
This extension is appended to the exact verified Stage 1 source by the audit script. -/
namespace CollatzRunyan.GeometricSpectral

set_option autoImplicit false

-- Arithmetic prerequisites for unrestricted binary cylinder lifting.
theorem shortcut_odd_nonmultiple_three (n : ℕ) (hn : n % 2 = 1) :
    shortcut n % 3 ≠ 0 := by
  have he : n % 2 ≠ 0 := by omega
  simp only [shortcut, if_neg he]
  omega

theorem shortcut_preserves_nonmultiple_three (n : ℕ) (hn : n % 3 ≠ 0) :
    shortcut n % 3 ≠ 0 := by
  by_cases he : n % 2 = 0
  · simp only [shortcut, if_pos he]
    omega
  · exact shortcut_odd_nonmultiple_three n (by omega)

theorem shortcut_orbit_nonmultiple_three (k n : ℕ) (hn : n % 3 ≠ 0) :
    shortcutOrbit k n % 3 ≠ 0 := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih =>
    exact ih (shortcut n) (shortcut_preserves_nonmultiple_three n hn)

theorem cylinder_endpoint_nonmultiple_three (k r : ℕ)
    (hm : 0 < shortcutOddCount k r) : shortcutOrbit k r % 3 ≠ 0 := by
  induction k generalizing r with
  | zero => simp [shortcutOddCount] at hm
  | succ k ih =>
    change 0 < shortcutOddCount k (shortcut r) + parity r at hm
    change shortcutOrbit k (shortcut r) % 3 ≠ 0
    by_cases he : r % 2 = 0
    · have hp : parity r = 0 := he
      rw [hp] at hm
      exact ih (shortcut r) (by omega)
    · exact shortcut_orbit_nonmultiple_three k (shortcut r)
        (shortcut_odd_nonmultiple_three r (by omega))

theorem nat_progression_of_mod (c x d : ℕ) (hle : c ≤ x)
    (hmod : c % d = x % d) : ∃ q : ℕ, c + d * q = x := by
  have hq : c / d ≤ x / d := Nat.div_le_div_right hle
  have hadd : c / d + (x / d - c / d) = x / d := by omega
  refine ⟨x / d - c / d, ?_⟩
  calc
    c + d * (x / d - c / d) =
        (c % d + d * (c / d)) + d * (x / d - c / d) := by
          rw [Nat.mod_add_div]
    _ = c % d + d * (c / d + (x / d - c / d)) := by
          rw [Nat.mul_add, Nat.add_assoc]
    _ = x := by rw [hadd, hmod, Nat.mod_add_div]

theorem binary_cylinder_lift_of_mod (k r j a : ℕ)
    (hle : shortcutOrbit k r ≤ 2 ^ j * a)
    (hmod : shortcutOrbit k r % (3 ^ shortcutOddCount k r) =
      (2 ^ j * a) % (3 ^ shortcutOddCount k r)) :
    ∃ q : ℕ, Missing (r + 2 ^ k * q) ↔ Missing a := by
  obtain ⟨q, hq⟩ := nat_progression_of_mod _ _ _ hle hmod
  exact ⟨q, binary_cylinder_lift k r q j a hq⟩

-- A positive missing seed not divisible by 3, if any positive seed is missing.
theorem missing_seed_nonmultiple_three (h : ∃ n : ℕ, 0 < n ∧ Missing n) :
    ∃ a : ℕ, 0 < a ∧ Missing a ∧ a % 3 ≠ 0 := by
  classical
  let n := Nat.find h
  have hn : 0 < n ∧ Missing n := Nat.find_spec h
  have hodd : n % 2 = 1 := by
    by_contra hh
    have he : n % 2 = 0 := by omega
    have hd : 2 * (n / 2) = n := by omega
    have hm : Missing (n / 2) := by
      apply (missing_double_iff (n / 2)).1
      rw [hd]
      exact hn.2
    have hpos : 0 < n / 2 := by omega
    have hmin : n ≤ n / 2 := Nat.find_min' h ⟨hpos, hm⟩
    omega
  have hmiss : Missing (3 * n + 1) :=
    (not_congr (basin_odd_branch_iff n hodd)).2 hn.2
  exact ⟨3 * n + 1, by omega, hmiss, by omega⟩

-- Analytic prerequisites. a is the positive Gaussian scale (a = πt).
noncomputable def gaussianWeight (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-a * (n : ℝ) ^ 2)

theorem gaussianWeight_pos (a : ℝ) (n : ℕ) : 0 < gaussianWeight a n :=
  Real.exp_pos _

theorem exp_linear_eq_pow (a : ℝ) (n : ℕ) :
    Real.exp (-a * (n : ℝ)) = Real.exp (-a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show -a * ((n + 1 : ℕ) : ℝ) = -a * (n : ℝ) + -a by push_cast; ring]
    rw [Real.exp_add, ih, pow_succ]

theorem gaussian_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun i : ℕ => gaussianWeight a (i + 1)) := by
  have hr : Real.exp (-a) < 1 := by
    calc
      Real.exp (-a) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hg : Summable (fun i : ℕ => Real.exp (-a) ^ i) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hr
  refine Summable.of_nonneg_of_le (fun i => (gaussianWeight_pos a (i + 1)).le) ?_ hg
  intro i
  rw [← exp_linear_eq_pow]
  unfold gaussianWeight
  apply Real.exp_le_exp.mpr
  have hi : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg (i : ℝ), show 0 ≤ (i : ℝ) by positivity]
  exact mul_le_mul_of_nonpos_left hi (by linarith)

noncomputable def basinWeight (w : ℕ → ℝ) (i : ℕ) : ℝ := by
  classical
  exact if Basin (i + 1) then w (i + 1) else 0

theorem missingWeight_summable (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 0 < n → 0 ≤ w n)
    (hs : Summable (fun i : ℕ => w (i + 1))) : Summable (missingWeight w) := by
  classical
  refine Summable.of_nonneg_of_le (missingWeight_nonneg w hw) ?_ hs
  intro i
  by_cases hb : Basin (i + 1)
  · simpa [missingWeight, hb] using hw (i + 1) (by omega)
  · simp [missingWeight, hb]

theorem basinWeight_summable (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 0 < n → 0 ≤ w n)
    (hs : Summable (fun i : ℕ => w (i + 1))) : Summable (basinWeight w) := by
  classical
  refine Summable.of_nonneg_of_le ?_ ?_ hs
  · intro i
    by_cases hb : Basin (i + 1)
    · simpa [basinWeight, hb] using hw (i + 1) (by omega)
    · simp [basinWeight, hb]
  · intro i
    by_cases hb : Basin (i + 1)
    · simp [basinWeight, hb]
    · simpa [basinWeight, hb] using hw (i + 1) (by omega)

theorem gaussian_missing_summable (a : ℝ) (ha : 0 < a) :
    Summable (missingWeight (gaussianWeight a)) :=
  missingWeight_summable _ (fun n _ => (gaussianWeight_pos a n).le)
    (gaussian_summable a ha)

theorem gaussian_missing_zero_iff (a : ℝ) (ha : 0 < a) :
    Converges ↔ (∑' i : ℕ, missingWeight (gaussianWeight a) i) = 0 :=
  positive_missing_series_iff _ (fun n _ => gaussianWeight_pos a n)
    (gaussian_missing_summable a ha)

noncomputable def fullTheta (t : ℝ) : ℝ :=
  1 + 2 * (∑' i : ℕ, gaussianWeight (Real.pi * t) (i + 1))
noncomputable def basinTheta (t : ℝ) : ℝ :=
  1 + 2 * (∑' i : ℕ, basinWeight (gaussianWeight (Real.pi * t)) i)
noncomputable def missingTheta (t : ℝ) : ℝ :=
  2 * (∑' i : ℕ, missingWeight (gaussianWeight (Real.pi * t)) i)

theorem theta_partition (t : ℝ) (ht : 0 < t) :
    fullTheta t = basinTheta t + missingTheta t := by
  classical
  let w := gaussianWeight (Real.pi * t)
  have ha : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hs : Summable (fun i : ℕ => w (i + 1)) := gaussian_summable _ ha
  have hw : ∀ n : ℕ, 0 < n → 0 ≤ w n := fun n _ => (gaussianWeight_pos _ n).le
  have hb := basinWeight_summable w hw hs
  have hm := missingWeight_summable w hw hs
  have hsum : (∑' i : ℕ, w (i + 1)) =
      (∑' i : ℕ, basinWeight w i) + ∑' i : ℕ, missingWeight w i := by
    calc
      (∑' i : ℕ, w (i + 1)) =
          ∑' i : ℕ, (basinWeight w i + missingWeight w i) := by
        apply tsum_congr
        intro i
        by_cases h : Basin (i + 1) <;> simp [basinWeight, missingWeight, h]
      _ = _ := hb.tsum_add hm
  unfold fullTheta basinTheta missingTheta
  change 1 + 2 * (∑' i : ℕ, w (i + 1)) =
    (1 + 2 * (∑' i : ℕ, basinWeight w i)) + 2 * (∑' i : ℕ, missingWeight w i)
  rw [hsum]
  ring

theorem theta_equality_iff (t : ℝ) (ht : 0 < t) :
    Converges ↔ basinTheta t = fullTheta t := by
  have hp := theta_partition t ht
  have hz := gaussian_missing_zero_iff (Real.pi * t) (mul_pos Real.pi_pos ht)
  constructor
  · intro hc
    have he := hz.mp hc
    unfold missingTheta at hp
    rw [he] at hp
    linarith
  · intro he
    apply hz.mpr
    unfold missingTheta at hp
    linarith

-- Scaled single-point defect: sqrt(2) Θ_B(2) − Θ_B(1/2).
noncomputable def thetaKernel (n : ℕ) : ℝ :=
  gaussianWeight (Real.pi * (1 / 2)) n - Real.sqrt 2 * gaussianWeight (Real.pi * 2) n

theorem thetaKernel_pos (n : ℕ) (hn : 0 < n) : 0 < thetaKernel n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hpi := Real.pi_gt_three
  have hmul : 0 ≤ Real.pi * ((n : ℝ) ^ 2 - 1) :=
    mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsq)
  have hx : 1 < (3 * Real.pi / 2) * (n : ℝ) ^ 2 := by nlinarith
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs2 : Real.sqrt 2 ≤ 2 := by nlinarith [sq_nonneg (Real.sqrt 2 - 1)]
  have he : Real.sqrt 2 < Real.exp ((3 * Real.pi / 2) * (n : ℝ) ^ 2) := by
    linarith [Real.add_one_le_exp ((3 * Real.pi / 2) * (n : ℝ) ^ 2)]
  have hprod := mul_lt_mul_of_pos_right he (gaussianWeight_pos (Real.pi * 2) n)
  have heq : Real.exp ((3 * Real.pi / 2) * (n : ℝ) ^ 2) *
      gaussianWeight (Real.pi * 2) n = gaussianWeight (Real.pi * (1 / 2)) n := by
    unfold gaussianWeight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hprod
  exact sub_pos.mpr hprod

theorem thetaKernel_summable : Summable (fun i : ℕ => thetaKernel (i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => (thetaKernel_pos (i + 1) (by omega)).le) ?_
    (gaussian_summable (Real.pi * (1 / 2)) (by positivity))
  intro i
  unfold thetaKernel
  exact sub_le_self _ (mul_nonneg (Real.sqrt_nonneg _) (gaussianWeight_pos _ _).le)

theorem thetaKernel_missing_summable : Summable (missingWeight thetaKernel) :=
  missingWeight_summable _ (fun n hn => (thetaKernel_pos n hn).le) thetaKernel_summable

theorem thetaKernel_missing_identity :
    (∑' i : ℕ, missingWeight thetaKernel i) =
      (∑' i : ℕ, missingWeight (gaussianWeight (Real.pi * (1 / 2))) i) -
      Real.sqrt 2 * (∑' i : ℕ, missingWeight (gaussianWeight (Real.pi * 2)) i) := by
  classical
  let f := missingWeight (gaussianWeight (Real.pi * (1 / 2)))
  let g := missingWeight (gaussianWeight (Real.pi * 2))
  have hf : Summable f := gaussian_missing_summable _ (by positivity)
  have hg : Summable g := gaussian_missing_summable _ (by positivity)
  change (∑' i : ℕ, missingWeight thetaKernel i) = (∑' i : ℕ, f i) - Real.sqrt 2 * (∑' i : ℕ, g i)
  calc
    (∑' i : ℕ, missingWeight thetaKernel i) =
        ∑' i : ℕ, (f i - Real.sqrt 2 * g i) := by
      apply tsum_congr
      intro i
      by_cases hb : Basin (i + 1) <;> simp [f, g, missingWeight, thetaKernel, hb]
    _ = (∑' i : ℕ, f i) - ∑' i : ℕ, Real.sqrt 2 * g i := hf.tsum_sub (hg.mul_left _)
    _ = _ := by rw [tsum_mul_left]

/-- Algebraic defect identity, conditional only on the classical single-point
    Jacobi theta identity (not on Collatz convergence). -/
theorem theta_defect_identity (hj : fullTheta (1 / 2) = Real.sqrt 2 * fullTheta 2) :
    Real.sqrt 2 * basinTheta 2 - basinTheta (1 / 2) =
      2 * (∑' i : ℕ, missingWeight thetaKernel i) := by
  have h1 := theta_partition (1 / 2) (by norm_num)
  have h2 := theta_partition 2 (by norm_num)
  rw [h1, h2] at hj
  unfold missingTheta at hj
  rw [thetaKernel_missing_identity]
  nlinarith

theorem theta_defect_iff_of_jacobi
    (hj : fullTheta (1 / 2) = Real.sqrt 2 * fullTheta 2) :
    Converges ↔ Real.sqrt 2 * basinTheta 2 - basinTheta (1 / 2) = 0 := by
  rw [theta_defect_identity hj]
  have h := positive_missing_series_iff thetaKernel thetaKernel_pos thetaKernel_missing_summable
  constructor
  · intro hc
    rw [h.mp hc]
    ring
  · intro hz
    apply h.mpr
    linarith

#print axioms shortcut_odd_nonmultiple_three
#print axioms shortcut_preserves_nonmultiple_three
#print axioms shortcut_orbit_nonmultiple_three
#print axioms cylinder_endpoint_nonmultiple_three
#print axioms nat_progression_of_mod
#print axioms binary_cylinder_lift_of_mod
#print axioms missing_seed_nonmultiple_three
#print axioms gaussianWeight_pos
#print axioms exp_linear_eq_pow
#print axioms gaussian_summable
#print axioms missingWeight_summable
#print axioms basinWeight_summable
#print axioms gaussian_missing_summable
#print axioms gaussian_missing_zero_iff
#print axioms theta_partition
#print axioms theta_equality_iff
#print axioms thetaKernel_pos
#print axioms thetaKernel_summable
#print axioms thetaKernel_missing_summable
#print axioms thetaKernel_missing_identity
#print axioms theta_defect_identity
#print axioms theta_defect_iff_of_jacobi

end CollatzRunyan.GeometricSpectral

/-! Stage 3: exact finite inverse-branch certificates and limits on uniform
    prefix/transfer arguments. No global convergence or analytic continuation
    is asserted. The previous two stages are appended byte-for-byte first. -/
namespace CollatzRunyan.GeometricSpectral
set_option autoImplicit false

-- Actual odd inverse branches, with no approximation to the affine offset.
theorem odd_inverse_missing_iff (m y k : ℕ) (ho : m % 2 = 1)
    (h : 3 * m + 1 = 2 ^ k * y) : Missing m ↔ Missing y := by
  have hb := not_congr (basin_odd_branch_iff m ho)
  rw [h] at hb
  exact hb.symm.trans (missing_pow_two_iff k y)

theorem odd_inverse_of_even_mod_three (z : ℕ) (hz : 4 ≤ z)
    (he : z % 2 = 0) (h3 : z % 3 = 1) :
    ∃ m : ℕ, 0 < m ∧ m % 2 = 1 ∧ 3 * m + 1 = z := by
  exact ⟨z / 3, by omega, by omega, by omega⟩

theorem two_even_power_mod_three (j : ℕ) : (2 ^ (2 * j) : ℕ) % 3 = 1 := by
  rw [pow_mul]
  change 4 ^ j % 3 = 1
  induction j with
  | zero => decide
  | succ j ih => rw [pow_succ, Nat.mul_mod, ih]

theorem shortcut_zero_iterates (k : ℕ) :
    shortcutOrbit k 0 = 0 ∧ shortcutOddCount k 0 = 0 := by
  induction k with
  | zero => simp [shortcutOrbit, shortcutOddCount]
  | succ k ih => simpa [shortcutOrbit, shortcutOddCount, shortcut, parity] using ih

theorem even_prefix_exact (k a : ℕ) :
    shortcutOrbit k (2 ^ k * a) = a ∧ shortcutOddCount k (2 ^ k * a) = 0 := by
  have h := binary_cylinder_affine k 0 a
  simpa [(shortcut_zero_iterates k).1, (shortcut_zero_iterates k).2] using h

theorem missing_arbitrarily_long_even_prefix (h : ∃ a : ℕ, 0 < a ∧ Missing a)
    (k : ℕ) : ∃ n : ℕ, 0 < n ∧ Missing n ∧ shortcutOddCount k n = 0 := by
  obtain ⟨a, ha, hm⟩ := h
  exact ⟨2 ^ k * a, by positivity, (missing_pow_two_iff k a).2 hm,
    (even_prefix_exact k a).2⟩

theorem odd_inverse_prefix_count (m a k : ℕ) (ho : m % 2 = 1)
    (h : 3 * m + 1 = 2 ^ (k + 1) * a) : shortcutOddCount (k + 1) m = 1 := by
  have he : m % 2 ≠ 0 := by omega
  have hp : parity m = 1 := ho
  have hs : shortcut m = 2 ^ k * a := by
    simp only [shortcut, if_neg he]
    rw [h, pow_succ]
    have hh : 2 ^ k * 2 * a = 2 * (2 ^ k * a) := by ring
    rw [hh]
    omega
  simp only [shortcutOddCount, hs, hp, (even_prefix_exact k a).2]

theorem missing_arbitrarily_long_odd_prefix (h : ∃ a : ℕ, 0 < a ∧ Missing a)
    (L : ℕ) : ∃ m : ℕ, 0 < m ∧ Missing m ∧ m % 2 = 1 ∧
      shortcutOddCount (L + 1) m = 1 := by
  obtain ⟨a, ha, hm, h3⟩ := missing_seed_nonmultiple_three h
  have hj : (2 ^ (2 * (L + 1)) : ℕ) % 3 = 1 := two_even_power_mod_three (L + 1)
  have hex : ∃ k : ℕ, L ≤ k ∧ (2 ^ (k + 1) * a) % 3 = 1 := by
    by_cases h1 : a % 3 = 1
    · refine ⟨2 * L + 1, by omega, ?_⟩
      rw [show 2 * L + 1 + 1 = 2 * (L + 1) by omega, Nat.mul_mod, hj, h1]
    · have h2 : a % 3 = 2 := by omega
      refine ⟨2 * (L + 1), by omega, ?_⟩
      rw [pow_succ, Nat.mul_assoc, Nat.mul_mod, hj]
      have h2a : (2 * a) % 3 = 1 := by omega
      rw [h2a]
  obtain ⟨k, hk, hmod⟩ := hex
  have hz : 2 ^ (k + 1) * a = 2 * (2 ^ k * a) := by rw [pow_succ]; ring
  have hpos : 0 < 2 ^ k * a := by positivity
  have hge : 4 ≤ 2 ^ (k + 1) * a := by omega
  have he : (2 ^ (k + 1) * a) % 2 = 0 := by omega
  obtain ⟨m, mp, mo, me⟩ := odd_inverse_of_even_mod_three _ hge he hmod
  have hsplit : 2 ^ (k + 1) * a = 2 ^ (L + 1) * (2 ^ (k - L) * a) := by
    have hh : L + 1 + (k - L) = k + 1 := by omega
    rw [← mul_assoc, ← pow_add, hh]
  exact ⟨m, mp, (odd_inverse_missing_iff m a (k + 1) mo me).2 hm, mo,
    odd_inverse_prefix_count m (2 ^ (k - L) * a) L mo (me.trans hsplit)⟩

-- Orbit minima: the global count cannot be replaced by a count of minima.
theorem shortcut_pos_stage3 (n : ℕ) (hn : 0 < n) : 0 < shortcut n := by
  by_cases h : n % 2 = 0
  · simp only [shortcut, if_pos h]; omega
  · simp only [shortcut, if_neg h]; omega

theorem shortcutOrbit_pos_stage3 (k n : ℕ) (hn : 0 < n) : 0 < shortcutOrbit k n := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih => exact ih (shortcut n) (shortcut_pos_stage3 n hn)

theorem shortcutOrbit_add_stage3 (k l n : ℕ) :
    shortcutOrbit (k + l) n = shortcutOrbit l (shortcutOrbit k n) := by
  induction k generalizing n with
  | zero => simp [shortcutOrbit]
  | succ k ih =>
    rw [show k + 1 + l = (k + l) + 1 by omega]
    simp only [shortcutOrbit]
    exact ih (shortcut n)

def OrbitMinimum (n : ℕ) : Prop := ∀ k : ℕ, n ≤ shortcutOrbit k n

theorem missing_hits_orbit_minimum (n : ℕ) (hn : 0 < n) (hm : Missing n) :
    ∃ k : ℕ, 0 < shortcutOrbit k n ∧ Missing (shortcutOrbit k n) ∧
      OrbitMinimum (shortcutOrbit k n) := by
  classical
  have h : ∃ m : ℕ, ∃ k : ℕ, shortcutOrbit k n = m := ⟨n, 0, rfl⟩
  obtain ⟨k, hk⟩ := Nat.find_spec h
  refine ⟨k, shortcutOrbit_pos_stage3 k n hn,
    (not_congr (shortcut_orbit_basin_iff k n)).2 hm, ?_⟩
  intro l
  rw [← shortcutOrbit_add_stage3]
  rw [hk]
  exact Nat.find_min' h ⟨k + l, rfl⟩

theorem positive_orbit_minimum_odd (n : ℕ) (hn : 0 < n) (h : OrbitMinimum n) :
    n % 2 = 1 := by
  have hh := h 1
  change n ≤ shortcut n at hh
  by_contra hodd
  have he : n % 2 = 0 := by omega
  simp only [shortcut, if_pos he] at hh
  omega

-- Exact finite transfer certificate at s = 21/25 (0.84).
-- A branch is active when its child is not a multiple of 3.
def activeResidue (y k : ℕ) : Bool :=
  decide ((2 ^ k * y) % 3 = 1 ∧ (2 ^ k * y) % 9 ≠ 1)

def childResidue (y k : ℕ) : ℕ := ((2 ^ k * y - 1) / 3) % 3

-- Each entry records (k, child mod 3). This is the exact five-branch table.
def activeRow (y : ℕ) : List (ℕ × ℕ) :=
  ((List.range 5).map (fun k => k + 1)).filterMap
    (fun k => if activeResidue y k then some (k, childResidue y k) else none)

theorem five_branch_residue_table :
    activeRow 1 = [(2,1),(4,2)] ∧
    activeRow 2 = [(1,1),(3,2)] ∧
    activeRow 4 = [(2,2)] ∧
    activeRow 5 = [(3,1),(5,2)] ∧
    activeRow 7 = [(4,1)] ∧
    activeRow 8 = [(1,2),(5,1)] := by decide

-- These strictly rational lower bounds are certified by raising to power 25.
-- They imply bounds on (3 / 2^k)^(21/25) by monotonicity of positive powers.
theorem five_branch_rational_certificates :
    (1405 : ℚ)^25 * (2 : ℚ)^21 < 1000^25 * 3^21 ∧
    (785 : ℚ)^25 * (4 : ℚ)^21 < 1000^25 * 3^21 ∧
    (438 : ℚ)^25 * (8 : ℚ)^21 < 1000^25 * 3^21 ∧
    (245 : ℚ)^25 * (16 : ℚ)^21 < 1000^25 * 3^21 ∧
    (136 : ℚ)^25 * (32 : ℚ)^21 < 1000^25 * 3^21 := by norm_num

theorem five_branch_lower_sum :
    (3 : ℚ) < (1405 + 785 + 438 + 245 + 136) / 1000 := by norm_num

-- This algebraic identity is a certificate for the two-type averaged table.
theorem five_branch_total (w1 w2 w3 w4 w5 f1 f2 : ℝ) :
    (w2*f1+w4*f2) + (w1*f1+w3*f2) + w2*f2 +
      (w3*f1+w5*f2) + w4*f1 + (w1*f2+w5*f1) =
    (w1+w2+w3+w4+w5)*(f1+f2) := by ring

-- A positive potential depending on mod 3 cannot contract on all six
-- mod-9 parent types when the sum of the five branch weights exceeds 3.
theorem five_branch_no_two_type_contraction
    (w1 w2 w3 w4 w5 f1 f2 : ℝ)
    (hf : 0 < f1 + f2) (hw : 3 < w1+w2+w3+w4+w5)
    (h1 : w2*f1+w4*f2 ≤ f1) (h2 : w1*f1+w3*f2 ≤ f2)
    (h4 : w2*f2 ≤ f1) (h5 : w3*f1+w5*f2 ≤ f2)
    (h7 : w4*f1 ≤ f1) (h8 : w1*f2+w5*f1 ≤ f2) : False := by
  have ht := five_branch_total w1 w2 w3 w4 w5 f1 f2
  have hlt : 3*(f1+f2) < (w1+w2+w3+w4+w5)*(f1+f2) :=
    mul_lt_mul_of_pos_right hw hf
  linarith

-- General algebraic averaging obstruction, independently of residue depth.
-- The transfer mass identity must be established for the chosen operator.
theorem averaged_transfer_no_contraction (mass output rho : ℝ)
    (hm : 0 < mass) (hr : 1 < rho) (hid : output = rho * mass)
    (hcontract : output ≤ mass) : False := by
  have hlt := mul_lt_mul_of_pos_right hr hm
  rw [one_mul] at hlt
  linarith

-- Exact counting recurrence for the invariant missing indicator.
noncomputable def missingIndicator (n : ℕ) : ℕ := by
  classical
  exact if Missing n then 1 else 0

theorem missingIndicator_double (n : ℕ) : missingIndicator (2*n) = missingIndicator n := by
  classical
  simp only [missingIndicator, missing_double_iff]

theorem missingIndicator_odd (j : ℕ) :
    missingIndicator (2*j+1) = missingIndicator (3*j+2) := by
  classical
  have he : (2*j+1) % 2 ≠ 0 := by omega
  have hs : shortcut (2*j+1) = 3*j+2 := by
    simp only [shortcut, if_neg he]
    omega
  have h : Missing (shortcut (2*j+1)) ↔ Missing (2*j+1) :=
    not_congr (shortcut_basin_iff (2*j+1))
  rw [hs] at h
  simp only [missingIndicator, h]

-- Counts positive integers 1,...,N and the N values 2,5,...,3N-1.
noncomputable def missingCount : ℕ → ℕ
  | 0 => 0
  | n+1 => missingCount n + missingIndicator (n+1)

noncomputable def missingResidueTwoCount : ℕ → ℕ
  | 0 => 0
  | n+1 => missingResidueTwoCount n + missingIndicator (3*n+2)

theorem missing_count_identity (N : ℕ) :
    missingCount (2*N) = missingCount N + missingResidueTwoCount N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [show 2*(N+1) = (2*N+1)+1 by omega]
    simp only [missingCount, missingResidueTwoCount]
    rw [ih, missingIndicator_odd, show 2*N+1+1 = 2*(N+1) by omega,
      missingIndicator_double]
    omega

#print axioms odd_inverse_missing_iff
#print axioms odd_inverse_of_even_mod_three
#print axioms two_even_power_mod_three
#print axioms shortcut_zero_iterates
#print axioms even_prefix_exact
#print axioms missing_arbitrarily_long_even_prefix
#print axioms odd_inverse_prefix_count
#print axioms missing_arbitrarily_long_odd_prefix
#print axioms shortcut_pos_stage3
#print axioms shortcutOrbit_pos_stage3
#print axioms shortcutOrbit_add_stage3
#print axioms missing_hits_orbit_minimum
#print axioms positive_orbit_minimum_odd
#print axioms five_branch_residue_table
#print axioms five_branch_rational_certificates
#print axioms five_branch_lower_sum
#print axioms five_branch_total
#print axioms five_branch_no_two_type_contraction
#print axioms averaged_transfer_no_contraction
#print axioms missingIndicator_double
#print axioms missingIndicator_odd
#print axioms missing_count_identity

end CollatzRunyan.GeometricSpectral

/-! Stage 4: exact coefficient sandwich for finite no-descent windows,
    least missing integers, and smaller coalescence certificates.
    These lemmas do not assert global descent or a counting upper bound. -/
namespace CollatzRunyan.GeometricSpectral
set_option autoImplicit false

-- Twice the shortcut map has an exact division-free expression.
theorem shortcut_twice_formula (n : ℕ) :
    2 * shortcut n = 3 ^ parity n * n + parity n := by
  by_cases he : n % 2 = 0
  · have hp : parity n = 0 := he
    simp only [shortcut, if_pos he, hp, pow_zero, one_mul, add_zero]
    omega
  · have hp : parity n = 1 := by unfold parity; omega
    simp only [shortcut, if_neg he, hp, pow_one]
    omega

-- Discarding the nonnegative affine correction gives a lower bound.
theorem shortcut_coefficient_lower (k n : ℕ) :
    3 ^ shortcutOddCount k n * n ≤ 2 ^ k * shortcutOrbit k n := by
  induction k generalizing n with
  | zero => simp [shortcutOddCount, shortcutOrbit]
  | succ k ih =>
    have hs : 3 ^ parity n * n ≤ 2 * shortcut n := by
      rw [shortcut_twice_formula]
      omega
    change 3 ^ (shortcutOddCount k (shortcut n) + parity n) * n ≤
      2 ^ (k + 1) * shortcutOrbit k (shortcut n)
    calc
      _ = 3 ^ shortcutOddCount k (shortcut n) * (3 ^ parity n * n) := by
        rw [pow_add]; ring
      _ ≤ 3 ^ shortcutOddCount k (shortcut n) * (2 * shortcut n) :=
        Nat.mul_le_mul_left _ hs
      _ = 2 * (3 ^ shortcutOddCount k (shortcut n) * shortcut n) := by ring
      _ ≤ 2 * (2 ^ k * shortcutOrbit k (shortcut n)) :=
        Nat.mul_le_mul_left _ (ih (shortcut n))
      _ = _ := by rw [pow_succ]; ring

-- For a trajectory above a fixed floor m, control the affine term exactly.
theorem shortcut_floor_step (m n : ℕ) (h : m ≤ n) :
    2 * m ^ parity n * shortcut n ≤ (3 * m + 1) ^ parity n * n := by
  by_cases he : n % 2 = 0
  · have hp : parity n = 0 := he
    have hs := shortcut_twice_formula n
    rw [hp, pow_zero, one_mul, add_zero] at hs
    simpa only [hp, pow_zero, mul_one, one_mul] using hs.le
  · have hp : parity n = 1 := by unfold parity; omega
    have hs := shortcut_twice_formula n
    rw [hp, pow_one] at hs
    simp only [hp, pow_one]
    calc
      2 * m * shortcut n = m * (2 * shortcut n) := by ring
      _ = m * (3 * n + 1) := by rw [hs]
      _ ≤ (3 * m + 1) * n := by nlinarith

theorem shortcut_floor_upper (k m n : ℕ)
    (h : ∀ j : ℕ, j ≤ k → m ≤ shortcutOrbit j n) :
    2 ^ k * m ^ shortcutOddCount k n * shortcutOrbit k n ≤
      (3 * m + 1) ^ shortcutOddCount k n * n := by
  induction k generalizing n with
  | zero => simp [shortcutOddCount, shortcutOrbit]
  | succ k ih =>
    have h0 : m ≤ n := h 0 (by omega)
    have htail : ∀ j : ℕ, j ≤ k → m ≤ shortcutOrbit j (shortcut n) := by
      intro j hj
      exact h (j + 1) (by omega)
    have hi := ih (shortcut n) htail
    have hs := shortcut_floor_step m n h0
    change 2 ^ (k + 1) * m ^ (shortcutOddCount k (shortcut n) + parity n) *
      shortcutOrbit k (shortcut n) ≤
      (3 * m + 1) ^ (shortcutOddCount k (shortcut n) + parity n) * n
    calc
      _ = (2 * m ^ parity n) *
          (2 ^ k * m ^ shortcutOddCount k (shortcut n) * shortcutOrbit k (shortcut n)) := by
        rw [pow_succ, pow_add]; ring
      _ ≤ (2 * m ^ parity n) *
          ((3 * m + 1) ^ shortcutOddCount k (shortcut n) * shortcut n) :=
        Nat.mul_le_mul_left _ hi
      _ = (3 * m + 1) ^ shortcutOddCount k (shortcut n) *
          (2 * m ^ parity n * shortcut n) := by ring
      _ ≤ (3 * m + 1) ^ shortcutOddCount k (shortcut n) *
          ((3 * m + 1) ^ parity n * n) := Nat.mul_le_mul_left _ hs
      _ = _ := by rw [pow_add]; ring

def NoDescentThrough (k n : ℕ) : Prop := ∀ j : ℕ, j ≤ k → n ≤ shortcutOrbit j n

theorem prefix_minimum_power (k n : ℕ) (hn : 0 < n)
    (h : NoDescentThrough k n) :
    2 ^ k * n ^ shortcutOddCount k n ≤ (3 * n + 1) ^ shortcutOddCount k n := by
  have hu := shortcut_floor_upper k n n h
  have hl := Nat.mul_le_mul_left (2 ^ k * n ^ shortcutOddCount k n) (h k (by omega))
  have hh := hl.trans hu
  by_contra hc
  have hlt : (3 * n + 1) ^ shortcutOddCount k n < 2 ^ k * n ^ shortcutOddCount k n := by omega
  exact (not_lt_of_ge hh) (Nat.mul_lt_mul_of_pos_right hlt hn)

theorem orbit_minimum_power (k n : ℕ) (hn : 0 < n) (h : OrbitMinimum n) :
    2 ^ k * n ^ shortcutOddCount k n ≤ (3 * n + 1) ^ shortcutOddCount k n :=
  prefix_minimum_power k n hn (fun j _ => h j)

-- A noncontracting multiplicative coefficient is sufficient for finite non-descent.
theorem coefficient_no_descent_at (k n : ℕ) (h : 2 ^ k ≤ 3 ^ shortcutOddCount k n) :
    n ≤ shortcutOrbit k n := by
  have hh := (Nat.mul_le_mul_right n h).trans (shortcut_coefficient_lower k n)
  by_contra hc
  have hlt : shortcutOrbit k n < n := by omega
  have hp : 0 < (2 : ℕ) ^ k := by positivity
  exact (not_lt_of_ge hh) (Nat.mul_lt_mul_of_pos_left hlt hp)

theorem coefficient_prefix_no_descent (k n : ℕ)
    (h : ∀ j : ℕ, j ≤ k → 2 ^ j ≤ 3 ^ shortcutOddCount j n) :
    NoDescentThrough k n := by
  intro j hj
  exact coefficient_no_descent_at j n (h j hj)

-- The least missing integer is stronger than an orbit minimum: all smaller
-- positive integers belong to the basin, even if not in its forward orbit.
def LeastMissing (n : ℕ) : Prop :=
  0 < n ∧ Missing n ∧ ∀ m : ℕ, 0 < m → m < n → Basin m

theorem least_missing_exists (h : ∃ n : ℕ, 0 < n ∧ Missing n) :
    ∃ n : ℕ, LeastMissing n := by
  classical
  obtain ⟨hp, hm⟩ := Nat.find_spec h
  refine ⟨Nat.find h, hp, hm, ?_⟩
  intro m mp ml
  by_contra hb
  exact (not_lt_of_ge (Nat.find_min' h ⟨mp, hb⟩)) ml

theorem least_missing_gt_one (n : ℕ) (h : LeastMissing n) : 1 < n := by
  have hp := h.1
  by_contra hn
  have he : n = 1 := by omega
  apply h.2.1
  rw [he]
  exact basin_one

-- A smaller positive coalescing trajectory certifies that n is not least missing.
theorem coalescing_basin_iff (n m j l : ℕ)
    (h : shortcutOrbit j n = shortcutOrbit l m) : Basin n ↔ Basin m := by
  calc
    Basin n ↔ Basin (shortcutOrbit j n) := (shortcut_orbit_basin_iff j n).symm
    _ ↔ Basin (shortcutOrbit l m) := by rw [h]
    _ ↔ Basin m := shortcut_orbit_basin_iff l m

theorem least_missing_no_smaller_coalescence (n m j l : ℕ)
    (h : LeastMissing n) (hp : 0 < m) (hl : m < n) :
    shortcutOrbit j n ≠ shortcutOrbit l m := by
  intro he
  exact h.2.1 ((coalescing_basin_iff n m j l he).2 (h.2.2 m hp hl))

theorem least_missing_orbit_minimum (n : ℕ) (h : LeastMissing n) : OrbitMinimum n := by
  intro k
  by_contra hc
  have hl : shortcutOrbit k n < n := by omega
  have hp := shortcutOrbit_pos_stage3 k n h.1
  exact h.2.1 ((shortcut_orbit_basin_iff k n).1 (h.2.2 _ hp hl))

-- A smaller inverse odd branch exists whenever the least missing n is 2 mod 3.
theorem least_missing_not_two_mod_three (n : ℕ) (h : LeastMissing n) : n % 3 ≠ 2 := by
  intro h3
  have hn := least_missing_gt_one n h
  have he : (2*n) % 2 = 0 := by omega
  have hm : (2*n) % 3 = 1 := by omega
  obtain ⟨m, mp, mo, me⟩ := odd_inverse_of_even_mod_three (2*n) (by omega) he hm
  have ml : m < n := by omega
  have hEq : 3*m+1 = 2^1*n := by simpa using me
  exact ((odd_inverse_missing_iff m n 1 mo hEq).2 h.2.1) (h.2.2 m mp ml)

-- n = 1 mod 4 admits immediate descent in two shortcut steps when n > 1.
theorem least_missing_three_mod_four (n : ℕ) (h : LeastMissing n) : n % 4 = 3 := by
  have hn := least_missing_gt_one n h
  have ho := positive_orbit_minimum_odd n h.1 (least_missing_orbit_minimum n h)
  by_contra hc
  have h1 : n % 4 = 1 := by omega
  have he : n % 2 ≠ 0 := by omega
  have hs : shortcut n = (3*n+1)/2 := by simp only [shortcut, if_neg he]
  have hse : shortcut n % 2 = 0 := by rw [hs]; omega
  have hdesc : shortcutOrbit 2 n < n := by
    change shortcut (shortcut n) < n
    have hs2 : shortcut (shortcut n) = shortcut n / 2 := if_pos hse
    rw [hs2, hs]
    omega
  exact (not_lt_of_ge ((least_missing_orbit_minimum n h) 2)) hdesc

theorem least_missing_mod_twelve (n : ℕ) (h : LeastMissing n) :
    n % 12 = 3 ∨ n % 12 = 7 := by
  have h3 := least_missing_not_two_mod_three n h
  have h4 := least_missing_three_mod_four n h
  omega

-- General inverse-cylinder certificate: a strictly smaller integer maps
-- to the candidate along the given affine cylinder.
theorem least_missing_excludes_inverse_cylinder (k r q : ℕ)
    (hp : 0 < r + 2 ^ k * q)
    (hl : r + 2 ^ k * q < shortcutOrbit k r + 3 ^ shortcutOddCount k r * q) :
    ¬ LeastMissing (shortcutOrbit k r + 3 ^ shortcutOddCount k r * q) := by
  intro hm
  apply least_missing_no_smaller_coalescence _ _ 0 k hm hp hl
  change shortcutOrbit k r + 3 ^ shortcutOddCount k r * q =
    shortcutOrbit k (r + 2 ^ k * q)
  exact (binary_cylinder_affine k r q).1.symm

-- T^3(3 + 8q) = 4 + 9q. This excludes an entire inverse residue class.
theorem least_missing_not_four_mod_nine (n : ℕ) (h : LeastMissing n) : n % 9 ≠ 4 := by
  intro hr
  have hn : n = 4 + 9 * (n / 9) := by omega
  have he : shortcutOrbit 3 3 = 4 := by decide
  have ho : shortcutOddCount 3 3 = 2 := by decide
  have hc := least_missing_excludes_inverse_cylinder 3 3 (n / 9)
    (by norm_num <;> omega) (by rw [he, ho]; norm_num <;> omega)
  rw [he, ho] at hc
  norm_num at hc
  apply hc
  rw [← hn]
  exact h

-- Multiples of three have only doubled ancestors: no odd branch can
-- enter the zero residue class modulo three.
theorem multiple_three_preimage_double (k n : ℕ)
    (h : shortcutOrbit k n % 3 = 0) :
    n = 2 ^ k * shortcutOrbit k n := by
  induction k generalizing n with
  | zero => simp [shortcutOrbit]
  | succ k ih =>
    change shortcutOrbit k (shortcut n) % 3 = 0 at h
    have he : n % 2 = 0 := by
      by_contra hne
      exact (shortcut_orbit_nonmultiple_three k (shortcut n)
        (shortcut_odd_nonmultiple_three n (by omega))) h
    have hs : 2 * shortcut n = n := by
      simp only [shortcut, if_pos he]
      omega
    have hi := ih (shortcut n) h
    change n = 2 ^ (k + 1) * shortcutOrbit k (shortcut n)
    calc
      n = 2 * shortcut n := hs.symm
      _ = 2 * (2 ^ k * shortcutOrbit k (shortcut n)) := congrArg (fun a : ℕ => 2 * a) hi
      _ = _ := by rw [pow_succ]; ring

theorem multiple_three_no_smaller_ancestor (k m n : ℕ)
    (h3 : n % 3 = 0) (he : shortcutOrbit k m = n) : n ≤ m := by
  have h := multiple_three_preimage_double k m (by rw [he]; exact h3)
  rw [he] at h
  have hp : 0 < (2 : ℕ) ^ k := by positivity
  calc
    n = 1 * n := by simp
    _ ≤ 2 ^ k * n := Nat.mul_le_mul_right _ (by omega)
    _ = m := h.symm

-- Independent proof target: smaller coalescence for every n > 1.
-- No assumption that every trajectory already reaches one is used here.
theorem universal_smaller_coalescence_implies_converges
    (h : ∀ n : ℕ, 1 < n → ∃ m j l : ℕ, 0 < m ∧ m < n ∧
      shortcutOrbit j n = shortcutOrbit l m) : Converges := by
  classical
  intro n hn
  by_contra hb
  obtain ⟨a, ha⟩ := least_missing_exists ⟨n, hn, hb⟩
  obtain ⟨m, j, l, hp, hl, he⟩ := h a (least_missing_gt_one a ha)
  exact least_missing_no_smaller_coalescence a m j l ha hp hl he

#print axioms shortcut_twice_formula
#print axioms shortcut_coefficient_lower
#print axioms shortcut_floor_step
#print axioms shortcut_floor_upper
#print axioms prefix_minimum_power
#print axioms orbit_minimum_power
#print axioms coefficient_no_descent_at
#print axioms coefficient_prefix_no_descent
#print axioms least_missing_exists
#print axioms least_missing_gt_one
#print axioms coalescing_basin_iff
#print axioms least_missing_no_smaller_coalescence
#print axioms least_missing_orbit_minimum
#print axioms least_missing_not_two_mod_three
#print axioms least_missing_three_mod_four
#print axioms least_missing_mod_twelve
#print axioms least_missing_excludes_inverse_cylinder
#print axioms least_missing_not_four_mod_nine
#print axioms multiple_three_preimage_double
#print axioms multiple_three_no_smaller_ancestor
#print axioms universal_smaller_coalescence_implies_converges

end CollatzRunyan.GeometricSpectral


/-! Stage 5: uniform affine coalescence certificates and a finite binary sieve.
    This does not prove that the remaining residue classes are empty. -/
namespace CollatzRunyan.GeometricSpectral
set_option autoImplicit false

-- Two affine cylinders with equal endpoint and slope coalesce uniformly.
theorem affine_pair_coalescence (j l r b d e q : ℕ)
    (hc : shortcutOrbit j r = shortcutOrbit l b)
    (ha : 3 ^ shortcutOddCount j r * d = 3 ^ shortcutOddCount l b * e) :
    shortcutOrbit j (r + 2 ^ j * (d*q)) =
      shortcutOrbit l (b + 2 ^ l * (e*q)) := by
  rw [(binary_cylinder_affine j r (d*q)).1,
      (binary_cylinder_affine l b (e*q)).1, hc]
  simp only [← mul_assoc, ha]

-- The same certificate excludes a whole progression of least missing integers.
theorem least_missing_excludes_affine_pair (j l r b d e q : ℕ)
    (hb : 0 < b) (hbr : b < r)
    (hs : 2 ^ l * e ≤ 2 ^ j * d)
    (hc : shortcutOrbit j r = shortcutOrbit l b)
    (ha : 3 ^ shortcutOddCount j r * d = 3 ^ shortcutOddCount l b * e) :
    ¬ LeastMissing (r + 2 ^ j * (d*q)) := by
  intro hm
  have hp : 0 < b + 2 ^ l * (e*q) := by omega
  have hsl := Nat.mul_le_mul_right q hs
  have hlt : b + 2 ^ l * (e*q) < r + 2 ^ j * (d*q) := by
    rw [← mul_assoc, ← mul_assoc]
    omega
  exact least_missing_no_smaller_coalescence _ _ j l hm hp hlt
    (affine_pair_coalescence j l r b d e q hc ha)

theorem least_missing_excludes_progression (n M r : ℕ) (hn : LeastMissing n)
    (h : ∀ q : ℕ, ¬ LeastMissing (r + M*q)) : n % M ≠ r := by
  intro hr
  have he : r + M * (n / M) = n := by
    rw [← hr, Nat.mod_add_div]
  apply h (n / M)
  rw [he]
  exact hn

-- Correct the earlier prose transcription: 19, not 31, survives modulo 36.
theorem least_missing_mod36_stage5 (n : ℕ) (h : LeastMissing n) :
    n % 36 = 3 ∨ n % 36 = 7 ∨ n % 36 = 15 ∨ n % 36 = 19 ∨ n % 36 = 27 := by
  have h12 := least_missing_mod_twelve n h
  have h9 := least_missing_not_four_mod_nine n h
  omega

theorem least_missing_mod9_stage5 (n : ℕ) (h : LeastMissing n) :
    n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7 := by
  have h3 := least_missing_not_two_mod_three n h
  have h9 := least_missing_not_four_mod_nine n h
  omega

theorem least_missing_not_16_3 (n : ℕ) (hn : LeastMissing n) : n % 16 ≠ 3 := by
  apply least_missing_excludes_progression n 16 3 hn
  intro q
  have h := least_missing_excludes_affine_pair 4 0 3 2 1 9 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_32_11 (n : ℕ) (hn : LeastMissing n) : n % 32 ≠ 11 := by
  apply least_missing_excludes_progression n 32 11 hn
  intro q
  have h := least_missing_excludes_affine_pair 5 0 11 10 1 27 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_32_23 (n : ℕ) (hn : LeastMissing n) : n % 32 ≠ 23 := by
  apply least_missing_excludes_progression n 32 23 hn
  intro q
  have h := least_missing_excludes_affine_pair 5 0 23 20 1 27 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

-- Bidirectional certificate (both starting points may initially rise).
theorem coalescence_64_15 (q : ℕ) :
    shortcutOrbit 6 (15 + 64*q) = shortcutOrbit 1 (13 + 54*q) := by
  have h := affine_pair_coalescence 6 1 15 13 1 27 q (by decide) (by decide)
  rw [← mul_assoc, ← mul_assoc] at h
  exact h

theorem least_missing_not_64_15 (n : ℕ) (hn : LeastMissing n) : n % 64 ≠ 15 := by
  apply least_missing_excludes_progression n 64 15 hn
  intro q
  have h := least_missing_excludes_affine_pair 6 1 15 13 1 27 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_128_7 (n : ℕ) (hn : LeastMissing n) : n % 128 ≠ 7 := by
  apply least_missing_excludes_progression n 128 7 hn
  intro q
  have h := least_missing_excludes_affine_pair 7 0 7 5 1 81 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_128_59 (n : ℕ) (hn : LeastMissing n) : n % 128 ≠ 59 := by
  apply least_missing_excludes_progression n 128 59 hn
  intro q
  have h := least_missing_excludes_affine_pair 7 0 59 38 1 81 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

-- Bidirectional certificate (both starting points may initially rise).
theorem coalescence_128_95 (q : ℕ) :
    shortcutOrbit 7 (95 + 128*q) = shortcutOrbit 5 (71 + 96*q) := by
  have h := affine_pair_coalescence 7 5 95 71 1 3 q (by decide) (by decide)
  rw [← mul_assoc, ← mul_assoc] at h
  exact h

theorem least_missing_not_128_95 (n : ℕ) (hn : LeastMissing n) : n % 128 ≠ 95 := by
  apply least_missing_excludes_progression n 128 95 hn
  intro q
  have h := least_missing_excludes_affine_pair 7 5 95 71 1 3 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_256_39 (n : ℕ) (hn : LeastMissing n) : n % 256 ≠ 39 := by
  apply least_missing_excludes_progression n 256 39 hn
  intro q
  have h := least_missing_excludes_affine_pair 8 0 39 38 1 243 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

-- Bidirectional certificate (both starting points may initially rise).
theorem coalescence_256_63 (q : ℕ) :
    shortcutOrbit 8 (63 + 256*q) = shortcutOrbit 6 (47 + 192*q) := by
  have h := affine_pair_coalescence 8 6 63 47 1 3 q (by decide) (by decide)
  rw [← mul_assoc, ← mul_assoc] at h
  exact h

theorem least_missing_not_256_63 (n : ℕ) (hn : LeastMissing n) : n % 256 ≠ 63 := by
  apply least_missing_excludes_progression n 256 63 hn
  intro q
  have h := least_missing_excludes_affine_pair 8 6 63 47 1 3 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_256_123 (n : ℕ) (hn : LeastMissing n) : n % 256 ≠ 123 := by
  apply least_missing_excludes_progression n 256 123 hn
  intro q
  have h := least_missing_excludes_affine_pair 8 0 123 118 1 243 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_256_175 (n : ℕ) (hn : LeastMissing n) : n % 256 ≠ 175 := by
  apply least_missing_excludes_progression n 256 175 hn
  intro q
  have h := least_missing_excludes_affine_pair 8 0 175 167 1 243 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_256_199 (n : ℕ) (hn : LeastMissing n) : n % 256 ≠ 199 := by
  apply least_missing_excludes_progression n 256 199 hn
  intro q
  have h := least_missing_excludes_affine_pair 8 0 199 190 1 243 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

theorem least_missing_not_256_219 (n : ℕ) (hn : LeastMissing n) : n % 256 ≠ 219 := by
  apply least_missing_excludes_progression n 256 219 hn
  intro q
  have h := least_missing_excludes_affine_pair 8 0 219 209 1 243 q
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [← mul_assoc] at h
  exact h

-- Closed finite coverage check, using kernel reduction (not native_decide).
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem stage5_binary_table : ∀ r : Fin 256, r.val % 4 = 3 →
    r.val % 16 ≠ 3 →
    r.val % 32 ≠ 11 →
    r.val % 32 ≠ 23 →
    r.val % 64 ≠ 15 →
    r.val % 128 ≠ 7 →
    r.val % 128 ≠ 59 →
    r.val % 128 ≠ 95 →
    r.val % 256 ≠ 39 →
    r.val % 256 ≠ 63 →
    r.val % 256 ≠ 123 →
    r.val % 256 ≠ 175 →
    r.val % 256 ≠ 199 →
    r.val % 256 ≠ 219 →
    r.val ∈ ([27, 31, 47, 71, 91, 103, 111, 127, 155, 159, 167, 191, 231, 239, 251, 255] : List ℕ) := by decide

theorem least_missing_mod256_stage5 (n : ℕ) (hn : LeastMissing n) :
    n % 256 ∈ ([27, 31, 47, 71, 91, 103, 111, 127, 155, 159, 167, 191, 231, 239, 251, 255] : List ℕ) := by
  let r : Fin 256 := ⟨n % 256, Nat.mod_lt n (by decide)⟩
  have h4 : r.val % 4 = 3 := by
    dsimp [r]
    have h := least_missing_three_mod_four n hn
    omega
  have h16_3 : r.val % 16 ≠ 3 := by
    dsimp [r]
    have h := least_missing_not_16_3 n hn
    omega
  have h32_11 : r.val % 32 ≠ 11 := by
    dsimp [r]
    have h := least_missing_not_32_11 n hn
    omega
  have h32_23 : r.val % 32 ≠ 23 := by
    dsimp [r]
    have h := least_missing_not_32_23 n hn
    omega
  have h64_15 : r.val % 64 ≠ 15 := by
    dsimp [r]
    have h := least_missing_not_64_15 n hn
    omega
  have h128_7 : r.val % 128 ≠ 7 := by
    dsimp [r]
    have h := least_missing_not_128_7 n hn
    omega
  have h128_59 : r.val % 128 ≠ 59 := by
    dsimp [r]
    have h := least_missing_not_128_59 n hn
    omega
  have h128_95 : r.val % 128 ≠ 95 := by
    dsimp [r]
    have h := least_missing_not_128_95 n hn
    omega
  have h256_39 : r.val % 256 ≠ 39 := by
    dsimp [r]
    have h := least_missing_not_256_39 n hn
    omega
  have h256_63 : r.val % 256 ≠ 63 := by
    dsimp [r]
    have h := least_missing_not_256_63 n hn
    omega
  have h256_123 : r.val % 256 ≠ 123 := by
    dsimp [r]
    have h := least_missing_not_256_123 n hn
    omega
  have h256_175 : r.val % 256 ≠ 175 := by
    dsimp [r]
    have h := least_missing_not_256_175 n hn
    omega
  have h256_199 : r.val % 256 ≠ 199 := by
    dsimp [r]
    have h := least_missing_not_256_199 n hn
    omega
  have h256_219 : r.val % 256 ≠ 219 := by
    dsimp [r]
    have h := least_missing_not_256_219 n hn
    omega
  exact stage5_binary_table r h4
    h16_3 h32_11 h32_23 h64_15 h128_7 h128_59 h128_95 h256_39 h256_63 h256_123 h256_175 h256_199 h256_219

-- Both binary and ternary restrictions are simultaneously necessary.
theorem least_missing_joint_sieve (n : ℕ) (hn : LeastMissing n) :
    n % 256 ∈ ([27, 31, 47, 71, 91, 103, 111, 127, 155, 159, 167, 191, 231, 239, 251, 255] : List ℕ) ∧
      (n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7) :=
  ⟨least_missing_mod256_stage5 n hn, least_missing_mod9_stage5 n hn⟩

#print axioms affine_pair_coalescence
#print axioms least_missing_excludes_affine_pair
#print axioms least_missing_excludes_progression
#print axioms least_missing_mod36_stage5
#print axioms least_missing_mod9_stage5
#print axioms least_missing_not_16_3
#print axioms least_missing_not_32_11
#print axioms least_missing_not_32_23
#print axioms coalescence_64_15
#print axioms least_missing_not_64_15
#print axioms least_missing_not_128_7
#print axioms least_missing_not_128_59
#print axioms coalescence_128_95
#print axioms least_missing_not_128_95
#print axioms least_missing_not_256_39
#print axioms coalescence_256_63
#print axioms least_missing_not_256_63
#print axioms least_missing_not_256_123
#print axioms least_missing_not_256_175
#print axioms least_missing_not_256_199
#print axioms least_missing_not_256_219
#print axioms stage5_binary_table
#print axioms least_missing_mod256_stage5
#print axioms least_missing_joint_sieve

end CollatzRunyan.GeometricSpectral

/-! Stage 6: compositional coalescence, all-odd bounds and mixed-residue certificates.
    The finite table is not a global coverage theorem. -/
namespace CollatzRunyan.GeometricSpectral
set_option autoImplicit false

def Stage6Coalesces (a b : ℕ) : Prop :=
  ∃ j l : ℕ, shortcutOrbit j a = shortcutOrbit l b

theorem stage6_coalesces_refl (a : ℕ) : Stage6Coalesces a a :=
  ⟨0, 0, rfl⟩

theorem stage6_coalesces_symm (a b : ℕ) (h : Stage6Coalesces a b) :
    Stage6Coalesces b a := by
  obtain ⟨j, l, hj⟩ := h
  exact ⟨l, j, hj.symm⟩

theorem stage6_coalesces_trans (a b c : ℕ)
    (hab : Stage6Coalesces a b) (hbc : Stage6Coalesces b c) :
    Stage6Coalesces a c := by
  obtain ⟨j, l, h₁⟩ := hab
  obtain ⟨p, q, h₂⟩ := hbc
  refine ⟨j + p, q + l, ?_⟩
  calc
    shortcutOrbit (j+p) a = shortcutOrbit p (shortcutOrbit j a) := shortcutOrbit_add_stage3 j p a
    _ = shortcutOrbit p (shortcutOrbit l b) := by rw [h₁]
    _ = shortcutOrbit (l+p) b := (shortcutOrbit_add_stage3 l p b).symm
    _ = shortcutOrbit (p+l) b := by rw [Nat.add_comm l p]
    _ = shortcutOrbit l (shortcutOrbit p b) := shortcutOrbit_add_stage3 p l b
    _ = shortcutOrbit l (shortcutOrbit q c) := by rw [h₂]
    _ = shortcutOrbit (q+l) c := (shortcutOrbit_add_stage3 q l c).symm

theorem stage6_coalesces_basin_iff (a b : ℕ) (h : Stage6Coalesces a b) : Basin a ↔ Basin b := by
  obtain ⟨j, l, he⟩ := h
  exact coalescing_basin_iff a b j l he

theorem stage6_chain_excludes_least (a b c : ℕ) (h : LeastMissing a)
    (hab : Stage6Coalesces a b) (hbc : Stage6Coalesces b c)
    (hc : 0 < c) (hlt : c < a) : False := by
  exact h.2.1 ((stage6_coalesces_basin_iff a c (stage6_coalesces_trans a b c hab hbc)).2
    (h.2.2 c hc hlt))

-- Exact shifted all-odd iterate, including the parity count.
theorem stage6_all_odd_shifted (k n q : ℕ) (h : n+1 = 2^k*q) :
    shortcutOddCount k n = k ∧ shortcutOrbit k n + 1 = 3^k*q := by
  induction k generalizing n q with
  | zero =>
    constructor
    · rfl
    · simpa [shortcutOrbit] using h
  | succ k ih =>
    have he : n+1 = 2*(2^k*q) := by rw [h, pow_succ]; ring
    have hp : parity n = 1 := by unfold parity; omega
    have hs := shortcut_twice_formula n
    rw [hp, pow_one] at hs
    have ht : shortcut n+1 = 2^k*(3*q) := by
      have hx : shortcut n+1 = 3*(2^k*q) := by omega
      rw [hx]; ring
    obtain ⟨hc, ho⟩ := ih (shortcut n) (3*q) ht
    constructor
    · change shortcutOddCount k (shortcut n) + parity n = k+1
      rw [hc, hp]
    · change shortcutOrbit k (shortcut n)+1 = 3^(k+1)*q
      rw [ho, pow_succ]; ring

theorem stage6_shifted_step_upper (n : ℕ) : 2*(shortcut n+1) ≤ 3*(n+1) := by
  by_cases he : n % 2 = 0
  · simp only [shortcut, if_pos he]
    omega
  · simp only [shortcut, if_neg he]
    omega

theorem stage6_shifted_orbit_upper (k n : ℕ) :
    2^k*(shortcutOrbit k n+1) ≤ 3^k*(n+1) := by
  induction k generalizing n with
  | zero => simp [shortcutOrbit]
  | succ k ih =>
    change 2^(k+1)*(shortcutOrbit k (shortcut n)+1) ≤ 3^(k+1)*(n+1)
    calc
      _ = 2*(2^k*(shortcutOrbit k (shortcut n)+1)) := by rw [pow_succ]; ring
      _ ≤ 2*(3^k*(shortcut n+1)) := Nat.mul_le_mul_left _ (ih (shortcut n))
      _ = 3^k*(2*(shortcut n+1)) := by ring
      _ ≤ 3^k*(3*(n+1)) := Nat.mul_le_mul_left _ (stage6_shifted_step_upper n)
      _ = _ := by rw [pow_succ]; ring

theorem stage6_all_odd_no_equal_depth_smaller (k n q b : ℕ)
    (h : n+1 = 2^k*q) (hb : b < n) :
    shortcutOrbit k b ≠ shortcutOrbit k n := by
  intro he
  have hu := stage6_shifted_orbit_upper k b
  rw [he, (stage6_all_odd_shifted k n q h).2] at hu
  have heq : 2^k*(3^k*q) = 3^k*(n+1) := by rw [h]; ring
  rw [heq] at hu
  exact (not_lt_of_ge hu) (Nat.mul_lt_mul_of_pos_left (by omega : b+1 < n+1) (by positivity))

-- The mixed-residue table uses the verified Stage 5 affine-pair theorem.
-- Each record gives r,b,j,l,d,e with 2^j*d = 9216.
structure Stage6Certificate where
  r : ℕ
  b : ℕ
  j : ℕ
  l : ℕ
  d : ℕ
  e : ℕ

def stage6Certificates : List Stage6Certificate := [
  ⟨255, 191, 10, 8, 9, 27⟩,
  ⟨367, 349, 9, 1, 18, 4374⟩,
  ⟨411, 391, 9, 1, 18, 4374⟩,
  ⟨423, 302, 10, 0, 9, 6561⟩,
  ⟨487, 463, 9, 1, 18, 4374⟩,
  ⟨507, 362, 10, 0, 9, 6561⟩,
  ⟨583, 416, 10, 0, 9, 6561⟩,
  ⟨615, 519, 10, 5, 9, 243⟩,
  ⟨799, 759, 9, 1, 18, 4374⟩,
  ⟨879, 835, 9, 1, 18, 4374⟩,
  ⟨999, 949, 9, 1, 18, 4374⟩,
  ⟨1279, 959, 10, 8, 9, 27⟩,
  ⟨1311, 1245, 9, 1, 18, 4374⟩,
  ⟨1371, 977, 10, 0, 9, 6561⟩,
  ⟨1407, 1055, 9, 7, 18, 54⟩,
  ⟨1447, 1031, 10, 0, 9, 6561⟩,
  ⟨1531, 1091, 10, 0, 9, 6561⟩,
  ⟨1563, 1319, 10, 5, 9, 243⟩,
  ⟨1639, 1383, 10, 5, 9, 243⟩,
  ⟨1839, 1310, 10, 0, 9, 6561⟩,
  ⟨1947, 1849, 9, 1, 18, 4374⟩,
  ⟨2023, 1921, 9, 1, 18, 4374⟩,
  ⟨2395, 1706, 10, 0, 9, 6561⟩,
  ⟨2415, 2293, 9, 1, 18, 4374⟩,
  ⟨2431, 1823, 9, 7, 18, 54⟩,
  ⟨2535, 2407, 9, 1, 18, 4374⟩,
  ⟨2631, 1874, 10, 0, 9, 6561⟩,
  ⟨2847, 2703, 9, 1, 18, 4374⟩,
  ⟨2863, 2039, 10, 0, 9, 6561⟩,
  ⟨2943, 2207, 9, 7, 18, 54⟩,
  ⟨2971, 2821, 9, 1, 18, 4374⟩,
  ⟨3327, 2495, 10, 8, 9, 27⟩,
  ⟨3439, 3265, 9, 1, 18, 4374⟩,
  ⟨3483, 3307, 9, 1, 18, 4374⟩,
  ⟨3495, 2489, 10, 0, 9, 6561⟩,
  ⟨3579, 2549, 10, 0, 9, 6561⟩,
  ⟨3655, 2603, 10, 0, 9, 6561⟩,
  ⟨3687, 3111, 10, 5, 9, 243⟩,
  ⟨3871, 3675, 9, 1, 18, 4374⟩,
  ⟨3951, 3751, 9, 1, 18, 4374⟩,
  ⟨3967, 2975, 9, 7, 18, 54⟩,
  ⟨4071, 3865, 9, 1, 18, 4374⟩,
  ⟨4383, 4161, 9, 1, 18, 4374⟩,
  ⟨4443, 3164, 10, 0, 9, 6561⟩,
  ⟨4479, 3359, 9, 7, 18, 54⟩,
  ⟨4507, 4279, 9, 1, 18, 4374⟩,
  ⟨4519, 3218, 10, 0, 9, 6561⟩,
  ⟨4635, 3911, 10, 5, 9, 243⟩,
  ⟨4911, 3497, 10, 0, 9, 6561⟩,
  ⟨4975, 4723, 9, 1, 18, 4374⟩,
  ⟨5019, 4765, 9, 1, 18, 4374⟩,
  ⟨5095, 4837, 9, 1, 18, 4374⟩,
  ⟨5407, 5133, 9, 1, 18, 4374⟩,
  ⟨5487, 5209, 9, 1, 18, 4374⟩,
  ⟨5607, 5323, 9, 1, 18, 4374⟩,
  ⟨5659, 4775, 10, 5, 9, 243⟩,
  ⟨5703, 4061, 10, 0, 9, 6561⟩,
  ⟨5919, 5619, 9, 1, 18, 4374⟩,
  ⟨6015, 4511, 9, 7, 18, 54⟩,
  ⟨6399, 4799, 10, 8, 9, 27⟩,
  ⟨6555, 6223, 9, 1, 18, 4374⟩,
  ⟨6567, 4676, 10, 0, 9, 6561⟩,
  ⟨6631, 6295, 9, 1, 18, 4374⟩,
  ⟨6651, 4736, 10, 0, 9, 6561⟩,
  ⟨6759, 5703, 10, 5, 9, 243⟩,
  ⟨7023, 6667, 9, 1, 18, 4374⟩,
  ⟨7039, 5279, 9, 7, 18, 54⟩,
  ⟨7143, 6781, 9, 1, 18, 4374⟩,
  ⟨7423, 5567, 10, 8, 9, 27⟩,
  ⟨7455, 7077, 9, 1, 18, 4374⟩,
  ⟨7515, 5351, 10, 0, 9, 6561⟩,
  ⟨7551, 5663, 9, 7, 18, 54⟩,
  ⟨7579, 7195, 9, 1, 18, 4374⟩,
  ⟨7675, 5465, 10, 0, 9, 6561⟩,
  ⟨7707, 6503, 10, 5, 9, 243⟩,
  ⟨7783, 6567, 10, 5, 9, 243⟩,
  ⟨7983, 5684, 10, 0, 9, 6561⟩,
  ⟨8047, 7639, 9, 1, 18, 4374⟩,
  ⟨8091, 7681, 9, 1, 18, 4374⟩,
  ⟨8479, 8049, 9, 1, 18, 4374⟩,
  ⟨8539, 6080, 10, 0, 9, 6561⟩,
  ⟨8559, 8125, 9, 1, 18, 4374⟩,
  ⟨8575, 6431, 9, 7, 18, 54⟩,
  ⟨8679, 8239, 9, 1, 18, 4374⟩,
  ⟨8731, 7367, 10, 5, 9, 243⟩,
  ⟨8775, 6248, 10, 0, 9, 6561⟩,
  ⟨8991, 8535, 9, 1, 18, 4374⟩,
  ⟨9007, 6413, 10, 0, 9, 6561⟩,
  ⟨9087, 6815, 9, 7, 18, 54⟩,
  ⟨9115, 8653, 9, 1, 18, 4374⟩
]

def stage6Certificate (i : Fin 90) : Stage6Certificate :=
  stage6Certificates.get ⟨i.val, by simpa [stage6Certificates] using i.isLt⟩

def Stage6Valid (c : Stage6Certificate) : Prop :=
  2^c.j*c.d = 9216 ∧ 0 < c.b ∧ c.b < c.r ∧
  2^c.l*c.e ≤ 2^c.j*c.d ∧
  shortcutOrbit c.j c.r = shortcutOrbit c.l c.b ∧
  3^shortcutOddCount c.j c.r*c.d = 3^shortcutOddCount c.l c.b*c.e

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem stage6_certificate_valid (i : Fin 90) : Stage6Valid (stage6Certificate i) := by
  fin_cases i <;> unfold Stage6Valid <;> decide

theorem stage6_certificate_excludes (n : ℕ) (hn : LeastMissing n) (i : Fin 90) :
    n % 9216 ≠ (stage6Certificate i).r := by
  let c := stage6Certificate i
  change n % 9216 ≠ c.r
  obtain ⟨hm, hp, hb, hs, hc, ha⟩ := stage6_certificate_valid i
  change 2^c.j*c.d = 9216 at hm
  apply least_missing_excludes_progression n 9216 c.r hn
  intro q
  have h := least_missing_excludes_affine_pair c.j c.l c.r c.b c.d c.e q hp hb hs hc ha
  rw [← mul_assoc, hm] at h
  exact h

#print axioms stage6_coalesces_refl
#print axioms stage6_coalesces_symm
#print axioms stage6_coalesces_trans
#print axioms stage6_coalesces_basin_iff
#print axioms stage6_chain_excludes_least
#print axioms stage6_all_odd_shifted
#print axioms stage6_shifted_step_upper
#print axioms stage6_shifted_orbit_upper
#print axioms stage6_all_odd_no_equal_depth_smaller
#print axioms stage6_certificate_valid
#print axioms stage6_certificate_excludes

end CollatzRunyan.GeometricSpectral
