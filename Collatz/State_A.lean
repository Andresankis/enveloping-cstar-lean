import Mathlib

/-!
# Algebraic states
-/

set_option linter.defProp false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

structure AlgState (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] where
  toFun : A → ℂ
  map_one : toFun 1 = 1
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_smul : ∀ (r : ℂ) (a : A), toFun (r • a) = r * toFun a
  positive_re : ∀ a, (toFun (star a * a)).re ≥ 0
  positive_im : ∀ a, (toFun (star a * a)).im = 0

namespace AlgState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

instance : CoeFun (AlgState A) (fun _ => A → ℂ) := ⟨AlgState.toFun⟩

lemma map_zero (ω : AlgState A) : ω 0 = 0 := by
  have h : ω 0 + ω 0 = ω 0 + 0 := by
    rw [add_zero, ← ω.map_add, add_zero]
  exact add_left_cancel h

lemma map_neg (ω : AlgState A) (a : A) : ω (-a) = -ω a := by
  have h : ω (-a) + ω a = 0 := by
    rw [← ω.map_add, neg_add_cancel, ω.map_zero]
  exact add_eq_zero_iff_eq_neg.mp h

lemma map_sub (ω : AlgState A) (a b : A) : ω (a - b) = ω a - ω b := by
  rw [sub_eq_add_neg, ω.map_add, ω.map_neg, sub_eq_add_neg]

lemma coe_star (ω : AlgState A) (a : A) : ω (star a) = star (ω a) := by
  -- Step 1: Im(ω(star a)) = -Im(ω a)
  have h1 : (ω (star a)).im = -(ω a).im := by
    have h := ω.positive_im (1 + a)
    have h_expand : star (1 + a) * (1 + a) = 1 + a + star a + star a * a := by
      rw [star_add, star_one, add_mul, one_mul, mul_add, mul_one]
      abel_nf
    rw [h_expand] at h
    simp only [ω.map_add, ω.map_one, Complex.add_im, Complex.one_im, zero_add] at h
    have h_im : (ω (star a * a)).im = 0 := ω.positive_im a
    linarith
  -- Step 2: Re(ω(star a)) = Re(ω a)
  have h2 : (ω (star a)).re = (ω a).re := by
    have h := ω.positive_im (1 + Complex.I • a)
    have h_star : star (1 + Complex.I • a) = 1 - Complex.I • star a := by
      rw [star_add, star_one, star_smul, Complex.star_def, Complex.conj_I]
      rw [neg_smul, sub_eq_add_neg]
    rw [h_star] at h
    have h_expand : (1 - Complex.I • star a) * (1 + Complex.I • a) =
        1 + Complex.I • a - Complex.I • star a + star a * a := by
      rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [Complex.I_mul_I]
      simp only [neg_smul, one_smul]
      abel_nf
    rw [h_expand] at h
    simp only [ω.map_add, ω.map_sub, ω.map_one, ω.map_smul,
               Complex.add_im, Complex.sub_im, Complex.one_im,
               Complex.mul_im, Complex.I_re, Complex.I_im] at h
    have h_im : (ω (star a * a)).im = 0 := ω.positive_im a
    linarith
  -- Assembly
  rw [Complex.star_def, Complex.ext_iff]
  exact ⟨h2, h1⟩


lemma coe_star_mul_comm (ω : AlgState A) (a b : A) :
    ω (star b * a) = star (ω (star a * b)) := by
  have h : star b * a = star (star a * b) := by
    rw [star_mul, star_star]
  rw [h, ω.coe_star]

lemma quadratic_expand (ω : AlgState A) (a b : A) (z : ℂ) :
    ω (star (a + z • b) * (a + z • b)) =
      ω (star a * a) + z * ω (star a * b) +
        star z * ω (star b * a) + (star z * z) * ω (star b * b) := by
  have h_mul : star (a + z • b) * (a + z • b) =
      star a * a + z • (star a * b) + star z • (star b * a) +
        (star z * z) • (star b * b) := by
    rw [star_add, star_smul, add_mul, mul_add, mul_add]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm z (star z)]
    abel
  rw [h_mul]
  simp only [ω.map_add, ω.map_smul]

lemma omega_selfadjoint_real (ω : AlgState A) (a : A) :
    ω (star a * a) = ↑(ω (star a * a)).re := by
  apply Complex.ext
  · simp
  · exact ω.positive_im a

lemma omega_selfadjoint_re_nonneg (ω : AlgState A) (a : A) :
    (ω (star a * a)).re ≥ 0 := ω.positive_re a

lemma re_mul (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im :=
  Complex.mul_re z w

lemma re_star_mul (z w : ℂ) : (star z * w).re = z.re * w.re + z.im * w.im := by
  simp [Complex.mul_re]

lemma re_star_mul_self (z : ℂ) : (star z * z).re = Complex.normSq z := by
  simp [Complex.mul_re, Complex.normSq]

lemma im_star_mul_self (z : ℂ) : (star z * z).im = 0 := by
  simp [Complex.mul_im]
  ring

lemma quadratic_nonneg (ω : AlgState A) (a b : A) (z : ℂ) :
    0 ≤ (ω (star a * a)).re + 2 * (z.re * (ω (star a * b)).re -
      z.im * (ω (star a * b)).im) + Complex.normSq z * (ω (star b * b)).re := by
  have h := ω.positive_re (a + z • b)
  rw [quadratic_expand] at h
  rw [ω.coe_star_mul_comm a b] at h
  have hC : (ω (star b * b)).im = 0 := ω.positive_im b
  have h_eq : (ω (star a * a) + z * ω (star a * b) + star z * star (ω (star a * b)) +
      (star z * z) * ω (star b * b)).re =
      (ω (star a * a)).re + 2 * (z.re * (ω (star a * b)).re -
        z.im * (ω (star a * b)).im) + Complex.normSq z * (ω (star b * b)).re := by
    rw [show star z * star (ω (star a * b)) = star (z * ω (star a * b)) from
        (map_mul (starRingEnd ℂ) z (ω (star a * b))).symm]
    rw [Complex.add_re, Complex.add_re, Complex.add_re]
    rw [Complex.mul_re]
    rw [show (star (z * ω (star a * b))).re = (z * ω (star a * b)).re from
        Complex.conj_re (z * ω (star a * b))]
    rw [Complex.mul_re]
    rw [Complex.mul_re]
    rw [show (star z * z).re = Complex.normSq z from re_star_mul_self z]
    rw [show (star z * z).im = 0 from im_star_mul_self z]
    rw [hC, Complex.normSq_apply]
    ring
  rw [h_eq] at h
  exact h

lemma cauchy_schwarz_pos (ω : AlgState A) (a b : A) (hC : (ω (star b * b)).re > 0) :
    Complex.normSq (ω (star a * b)) ≤
      (ω (star a * a)).re * (ω (star b * b)).re := by
  set A_val := (ω (star a * a)).re with hA_val
  set B_val := ω (star a * b) with hB_val
  set C_val := (ω (star b * b)).re with hC_val
  have hC_pos : 0 < C_val := hC
  have hC_ne : (C_val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hC_pos
  let z : ℂ := -star B_val / (C_val : ℂ)
  have hz_re : z.re = -B_val.re / C_val := by
    simp only [z, Complex.div_re, Complex.neg_re, Complex.star_def,
               Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [Complex.normSq_ofReal]
    field_simp
    ring
  have hz_im : z.im = B_val.im / C_val := by
    simp only [z, Complex.div_im, Complex.neg_im, Complex.star_def,
               Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [Complex.normSq_ofReal]
    field_simp
    ring
  have hz_normSq : Complex.normSq z = Complex.normSq B_val / C_val^2 := by
    rw [Complex.normSq_apply, Complex.normSq_apply, hz_re, hz_im]
    field_simp
  have h_quad := quadratic_nonneg ω a b z
  rw [show (ω (star a * a)).re = A_val from hA_val.symm,
      show (ω (star b * b)).re = C_val from hC_val.symm,
      show (ω (star a * b)).re = B_val.re from by rw [← hB_val],
      show (ω (star a * b)).im = B_val.im from by rw [← hB_val]] at h_quad
  rw [hz_re, hz_im, hz_normSq] at h_quad
  rw [Complex.normSq_apply] at h_quad
  have h_key : 2 * (-B_val.re / C_val * B_val.re - B_val.im / C_val * B_val.im) +
      (B_val.re * B_val.re + B_val.im * B_val.im) / C_val^2 * C_val =
      -(B_val.re * B_val.re + B_val.im * B_val.im) / C_val := by
    field_simp
    ring
  have h_final : (B_val.re * B_val.re + B_val.im * B_val.im) / C_val ≤ A_val := by
    have h := h_quad
    rw [add_assoc] at h
    rw [h_key] at h
    rw [show A_val + -(B_val.re * B_val.re + B_val.im * B_val.im) / C_val =
        A_val - (B_val.re * B_val.re + B_val.im * B_val.im) / C_val from by ring] at h
    linarith
  have h_mul : B_val.re * B_val.re + B_val.im * B_val.im ≤ A_val * C_val :=
    (div_le_iff₀ hC_pos).mp h_final
  have h_normSq_eq : Complex.normSq B_val = B_val.re * B_val.re + B_val.im * B_val.im := by
    rw [Complex.normSq_apply]
  rw [show Complex.normSq (ω (star a * b)) = Complex.normSq B_val from by
        rw [← hB_val]]
  rw [h_normSq_eq]
  exact h_mul

lemma cauchy_schwarz (ω : AlgState A) (a b : A) :
    Complex.normSq (ω (star a * b)) ≤
      (ω (star a * a)).re * (ω (star b * b)).re := by
  have hC_nonneg : 0 ≤ (ω (star b * b)).re := ω.positive_re b
  rcases eq_or_lt_of_le hC_nonneg with hC0 | hC_pos
  · -- The case C = 0
    set A_val := (ω (star a * a)).re with hA_val
    set B_val := ω (star a * b) with hB_val
    have hB_zero : Complex.normSq B_val = 0 := by
      by_contra hB_ne
      have hB_pos : 0 < Complex.normSq B_val :=
        lt_of_le_of_ne (Complex.normSq_nonneg B_val) (Ne.symm hB_ne)
      have h2pos : (0 : ℝ) < 2 * Complex.normSq B_val := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (A_val / (2 * Complex.normSq B_val))
      have hn' : A_val < (n : ℝ) * (2 * Complex.normSq B_val) := by
        rw [div_lt_iff₀ h2pos] at hn
        linarith
      let z : ℂ := -(n : ℂ) * star B_val
      have hn_re : ((n : ℂ)).re = (n : ℝ) := Complex.natCast_re n
      have hn_im : ((n : ℂ)).im = 0 := Complex.natCast_im n
      have hz_re : z.re = -(n : ℝ) * B_val.re := by
        simp only [z, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
                   Complex.neg_re, Complex.neg_im, hn_re, hn_im]
        ring
      have hz_im : z.im = (n : ℝ) * B_val.im := by
        simp only [z, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
                   Complex.neg_re, Complex.neg_im, hn_re, hn_im]
        ring
      have hz_normSq : Complex.normSq z = (n : ℝ)^2 * Complex.normSq B_val := by
        rw [Complex.normSq_apply, hz_re, hz_im, Complex.normSq_apply]
        ring
      have h_quad := quadratic_nonneg ω a b z
      rw [show (ω (star a * a)).re = A_val from hA_val.symm,
          show (ω (star b * b)).re = 0 from hC0.symm,
          show (ω (star a * b)).re = B_val.re from by rw [← hB_val],
          show (ω (star a * b)).im = B_val.im from by rw [← hB_val]] at h_quad
      rw [hz_re, hz_im, hz_normSq] at h_quad
      rw [Complex.normSq_apply] at h_quad
      have h_normSq_B : Complex.normSq B_val = B_val.re * B_val.re + B_val.im * B_val.im := by
        rw [Complex.normSq_apply]
      rw [h_normSq_B] at hn'
      have h_contra : 0 ≤ A_val - 2 * (n : ℝ) * (B_val.re * B_val.re + B_val.im * B_val.im) := by
        have h := h_quad
        ring_nf at h
        linarith
      nlinarith [h_contra, hn']
    rw [show Complex.normSq (ω (star a * b)) = Complex.normSq B_val from by rw [← hB_val],
        hB_zero]
    rw [show (ω (star b * b)).re = 0 from hC0.symm, mul_zero]
  · exact cauchy_schwarz_pos ω a b hC_pos

/-- The radical of a state: the set of a with ω (star a * a) = 0 -/
abbrev radical (ω : AlgState A) : Set A := {a | ω (star a * a) = 0}

lemma mem_radical_zero (ω : AlgState A) : (0 : A) ∈ ω.radical := by
  simp [radical, AlgState.map_zero]

/-- Auxiliary lemma: if ω (star a * a) = 0, then ω (star a * b) = 0 for any b -/
lemma omega_star_mul_eq_zero (ω : AlgState A) {a : A}
    (ha : ω (star a * a) = 0) (b : A) : ω (star a * b) = 0 := by
  have h_cs := cauchy_schwarz ω a b
  have h_re_zero : (ω (star a * a)).re = 0 := by rw [ha]; simp
  rw [h_re_zero, zero_mul] at h_cs
  have h_normSq_zero : Complex.normSq (ω (star a * b)) = 0 :=
    le_antisymm h_cs (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp h_normSq_zero

lemma radical_add (ω : AlgState A) {a b : A}
    (ha : a ∈ ω.radical) (hb : b ∈ ω.radical) : a + b ∈ ω.radical := by
  simp only [radical, Set.mem_ofPred_eq] at ha hb ⊢
  rw [star_add, add_mul, mul_add, mul_add]
  rw [ω.map_add, ω.map_add, ω.map_add]
  rw [ha, hb, omega_star_mul_eq_zero ω ha b, omega_star_mul_eq_zero ω hb a]
  ring

lemma radical_neg (ω : AlgState A) {a : A} (ha : a ∈ ω.radical) : -a ∈ ω.radical := by
  simp only [radical, Set.mem_ofPred_eq] at ha ⊢
  rw [star_neg, neg_mul_neg]
  exact ha

lemma radical_smul (ω : AlgState A) (r : ℂ) {a : A}
    (ha : a ∈ ω.radical) : r • a ∈ ω.radical := by
  simp only [radical, Set.mem_ofPred_eq] at ha ⊢
  have h_smul_eq : star (r • a) * (r • a) = (star r * r) • (star a * a) := by
    rw [star_smul, smul_mul_assoc, mul_smul_comm]
    rw [smul_smul]
  rw [h_smul_eq, ω.map_smul]
  rw [ha, mul_zero]

/-- The radical as a submodule over ℂ -/
abbrev radicalSubmodule (ω : AlgState A) : Submodule ℂ A where
  carrier := ω.radical
  zero_mem' := mem_radical_zero ω
  add_mem' := fun ha hb => radical_add ω ha hb
  smul_mem' := fun r _ ha => radical_smul ω r ha

/-- Auxiliary lemma: if ω (star b * b) = 0, then ω (star a * b) = 0 -/
lemma omega_mul_star_eq_zero (ω : AlgState A) {b : A}
    (hb : ω (star b * b) = 0) (a : A) : ω (star a * b) = 0 := by
  have h := omega_star_mul_eq_zero ω hb a
  have h2 := ω.coe_star_mul_comm b a
  rw [h2, h, star_zero]

/-- The inner product on the quotient is well-defined -/
lemma inner_well_defined (ω : AlgState A) {a a' b b' : A}
    (ha : a - a' ∈ ω.radical) (hb : b - b' ∈ ω.radical) :
    ω (star a * b) = ω (star a' * b') := by
  have ha_eq : a = a' + (a - a') := by abel
  have hb_eq : b = b' + (b - b') := by abel
  rw [ha_eq, hb_eq, star_add, add_mul, mul_add, mul_add]
  simp only [ω.map_add]
  rw [omega_mul_star_eq_zero ω hb a']
  rw [omega_star_mul_eq_zero ω ha b']
  rw [omega_star_mul_eq_zero ω ha (b - b')]
  ring

/-- The GNS pre-Hilbert space as the quotient A / radical -/
abbrev GNSPreSpace (ω : AlgState A) := A ⧸ radicalSubmodule ω

/-- The inner product on the GNS space -/
noncomputable def gnsInner (ω : AlgState A) (x y : GNSPreSpace ω) : ℂ :=
  Quotient.lift₂
    (s₁ := (radicalSubmodule ω).quotientRel)
    (s₂ := (radicalSubmodule ω).quotientRel)
    (fun (a b : A) => ω (star a * b))
    (fun a₁ b₁ a₂ b₂ ha hb =>
      inner_well_defined ω (a := a₁) (a' := a₂) (b := b₁) (b' := b₂)
        ((Submodule.quotientRel_def (radicalSubmodule ω)).mp ha)
        ((Submodule.quotientRel_def (radicalSubmodule ω)).mp hb))
    x y

lemma gnsInner_self_nonneg (ω : AlgState A) (x : GNSPreSpace ω) :
    (gnsInner ω x x).re ≥ 0 ∧ (gnsInner ω x x).im = 0 := by
  induction x using Quotient.inductionOn with
  | h a =>
    simp only [gnsInner, Quotient.lift₂_mk]
    exact ⟨ω.positive_re a, ω.positive_im a⟩

lemma gnsInner_conj_symm (ω : AlgState A) (x y : GNSPreSpace ω) :
    gnsInner ω x y = star (gnsInner ω y x) := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      simp only [gnsInner, Quotient.lift₂_mk]
      exact ω.coe_star_mul_comm b a

lemma gnsInner_add_left (ω : AlgState A) (x y z : GNSPreSpace ω) :
    gnsInner ω (x + y) z = gnsInner ω x z + gnsInner ω y z := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      induction z using Quotient.inductionOn with
      | h c =>
        change ω (star (a + b) * c) = ω (star a * c) + ω (star b * c)
        rw [star_add, add_mul, ω.map_add]

lemma gnsInner_smul_left (ω : AlgState A) (r : ℂ) (x y : GNSPreSpace ω) :
    gnsInner ω (r • x) y = star r * gnsInner ω x y := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      change ω (star (r • a) * b) = star r * ω (star a * b)
      rw [star_smul, smul_mul_assoc, ω.map_smul]

lemma gnsInner_smul_right (ω : AlgState A) (x y : GNSPreSpace ω) (r : ℂ) :
    gnsInner ω x (r • y) = r * gnsInner ω x y := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      change ω (star a * (r • b)) = r * ω (star a * b)
      rw [mul_smul_comm, ω.map_smul]

noncomputable instance (ω : AlgState A) :
    PreInnerProductSpace.Core ℂ (GNSPreSpace ω) where
  toInner := ⟨fun x y => gnsInner ω x y⟩
  conj_inner_symm := fun x y => (gnsInner_conj_symm ω x y).symm
  re_inner_nonneg := fun x => (gnsInner_self_nonneg ω x).1
  add_left := fun x y z => gnsInner_add_left ω x y z
  smul_left := fun x y r => gnsInner_smul_left ω r x y

noncomputable def gnsNorm (ω : AlgState A) (x : GNSPreSpace ω) : ℝ :=
  Real.sqrt (gnsInner ω x x).re

lemma gnsNorm_nonneg (ω : AlgState A) (x : GNSPreSpace ω) :
    0 ≤ gnsNorm ω x := Real.sqrt_nonneg _

lemma gnsNorm_eq_zero_iff (ω : AlgState A) (x : GNSPreSpace ω) :
    gnsNorm ω x = 0 ↔ x = 0 := by
  rw [gnsNorm, Real.sqrt_eq_zero']
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- h : (gnsInner ω x x).re ≤ 0
    have h_nonneg := (gnsInner_self_nonneg ω x).1
    have h_re : (gnsInner ω x x).re = 0 := le_antisymm h h_nonneg
    have h_im := (gnsInner_self_nonneg ω x).2
    have h_zero : gnsInner ω x x = 0 := Complex.ext h_re h_im
    induction x using Quotient.inductionOn with
    | h a =>
      change ω (star a * a) = 0 at h_zero
      have ha : a ∈ radicalSubmodule ω := h_zero
      have h_rel : (radicalSubmodule ω).quotientRel a 0 := by
        rw [Submodule.quotientRel_def, sub_zero]
        exact ha
      exact Quotient.sound h_rel
  · -- h : x = 0
    rw [h]
    change (ω (star (0 : A) * 0)).re ≤ 0
    simp [ω.map_zero]

lemma gnsInner_add_right (ω : AlgState A) (x y z : GNSPreSpace ω) :
    gnsInner ω x (y + z) = gnsInner ω x y + gnsInner ω x z := by
  have h1 : gnsInner ω x (y + z) = star (gnsInner ω (y + z) x) :=
    gnsInner_conj_symm ω x (y + z)
  have h2 : gnsInner ω (y + z) x = gnsInner ω y x + gnsInner ω z x :=
    gnsInner_add_left ω y z x
  have h3 : gnsInner ω y x = star (gnsInner ω x y) :=
    gnsInner_conj_symm ω y x
  have h4 : gnsInner ω z x = star (gnsInner ω x z) :=
    gnsInner_conj_symm ω z x
  rw [h1, h2, h3, h4, star_add, star_star, star_star]

lemma gnsInner_re_le_norm (ω : AlgState A) (x y : GNSPreSpace ω) :
    (gnsInner ω x y).re ≤ gnsNorm ω x * gnsNorm ω y := by
  have h1 : (gnsInner ω x y).re ≤ ‖gnsInner ω x y‖ := Complex.re_le_norm _
  have h2 : Complex.normSq (gnsInner ω x y) ≤
      (gnsInner ω x x).re * (gnsInner ω y y).re := by
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        change Complex.normSq (ω (star a * b)) ≤
          (ω (star a * a)).re * (ω (star b * b)).re
        exact cauchy_schwarz ω a b
  have h3x : (gnsInner ω x x).re = (gnsNorm ω x)^2 := by
    rw [gnsNorm, Real.sq_sqrt (gnsInner_self_nonneg ω x).1]
  have h3y : (gnsInner ω y y).re = (gnsNorm ω y)^2 := by
    rw [gnsNorm, Real.sq_sqrt (gnsInner_self_nonneg ω y).1]
  have h4 : ‖gnsInner ω x y‖^2 ≤ (gnsNorm ω x * gnsNorm ω y)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (gnsInner ω x y)
        ≤ (gnsInner ω x x).re * (gnsInner ω y y).re := h2
      _ = (gnsNorm ω x)^2 * (gnsNorm ω y)^2 := by rw [h3x, h3y]
      _ = (gnsNorm ω x * gnsNorm ω y)^2 := by ring
  have h5 : ‖gnsInner ω x y‖ ≤ gnsNorm ω x * gnsNorm ω y := by
    have h6 : 0 ≤ ‖gnsInner ω x y‖ := norm_nonneg _
    have h7 : 0 ≤ gnsNorm ω x * gnsNorm ω y :=
      mul_nonneg (gnsNorm_nonneg ω x) (gnsNorm_nonneg ω y)
    nlinarith [h4, h6, h7]
  linarith

lemma gnsNorm_triangle (ω : AlgState A) (x y : GNSPreSpace ω) :
    gnsNorm ω (x + y) ≤ gnsNorm ω x + gnsNorm ω y := by
  have h_re := gnsInner_re_le_norm ω x y
  have h_conj : gnsInner ω y x = star (gnsInner ω x y) :=
    gnsInner_conj_symm ω y x
  have h_add1 : gnsInner ω (x + y) (x + y) =
      gnsInner ω x (x + y) + gnsInner ω y (x + y) :=
    gnsInner_add_left ω x y (x + y)
  have h_add2 : gnsInner ω x (x + y) = gnsInner ω x x + gnsInner ω x y :=
    gnsInner_add_right ω x x y
  have h_add3 : gnsInner ω y (x + y) = gnsInner ω y x + gnsInner ω y y :=
    gnsInner_add_right ω y x y
  have h_expand : gnsInner ω (x + y) (x + y) =
      gnsInner ω x x + gnsInner ω x y + gnsInner ω y x + gnsInner ω y y := by
    rw [h_add1, h_add2, h_add3]; abel
  have h_re_sum : (gnsInner ω (x + y) (x + y)).re =
      (gnsInner ω x x).re + 2 * (gnsInner ω x y).re + (gnsInner ω y y).re := by
    rw [h_expand, h_conj]
    simp only [Complex.add_re]
    rw [show (star (gnsInner ω x y)).re = (gnsInner ω x y).re from by simp]
    ring
  have hx : (gnsInner ω x x).re = (gnsNorm ω x)^2 := by
    rw [gnsNorm, Real.sq_sqrt (gnsInner_self_nonneg ω x).1]
  have hy : (gnsInner ω y y).re = (gnsNorm ω y)^2 := by
    rw [gnsNorm, Real.sq_sqrt (gnsInner_self_nonneg ω y).1]
  have key : (gnsInner ω (x + y) (x + y)).re ≤
      (gnsNorm ω x + gnsNorm ω y)^2 := by
    rw [h_re_sum, hx, hy]
    nlinarith [h_re, sq_nonneg (gnsNorm ω x - gnsNorm ω y)]
  have hsum_nonneg : 0 ≤ gnsNorm ω x + gnsNorm ω y :=
    add_nonneg (gnsNorm_nonneg ω x) (gnsNorm_nonneg ω y)
  have step : Real.sqrt (gnsInner ω (x + y) (x + y)).re ≤
      Real.sqrt ((gnsNorm ω x + gnsNorm ω y)^2) := Real.sqrt_le_sqrt key
  rw [Real.sqrt_sq hsum_nonneg] at step
  exact step

noncomputable instance (ω : AlgState A) : Norm (GNSPreSpace ω) :=
  ⟨gnsNorm ω⟩

lemma gnsNorm_smul (ω : AlgState A) (r : ℂ) (x : GNSPreSpace ω) :
    ‖r • x‖ = ‖r‖ * ‖x‖ := by
  change gnsNorm ω (r • x) = ‖r‖ * gnsNorm ω x
  have h_inner : gnsInner ω (r • x) (r • x) = (star r * r) * gnsInner ω x x := by
    rw [gnsInner_smul_left, gnsInner_smul_right]
    ring
  have h_re : (gnsInner ω (r • x) (r • x)).re =
      Complex.normSq r * (gnsInner ω x x).re := by
    rw [h_inner]
    rw [show (star r * r * gnsInner ω x x).re =
        (star r * r).re * (gnsInner ω x x).re -
        (star r * r).im * (gnsInner ω x x).im from Complex.mul_re _ _]
    rw [show (star r * r).im = 0 from im_star_mul_self r]
    rw [show (star r * r).re = Complex.normSq r from re_star_mul_self r]
    rw [(gnsInner_self_nonneg ω x).2]
    ring
  have h_normSq : Complex.normSq r = ‖r‖^2 := by
    rw [Complex.normSq_eq_norm_sq]
  have hx : (gnsInner ω x x).re = (gnsNorm ω x)^2 := by
    rw [gnsNorm, Real.sq_sqrt (gnsInner_self_nonneg ω x).1]
  have h_sq : (gnsNorm ω (r • x))^2 = (‖r‖ * gnsNorm ω x)^2 := by
    rw [gnsNorm, Real.sq_sqrt (gnsInner_self_nonneg ω (r • x)).1]
    rw [h_re, h_normSq, hx]
    ring
  have h_left_nn : 0 ≤ gnsNorm ω (r • x) := gnsNorm_nonneg ω _
  have h_right_nn : 0 ≤ ‖r‖ * gnsNorm ω x :=
    mul_nonneg (norm_nonneg r) (gnsNorm_nonneg ω x)
  nlinarith [h_sq, h_left_nn, h_right_nn]

noncomputable def gnsSeminormedCore (ω : AlgState A) :
    SeminormedSpace.Core ℂ (GNSPreSpace ω) where
  norm_nonneg := fun x => gnsNorm_nonneg ω x
  norm_smul := fun r x => gnsNorm_smul ω r x
  norm_triangle := fun x y => gnsNorm_triangle ω x y

noncomputable instance (ω : AlgState A) : SeminormedAddCommGroup (GNSPreSpace ω) :=
  SeminormedAddCommGroup.ofCore (gnsSeminormedCore ω)

noncomputable instance (ω : AlgState A) : NormedSpace ℂ (GNSPreSpace ω) :=
  NormedSpace.mk (fun r x => by
    change ‖r • x‖ ≤ ‖r‖ * ‖x‖
    rw [gnsNorm_smul ω r x])

noncomputable instance (ω : AlgState A) : Inner ℂ (GNSPreSpace ω) :=
  ⟨fun x y => gnsInner ω x y⟩

noncomputable instance (ω : AlgState A) :
    InnerProductSpace ℂ (GNSPreSpace ω) :=
  InnerProductSpace.mk
    (fun x => by
      change (gnsNorm ω x)^2 = (gnsInner ω x x).re
      unfold gnsNorm
      exact Real.sq_sqrt (gnsInner_self_nonneg ω x).1)
    (fun x y => (gnsInner_conj_symm ω x y).symm)
    (fun x y z => gnsInner_add_left ω x y z)
    (fun x y r => gnsInner_smul_left ω r x y)

/-- The GNS Hilbert space as the completion of the pre-Hilbert space -/
noncomputable abbrev GNS (ω : AlgState A) : Type _ :=
  UniformSpace.Completion (GNSPreSpace ω)

noncomputable instance (ω : AlgState A) : InnerProductSpace ℂ (GNS ω) :=
  inferInstance

noncomputable instance (ω : AlgState A) : CompleteSpace (GNS ω) :=
  inferInstance
lemma radical_mul (ω : AlgState A) {b : A} (hb : b ∈ ω.radical) (a : A) :
    a * b ∈ ω.radical := by
  change ω (star (a * b) * (a * b)) = 0
  have h : ω (star b * (star a * a * b)) = 0 :=
    omega_star_mul_eq_zero ω hb (star a * a * b)
  have h_eq : star (a * b) * (a * b) = star b * (star a * a * b) := by
    simp only [star_mul, mul_assoc]
  rw [h_eq]
  exact h

noncomputable def gnsRepLinear (ω : AlgState A) (a : A) :
    GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω :=
  Submodule.liftQ (radicalSubmodule ω)
    { toFun := fun b => Submodule.mkQ (radicalSubmodule ω) (a * b)
      map_add' := fun x y => by
        rw [mul_add]
        exact (Submodule.mkQ (radicalSubmodule ω)).map_add (a * x) (a * y)
      map_smul' := fun r x => by
        rw [mul_smul_comm]
        exact (Submodule.mkQ (radicalSubmodule ω)).map_smul r (a * x) }
    (by
      intro b hb
      change (Submodule.mkQ (radicalSubmodule ω)) (a * b) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact radical_mul ω hb a)

lemma gnsRepLinear_mul (ω : AlgState A) (a b : A) :
    gnsRepLinear ω (a * b) =
      (gnsRepLinear ω a).comp (gnsRepLinear ω b) := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (radicalSubmodule ω) x
  simp only [LinearMap.comp_apply]
  change (Submodule.mkQ (radicalSubmodule ω)) ((a * b) * c) =
    (Submodule.mkQ (radicalSubmodule ω)) (a * (b * c))
  rw [mul_assoc]

lemma gnsRepLinear_star_adjoint (ω : AlgState A) (a : A)
    (x y : GNSPreSpace ω) :
    gnsInner ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) y =
    gnsInner ω x ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (radicalSubmodule ω) x
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective (radicalSubmodule ω) y
  have h1 : (gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω)
      (Submodule.mkQ (radicalSubmodule ω) c) =
      Submodule.mkQ (radicalSubmodule ω) (a * c) := rfl
  have h2 : (gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω)
      (Submodule.mkQ (radicalSubmodule ω) d) =
      Submodule.mkQ (radicalSubmodule ω) (star a * d) := rfl
  rw [h1, h2]
  -- Replace mkQ with Quotient.mk so that Quotient.lift₂_mk applies
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
  -- Now we can apply Quotient.lift₂_mk
  change ω (star (a * c) * d) = ω (star c * (star a * d))
  rw [star_mul, mul_assoc]

/-- The cyclic vector of the GNS representation: the class of the unit in A / radical -/
noncomputable def gnsCyclic (ω : AlgState A) : GNSPreSpace ω :=
  Submodule.mkQ (radicalSubmodule ω) (1 : A)

/-- Fundamental property of GNS: ω a = ⟪Ω, π(a) Ω⟫ -/
lemma gns_cyclic_inner (ω : AlgState A) (a : A) :
    gnsInner ω (gnsCyclic ω)
      ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) (gnsCyclic ω)) = ω a := by
  change gnsInner ω (Submodule.mkQ (radicalSubmodule ω) 1)
    (Submodule.mkQ (radicalSubmodule ω) (a * 1)) = ω a
  rw [mul_one, Submodule.mkQ_apply, Submodule.mkQ_apply]
  change ω (star 1 * a) = ω a
  rw [star_one, one_mul]

/-- The operator norm of π_ω(a) as the supremum over the unit sphere -/
noncomputable def opNorm (ω : AlgState A) (a : A) : ENNReal :=
  ⨆ (x : GNSPreSpace ω),
    ENNReal.ofReal
      (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
        gnsNorm ω x)

lemma gnsNorm_zero (ω : AlgState A) : gnsNorm ω (0 : GNSPreSpace ω) = 0 := by
  change ‖(0 : GNSPreSpace ω)‖ = 0
  exact norm_zero

/-- The maximal C*-seminorm on A: the supremum over all states -/
noncomputable def maximalSeminorm (a : A) : ENNReal :=
  ⨆ (ω : AlgState A), opNorm ω a

lemma maximalSeminorm_zero : maximalSeminorm (0 : A) = 0 := by
  unfold maximalSeminorm opNorm
  apply le_antisymm
  · apply iSup_le; intro ω
    apply iSup_le; intro x
    have h : (gnsRepLinear ω (0 : A) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x = 0 := by
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (radicalSubmodule ω) x
      change Submodule.mkQ (radicalSubmodule ω) ((0 : A) * b) = 0
      rw [zero_mul]; rfl
    rw [h, gnsNorm_zero]
    simp
  · exact bot_le

lemma gnsRepLinear_add (ω : AlgState A) (a b : A) :
    gnsRepLinear ω (a + b) = gnsRepLinear ω a + gnsRepLinear ω b := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (radicalSubmodule ω) x
  change Submodule.mkQ (radicalSubmodule ω) ((a + b) * c) =
    Submodule.mkQ (radicalSubmodule ω) (a * c) +
    Submodule.mkQ (radicalSubmodule ω) (b * c)
  rw [add_mul]
  exact (Submodule.mkQ (radicalSubmodule ω)).map_add (a * c) (b * c)

lemma opNorm_add_le (ω : AlgState A) (a b : A) :
    opNorm ω (a + b) ≤ opNorm ω a + opNorm ω b := by
  unfold opNorm
  apply iSup_le
  intro x
  have h_app : (gnsRepLinear ω (a + b) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x =
      (gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x +
      (gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x := by
    rw [gnsRepLinear_add, LinearMap.add_apply]
  rw [h_app]
  have h1 : gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x +
      (gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) ≤
      gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) +
      gnsNorm ω ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) :=
    gnsNorm_triangle ω _ _
  have h3 : (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) +
      gnsNorm ω ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x)) / gnsNorm ω x =
      gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x +
      gnsNorm ω ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x :=
    add_div _ _ _
  calc ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x +
          (gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)
      ≤ ENNReal.ofReal ((gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) +
              gnsNorm ω ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x)) / gnsNorm ω x) :=
        ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right h1 (gnsNorm_nonneg ω x))
    _ = ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x +
            gnsNorm ω ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x) := by
        rw [h3]
    _ = ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x) +
        ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x) := by
        rw [ENNReal.ofReal_add]
        · exact div_nonneg (gnsNorm_nonneg ω _) (gnsNorm_nonneg ω _)
        · exact div_nonneg (gnsNorm_nonneg ω _) (gnsNorm_nonneg ω _)
    _ ≤ opNorm ω a + opNorm ω b := by
        apply add_le_add
        · exact le_iSup (fun x => ENNReal.ofReal
              (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)) x
        · exact le_iSup (fun x => ENNReal.ofReal
              (gnsNorm ω ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)) x

lemma maximalSeminorm_add_le (a b : A) :
    maximalSeminorm (a + b) ≤ maximalSeminorm a + maximalSeminorm b := by
  unfold maximalSeminorm
  apply iSup_le
  intro ω
  calc opNorm ω (a + b)
      ≤ opNorm ω a + opNorm ω b := opNorm_add_le ω a b
    _ ≤ maximalSeminorm a + maximalSeminorm b := by
        apply add_le_add
        · exact le_iSup (fun ω => opNorm ω a) ω
        · exact le_iSup (fun ω => opNorm ω b) ω

lemma opNorm_mul_le (ω : AlgState A) (a b : A) :
    opNorm ω (a * b) ≤ opNorm ω a * opNorm ω b := by
  unfold opNorm
  apply iSup_le
  intro x
  have h_comp : (gnsRepLinear ω (a * b) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x =
      (gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω)
        ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) := by
    rw [gnsRepLinear_mul, LinearMap.comp_apply]
  rw [h_comp]
  by_cases hy : (gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x = 0
  · rw [hy, show (gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) 0 = 0 from
      LinearMap.map_zero _]
    rw [gnsNorm_zero]
    simp
  · set y := (gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x with hy_def
    have hy_pos : 0 < gnsNorm ω y := by
      rw [lt_iff_le_and_ne]
      exact ⟨gnsNorm_nonneg ω y, fun h => hy ((gnsNorm_eq_zero_iff ω y).mp h.symm)⟩
    have h_decomp : gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω x =
        (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω y) *
        (gnsNorm ω y / gnsNorm ω x) := by
      field_simp
    rw [h_decomp]
    rw [ENNReal.ofReal_mul (div_nonneg (gnsNorm_nonneg ω _) (le_of_lt hy_pos))]
    apply mul_le_mul
    · exact le_iSup (fun x => ENNReal.ofReal
          (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)) y
    · exact le_iSup (fun x => ENNReal.ofReal
          (gnsNorm ω ((gnsRepLinear ω b : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)) x
    · exact bot_le
    · exact bot_le

lemma maximalSeminorm_mul_le (a b : A) :
    maximalSeminorm (a * b) ≤ maximalSeminorm a * maximalSeminorm b := by
  unfold maximalSeminorm
  apply iSup_le
  intro ω
  calc opNorm ω (a * b)
      ≤ opNorm ω a * opNorm ω b := opNorm_mul_le ω a b
    _ ≤ maximalSeminorm a * maximalSeminorm b := by
        apply mul_le_mul
        · exact le_iSup (fun ω => opNorm ω a) ω
        · exact le_iSup (fun ω => opNorm ω b) ω
        · exact bot_le
        · exact bot_le

/-- Auxiliary: ‖π(a*) x‖² = ⟪x, π(a) π(a*) x⟫ -/
lemma gnsNorm_star_sq (ω : AlgState A) (a : A) (x : GNSPreSpace ω) :
    (gnsNorm ω ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x))^2 =
    (gnsInner ω x ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω)
        ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x))).re := by
  rw [gnsNorm, Real.sq_sqrt (gnsInner_self_nonneg ω _).1]
  have h := gnsRepLinear_star_adjoint ω (star a) x
    ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x)
  simp only [star_star] at h
  rw [h]

/-- Key inequality: ‖π(a*) x‖ ≤ opNorm ω a · ‖x‖ -/
lemma gnsNorm_star_le_opNorm_mul (ω : AlgState A) (a : A) (x : GNSPreSpace ω)
    (hfin : opNorm ω a < ⊤) :
    gnsNorm ω ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) ≤
    (opNorm ω a).toReal * gnsNorm ω x := by
  set y := (gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x with hy_def
  by_cases hy : y = 0
  · rw [hy, gnsNorm_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (gnsNorm_nonneg ω x)
  · have hy_pos : 0 < gnsNorm ω y := by
      rw [lt_iff_le_and_ne]
      exact ⟨gnsNorm_nonneg ω y, fun h => hy ((gnsNorm_eq_zero_iff ω y).mp h.symm)⟩
    have h_op_y : gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) ≤
        (opNorm ω a).toReal * gnsNorm ω y := by
      have h_le : ENNReal.ofReal
          (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω y) ≤
          opNorm ω a :=
        le_iSup (fun x => ENNReal.ofReal
          (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)) y
      have hfin_ne : opNorm ω a ≠ ⊤ := ne_of_lt hfin
      rw [← ENNReal.ofReal_toReal hfin_ne] at h_le
      have h_real : gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) /
          gnsNorm ω y ≤ (opNorm ω a).toReal :=
        (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h_le
      rwa [div_le_iff₀ hy_pos] at h_real
    have h_sq := gnsNorm_star_sq ω a x
    rw [← hy_def] at h_sq
    have h_cs : (gnsInner ω x ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y)).re ≤
        gnsNorm ω x * gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) :=
      gnsInner_re_le_norm ω x _
    have h_main : (gnsNorm ω y)^2 ≤ gnsNorm ω x * ((opNorm ω a).toReal * gnsNorm ω y) := by
      calc (gnsNorm ω y)^2
          = (gnsInner ω x ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y)).re := h_sq
        _ ≤ gnsNorm ω x * gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) := h_cs
        _ ≤ gnsNorm ω x * ((opNorm ω a).toReal * gnsNorm ω y) :=
            mul_le_mul_of_nonneg_left h_op_y (gnsNorm_nonneg ω x)
    have h_main' : gnsNorm ω y * gnsNorm ω y ≤
        gnsNorm ω y * ((opNorm ω a).toReal * gnsNorm ω x) := by
      have h_rearr : gnsNorm ω x * ((opNorm ω a).toReal * gnsNorm ω y) =
          gnsNorm ω y * ((opNorm ω a).toReal * gnsNorm ω x) := by ring
      calc gnsNorm ω y * gnsNorm ω y = (gnsNorm ω y)^2 := by ring
        _ ≤ gnsNorm ω x * ((opNorm ω a).toReal * gnsNorm ω y) := h_main
        _ = gnsNorm ω y * ((opNorm ω a).toReal * gnsNorm ω x) := h_rearr
    exact le_of_mul_le_mul_left h_main' hy_pos

/-- B.1: \*-invariance of the operator norm -/
lemma opNorm_star (ω : AlgState A) (a : A) (hfin : opNorm ω a < ⊤) :
    opNorm ω (star a) = opNorm ω a := by
  have h1 : opNorm ω (star a) ≤ opNorm ω a := by
    apply iSup_le
    intro x
    by_cases hx : gnsNorm ω x = 0
    · rw [show gnsNorm ω ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x = 0 from by
        rw [hx, div_zero]]
      simp
    · have hx_pos : 0 < gnsNorm ω x :=
        lt_of_le_of_ne (gnsNorm_nonneg ω x) (Ne.symm hx)
      have h := gnsNorm_star_le_opNorm_mul ω a x hfin
      have h_div : gnsNorm ω ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
          gnsNorm ω x ≤ (opNorm ω a).toReal := by
        rwa [div_le_iff₀ hx_pos]
      calc ENNReal.ofReal
            (gnsNorm ω ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)
          ≤ ENNReal.ofReal ((opNorm ω a).toReal) := ENNReal.ofReal_le_ofReal h_div
        _ = opNorm ω a := ENNReal.ofReal_toReal (ne_of_lt hfin)
  have h2 : opNorm ω a ≤ opNorm ω (star a) := by
    have hfin' : opNorm ω (star a) < ⊤ := lt_of_le_of_lt h1 hfin
    apply iSup_le
    intro x
    by_cases hx : gnsNorm ω x = 0
    · rw [show gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x = 0 from by
        rw [hx, div_zero]]
      simp
    · have hx_pos : 0 < gnsNorm ω x :=
        lt_of_le_of_ne (gnsNorm_nonneg ω x) (Ne.symm hx)
      have h := gnsNorm_star_le_opNorm_mul ω (star a) x hfin'
      simp only [star_star] at h
      have h_div : gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
          gnsNorm ω x ≤ (opNorm ω (star a)).toReal := by
        rwa [div_le_iff₀ hx_pos]
      calc ENNReal.ofReal
            (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)
          ≤ ENNReal.ofReal ((opNorm ω (star a)).toReal) := ENNReal.ofReal_le_ofReal h_div
        _ = opNorm ω (star a) := ENNReal.ofReal_toReal (ne_of_lt hfin')
  exact le_antisymm h1 h2


/-- The ≤ direction in the C*-identity for a single state -/
lemma opNorm_cstar_le (ω : AlgState A) (a : A) (hfin : opNorm ω a < ⊤) :
    opNorm ω (star a * a) ≤ opNorm ω a * opNorm ω a := by
  set C := (opNorm ω a).toReal with hC_def
  have hC_nn : 0 ≤ C := ENNReal.toReal_nonneg
  have hC_eq : opNorm ω a = ENNReal.ofReal C :=
    (ENNReal.ofReal_toReal (ne_of_lt hfin)).symm
  have h_prod : opNorm ω a * opNorm ω a = ENNReal.ofReal (C * C) := by
    rw [hC_eq, ← ENNReal.ofReal_mul hC_nn]
  rw [h_prod]
  apply iSup_le
  intro x
  by_cases hx : gnsNorm ω x = 0
  · rw [show gnsNorm ω ((gnsRepLinear ω (star a * a) :
        GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x = 0 from by
      rw [hx, div_zero]]
    simp
  · have hx_pos : 0 < gnsNorm ω x :=
      lt_of_le_of_ne (gnsNorm_nonneg ω x) (Ne.symm hx)
    apply ENNReal.ofReal_le_ofReal
    have h_mul : (gnsRepLinear ω (star a * a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x =
        (gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω)
          ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) := by
      rw [gnsRepLinear_mul, LinearMap.comp_apply]
    rw [h_mul]
    have h_star := gnsNorm_star_le_opNorm_mul ω a
      ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) hfin
    have h_x_le : gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
        gnsNorm ω x ≤ C := by
      have h_le : ENNReal.ofReal
          (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
            gnsNorm ω x) ≤ ENNReal.ofReal C := by
        rw [← hC_eq]
        exact le_iSup (fun x => ENNReal.ofReal
          (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
            gnsNorm ω x)) x
      exact (ENNReal.ofReal_le_ofReal_iff hC_nn).mp h_le
    calc gnsNorm ω ((gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω)
            ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x)) / gnsNorm ω x
        ≤ C * gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x :=
          div_le_div_of_nonneg_right h_star (le_of_lt hx_pos)
      _ = C * (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x) := by
          ring
      _ ≤ C * C := mul_le_mul_of_nonneg_left h_x_le hC_nn

/-- The ≥ direction in the C*-identity for a single state.
    No finiteness hypothesis is needed — the supremum is always defined. -/
lemma opNorm_le_cstar (ω : AlgState A) (a : A) :
    opNorm ω a * opNorm ω a ≤ opNorm ω (star a * a) := by
  have h_pointwise : ∀ z : GNSPreSpace ω,
      ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) /
        gnsNorm ω z) *
      ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) /
        gnsNorm ω z) ≤ opNorm ω (star a * a) := by
    intro z
    by_cases hz : gnsNorm ω z = 0
    · rw [hz, div_zero, ENNReal.ofReal_zero, mul_zero]
      exact bot_le
    · have hz_pos : 0 < gnsNorm ω z :=
        lt_of_le_of_ne (gnsNorm_nonneg ω z) (Ne.symm hz)
      have h_real : (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) /
          gnsNorm ω z)^2 ≤
          gnsNorm ω ((gnsRepLinear ω (star a * a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) /
            gnsNorm ω z := by
        have h_cs : (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z))^2
            ≤ gnsNorm ω ((gnsRepLinear ω (star a * a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) *
                gnsNorm ω z := by
          have h_base : (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z))^2
              ≤ gnsNorm ω z *
                  gnsNorm ω ((gnsRepLinear ω (star a * a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) := by
            rw [show (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z))^2
                = (gnsInner ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z)
                      ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z)).re from by
              rw [gnsNorm, Real.sq_sqrt (gnsInner_self_nonneg ω _).1]]
            rw [gnsRepLinear_star_adjoint ω a z
              ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z)]
            rw [show (gnsRepLinear ω (star a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω)
                  ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) =
                (gnsRepLinear ω (star a * a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z from by
              rw [gnsRepLinear_mul, LinearMap.comp_apply]]
            exact gnsInner_re_le_norm ω z _
          rw [mul_comm] at h_base
          exact h_base
        rw [div_pow, div_le_iff₀ (pow_pos hz_pos 2)]
        have h_simp : gnsNorm ω ((gnsRepLinear ω (star a * a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) /
            gnsNorm ω z * (gnsNorm ω z)^2 =
            gnsNorm ω ((gnsRepLinear ω (star a * a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) *
              gnsNorm ω z := by
          field_simp
        rw [h_simp]
        exact h_cs
      rw [show ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) / gnsNorm ω z) *
          ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) / gnsNorm ω z)
          = ENNReal.ofReal ((gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) / gnsNorm ω z)^2) from by
        rw [pow_two, ENNReal.ofReal_mul (div_nonneg (gnsNorm_nonneg ω _) (gnsNorm_nonneg ω _))]]
      exact le_trans (ENNReal.ofReal_le_ofReal h_real)
        (le_iSup (fun z => ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω (star a * a) :
          GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) z) / gnsNorm ω z)) z)
  change (⨆ x, ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
      GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)) *
    (⨆ x, ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
      GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)) ≤ opNorm ω (star a * a)
  rw [ENNReal.iSup_mul]
  apply iSup_le; intro x
  rw [ENNReal.mul_iSup]
  apply iSup_le; intro y
  by_cases hxy : ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
        GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)
      ≤ ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
        GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω y)
  · calc ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)
            * ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω y)
          ≤ ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω y)
            * ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω y) :=
            mul_le_mul_of_nonneg_right hxy bot_le
        _ ≤ opNorm ω (star a * a) := h_pointwise y
  · have hxy' : ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
        GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω y)
        < ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
        GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x) :=
      not_le.mp hxy
    calc ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)
            * ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) y) / gnsNorm ω y)
          ≤ ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x)
            * ENNReal.ofReal (gnsNorm ω ((gnsRepLinear ω a :
              GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) / gnsNorm ω x) :=
            mul_le_mul_of_nonneg_left hxy'.le bot_le
        _ ≤ opNorm ω (star a * a) := h_pointwise x

/-- The C*-identity for the operator norm of a single state -/
lemma opNorm_cstar_self (ω : AlgState A) (a : A) (hfin : opNorm ω a < ⊤) :
    opNorm ω (star a * a) = opNorm ω a * opNorm ω a := by
  have h1 := opNorm_cstar_le ω a hfin
  exact le_antisymm h1 (opNorm_le_cstar ω a)


/-- The doubling of a state ω by an element b.
    ω_b(x) := ω(b* x b) / ω(b* b).
    Requires ω(b* b) ≠ 0 (otherwise b lies in the radical) -/
noncomputable def doubledState (ω : AlgState A) (b : A)
    (hb : ω (star b * b) ≠ 0) : AlgState A where
  toFun := fun x => ω (star b * x * b) / ω (star b * b)
  map_one := by
    rw [mul_one]
    exact div_self hb
  map_add := by
    intro x y
    have h_expand : star b * (x + y) * b = star b * x * b + star b * y * b := by
      rw [mul_add, add_mul]
    rw [h_expand, ω.map_add, add_div]
  map_smul := by
    intro r x
    have h_step : star b * (r • x) * b = r • (star b * x * b) := by
      rw [mul_smul_comm, smul_mul_assoc]
    rw [h_step, ω.map_smul, mul_div_assoc]
  positive_re := by
    intro x
    have h_prod : star b * (star x * x) * b = star (x * b) * (x * b) := by
      rw [star_mul]
      simp only [mul_assoc]
    rw [h_prod]
    have h_num_real : ω (star (x * b) * (x * b)) =
        ↑(ω (star (x * b) * (x * b))).re := ω.omega_selfadjoint_real (x * b)
    have h_den_real : ω (star b * b) = ↑(ω (star b * b)).re := ω.omega_selfadjoint_real b
    have h_num_nn : 0 ≤ (ω (star (x * b) * (x * b))).re := ω.positive_re (x * b)
    have h_den_pos : 0 < (ω (star b * b)).re := by
      have h_nonneg : 0 ≤ (ω (star b * b)).re := ω.positive_re b
      rcases lt_or_eq_of_le h_nonneg with h | h
      · exact h
      · exfalso
        apply hb
        rw [h_den_real]
        exact_mod_cast h.symm
    rw [h_num_real, h_den_real, ← Complex.ofReal_div]
    simp only [Complex.ofReal_re]
    exact div_nonneg h_num_nn (le_of_lt h_den_pos)
  positive_im := by
    intro x
    have h_prod : star b * (star x * x) * b = star (x * b) * (x * b) := by
      rw [star_mul]
      simp only [mul_assoc]
    rw [h_prod]
    have h_num_real : ω (star (x * b) * (x * b)) =
        ↑(ω (star (x * b) * (x * b))).re := ω.omega_selfadjoint_real (x * b)
    have h_den_real : ω (star b * b) = ↑(ω (star b * b)).re := ω.omega_selfadjoint_real b
    rw [h_num_real, h_den_real, ← Complex.ofReal_div]
    simp


/-- Auxiliary lemma: the value of the state ω_b on a positive element
    does not exceed the operator norm of π(a* a).
    Requires finiteness of opNorm (otherwise .toReal gives 0) -/
lemma doubledState_self_le_opNorm (ω : AlgState A) (b : A) (hb : ω (star b * b) ≠ 0)
    (x : A) (hfin : opNorm (doubledState ω b hb) (star x * x) < ⊤) :
    ((doubledState ω b hb) (star x * x)).re ≤
      (opNorm (doubledState ω b hb) (star x * x)).toReal := by
  set ω_b := doubledState ω b hb with hω_b
  have hfin' : opNorm ω_b (star x * x) < ⊤ := hfin
  have h_re_eq : (ω_b (star x * x)).re =
      (gnsInner ω_b (gnsCyclic ω_b)
        ((gnsRepLinear ω_b (star x * x) : GNSPreSpace ω_b →ₗ[ℂ] GNSPreSpace ω_b)
          (gnsCyclic ω_b))).re := by
    rw [gns_cyclic_inner]
  rw [h_re_eq]
  have h_cs := gnsInner_re_le_norm ω_b (gnsCyclic ω_b)
    ((gnsRepLinear ω_b (star x * x) : GNSPreSpace ω_b →ₗ[ℂ] GNSPreSpace ω_b)
      (gnsCyclic ω_b))
  have h_norm_cyc : gnsNorm ω_b (gnsCyclic ω_b) = 1 := by
    unfold gnsCyclic gnsNorm
    rw [show gnsInner ω_b (Submodule.mkQ (radicalSubmodule ω_b) 1)
          (Submodule.mkQ (radicalSubmodule ω_b) 1) = ω_b 1 from by
      change ω_b (star 1 * 1) = ω_b 1
      rw [star_one, one_mul]]
    rw [ω_b.map_one]; simp
  have h_le : ENNReal.ofReal
      (gnsNorm ω_b ((gnsRepLinear ω_b (star x * x) :
        GNSPreSpace ω_b →ₗ[ℂ] GNSPreSpace ω_b) (gnsCyclic ω_b))) ≤
      opNorm ω_b (star x * x) := by
    unfold opNorm
    have h_iSup := le_iSup (fun u => ENNReal.ofReal
      (gnsNorm ω_b ((gnsRepLinear ω_b (star x * x) :
        GNSPreSpace ω_b →ₗ[ℂ] GNSPreSpace ω_b) u) / gnsNorm ω_b u))
      (gnsCyclic ω_b)
    rwa [h_norm_cyc, div_one] at h_iSup
  have h_real : gnsNorm ω_b ((gnsRepLinear ω_b (star x * x) :
        GNSPreSpace ω_b →ₗ[ℂ] GNSPreSpace ω_b) (gnsCyclic ω_b)) ≤
      (opNorm ω_b (star x * x)).toReal := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt hfin')] at h_le
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h_le
  calc (gnsInner ω_b (gnsCyclic ω_b)
        ((gnsRepLinear ω_b (star x * x) : GNSPreSpace ω_b →ₗ[ℂ] GNSPreSpace ω_b)
          (gnsCyclic ω_b))).re
      ≤ gnsNorm ω_b (gnsCyclic ω_b) *
        gnsNorm ω_b ((gnsRepLinear ω_b (star x * x) :
          GNSPreSpace ω_b →ₗ[ℂ] GNSPreSpace ω_b) (gnsCyclic ω_b)) := h_cs
    _ = gnsNorm ω_b ((gnsRepLinear ω_b (star x * x) :
          GNSPreSpace ω_b →ₗ[ℂ] GNSPreSpace ω_b) (gnsCyclic ω_b)) := by
        rw [h_norm_cyc, one_mul]
    _ ≤ (opNorm ω_b (star x * x)).toReal := h_real

/-- \*-invariance of the maximal seminorm -/
theorem maximalSeminorm_star (a : A) (hfin : maximalSeminorm a < ⊤) :
    maximalSeminorm (star a) = maximalSeminorm a := by
  unfold maximalSeminorm at *
  apply le_antisymm
  · apply iSup_le; intro ω
    have hω : opNorm ω a < ⊤ := lt_of_le_of_lt (le_iSup (fun ω => opNorm ω a) ω) hfin
    rw [opNorm_star ω a hω]
    exact le_iSup (fun ω => opNorm ω a) ω
  · have hfin' : (⨆ ω, opNorm ω (star a)) < ⊤ := by
      calc (⨆ ω, opNorm ω (star a)) ≤ (⨆ ω, opNorm ω a) := by
            apply iSup_le; intro ω
            have hω : opNorm ω a < ⊤ := lt_of_le_of_lt (le_iSup (fun ω => opNorm ω a) ω) hfin
            rw [opNorm_star ω a hω]
            exact le_iSup (fun ω => opNorm ω a) ω
        _ < ⊤ := hfin
    apply iSup_le; intro ω
    have hω : opNorm ω (star a) < ⊤ :=
      lt_of_le_of_lt (le_iSup (fun ω => opNorm ω (star a)) ω) hfin'
    have h := opNorm_star ω (star a) hω
    rw [star_star] at h
    rw [h]
    exact le_iSup (fun ω => opNorm ω (star a)) ω

theorem maximalSeminorm_cstar (a : A) (hfin : maximalSeminorm a < ⊤) :
    maximalSeminorm (star a * a) = maximalSeminorm a * maximalSeminorm a := by
  unfold maximalSeminorm at *
  apply le_antisymm
  · apply iSup_le; intro ω
    have hω : opNorm ω a < ⊤ := lt_of_le_of_lt (le_iSup (fun ω => opNorm ω a) ω) hfin
    rw [opNorm_cstar_self ω a hω]
    exact mul_le_mul (le_iSup (fun ω => opNorm ω a) ω) (le_iSup (fun ω => opNorm ω a) ω) bot_le bot_le
  · rw [ENNReal.iSup_mul]
    apply iSup_le; intro ω
    rw [ENNReal.mul_iSup]
    apply iSup_le; intro ω'
    have hω : opNorm ω a < ⊤ := lt_of_le_of_lt (le_iSup (fun ω => opNorm ω a) ω) hfin
    have hω' : opNorm ω' a < ⊤ := lt_of_le_of_lt (le_iSup (fun ω => opNorm ω a) ω') hfin
    have hx1 : opNorm ω a * opNorm ω a = opNorm ω (star a * a) :=
      (opNorm_cstar_self ω a hω).symm
    have hx2 : opNorm ω' a * opNorm ω' a = opNorm ω' (star a * a) :=
      (opNorm_cstar_self ω' a hω').symm
    have h_bound : opNorm ω a * opNorm ω' a ≤
        max (opNorm ω a * opNorm ω a) (opNorm ω' a * opNorm ω' a) := by
      rcases le_total (opNorm ω a) (opNorm ω' a) with h | h
      · calc opNorm ω a * opNorm ω' a
            ≤ opNorm ω' a * opNorm ω' a := mul_le_mul_of_nonneg_right h bot_le
          _ ≤ max _ _ := le_max_right _ _
      · calc opNorm ω a * opNorm ω' a
            ≤ opNorm ω a * opNorm ω a := mul_le_mul_of_nonneg_left h bot_le
          _ ≤ max _ _ := le_max_left _ _
    rw [hx1, hx2] at h_bound
    refine le_trans h_bound ?_
    exact max_le (le_iSup (fun ω => opNorm ω (star a * a)) ω)
                 (le_iSup (fun ω => opNorm ω (star a * a)) ω')

/-- Finiteness hypothesis for the maximal seminorm -/
class maximalSeminormFinite : Prop where
  finite : ∀ a : A, maximalSeminorm a < ⊤

/-- The set of elements with zero maximal seminorm -/
def maximalIdealCarrier : Set A := { a | maximalSeminorm a = 0 }

lemma maximalIdeal_zero_mem : (0 : A) ∈ maximalIdealCarrier := by
  simp [maximalIdealCarrier, maximalSeminorm_zero]

lemma maximalIdeal_add_mem {a b : A}
    (ha : a ∈ maximalIdealCarrier) (hb : b ∈ maximalIdealCarrier) :
    a + b ∈ maximalIdealCarrier := by
  simp only [maximalIdealCarrier, Set.mem_ofPred_eq] at ha hb ⊢
  have h := maximalSeminorm_add_le a b
  rw [ha, hb, add_zero] at h
  exact le_antisymm h bot_le

/-- Left multiplication vanishes: if ‖b‖ = 0, then ‖a * b‖ = 0 -/
lemma maximalIdeal_mul_mem_left {a b : A}
    (hb : b ∈ maximalIdealCarrier) :
    a * b ∈ maximalIdealCarrier := by
  simp only [maximalIdealCarrier, Set.mem_ofPred_eq] at hb ⊢
  have h := maximalSeminorm_mul_le a b
  rw [hb, mul_zero] at h
  exact le_antisymm h bot_le

/-- Right multiplication vanishes: if ‖a‖ = 0, then ‖a * b‖ = 0 -/
lemma maximalIdeal_mul_mem_right {a b : A}
    (ha : a ∈ maximalIdealCarrier) :
    a * b ∈ maximalIdealCarrier := by
  simp only [maximalIdealCarrier, Set.mem_ofPred_eq] at ha ⊢
  have h := maximalSeminorm_mul_le a b
  rw [ha, zero_mul] at h
  exact le_antisymm h bot_le

/-- gnsRepLinear commutes with scalar multiplicatio -/
lemma gnsRepLinear_smul (ω : AlgState A) (c : ℂ) (a : A) :
    gnsRepLinear ω (c • a) = c • gnsRepLinear ω a := by
  apply LinearMap.ext
  intro x
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (radicalSubmodule ω) x
  change Submodule.mkQ (radicalSubmodule ω) ((c • a) * b) =
    c • Submodule.mkQ (radicalSubmodule ω) (a * b)
  rw [smul_mul_assoc]
  exact (Submodule.mkQ (radicalSubmodule ω)).map_smul c (a * b)

/-- Norm of π(c·a) x = ‖c‖ · norm of π(a) x -/
lemma gnsNorm_rep_smul (ω : AlgState A) (c : ℂ) (a : A) (x : GNSPreSpace ω) :
    gnsNorm ω ((gnsRepLinear ω (c • a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) =
    ‖c‖ * gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) := by
  rw [gnsRepLinear_smul, LinearMap.smul_apply]
  exact gnsNorm_smul ω c _

/-- Operator norm under smul: opNorm ω (c·a) = ‖c‖ · opNorm ω a -/
lemma opNorm_smul (ω : AlgState A) (c : ℂ) (a : A) :
    opNorm ω (c • a) = ENNReal.ofReal ‖c‖ * opNorm ω a := by
  unfold opNorm
  rw [show (fun x => ENNReal.ofReal
        (gnsNorm ω ((gnsRepLinear ω (c • a) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
          gnsNorm ω x))
      = (fun x => ENNReal.ofReal ‖c‖ * ENNReal.ofReal
          (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
            gnsNorm ω x)) from by
    funext x
    rw [gnsNorm_rep_smul]
    rw [show ‖c‖ * gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
          gnsNorm ω x = ‖c‖ * (gnsNorm ω ((gnsRepLinear ω a : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) x) /
          gnsNorm ω x) from by ring]
    rw [ENNReal.ofReal_mul (norm_nonneg c)]]
  rw [ENNReal.mul_iSup]

/-- Scalar multiplication preserves the zero norm -/
lemma maximalSeminorm_smul (c : ℂ) (a : A) :
    maximalSeminorm (c • a) = ENNReal.ofReal ‖c‖ * maximalSeminorm a := by
  unfold maximalSeminorm
  have h : (⨆ ω, opNorm ω (c • a)) = ⨆ ω, ENNReal.ofReal ‖c‖ * opNorm ω a := by
    apply iSup_congr
    intro ω
    exact opNorm_smul ω c a
  rw [h, ← ENNReal.mul_iSup]

lemma maximalIdeal_smul_mem (c : ℂ) {a : A}
    (ha : a ∈ maximalIdealCarrier) :
    c • a ∈ maximalIdealCarrier := by
  simp only [maximalIdealCarrier, Set.mem_ofPred_eq] at ha ⊢
  rw [maximalSeminorm_smul, ha, mul_zero]

/-- The kernel of the maximal seminorm as a submodule over ℂ -/
noncomputable def maximalSubmodule : Submodule ℂ A where
  carrier := maximalIdealCarrier
  zero_mem' := maximalIdeal_zero_mem
  add_mem' := fun ha hb => maximalIdeal_add_mem ha hb
  smul_mem' := fun c _ ha => maximalIdeal_smul_mem c ha

lemma maximalIdeal_neg_mem {a : A} (ha : a ∈ maximalIdealCarrier) :
    -a ∈ maximalIdealCarrier := by
  simp only [maximalIdealCarrier, Set.mem_ofPred_eq] at ha ⊢
  have h : -a = (-1 : ℂ) • a := by simp
  rw [h, maximalSeminorm_smul, ha, mul_zero]


/-- The kernel of the maximal seminorm as a two-sided ideal -/
noncomputable def maximalIdeal : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' maximalIdealCarrier maximalIdeal_zero_mem
    (fun ha hb => maximalIdeal_add_mem ha hb)
    (fun ha => maximalIdeal_neg_mem ha)
    (fun hy => maximalIdeal_mul_mem_left hy)
    (fun hx => maximalIdeal_mul_mem_right hx)

/-- The real norm induced by maximalSeminorm.
    Requires finiteness so that ENNReal.toReal works correctly -/
noncomputable def maximalNorm (_hfin : maximalSeminormFinite (A := A)) (a : A) : ℝ :=
  (maximalSeminorm a).toReal

lemma maximalNorm_nonneg (hfin : maximalSeminormFinite (A := A)) (a : A) :
    0 ≤ maximalNorm hfin a := ENNReal.toReal_nonneg

lemma maximalNorm_add_le (hfin : maximalSeminormFinite (A := A)) (a b : A) :
    maximalNorm hfin (a + b) ≤ maximalNorm hfin a + maximalNorm hfin b := by
  unfold maximalNorm
  have h_ab : maximalSeminorm (a + b) ≤ maximalSeminorm a + maximalSeminorm b :=
    maximalSeminorm_add_le a b
  have h_sum_ne : maximalSeminorm a + maximalSeminorm b ≠ ⊤ :=
    (ENNReal.add_lt_top.mpr ⟨hfin.finite a, hfin.finite b⟩).ne
  calc (maximalSeminorm (a + b)).toReal
      ≤ (maximalSeminorm a + maximalSeminorm b).toReal :=
        ENNReal.toReal_mono h_sum_ne h_ab
    _ = (maximalSeminorm a).toReal + (maximalSeminorm b).toReal :=
        ENNReal.toReal_add (hfin.finite a).ne (hfin.finite b).ne

lemma maximalNorm_smul (hfin : maximalSeminormFinite (A := A)) (c : ℂ) (a : A) :
    maximalNorm hfin (c • a) = ‖c‖ * maximalNorm hfin a := by
  unfold maximalNorm
  rw [maximalSeminorm_smul]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (norm_nonneg c)]

noncomputable instance [hfin : maximalSeminormFinite (A := A)] : Norm A :=
  ⟨maximalNorm hfin⟩

noncomputable def maximalSeminormedCore (hfin : maximalSeminormFinite (A := A)) :
    SeminormedSpace.Core ℂ A where
  norm_nonneg := fun a => maximalNorm_nonneg hfin a
  norm_smul := fun c a => maximalNorm_smul hfin c a
  norm_triangle := fun a b => maximalNorm_add_le hfin a b

noncomputable instance [hfin : maximalSeminormFinite (A := A)] :
    SeminormedAddCommGroup A :=
  SeminormedAddCommGroup.ofCore (maximalSeminormedCore hfin)

noncomputable instance [hfin : maximalSeminormFinite (A := A)] :
    NormedSpace ℂ A :=
  NormedSpace.mk (fun c a => by
    change maximalNorm hfin (c • a) ≤ ‖c‖ * maximalNorm hfin a
    rw [maximalNorm_smul])

lemma maximalNorm_mul_le (hfin : maximalSeminormFinite (A := A)) (a b : A) :
    maximalNorm hfin (a * b) ≤ maximalNorm hfin a * maximalNorm hfin b := by
  unfold maximalNorm
  have h_ab : maximalSeminorm (a * b) ≤ maximalSeminorm a * maximalSeminorm b :=
    maximalSeminorm_mul_le a b
  have h_prod_ne : maximalSeminorm a * maximalSeminorm b ≠ ⊤ :=
    (ENNReal.mul_lt_top (hfin.finite a) (hfin.finite b)).ne
  calc (maximalSeminorm (a * b)).toReal
      ≤ (maximalSeminorm a * maximalSeminorm b).toReal :=
        ENNReal.toReal_mono h_prod_ne h_ab
    _ = (maximalSeminorm a).toReal * (maximalSeminorm b).toReal :=
        ENNReal.toReal_mul


lemma gnsRepLinear_one (ω : AlgState A) :
    gnsRepLinear ω (1 : A) = (LinearMap.id : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (radicalSubmodule ω) x
  change Submodule.mkQ (radicalSubmodule ω) (1 * c) = Submodule.mkQ (radicalSubmodule ω) c
  rw [one_mul]

lemma opNorm_one_le (ω : AlgState A) : opNorm ω (1 : A) ≤ 1 := by
  unfold opNorm
  apply iSup_le
  intro x
  rw [show (gnsRepLinear ω (1 : A) : GNSPreSpace ω →ₗ[ℂ] GNSPreSpace ω) =
      LinearMap.id from gnsRepLinear_one ω]
  rw [LinearMap.id_apply]
  have h : ‖x‖ / ‖x‖ ≤ 1 := by
    by_cases hx : ‖x‖ = 0
    · rw [hx, div_zero]
      exact zero_le_one
    · have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
      rw [div_le_one hx_pos]
  calc ENNReal.ofReal (‖x‖ / ‖x‖)
      ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h
    _ = 1 := ENNReal.ofReal_one

lemma maximalSeminorm_one_le : maximalSeminorm (1 : A) ≤ 1 := by
  unfold maximalSeminorm
  apply iSup_le
  intro ω
  exact opNorm_one_le ω


/-- The norm of the unit is at most 1. Sufficient for NormedRing -/
lemma maximalNorm_one_le (hfin : maximalSeminormFinite (A := A)) :
    maximalNorm hfin (1 : A) ≤ 1 := by
  unfold maximalNorm
  have h_le : maximalSeminorm (1 : A) ≤ 1 := maximalSeminorm_one_le
  calc (maximalSeminorm (1 : A)).toReal
      ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) h_le
    _ = 1 := ENNReal.toReal_one

lemma maximalNorm_star (hfin : maximalSeminormFinite (A := A)) (a : A) :
    maximalNorm hfin (star a) = maximalNorm hfin a := by
  unfold maximalNorm
  rw [maximalSeminorm_star a (hfin.finite a)]

lemma maximalNorm_cstar (hfin : maximalSeminormFinite (A := A)) (a : A) :
    maximalNorm hfin (star a * a) = maximalNorm hfin a * maximalNorm hfin a := by
  unfold maximalNorm
  rw [maximalSeminorm_cstar a (hfin.finite a)]
  exact ENNReal.toReal_mul



lemma star_lipschitzWith (hfin : maximalSeminormFinite (A := A)) :
    LipschitzWith 1 (star : A → A) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h1 : star a - star b = star (a - b) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, star_add, star_neg]
  rw [h1]
  change maximalNorm hfin (star (a - b)) ≤ maximalNorm hfin (a - b)
  rw [maximalNorm_star]

lemma star_uniformContinuous (hfin : maximalSeminormFinite (A := A)) :
    UniformContinuous (star : A → A) :=
  (star_lipschitzWith hfin).uniformContinuous

noncomputable instance [hfin : maximalSeminormFinite (A := A)] : ContinuousStar A where
  continuous_star := (star_lipschitzWith hfin).continuous


/-- The enveloping C*-algebra: the completion of A with respect to the maximal norm -/
noncomputable abbrev envelopingCStar [hfin : maximalSeminormFinite (A := A)] : Type _ :=
  UniformSpace.Completion A

noncomputable instance [hfin : maximalSeminormFinite (A := A)] :
    NonUnitalSeminormedRing A where
  norm_mul_le := maximalNorm_mul_le hfin
  dist_eq := fun _ _ => rfl

noncomputable instance [hfin : maximalSeminormFinite (A := A)] :
    SeminormedRing A where
  norm_mul_le := maximalNorm_mul_le hfin
  dist_eq := fun _ _ => rfl


section EnvelopingCStar

variable [hfin : maximalSeminormFinite (A := A)]

noncomputable instance : Ring (envelopingCStar (A := A)) :=
  UniformSpace.Completion.ring

noncomputable instance : Star (envelopingCStar (A := A)) where
  star := UniformSpace.Completion.map (star : A → A)

lemma star_coe (a : A) :
    star ((a : envelopingCStar (A := A))) = ((star a : A) : envelopingCStar (A := A)) :=
  UniformSpace.Completion.map_coe (star_uniformContinuous hfin) a



noncomputable instance : InvolutiveStar (envelopingCStar (A := A)) where
  star_involutive x := by
    have h_dense : DenseRange (fun a : A => (a : envelopingCStar (A := A))) :=
      UniformSpace.Completion.denseRange_coe
    have h_cont : Continuous (fun x : envelopingCStar (A := A) => star (star x)) :=
      (UniformSpace.Completion.continuous_map (f := (star : A → A))).comp
        (UniformSpace.Completion.continuous_map (f := (star : A → A)))
    have h_eq : (fun x : envelopingCStar (A := A) => star (star x)) =
        (fun x : envelopingCStar (A := A) => x) := by
      apply DenseRange.equalizer h_dense h_cont continuous_id
      funext a
      simp only [Function.comp_apply, id_eq]
      rw [star_coe, star_coe, star_star]
    exact congrFun h_eq x

noncomputable instance : StarAddMonoid (envelopingCStar (A := A)) where
  star_add x y := by
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · apply isClosed_eq
      · exact (UniformSpace.Completion.continuous_map (f := (star : A → A))).comp
          (continuous_fst.add continuous_snd)
      · exact ((UniformSpace.Completion.continuous_map (f := (star : A → A))).comp continuous_fst).add
          ((UniformSpace.Completion.continuous_map (f := (star : A → A))).comp continuous_snd)
    · intro a b
      rw [← UniformSpace.Completion.coe_add, star_coe, star_coe, star_coe, star_add,
        UniformSpace.Completion.coe_add]

noncomputable instance : StarMul (envelopingCStar (A := A)) where
  star_mul x y := by
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · apply isClosed_eq
      · exact (UniformSpace.Completion.continuous_map (f := (star : A → A))).comp
          (continuous_fst.mul continuous_snd)
      · exact ((UniformSpace.Completion.continuous_map (f := (star : A → A))).comp continuous_snd).mul
          ((UniformSpace.Completion.continuous_map (f := (star : A → A))).comp continuous_fst)
    · intro a b
      rw [← UniformSpace.Completion.coe_mul, star_coe, star_coe, star_coe, star_mul,
        UniformSpace.Completion.coe_mul]


noncomputable instance : StarRing (envelopingCStar (A := A)) where
  star_add := fun x y => by
    let : StarAddMonoid (envelopingCStar (A := A)) := inferInstance
    let : Star (envelopingCStar (A := A)) := inferInstance
    exact star_add x y
  star_mul := fun x y => by
    let : StarMul (envelopingCStar (A := A)) := inferInstance
    let : Star (envelopingCStar (A := A)) := inferInstance
    exact star_mul x y
  star_involutive := fun x => by
    let : InvolutiveStar (envelopingCStar (A := A)) := inferInstance
    let : Star (envelopingCStar (A := A)) := inferInstance
    exact star_involutive x

noncomputable instance : NormedRing (envelopingCStar (A := A)) :=
  UniformSpace.Completion.instNormedRing A

noncomputable instance : NormedSpace ℂ (envelopingCStar (A := A)) :=
  UniformSpace.Completion.instNormedSpace ℂ A

lemma envelopingNorm_star (x : envelopingCStar (A := A)) :
    ‖star x‖ = ‖x‖ := by
  have h_dense : DenseRange (fun a : A => (a : envelopingCStar (A := A))) :=
    UniformSpace.Completion.denseRange_coe
  have h_lhs_cont : Continuous (fun x : envelopingCStar (A := A) => ‖star x‖) :=
    (UniformSpace.Completion.continuous_map (f := (star : A → A))).norm
  have h_rhs_cont : Continuous (fun x : envelopingCStar (A := A) => ‖x‖) :=
    continuous_norm
  have h_eq : (fun x : envelopingCStar (A := A) => ‖star x‖) =
      (fun x : envelopingCStar (A := A) => ‖x‖) := by
    apply DenseRange.equalizer h_dense h_lhs_cont h_rhs_cont
    funext a
    simp only [Function.comp_apply]
    rw [star_coe]
    -- ‖↑(star a)‖ = ‖↑a‖ — rewrite using maximalNorm_star
    show ‖((star a : A) : envelopingCStar (A := A))‖ = ‖((a : A) : envelopingCStar (A := A))‖
    -- use norm_coe (if available) — translate to maximalNorm
    rw [show ‖((star a : A) : envelopingCStar (A := A))‖ = maximalNorm hfin (star a) from
        UniformSpace.Completion.norm_coe (star a),
      show ‖((a : A) : envelopingCStar (A := A))‖ = maximalNorm hfin a from
        UniformSpace.Completion.norm_coe a,
      maximalNorm_star]
  exact congrFun h_eq x

noncomputable instance : NormedStarGroup (envelopingCStar (A := A)) where
  norm_star_le x := le_of_eq (envelopingNorm_star x)

noncomputable instance : Algebra ℂ (envelopingCStar (A := A)) :=
  UniformSpace.Completion.algebra A ℂ

noncomputable instance : NormedAlgebra ℂ (envelopingCStar (A := A)) where
  norm_smul_le r x := by
    exact NormedSpace.norm_smul_le r x

noncomputable instance : StarModule ℂ (envelopingCStar (A := A)) where
  star_smul r x := by
    have h_dense : DenseRange (fun a : A => (a : envelopingCStar (A := A))) :=
      UniformSpace.Completion.denseRange_coe
    have h_lhs_cont : Continuous (fun x : envelopingCStar (A := A) => star (r • x)) :=
      (UniformSpace.Completion.continuous_map (f := (star : A → A))).comp
        (continuous_const_smul r)
    have h_rhs_cont : Continuous (fun x : envelopingCStar (A := A) => star r • star x) :=
      (continuous_const_smul (star r)).comp
        (UniformSpace.Completion.continuous_map (f := (star : A → A)))
    have h_eq : (fun x : envelopingCStar (A := A) => star (r • x)) =
        (fun x : envelopingCStar (A := A) => star r • star x) := by
      apply DenseRange.equalizer h_dense h_lhs_cont h_rhs_cont
      funext a
      simp only [Function.comp_apply]
      -- LHS: star (r • ↑a) = star ↑(r • a) = ↑(star (r • a))
      rw [← UniformSpace.Completion.coe_smul, star_coe]
      -- RHS: star r • star ↑a = star r • ↑(star a) — expand star ↑a
      rw [star_coe]
      -- Now the goal: ↑(star (r • a)) = star r • ↑(star a)
      -- Apply star_smul on A
      rw [star_smul]
      -- Now: ↑(star r • star a) = star r • ↑(star a)
      exact UniformSpace.Completion.coe_smul (star r) (star a)
    exact congrFun h_eq x

lemma envelopingNorm_cstar (x : envelopingCStar (A := A)) :
    ‖star x * x‖ = ‖x‖ * ‖x‖ := by
  have h_dense : DenseRange (fun a : A => (a : envelopingCStar (A := A))) :=
    UniformSpace.Completion.denseRange_coe
  have h_lhs_cont : Continuous (fun x : envelopingCStar (A := A) => ‖star x * x‖) :=
    continuous_norm.comp
      (((UniformSpace.Completion.continuous_map (f := (star : A → A))).mul continuous_id))
  have h_rhs_cont : Continuous (fun x : envelopingCStar (A := A) => ‖x‖ * ‖x‖) :=
    continuous_norm.mul continuous_norm
  have h_eq : (fun x : envelopingCStar (A := A) => ‖star x * x‖) =
      (fun x : envelopingCStar (A := A) => ‖x‖ * ‖x‖) := by
    apply DenseRange.equalizer h_dense h_lhs_cont h_rhs_cont
    funext a
    simp only [Function.comp_apply]
    rw [star_coe, ← UniformSpace.Completion.coe_mul]
    show ‖((star a * a : A) : envelopingCStar (A := A))‖ =
        ‖((a : A) : envelopingCStar (A := A))‖ * ‖((a : A) : envelopingCStar (A := A))‖
    rw [show ‖((star a * a : A) : envelopingCStar (A := A))‖ = maximalNorm hfin (star a * a) from
        UniformSpace.Completion.norm_coe (star a * a),
      show ‖((a : A) : envelopingCStar (A := A))‖ = maximalNorm hfin a from
        UniformSpace.Completion.norm_coe a,
      maximalNorm_cstar]
  exact congrFun h_eq x

noncomputable instance : CStarRing (envelopingCStar (A := A)) where
  norm_mul_self_le x := le_of_eq (envelopingNorm_cstar x).symm

noncomputable instance : CStarAlgebra (envelopingCStar (A := A)) := by
  letI : NormedRing (envelopingCStar (A := A)) := inferInstance
  letI : StarRing (envelopingCStar (A := A)) := inferInstance
  letI : CompleteSpace (envelopingCStar (A := A)) := inferInstance
  letI : CStarRing (envelopingCStar (A := A)) := inferInstance
  letI : NormedAlgebra ℂ (envelopingCStar (A := A)) := inferInstance
  letI : StarModule ℂ (envelopingCStar (A := A)) := inferInstance
  exact CStarAlgebra.mk

/-- The canonical embedding A → C*(A) as a *-algebra homomorphism -/
noncomputable def envelopingUnit : A →⋆ₐ[ℂ] envelopingCStar (A := A) where
  toFun := fun a => (a : envelopingCStar (A := A))
  map_one' := rfl
  map_mul' := fun a b => by
    change ((a * b : A) : envelopingCStar (A := A)) =
      (a : envelopingCStar (A := A)) * (b : envelopingCStar (A := A))
    exact UniformSpace.Completion.coe_mul a b
  map_zero' := rfl
  map_add' := fun a b => by
    change ((a + b : A) : envelopingCStar (A := A)) =
      (a : envelopingCStar (A := A)) + (b : envelopingCStar (A := A))
    exact UniformSpace.Completion.coe_add a b
  commutes' := fun r => rfl
  map_star' := fun a => by
    change ((star a : A) : envelopingCStar (A := A)) = star (a : envelopingCStar (A := A))
    exact (star_coe a).symm

/-- A contracting *-homomorphism into a C*-algebra is uniformly continuous -/
lemma starAlgHom_uniformContinuous
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a) :
    UniformContinuous (φ : A → B) := by
  have h_lip : LipschitzWith 1 (φ : A → B) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    have h_eq : (φ : A → B) a - (φ : A → B) b = (φ : A → B) (a - b) :=
      ((φ : A →+ B).map_sub a b).symm
    rw [h_eq]
    exact hφ_cont (a - b)
  exact h_lip.uniformContinuous


/-- Auxiliary function: the extension of φ to the completion by continuity -/
noncomputable def envelopingLiftFun
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (_hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a) :
    envelopingCStar (A := A) → B :=
  UniformSpace.Completion.extension φ

lemma envelopingLiftFun_coe
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a)
    (a : A) :
    envelopingLiftFun (A := A) B φ hφ_cont (envelopingUnit (A := A) a) = φ a := by
  change UniformSpace.Completion.extension (φ : A → B)
    ((a : A) : envelopingCStar (A := A)) = φ a
  exact UniformSpace.Completion.extension_coe
    (starAlgHom_uniformContinuous (A := A) B φ hφ_cont) a

lemma envelopingLiftFun_one
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a) :
    envelopingLiftFun (A := A) B φ hφ_cont (1 : envelopingCStar (A := A)) = 1 := by
  have h_coe : (1 : envelopingCStar (A := A)) = envelopingUnit (A := A) (1 : A) := rfl
  rw [h_coe, envelopingLiftFun_coe]
  exact (φ : A →* B).map_one

lemma envelopingLiftFun_zero
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a) :
    envelopingLiftFun (A := A) B φ hφ_cont (0 : envelopingCStar (A := A)) = 0 := by
  have h_coe : (0 : envelopingCStar (A := A)) = envelopingUnit (A := A) (0 : A) := rfl
  rw [h_coe, envelopingLiftFun_coe]
  exact (φ : A →+ B).map_zero

lemma envelopingLiftFun_add
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a)
    (x y : envelopingCStar (A := A)) :
    envelopingLiftFun (A := A) B φ hφ_cont (x + y) =
      envelopingLiftFun (A := A) B φ hφ_cont x +
      envelopingLiftFun (A := A) B φ hφ_cont y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · apply isClosed_eq
    · exact (UniformSpace.Completion.continuous_extension).comp
        (continuous_fst.add continuous_snd)
    · exact ((UniformSpace.Completion.continuous_extension).comp continuous_fst).add
        ((UniformSpace.Completion.continuous_extension).comp continuous_snd)
  · intro a b
    rw [← UniformSpace.Completion.coe_add]
    -- Now the goal: Φ ↑(a + b) = Φ ↑a + Φ ↑b
    have h1 : envelopingLiftFun B φ hφ_cont ((a + b : A) : envelopingCStar (A := A)) = φ (a + b) :=
      envelopingLiftFun_coe B φ hφ_cont (a + b)
    have h2 : envelopingLiftFun B φ hφ_cont ((a : A) : envelopingCStar (A := A)) = φ a :=
      envelopingLiftFun_coe B φ hφ_cont a
    have h3 : envelopingLiftFun B φ hφ_cont ((b : A) : envelopingCStar (A := A)) = φ b :=
      envelopingLiftFun_coe B φ hφ_cont b
    rw [h1, h2, h3]
    exact (φ : A →+ B).map_add a b

lemma envelopingLiftFun_mul
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a)
    (x y : envelopingCStar (A := A)) :
    envelopingLiftFun (A := A) B φ hφ_cont (x * y) =
      envelopingLiftFun (A := A) B φ hφ_cont x *
      envelopingLiftFun (A := A) B φ hφ_cont y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · apply isClosed_eq
    · exact (UniformSpace.Completion.continuous_extension).comp
        (continuous_fst.mul continuous_snd)
    · exact ((UniformSpace.Completion.continuous_extension).comp continuous_fst).mul
        ((UniformSpace.Completion.continuous_extension).comp continuous_snd)
  · intro a b
    rw [← UniformSpace.Completion.coe_mul]
    have h1 : envelopingLiftFun B φ hφ_cont ((a * b : A) : envelopingCStar (A := A)) = φ (a * b) :=
      envelopingLiftFun_coe B φ hφ_cont (a * b)
    have h2 : envelopingLiftFun B φ hφ_cont ((a : A) : envelopingCStar (A := A)) = φ a :=
      envelopingLiftFun_coe B φ hφ_cont a
    have h3 : envelopingLiftFun B φ hφ_cont ((b : A) : envelopingCStar (A := A)) = φ b :=
      envelopingLiftFun_coe B φ hφ_cont b
    rw [h1, h2, h3]
    exact (φ : A →* B).map_mul a b

lemma envelopingLiftFun_star
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a)
    (x : envelopingCStar (A := A)) :
    envelopingLiftFun (A := A) B φ hφ_cont (star x) =
      star (envelopingLiftFun (A := A) B φ hφ_cont x) := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · apply isClosed_eq
    · exact (UniformSpace.Completion.continuous_extension).comp
        (UniformSpace.Completion.continuous_map (f := (star : A → A)))
    · exact continuous_star.comp UniformSpace.Completion.continuous_extension
  · intro a
    rw [star_coe]
    have h1 : envelopingLiftFun B φ hφ_cont ((star a : A) : envelopingCStar (A := A)) = φ (star a) :=
      envelopingLiftFun_coe B φ hφ_cont (star a)
    have h2 : envelopingLiftFun B φ hφ_cont ((a : A) : envelopingCStar (A := A)) = φ a :=
      envelopingLiftFun_coe B φ hφ_cont a
    rw [h1, h2]
    exact map_star φ a

lemma envelopingLiftFun_algebraMap
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a)
    (r : ℂ) :
    envelopingLiftFun (A := A) B φ hφ_cont (algebraMap ℂ (envelopingCStar (A := A)) r) =
      algebraMap ℂ B r := by
  have h_coe : algebraMap ℂ (envelopingCStar (A := A)) r =
      envelopingUnit (A := A) (algebraMap ℂ A r) := rfl
  rw [h_coe, envelopingLiftFun_coe]
  exact φ.commutes r

/-- The extension of φ to the enveloping C*-algebra as a *-homomorphism -/
noncomputable def envelopingLift
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a) :
    envelopingCStar (A := A) →⋆ₐ[ℂ] B where
  toFun := envelopingLiftFun (A := A) B φ hφ_cont
  map_one' := envelopingLiftFun_one B φ hφ_cont
  map_zero' := envelopingLiftFun_zero B φ hφ_cont
  map_add' := envelopingLiftFun_add B φ hφ_cont
  map_mul' := envelopingLiftFun_mul B φ hφ_cont
  map_star' := envelopingLiftFun_star B φ hφ_cont
  commutes' := envelopingLiftFun_algebraMap B φ hφ_cont

lemma envelopingLift_coe
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a)
    (a : A) :
    envelopingLift (A := A) B φ hφ_cont (envelopingUnit (A := A) a) = φ a :=
  envelopingLiftFun_coe B φ hφ_cont a


lemma envelopingLift_unique
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a)
    (Φ : envelopingCStar (A := A) →⋆ₐ[ℂ] B)
    (hΦ_cont : Continuous Φ)
    (hΦ : ∀ a : A, Φ (envelopingUnit (A := A) a) = φ a) :
    Φ = envelopingLift (A := A) B φ hφ_cont := by
  have h_dense : DenseRange (fun a : A => (a : envelopingCStar (A := A))) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun x : envelopingCStar (A := A) => Φ x) =
      (fun x : envelopingCStar (A := A) => envelopingLift (A := A) B φ hφ_cont x) := by
    apply DenseRange.equalizer h_dense
    · exact hΦ_cont
    · exact UniformSpace.Completion.continuous_extension
    · funext a
      simp only [Function.comp_apply]
      change Φ ((a : A) : envelopingCStar (A := A)) =
        envelopingLift B φ hφ_cont ((a : A) : envelopingCStar (A := A))
      rw [show Φ ((a : A) : envelopingCStar (A := A)) = φ a from hΦ a,
          show envelopingLift B φ hφ_cont ((a : A) : envelopingCStar (A := A)) = φ a from
            envelopingLift_coe B φ hφ_cont a]
  exact StarAlgHom.ext (fun x => congrFun h_eq x)


/-- The universal property of the enveloping C*-algebra:
    any contracting *-homomorphism φ : A → B into a C*-algebra B
    factors uniquely through A → C*(A) -/
theorem envelopingCStar_universal
    (B : Type*) [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B)
    (hφ_cont : ∀ a : A, ‖φ a‖ ≤ maximalNorm hfin a) :
    ∃! Φ : envelopingCStar (A := A) →⋆ₐ[ℂ] B,
      Continuous Φ ∧ ∀ a : A, Φ (envelopingUnit (A := A) a) = φ a :=
  ⟨envelopingLift (A := A) B φ hφ_cont,
   ⟨UniformSpace.Completion.continuous_extension,
    fun a => envelopingLift_coe B φ hφ_cont a⟩,
   fun Φ ⟨hΦ_cont, hΦ⟩ => envelopingLift_unique B φ hφ_cont Φ hΦ_cont hΦ⟩


end EnvelopingCStar

theorem AlgHom.spectrum_subset
    {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (Φ : A →ₐ[ℂ] B) (a : A) :
    spectrum ℂ (Φ a) ⊆ spectrum ℂ a := by
  intro x hA
  rw [spectrum.mem_iff] at hA
  rw [spectrum.mem_iff]
  intro h_unit
  apply hA
  have h_map : Φ (algebraMap ℂ A x - a) = algebraMap ℂ B x - Φ a := by
    have h1 : Φ (algebraMap ℂ A x - a) = Φ (algebraMap ℂ A x) - Φ a :=
      (Φ : A →+ B).map_sub (algebraMap ℂ A x) a
    rw [h1, AlgHom.commutes]
  rw [← h_map]
  exact h_unit.map Φ


end AlgState
