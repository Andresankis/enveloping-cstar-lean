import Mathlib

/-!
# C*-полунормы

Определение C*-полунормы (unbundled) на комплексной *-алгебре
со значениями в `ENNReal`.
-/

set_option linter.style.whitespace false

structure CStarSeminorm (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] where
  toFun : A → ENNReal
  map_zero : toFun 0 = 0
  map_one_le : toFun 1 ≤ 1
  map_add_le : ∀ a b, toFun (a + b) ≤ toFun a + toFun b
  map_mul_le : ∀ a b, toFun (a * b) ≤ toFun a * toFun b
  map_star : ∀ a, toFun (star a) = toFun a
  map_smul : ∀ (r : ℂ) (a : A), toFun (r • a) = (‖r‖₊ : ENNReal) * toFun a
  cstar_identity : ∀ a, toFun (star a * a) = (toFun a) ^ 2

namespace CStarSeminorm

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

instance : CoeFun (CStarSeminorm A) (fun _ => A → ENNReal) :=
  ⟨CStarSeminorm.toFun⟩

@[simp] lemma coe_zero (s : CStarSeminorm A) : s 0 = 0 := s.map_zero

@[simp] lemma coe_one_le (s : CStarSeminorm A) : s 1 ≤ 1 := s.map_one_le

@[simp] lemma coe_star (s : CStarSeminorm A) (a : A) : s (star a) = s a :=
  s.map_star a

lemma coe_add_le (s : CStarSeminorm A) (a b : A) : s (a + b) ≤ s a + s b :=
  s.map_add_le a b

lemma coe_mul_le (s : CStarSeminorm A) (a b : A) : s (a * b) ≤ s a * s b :=
  s.map_mul_le a b

lemma coe_smul (s : CStarSeminorm A) (r : ℂ) (a : A) :
    s (r • a) = (‖r‖₊ : ENNReal) * s a := s.map_smul r a

lemma coe_cstar (s : CStarSeminorm A) (a : A) : s (star a * a) = (s a) ^ 2 :=
  s.cstar_identity a

lemma coe_neg (s : CStarSeminorm A) (a : A) : s (-a) = s a := by
  have h : (-a : A) = (-1 : ℂ) • a := by simp
  rw [h, s.map_smul]
  simp

lemma coe_pow_le (s : CStarSeminorm A) (a : A) (n : ℕ) :
    s (a ^ n) ≤ (s a) ^ n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ]
    calc s (a ^ n * a) ≤ s (a ^ n) * s a := s.map_mul_le (a ^ n) a
      _ ≤ (s a) ^ n * s a := by gcongr
      _ = (s a) ^ (n + 1) := by rw [pow_succ]

lemma coe_natCast_le (s : CStarSeminorm A) (n : ℕ) :
    s (n : A) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_cast : ((n + 1 : ℕ) : A) = (n : A) + 1 := by
      push_cast
      ring_nf
    rw [h_cast]
    calc s ((n : A) + 1) ≤ s (n : A) + s 1 := s.map_add_le (n : A) 1
      _ ≤ (n : ENNReal) + 1 := add_le_add ih s.map_one_le
      _ = ((n + 1 : ℕ) : ENNReal) := by push_cast; ring_nf

lemma coe_sub_le (s : CStarSeminorm A) (a b : A) :
    s (a - b) ≤ s a + s b := by
  calc s (a - b) = s (a + (-b)) := by rw [sub_eq_add_neg]
    _ ≤ s a + s (-b) := s.map_add_le a (-b)
    _ = s a + s b := by rw [s.coe_neg]

/-- Радикал полунормы: множество элементов с нулевой полунормой -/
def radical (s : CStarSeminorm A) : Set A := {a | s a = 0}

lemma mem_radical_zero (s : CStarSeminorm A) : (0 : A) ∈ s.radical := by
  simp [radical]



end CStarSeminorm
