import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  calc
    _ = |(s n - a) + (t n - b)| := by
      ring_nf
    _ <= |s n - a| + |t n - b| := by
      exact abs_add_le (s n - a) (t n - b)
    _ < ε / 2 + ε / 2 := by
      have hss : n ≥ Ns := by
        exact le_of_max_le_left hn
      have htt : n ≥ Nt := by
        exact le_of_max_le_right hn
      have hs' : |s n - a| < ε / 2 := by
        apply hs
        trivial
      have ht' : |t n - b| < ε / 2 := by
        apply ht
        trivial
      linarith
    _ = ε := by ring_nf



theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε hε
  let e := ε / |c|
  have he : e > 0 := by
    exact div_pos hε acpos
  obtain ⟨N, hN⟩ := cs e he
  use N
  intro n hn
  simp
  calc
    _ = |c * (s n - a)| := by ring_nf
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ < |c| * e := by
      have f : |s n - a| < e := by
        apply hN
        trivial
      exact (mul_lt_mul_iff_of_pos_left acpos).mpr (hN n hn)
    _ = ε := by
      unfold e
      ring_nf
      rw [mul_comm, ← mul_assoc]
      have x : |c|⁻¹ * |c| = 1 := by
        ring_nf
        refine CommGroupWithZero.mul_inv_cancel |c| ?_
        simp [h]
      rw [x]
      ring_nf




theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc
    |s n| = |s n - a + a| := by ring_nf
    _ <= |s n - a| + |a| := by exact abs_add_le (s n - a) a
    _ < 1 + |a| := by
      have g := h (n:=n) hn
      linarith
    _ = |a| + 1 := by linarith


theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  simp
  use max N₀ N₁
  intro n hn
  simp at h₁
  calc
    _ <= B * |t n| := by
      have x : N₀ ≤ n := by exact le_of_max_le_left hn
      have y' : |s n| <= B := by
        exact Std.le_of_lt (h₀ n x)
      gcongr
    _ < B * (ε / B) := by
      have x : |t n| < ε / B := by
        apply h₁
        exact le_of_max_le_right hn
      gcongr
    _ = ε := by
      field_simp
      





theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    exact abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have x : N >= Na := by
      apply?
    apply hNa
    trivial
  have absb : |s N - b| < ε := by
    apply hNb
    apply?
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |a - s N + (s N - b)| := by
        ring_nf
      _ <= |a - s N| + |s N - b| := by
        apply?
      _ = |s N - a| + |s N - b| := by
        have y:  |a - s N| = |s N - a| := by apply?
        rw [y]
      _ < ε + ε := by linarith
      _ = 2 * ε := by linarith
      _ = |a - b| := by
        unfold ε
        field_simp
  apply?


section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
