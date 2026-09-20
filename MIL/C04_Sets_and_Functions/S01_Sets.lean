import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro a ha
  constructor
  rcases ha with h1 | h2
  exact mem_of_mem_inter_left h1
  exact mem_of_mem_inter_left h2
  rcases ha with h1 | h2
  left
  exact mem_of_mem_inter_right h1
  right
  exact mem_of_mem_inter_right h2

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro a ha
  constructor
  constructor
  exact mem_of_mem_inter_left ha
  intro h
  have h' : a ∈ t ∪ u := by exact mem_union_left u h
  exact ha.2 h'
  intro h
  have h' : a ∈ t ∪ u := by exact mem_union_right t h
  exact ha.2 h'

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    by
    apply Subset.antisymm
    repeat
    intro x hx
    exact ⟨hx.2, hx.1⟩

example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  exact inter_subset_left
  intro x hx
  constructor
  assumption
  exact mem_union_left t hx

example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  intro x hx
  rcases hx with h1 | h2
  trivial
  exact mem_of_mem_inter_left h2
  intro x hx
  left
  trivial

example : s \ t ∪ t = s ∪ t := by
  apply Subset.antisymm
  intro x hx
  obtain h1 | h2 := hx
  left
  exact mem_of_mem_inter_left h1
  right
  trivial
  intro x hx
  have h := Classical.em (x ∈ t)
  rcases h with h1 | h2
  right
  trivial
  left
  constructor
  rcases hx with h3 | h4
  trivial
  trivial
  trivial

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  intro x hx
  rcases hx with h1 | h2
  constructor
  left
  exact mem_of_mem_inter_left h1
  have h' := h1.2
  intro f
  exact h' (mem_of_mem_inter_right f)
  constructor
  right
  exact h2.1
  intro h3
  have h4 := h3.1
  exact h2.2 h4
  intro x hx
  let h := Classical.em (x ∈ s \ t)
  rcases h with h3 | h4
  left
  trivial
  right
  constructor
  by_contra
  have h : x ∉ s ∪ t := by
    intro f
    rcases f
    apply h4
    constructor
    trivial
    trivial
    trivial
  exact h hx.1
  intro f
  apply h4
  constructor
  trivial
  intro g
  have h : x ∈ (s ∩ t) := by
    exact mem_inter f g
  exact hx.2 h

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro x hn h
  obtain ⟨y, hy⟩ := h
  have h' : 2 * y = x := by linarith
  have h1 : x ∣ 2 * y := by
    use 1
    simp
    trivial
  simp at hn
  have h := Nat.prime_iff.symm.mpr hn.1
  unfold Prime at h
  have h₀ : x ≠ 0 := by linarith
  have h₁ : ¬ IsUnit x := by
    simp
    linarith
  have h₂ := h.2.2 2 y h1
  rcases h₂ with h3 | h4
  have h4 : x <= 2 := by
    apply Nat.le_of_dvd
    decide
    trivial
  have h4' : ¬ x > 2 := by
    exact Nat.not_lt.mpr h4
  exact h4' hn.2
  have h5 : y ≠ 0 := by
    intro f
    rw [f] at h'
    simp at h'
    symm at h'
    exact h₀ h'
  have g : x ≤ y := by
    apply Nat.le_of_dvd
    linarith
    trivial
  rw [hy] at g
  have h6 : y <= 0 := by
    linarith
  have h7 : x <= 0 := by
    linarith
  have h8 : ¬ x > 0 :=
    by exact Nat.not_lt.mpr h7
  have h8' : x > 0 := by
    linarith
  exact h8 h8'




#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x hx
  have h : x ∈ t := by
    apply ssubt
    trivial
  constructor
  apply h₀
  trivial
  apply h₁
  trivial


example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, hx⟩
  use x
  constructor
  apply ssubt
  exact hx.1
  exact hx.2.2

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  apply Subset.antisymm
  intro x hx
  rcases hx with h1 | h2
  rw [Set.mem_iInter]
  intro i
  right
  trivial
  rw [Set.mem_iInter]
  intro i
  rw [Set.mem_iInter] at h2
  left
  apply h2
  intro x hx
  rw [Set.mem_iInter] at hx
  cases Classical.em (x ∈ s)
  left
  trivial
  right
  rw [Set.mem_iInter]
  intro i
  have hxx := hx i
  cases hxx
  trivial
  false_or_by_contra
  trivial




def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  ext x
  constructor
  intro h
  trivial
  intro h
  let ⟨p, hp⟩ := Nat.exists_infinite_primes x
  rw [mem_iUnion₂]
  use p
  constructor
  simp
  exact hp.1
  exact hp.2


end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
