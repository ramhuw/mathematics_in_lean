import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro h
  intro x hx
  refine mem_preimage.mpr ?_
  apply h
  exact mem_image_of_mem f hx
  intro h x hx
  obtain ⟨y, hy⟩ := hx
  have h2 := h hy.1
  rw [← hy.2]
  exact mem_preimage.mp h2

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hx
  apply mem_preimage.mp at hx
  rcases hx with ⟨y, hy⟩
  have h3 := h hy.2
  rw [← h3]
  exact hy.1


example : f '' (f ⁻¹' u) ⊆ u := by
  intro x hx
  simp at hx
  rcases hx with ⟨a, ha⟩
  rw [← ha.2]
  exact ha.1

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x hx
  simp
  rcases h x with ⟨y, hy⟩
  use y
  rw [hy]
  constructor
  repeat
  trivial


example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x hx
  simp
  rcases hx with ⟨y, hy⟩
  use y
  constructor
  apply h
  exact hy.1
  exact hy.2

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  simp
  simp at hx
  apply h
  trivial

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  intro h
  simp at h
  simp
  trivial
  intro h
  simp at h
  simp
  trivial


example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x hx
  rcases hx with ⟨a, ha⟩
  simp
  constructor
  use a
  constructor
  exact mem_of_mem_inter_left ha.1
  exact ha.2
  use a
  constructor
  exact mem_of_mem_inter_right ha.1
  exact ha.2

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x hx
  simp
  rcases hx.1 with ⟨a, ha⟩
  rcases hx.2 with ⟨b, hb⟩
  have h' : a = b := by
    apply h
    rw [ha.2]
    rw [hb.2]
  use a
  constructor
  constructor
  exact ha.1
  rw [h']
  exact hb.1
  exact ha.2


example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x hx
  simp
  rcases hx.1 with ⟨a, ha⟩
  have h : a ∉ t := by
    intro h'
    rw [← ha.2] at hx
    have h'' : f a ∈ f '' t := by
      exact mem_image_of_mem f h'
    exact hx.2 h''
  use a
  constructor
  constructor
  exact ha.1
  trivial
  exact ha.2

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x hx
  simp
  simp at hx
  trivial

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  intro hx
  rcases hx with ⟨l, r⟩
  rcases l with ⟨y, hy⟩
  use y
  constructor
  constructor
  exact hy.1
  simp
  rw [hy.2]
  trivial
  exact hy.2
  intro hx
  rcases hx with ⟨y, hy⟩
  constructor
  use y
  constructor
  exact mem_of_mem_inter_left hy.1
  exact hy.2
  rw [← hy.2]
  simp at hy
  exact hy.1.2

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro x hx
  rcases hx with ⟨y, hy⟩
  constructor
  use y
  constructor
  exact mem_of_mem_inter_left hy.1
  exact hy.2
  simp at hy
  rw [← hy.2]
  exact hy.1.2

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x hx
  constructor
  apply mem_image_of_mem
  exact mem_of_mem_inter_left hx
  simp at hx
  exact hx.2

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x hx
  simp
  rcases hx with h1 | h2
  left
  use x
  right
  simp at h2
  trivial


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  intro hx
  rw [Set.mem_iUnion]
  obtain ⟨y, hy⟩ := hx
  rw [Set.mem_iUnion] at hy
  obtain ⟨i, hi⟩ := hy.1
  use i
  use y
  constructor
  exact hi
  exact hy.2
  intro hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  obtain ⟨y, hy⟩ := hi
  use y
  rw [Set.mem_iUnion]
  constructor
  use i
  exact hy.1
  exact hy.2


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro x hx
  rw [Set.mem_iInter]
  obtain ⟨y, hy⟩ := hx
  rw [Set.mem_iInter] at hy
  intro i
  let y' := hy.1 i
  simp
  constructor
  use y'
  exact hy.2

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x hx y hy hxy
  exact (sqrt_inj hx hy).mp hxy

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy hxy
  simp at hxy
  have h (a : ℝ) (ha : a ≥ 0) : a = sqrt (a ^ 2) := by
    exact Eq.symm (sqrt_sq ha)
  rw [h x, h y]
  rw [hxy]
  trivial
  trivial

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  intro hy
  obtain ⟨x, hx⟩ := hy
  simp
  rw [← hx.2]
  apply sqrt_nonneg
  intro hy
  use y^2
  constructor
  simp
  positivity
  exact sqrt_sq hy

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  intro hy
  simp
  simp at hy
  obtain ⟨x, hx⟩ := hy
  rw [← hx]
  exact sq_nonneg x
  intro hy
  simp
  use sqrt y
  exact sq_sqrt hy


end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  by
  constructor
  intro h
  intro y
  have h' : ∃ x, f x = f y := by
    use y
  unfold inverse
  rw [dif_pos h']
  apply h
  apply Classical.choose_spec h'
  intro h x y hxy
  have h' (a : α) : (inverse f) (f a) = a := by
    apply h
  rw [← h' x, ← h' y]
  rw [hxy]



example : Surjective f ↔ RightInverse (inverse f) f :=
  by
  constructor
  intro h
  intro y
  have h' : ∃ x, f x = y := by
    apply h
  unfold inverse
  rw [dif_pos h']
  apply Classical.choose_spec h'
  intro h y
  unfold RightInverse at h
  unfold LeftInverse at h
  use inverse f y
  apply h

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    unfold S
    simp
    exact h₁
  have h₃ : j ∉ S := by
    rw [← h]
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
