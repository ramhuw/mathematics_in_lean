import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left



example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  apply le_inf
  calc
    x ⊓ y ⊓ z ≤ x ⊓ y := by
      apply inf_le_left
    _ ≤ x := by
      apply inf_le_left
  apply le_inf
  calc
    x ⊓ y ⊓ z ≤ x ⊓ y := by
      apply inf_le_left
    _ ≤ y := by
      apply inf_le_right
  apply inf_le_right
  apply le_inf
  apply le_inf
  apply inf_le_left
  calc
    x ⊓ (y ⊓ z) ≤ y ⊓ z := by
      apply inf_le_right
    _ ≤ y := by
      apply inf_le_left
  calc
    x ⊓ (y ⊓ z) ≤ y ⊓ z := by
      apply inf_le_right
    _ ≤ z := by
      apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply sup_comm

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply sup_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  exact inf_sup_self


theorem absorb2 : x ⊔ x ⊓ y = x := by
  exact sup_inf_self

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h (a ⊔ b) a c]
  rw [inf_comm (a ⊔ b) a]
  have x : a ⊓ (a ⊔ b) = a := by
    exact absorb1 a b
  rw [x]
  have g : a ⊔ (a ⊔ b) = a ⊔ b := by
    rw [← sup_assoc]
    have g1 : a ⊔ a = a := by
      exact Std.max_self
    rw [g1]
  rw [inf_comm (a ⊔ b) c]
  rw [h c a b]
  rw [inf_comm c a, inf_comm c b]
  rw [← sup_assoc]
  rw [absorb2]


example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  have h1 : a ⊓ b ⊔ a = a := by
    rw [sup_comm]
    exact absorb2 a b
  rw [h1]
  rw [sup_comm (a⊓b) c]
  rw [h]
  rw [← inf_assoc]
  rw [sup_comm c a, sup_comm c b]
  rw [absorb1]



end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have g := add_le_add_right h (-a)
  calc
    0 = -a + a := by
      rw [add_comm]
      rw [add_neg_cancel]
    _ <= -a + b := by trivial
    _ = b - a := by
      rw [add_comm]
      rw [sub_eq_add_neg]

example (h: 0 ≤ b - a) : a ≤ b := by
  calc
    a = a + 0 := by
      simp
    _ ≤ a + (b - a) := by
      apply add_le_add_right
      trivial
    _ = b := by
      simp

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h : 0 ≤ (b - a) * c := by
    apply mul_nonneg
    have g := add_le_add_right h (-a)
    calc
      0 = -a + a := by
        rw [add_comm]
        rw [add_neg_cancel]
      _ <= -a + b := by trivial
      _ = b - a := by
        rw [add_comm]
        rw [sub_eq_add_neg]
    trivial
  calc
    a * c = 0 + a * c := by
      simp
    0 + a * c ≤ (b - a) * c + a * c := by
      simp
      trivial
  rw [sub_mul]
  simp


end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  exact dist_nonneg

end
