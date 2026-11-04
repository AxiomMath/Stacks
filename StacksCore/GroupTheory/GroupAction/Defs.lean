module

public import Mathlib.GroupTheory.GroupAction.Defs

/-! # Group actions -/

@[expose] public section

/-- When a group `G` acts on a commutative monoid `M` by monoid automorphisms (i.e.
`IsScalarTower G M M`), the orbit space `MulAction.orbitRel.Quotient G M` inherits a
commutative monoid structure from `M`. -/
instance instCommMonoidOrbitRelQuotient (G M : Type*) [Group G] [CommMonoid M] [MulAction G M]
    [IsScalarTower G M M] : CommMonoid (MulAction.orbitRel.Quotient G M) where
  mul x y := Quotient.liftOn₂' x y (.mk _ <| · * ·) <| by
    rintro _ _ x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact Quotient.sound ⟨a * b, by simp [smul_mul_assoc, mul_comm x, smul_smul]⟩
  mul_assoc x y z := Quotient.inductionOn₃' x y z fun _ _ _ ↦
    show Quotient.mk'' _ = Quotient.mk'' _ by rw [mul_assoc]
  one := Quotient.mk'' 1
  one_mul x := Quotient.inductionOn' x fun _ ↦ show Quotient.mk'' _ = Quotient.mk'' _ by simp
  mul_one x := Quotient.inductionOn' x fun _ ↦ show Quotient.mk'' _ = Quotient.mk'' _ by simp
  mul_comm x y := Quotient.inductionOn₂' x y fun _ _ ↦
    show Quotient.mk'' _ = Quotient.mk'' _ by rw [mul_comm]
