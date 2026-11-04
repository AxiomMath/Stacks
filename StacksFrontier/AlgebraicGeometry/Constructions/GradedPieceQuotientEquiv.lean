module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded

/-!
# A local quotient presentation gives the degreewise identification with an associated graded ring

Let `Z` be a scheme, `𝓐` a sheaf of graded `𝒪_Z`-algebras, `W ⊆ Z` an open, `R₀` a commutative
ring, `J ⊆ R₀` an ideal and `φ : R₀ ⟶ Γ(Z, W)` a ring homomorphism. Suppose that for every
`n : ℕ` there is an additive map

`Jⁿ ⟶ Γ(𝓐ₙ, W)`

which is surjective, kills exactly `Jⁿ⁺¹`, and carries multiplication by `r : R₀` to the action
of `φ r`. Then it descends to an additive bijection

`Jⁿ/Jⁿ⁺¹ ≃+ Γ(𝓐ₙ, W)`.

## Why this is its own module

This is the construction `AlgebraicGeometry.degreeEquiv` performs for the conormal algebra of an
immersion, from the fields `localMap_eq_zero_iff`, `localMap_surjective` and `localMap_smul` of
`Stacks.Conormal.ConormalAlgebraData`, and the same construction is what
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/GradedPullbackSectionsRing.lean` needs
from `Stacks.Conormal.reesPullbackMap` for the pullback of a Rees algebra. It is nothing but the
first isomorphism theorem for a surjection with a known kernel, so it is stated here once.

The imports are exactly those of
`StacksFrontier/AlgebraicGeometry/Divisors/RegularImmersion/ConormalSections.lean`, so that
delegating `degreeEquiv` to this module grows no import closure.

## Main definitions

* `Stacks.AssociatedGradedSections.pieceEquivOfLocalMap`: the degreewise bijection.

## Main results

* `Stacks.AssociatedGradedSections.pieceEquivOfLocalMap_mk`: it sends the class of a
  representative to its local section.

## Implementation notes

Linearity over `φ` is needed, and not merely additivity, because `AssociatedGraded.piece` is a
quotient of *submodules*: the kernel of the local map has to be exhibited as a submodule of
`AssociatedGraded.power J n` before it can be compared with `AssociatedGraded.power J (n + 1)`.

`AssociatedGraded.power J n` is `J ^ n • ⊤` and the local map is stated at the ideal power
`J ^ n`; the two are the same submodule of `R₀` by `AssociatedGraded.ring_power_eq`, and the
`LinearEquiv` between them is the identity on representatives.

No `@[stacks]` attribute is attached: this is the first isomorphism theorem, specialised.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.AssociatedGradedSections

variable {Z : Scheme.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf)
  {W : Z.Opens} {R₀ : Type u} [CommRing R₀] (J : Ideal R₀) (φ : R₀ →+* Γ(Z, W))

section LocalMap

variable (loc : (n : ℕ) → ↥(J ^ n) →+ (A.piece (n : ℤ)).val.obj (op W))
  (hker : ∀ (n : ℕ) (a : ↥(J ^ n)), loc n a = 0 ↔ (a : R₀) ∈ J ^ (n + 1))
  (hsurj : ∀ n : ℕ, Function.Surjective (loc n))
  (hlsmul : ∀ (n : ℕ) (r : R₀) (a b : ↥(J ^ n)), (b : R₀) = r * (a : R₀) →
    loc n b = (show Z.ringCatSheaf.obj.obj (op W) from φ r) • loc n a)

include hker hsurj hlsmul in
/-- **A local quotient presentation gives the degreewise identification.** An additive map out
of `Jⁿ` into the degree-`n` sections of `𝓐` over `W` which is surjective, kills exactly `Jⁿ⁺¹`
and is linear over `φ` descends to an additive bijection `Jⁿ/Jⁿ⁺¹ ≃+ Γ(𝓐ₙ, W)`.

This is the construction `AlgebraicGeometry.degreeEquiv` performs for the local presentation of
[Stacks, Tag 0630]; the three hypotheses are the fields `localMap_eq_zero_iff`,
`localMap_surjective` and `localMap_smul` of `Stacks.Conormal.ConormalAlgebraData`. Linearity is
needed because the kernel has to be a *submodule*, not merely a subgroup, for
`AssociatedGraded.piece` — a quotient of submodules — to be the source. -/
def pieceEquivOfLocalMap (n : ℕ) :
    AssociatedGraded.piece (M := R₀) J n ≃+ (A.piece (n : ℤ)).val.obj (op W) := by
  let TObj := (A.piece (n : ℤ)).val.obj (op W)
  let T := TObj.carrier
  letI : AddCommGroup T := TObj.isAddCommGroup
  let M := AssociatedGraded.power (M := R₀) J n
  let ePow : M ≃ₗ[R₀] ↥(J ^ n) :=
    { toFun x := ⟨x.1, by simpa only [M, AssociatedGraded.ring_power_eq] using x.property⟩
      invFun x := ⟨x.1, by simpa only [M, AssociatedGraded.ring_power_eq] using x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let g : M →+ T := (loc n).comp ePow.toAddEquiv.toAddMonoidHom
  let P : Submodule R₀ M :=
    (AssociatedGraded.power (M := R₀) J (n + 1)).comap (Submodule.subtype M)
  let K : Submodule R₀ M :=
    { carrier := {x | g x = 0}
      zero_mem' := by simp [g]
      add_mem' := by
        intro x y hx hy
        change g (x + y) = 0
        rw [map_add, hx, hy, add_zero]
      smul_mem' := by
        intro r x hx
        have hg : g (r • x) =
            (show Z.ringCatSheaf.obj.obj (op W) from φ r) • g x := by
          change loc n (ePow (r • x)) = _
          rw [ePow.map_smul]
          exact hlsmul n r (ePow x) (r • ePow x) (by simp)
        change g (r • x) = 0
        rw [hg, hx, smul_zero] }
  have hkerK : K = P := by
    ext x
    change loc n (ePow x) = 0 ↔ x ∈ P
    rw [hker n (ePow x)]
    change (x : R₀) ∈ _ ↔
      (x : R₀) ∈ AssociatedGraded.power (M := R₀) J (n + 1)
    simp only [AssociatedGraded.ring_power_eq]
  have hsurjg : Function.Surjective g := (hsurj n).comp ePow.surjective
  have hkerAdd : K.toAddSubgroup = g.ker := AddSubgroup.ext fun _ => Iff.rfl
  exact (Submodule.quotEquivOfEq P K hkerK.symm).toAddEquiv.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hkerAdd).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective g hsurjg))

include hker hsurj hlsmul in
/-- `pieceEquivOfLocalMap` sends the class of a representative to its local section. -/
theorem pieceEquivOfLocalMap_mk (n : ℕ)
    (a : AssociatedGraded.power (M := R₀) J n) :
    pieceEquivOfLocalMap A J φ loc hker hsurj hlsmul n (AssociatedGraded.mk J n a) =
      loc n ⟨(a : R₀), by simpa using a.property⟩ :=
  rfl

end LocalMap

end Stacks.AssociatedGradedSections

end
