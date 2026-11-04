module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ChangeOfRings.LowerShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.UpperShriekExistence

/-!
# Restriction of scalars and the derived upper shriek: the adjoint-uniqueness step

Let `φ : Λ₁ ⟶ Λ₂` be a homomorphism of torsion rings and let `f : X ⟶ Y` be a morphism of
schemes with `Y` quasi-compact, with a compactification `j`. By [Stacks, Tag 0G2C]
(`Stacks.EtaleCohomology.DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded`) the
derived lower shriek `Rf_!` has a right adjoint `Rf^!` over `Λ₁` and over `Λ₂`. This file proves
the step of [Stacks, Tag 0GLF] that is uniqueness of adjoints: an isomorphism

`Rf_!(-) ⊗^L_{Λ₁} Λ₂ ≅ Rf_!(- ⊗^L_{Λ₁} Λ₂)`

(the second square of [Stacks, Tag 0GL6]) gives, by passing to right adjoints along
`- ⊗^L_{Λ₁} Λ₂ ⊣ res` ([Stacks, Tag 07A6]), an isomorphism

`res ∘ Rf^! ≅ Rf^! ∘ res : D(Y_étale, Λ₂) ⥤ D(X_étale, Λ₁)`.

Both `Rf^!` are the right adjoints produced by Tag 0G2C, so neither is a hypothesis. The second
square of Tag 0GL6 is an argument here: it is a separate tag, and nothing in this file carries a
`@[stacks]` attribute. The left adjoints of `res` are arbitrary, so the step applies to any model
of `- ⊗^L_{Λ₁} Λ₂`, in particular to
`Stacks.EtaleCohomology.ChangeOfRings.derivedExtendScalars` with
`Stacks.EtaleCohomology.ChangeOfRings.derivedExtendRestrictScalarsAdj`.

## Main definitions

* `Stacks.EtaleCohomology.ChangeOfRings.upperShriekRestrictScalarsIsoOfLowerShriek`: the
  isomorphism `Rf^! ⋙ res ≅ res ⋙ Rf^!` obtained from the second square of Tag 0GL6.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology.ChangeOfRings

variable {Λ₁ Λ₂ : Type} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- `n = 0` in `Λ₂` as soon as `n = 0` in `Λ₁`: a ring receiving a map from a torsion ring is
torsion. -/
theorem natCast_eq_zero_of_ringHom (ψ : Λ₁ →+* Λ₂) {n : ℕ} (hΛ₁ : (n : Λ₁) = 0) : (n : Λ₂) = 0 := by
  rw [← map_natCast ψ n, hΛ₁, map_zero]

/-- **The adjoint-uniqueness step of [Stacks, Tag 0GLF].** Let `Λ₁` be torsion (`n = 0` in `Λ₁`
for some `n ≥ 1`), so that `Λ₂` is torsion too, let `j` be a compactification of `f : X ⟶ Y` with
`Y` quasi-compact, and let `L_X ⊣ res`, `L_Y ⊣ res` be left adjoints of restriction of scalars on
`X_étale` and `Y_étale`. An isomorphism `Rf_! ⋙ L_Y ≅ L_X ⋙ Rf_!` (the second square of
[Stacks, Tag 0GL6]) yields `Rf^! ⋙ res ≅ res ⋙ Rf^!`, both `Rf^!` being the right adjoints of
[Stacks, Tag 0G2C]. -/
def upperShriekRestrictScalarsIsoOfLowerShriek (n : ℕ) (hn : 0 < n) (hΛ₁ : (n : Λ₁) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] (j : CompactificationOf (Over.mk f))
    {LX : DerivedCategory (EtaleModules.{u, 0} Λ₁ X) ⥤ DerivedCategory (EtaleModules.{u, 0} Λ₂ X)}
    {LY : DerivedCategory (EtaleModules.{u, 0} Λ₁ Y) ⥤ DerivedCategory (EtaleModules.{u, 0} Λ₂ Y)}
    (adjX : LX ⊣ derivedRestrictScalars.{u, 0} φ X) (adjY : LY ⊣ derivedRestrictScalars.{u, 0} φ Y)
    (e : derivedLowerShriekUnbounded.{u, 0} f j Λ₁ ⋙ LY ≅
      LX ⋙ derivedLowerShriekUnbounded.{u, 0} f j Λ₂) :
    letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ₁ n hn hΛ₁ f j
    letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ₂ n hn
      (natCast_eq_zero_of_ringHom φ hΛ₁) f j
    (derivedLowerShriekUnbounded.{u, 0} f j Λ₂).rightAdjoint ⋙ derivedRestrictScalars.{u, 0} φ X ≅
      derivedRestrictScalars.{u, 0} φ Y ⋙
        (derivedLowerShriekUnbounded.{u, 0} f j Λ₁).rightAdjoint :=
  letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ₁ n hn hΛ₁ f j
  letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ₂ n hn
    (natCast_eq_zero_of_ringHom φ hΛ₁) f j
  ((conjugateIsoEquiv ((Adjunction.ofIsLeftAdjoint _).comp adjY)
    (adjX.comp (Adjunction.ofIsLeftAdjoint _))) e.symm).symm

end Stacks.EtaleCohomology.ChangeOfRings

end
