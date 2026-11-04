module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidalComp

/-!
# The composition isomorphism of derived pullbacks on `D_QCoh` is monoidal

For morphisms of schemes `f₁ : X ⟶ Y` and `f₂ : Y ⟶ Z`, the isomorphism
`Lf₂^* ⋙ Lf₁^* ≅ L(f₁ ≫ f₂)^*` of [Stacks, Tag 0D5S] on the quasi-coherent derived categories is a
monoidal natural isomorphism for the monoidal structures
`Stacks.Duality.monoidal_quasiCoherentDerivedPullback` of [Stacks, Tag 079U]; so is the
isomorphism `Lh₁^* ≅ Lh₂^*` attached to an equality `h₁ = h₂`.

## Main results

* `Stacks.Duality.derivedPullbackCompIso_isMonoidal` — on `D(𝒪)`, for the canonical monoidal
  structures.
* `Stacks.Duality.quasiCoherentDerivedPullbackCompIso_isMonoidal`
* `Stacks.Duality.quasiCoherentDerivedPullbackCongr_isMonoidal`

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z)

/-- **The composition isomorphism `Lf₂^* ⋙ Lf₁^* ≅ L(f₁ ≫ f₂)^*` on `D(𝒪)` is monoidal**, for the
monoidal structures `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal`
of [Stacks, Tag 079U] at the locally small models. -/
theorem derivedPullbackCompIso_isMonoidal :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    letI := Scheme.Modules.canonicalDerivedMonoidal Y
    letI := Scheme.Modules.canonicalDerivedMonoidal Z
    letI : (derivedPullback f₁).Monoidal :=
      Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f₁.toLRSHom.toShHom
    letI : (derivedPullback f₂).Monoidal :=
      Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f₂.toLRSHom.toShHom
    letI : (derivedPullback (f₁ ≫ f₂)).Monoidal :=
      Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
        (f₁ ≫ f₂).toLRSHom.toShHom
    NatTrans.IsMonoidal (derivedPullbackCompIso f₁ f₂).hom :=
  Stacks.Cohomology.DerivedPullbackTensor.isMonoidal_derivedPullbackCompIsoCanonical_hom_canonical
    f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom

/-- **The composition isomorphism `Lf₂^* ⋙ Lf₁^* ≅ L(f₁ ≫ f₂)^*` on `D_QCoh` is monoidal**, for
the monoidal structures `Stacks.Duality.monoidal_quasiCoherentDerivedPullback` of
[Stacks, Tag 079U]. -/
instance quasiCoherentDerivedPullbackCompIso_isMonoidal :
    NatTrans.IsMonoidal (quasiCoherentDerivedPullbackCompIso f₁ f₂).hom :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := Scheme.Modules.canonicalDerivedMonoidal Y
  letI := Scheme.Modules.canonicalDerivedMonoidal Z
  letI : (derivedPullback f₁).Monoidal :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f₁.toLRSHom.toShHom
  letI : (derivedPullback f₂).Monoidal :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f₂.toLRSHom.toShHom
  letI : (derivedPullback (f₁ ≫ f₂)).Monoidal :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
      (f₁ ≫ f₂).toLRSHom.toShHom
  haveI := derivedPullbackCompIso_isMonoidal f₁ f₂
  ObjectProperty.isMonoidal_lift_comp _ _ _ _ _ _ (derivedPullbackCompIso f₁ f₂).hom _
    (fun _ ↦ rfl)

/-- The isomorphism `Lh₁^* ≅ Lh₂^*` on `D_QCoh` attached to an equality `h₁ = h₂` is the identity
when `h₁` and `h₂` are the same morphism. -/
theorem quasiCoherentDerivedPullbackCongr_refl (h : X ⟶ Y) :
    (quasiCoherentDerivedPullbackCongr (rfl : h = h)).hom = 𝟙 _ := by
  ext K
  rfl

/-- **The isomorphism `Lh₁^* ≅ Lh₂^*` on `D_QCoh` attached to an equality `h₁ = h₂` is monoidal**,
for the monoidal structures `Stacks.Duality.monoidal_quasiCoherentDerivedPullback`. -/
instance quasiCoherentDerivedPullbackCongr_isMonoidal {h₁ h₂ : X ⟶ Y} (e : h₁ = h₂) :
    NatTrans.IsMonoidal (quasiCoherentDerivedPullbackCongr e).hom := by
  subst e
  rw [quasiCoherentDerivedPullbackCongr_refl]
  infer_instance

end Stacks.Duality

end
