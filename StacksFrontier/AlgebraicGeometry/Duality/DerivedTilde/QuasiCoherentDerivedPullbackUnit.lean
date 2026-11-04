module

public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import
  StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackTensorIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidalUnit

/-!
# The unit of the monoidal structure of `Lf^*` on `D_QCoh`

For a morphism of schemes `f : X ⟶ Y`, the oplax unit `Lf^*𝒪_Y ⟶ 𝒪_X` of
`Stacks.Duality.monoidal_quasiCoherentDerivedPullback` is the comparison
`Stacks.Duality.derivedPullbackStructureSheafIso`, and the lax unit of `Lf^*` on `D(𝒪)` is its
inverse.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A left inverse of the inverse of an isomorphism is its hom. -/
private lemma eq_hom_of_comp_eq_id {C : Type*} [Category C] {A B : C} (e : A ≅ B) {ε : B ⟶ A}
    {η : A ⟶ B} (hε : ε = e.inv) (h : ε ≫ η = 𝟙 B) : η = e.hom := by
  subst hε
  rw [← Category.id_comp η, ← e.hom_inv_id, Category.assoc, h, Category.comp_id]

/-- **The oplax unit of `Lf^*` on `D_QCoh` is `Lf^*𝒪_Y ≅ 𝒪_X`**: its underlying morphism is
`Stacks.Duality.derivedPullbackStructureSheafIso`. -/
theorem quasiCoherentDerivedPullback_η_hom :
    (Functor.OplaxMonoidal.η (quasiCoherentDerivedPullback' f)).hom =
      (derivedPullbackStructureSheafIso f).hom := by
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let := Scheme.Modules.canonicalDerivedMonoidal Y
  let : (derivedPullback f).Monoidal :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f.toLRSHom.toShHom
  have hη :
      Functor.OplaxMonoidal.η (derivedPullback f) = (derivedPullbackStructureSheafIso f).hom :=
    eq_hom_of_comp_eq_id (derivedPullbackStructureSheafIso f)
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal_ε_eq
        f.toLRSHom.toShHom) (Functor.Monoidal.ε_η (derivedPullback f))
  have e₁ : (Functor.OplaxMonoidal.η (quasiCoherentDerivedPullback' f)).hom =
      Functor.OplaxMonoidal.η (ObjectProperty.ι _ ⋙ derivedPullback f) := rfl
  have e₂ : Functor.OplaxMonoidal.η (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
      (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf))) = 𝟙 _ := rfl
  exact e₁.trans ((Functor.OplaxMonoidal.comp_η _ _).trans ((congrArg (· ≫ _)
    ((congrArg _ e₂).trans (CategoryTheory.Functor.map_id _ _))).trans
      ((Category.id_comp _).trans hη)))

end Stacks.Duality
