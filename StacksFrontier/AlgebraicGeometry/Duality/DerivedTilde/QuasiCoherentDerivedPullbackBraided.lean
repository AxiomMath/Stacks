module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackTensorIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackBraided

/-!
# Derived pullback is braided on `D_QCoh`

For a scheme `X`, at the locally small model, `D_QCoh(𝒪_X)` is a full symmetric monoidal
subcategory of `D(𝒪_X)` with the symmetry
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`, induced by the Koszul symmetry
of complexes. For a morphism of schemes `f : X ⟶ Y`, the strong monoidal functor
`Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` of `Stacks.Duality.monoidal_quasiCoherentDerivedPullback`
is braided: its tensorator `Lf^*(K ⊗ᴸ M) ≅ Lf^*K ⊗ᴸ Lf^*M` of [Stacks, Tag 079U] commutes with
the symmetries.

## Main definitions

* `Stacks.Duality.symmetricCategory_quasiCoherentDerivedCategory` — the symmetric structure.
* `Stacks.Duality.braided_quasiCoherentDerivedPullback` — `Lf^*` is braided.

## Main results

* `Stacks.Duality.quasiCoherentDerivedPullback_δ_braiding` — the tensorator in oplax form,
  `δ(K, M) ≫ β_{Lf^*K, Lf^*M} = Lf^*(β_{K,M}) ≫ δ(M, K)`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
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

/-- **`D_QCoh(𝒪_X)` is a symmetric monoidal category**, as a full monoidal subcategory of
`D(𝒪_X)` with the symmetry `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`
induced by the Koszul symmetry of complexes. -/
instance symmetricCategory_quasiCoherentDerivedCategory (X : Scheme.{u}) :
    SymmetricCategory (quasiCoherentDerivedCategory X) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI : SymmetricCategory (DerivedCategory X.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf
  ObjectProperty.fullSymmetricSubcategory _

/-- The braiding of `D_QCoh(𝒪_X)` is the braiding of `D(𝒪_X)`. -/
theorem braiding_hom_quasiCoherentDerivedCategory (X : Scheme.{u})
    (K M : quasiCoherentDerivedCategory X) :
    (β_ K M).hom.hom =
      (@BraidedCategory.braiding _ _ (Scheme.Modules.canonicalDerivedMonoidal X)
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf).toBraidedCategory
        K.obj M.obj).hom :=
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Derived pullback `Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` is a braided monoidal functor**,
extending `Stacks.Duality.monoidal_quasiCoherentDerivedPullback`: the tensorator of
[Stacks, Tag 079U] commutes with the symmetries. It is the restriction of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalBraided`. -/
instance braided_quasiCoherentDerivedPullback : (quasiCoherentDerivedPullback' f).Braided :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  letI := Scheme.Modules.canonicalDerivedMonoidal Y
  letI : SymmetricCategory (DerivedCategory X.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf
  letI : SymmetricCategory (DerivedCategory Y.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Y.sheaf
  letI : (derivedPullback f).Braided :=
    Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalBraided f.toLRSHom.toShHom
  { toMonoidal := monoidal_quasiCoherentDerivedPullback f
    braided := (ObjectProperty.liftLaxBraided
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (ObjectProperty.ι _ ⋙ derivedPullback f)
      (isQuasicoherent_homology_derivedPullback' f)).braided }

/-- `braided_quasiCoherentDerivedPullback` extends `monoidal_quasiCoherentDerivedPullback`. -/
lemma braided_quasiCoherentDerivedPullback_toMonoidal :
    (braided_quasiCoherentDerivedPullback f).toMonoidal = monoidal_quasiCoherentDerivedPullback f :=
  rfl

/-- **The tensorator of `Lf^*` on `D_QCoh` commutes with the symmetries** ([Stacks, Tag 079U]):
for `K`, `M` in `D_QCoh(𝒪_Y)`, `δ(K, M) ≫ β_{Lf^*K, Lf^*M} = Lf^*(β_{K,M}) ≫ δ(M, K)`, where `δ`
is the oplax tensorator of `Stacks.Duality.monoidal_quasiCoherentDerivedPullback`. -/
theorem quasiCoherentDerivedPullback_δ_braiding (K M : quasiCoherentDerivedCategory Y) :
    Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) K M ≫
        (β_ ((quasiCoherentDerivedPullback' f).obj K)
          ((quasiCoherentDerivedPullback' f).obj M)).hom =
      (quasiCoherentDerivedPullback' f).map (β_ K M).hom ≫
        Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' f) M K :=
  (Functor.map_braiding_comp_δ _ K M).symm

end Stacks.Duality

end
