module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback of a quasi-coherent module on an affine base

Let `R` be a commutative ring and let `f : X ⟶ Spec R` be a morphism of ringed spaces. For an
`R`-module `M`, the derived pullback `Lf^*M̃` of the associated sheaf is computed by any K-flat
resolution of `M` over `R`: if `P^•` is a K-flat complex of `R`-modules quasi-isomorphic to `M`
in degree `0`, then `Lf^*M̃ ≅ f^*P̃^•`, the degreewise pullback of the degreewise sheafification
of `P^•`.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfATilde.derivedPullbackTildeIso`: a K-flat complex of
  `R`-modules computes the derived pullback of its sheafification.
* `Stacks.Cohomology.DerivedPullbackOfATilde.derivedPullbackTildeSingleIso`: `Lf^*M̃` is the
  degreewise pullback of the sheafification of a K-flat resolution of `M`.
* `Stacks.Cohomology.DerivedPullbackOfATilde.modulePullbackTildeFreeIsoCoproduct`: for a free
  module the degreewise pullback `f^*M̃` is a direct sum of copies of `𝒪_X`, indexed by a basis.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Cohomology.DerivedPullbackOfATilde

variable {R : CommRingCat.{u}} {X : RingedSpace.{u, u}} (f : X ⟶ (Spec R).toRingedSpace)

/-- Sheafification `M ↦ M̃` of an `R`-module, as a functor to the category of
`𝒪_{Spec R}`-modules of the ringed space `Spec R`. -/
def tildeFunctor (R : CommRingCat.{u}) :
    ModuleCat.{u} R ⥤ SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace) :=
  tilde.functor R

/-- Sheafification `M ↦ M̃` is an additive functor. -/
instance tildeFunctor_additive : (tildeFunctor R).Additive :=
  inferInstanceAs ((tilde.functor R).Additive)

/-- Sheafification `M ↦ M̃` is exact: it preserves homology. -/
instance tildeFunctor_preservesHomology : (tildeFunctor R).PreservesHomology :=
  Stacks.AffineTilde.tildeFunctor_preservesHomology R

/-- Degreewise sheafification of a complex of `R`-modules. -/
abbrev tildeComplex (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) ℤ :=
  ((tildeFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- For a K-flat complex `P` of `R`-modules, the derived pullback of its degreewise
sheafification `P̃` is the degreewise pullback of `P̃`: `Lf^*P̃ ≅ f^*P̃`. -/
def derivedPullbackTildeIso (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : CochainComplex.KFlat.{u, u} P) :
    (derivedPullback f).obj (DerivedCategory.Q.obj (tildeComplex P)) ≅
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (tildeComplex P)) :=
  haveI : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (tildeComplex P))) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.TildeStalk.kFlatComplex_tilde R P hP)
  (derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} _)).app (tildeComplex P)).symm ≪≫
    asIso ((derivedPullbackComparison f).app _) ≪≫
    DerivedCategory.Qh.mapIso (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app (tildeComplex P)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- A quasi-isomorphism of complexes of `R`-modules becomes an isomorphism in `D(𝒪_{Spec R})`
after degreewise sheafification. -/
theorem isIso_Q_map_tildeComplex_map {P Q' : CochainComplex (ModuleCat.{u} R) ℤ} (g : P ⟶ Q')
    (hg : QuasiIso g) :
    IsIso (DerivedCategory.Q.map
      (((tildeFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

/-- For a K-flat resolution `P^• ⟶ M` of an `R`-module `M`, `Lf^*M̃ ≅ f^*P̃^•` in `D(𝒪_X)`: the
derived pullback of `M̃` is the degreewise pullback of the sheafification of `P^•`. -/
def derivedPullbackTildeSingleIso (M : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) (hg : QuasiIso g) :
    (derivedPullback f).obj (DerivedCategory.Q.obj
        (tildeComplex ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))) ≅
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (tildeComplex P)) :=
  have := isIso_Q_map_tildeComplex_map (R := R) g hg
  (derivedPullback f).mapIso (asIso (DerivedCategory.Q.map
      (((tildeFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)).map g))).symm ≪≫
    derivedPullbackTildeIso f P hP

/-! ### Free modules -/

/-- The sheafification of a free module is the free sheaf on the same index type,
`(R^{(J)})^~ ≅ 𝒪_{Spec R}^{(J)}`. -/
def tildeFreeIso {J : Type u} (N : ModuleCat.{u} R) (b : Module.Basis J R N) :
    (tildeFunctor R).obj N ≅
      SheafOfModules.free.{u} (R := structureSheafRing (Spec R).toRingedSpace) J :=
  (tildeFunctor R).mapIso (b.repr.toModuleIso : N ≅ ModuleCat.of R (J →₀ R)) ≪≫
    AlgebraicGeometry.tildeFinsupp (R := R) J

/-- The pullback of the sheafification of a free module is free on the same index type,
`f^*(M^~) ≅ 𝒪_X^{(J)}` for `M` free on `J`. -/
def modulePullbackTildeFreeIso {J : Type u} (N : ModuleCat.{u} R) (b : Module.Basis J R N) :
    (modulePullback f).obj ((tildeFunctor R).obj N) ≅
      SheafOfModules.free.{u} (R := structureSheafRing X) J :=
  (modulePullback f).mapIso (tildeFreeIso N b) ≪≫ modulePullbackObjFreeIso f J

/-- The free sheaf on `J` is the coproduct of `J` copies of the structure sheaf. -/
def freeIsoCoproduct (Y : RingedSpace.{u, u}) (J : Type u) :
    SheafOfModules.free.{u} (R := structureSheafRing Y) J ≅
      ∐ fun _ : J => SheafOfModules.unit (structureSheafRing Y) :=
  Iso.refl _

/-- The pullback of the sheafification of a free module is a direct sum of copies of the
structure sheaf, indexed by a basis of the module. -/
def modulePullbackTildeFreeIsoCoproduct {J : Type u} (N : ModuleCat.{u} R)
    (b : Module.Basis J R N) :
    (modulePullback f).obj ((tildeFunctor R).obj N) ≅
      ∐ fun _ : J => SheafOfModules.unit (structureSheafRing X) :=
  modulePullbackTildeFreeIso f N b ≪≫ freeIsoCoproduct X J

end Stacks.Cohomology.DerivedPullbackOfATilde

end
