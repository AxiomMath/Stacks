module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackComplexMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.CategoryTheory.BifunctorProdMap

/-!
# The cochain-level comparison of Hom complexes, at the Tag 0A8Z spelling

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `E`, `F` be cochain
complexes of `𝒪_Y`-modules.  This file builds the canonical map of complexes of
`𝒪_X`-modules

`h^*𝓗om^•_{𝒪_Y}(E, F) ⟶ 𝓗om^•_{𝒪_X}(h^*E, h^*F)`

at the **internal Hom complex of Tag 0A8Z**, `AlgebraicGeometry.RingedSite.sheafHomComplex`.

## Why a second cochain-level comparison

`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackComplexMap`
already builds a cochain-level comparison, `pullbackSheafHomComplexMap`, from the same recipe —
the abstract transpose construction
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` — but at the
**monoidal-closed** internal hom of `Comp(Mod(𝒪))`, `MonoidalClosed.internalHom`.  That is a
*different complex* from the internal Hom complex of Tag 0A8Z: `ihom` is a degreewise
sheafification of a presheaf Hom while the internal Hom sheaf of Tag 03EM is already a sheaf, and
the implementation notes of that file record that ascribing `pullbackSheafHomComplexMap` the
Tag 0A8Z type is a type mismatch, machine-checked.

Tag 08DM — `Stacks.SheafOfModules.strictlyPerfectHomComparison`, the comparison identifying
`R𝓗om(QE, QF)` with the class of the Hom complex at a strictly perfect `E` — is stated at the
Tag 0A8Z complex.  So the derived-level equation that the source's proof of Tag 0GM7 clause (1)
runs on, *the model description of the map of Tag 08I3*, can only be written with a comparison at
that spelling.  This file supplies it, with no new mathematics, exactly as the implementation
notes of `…InternalHomPullbackComplexMap` predicted: the transpose construction is instantiated
at `AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor` and
`AlgebraicGeometry.RingedSite.curryHomEquivPair` on both sides, and the monoidality comparison it
is fed is the Tag 01CD comparison `pullbackTensorComplexNatIso` unchanged — the total tensor
complex `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` that the latter is stated at
being, by definition, `Functor.uncurry.obj (… .map₂HomologicalComplexReg …)`: the
`Functor.uncurry.obj (… .map₂HomologicalComplex …)` that `curryHomEquivPair` is stated at, with the
regular-hinted copies `HomologicalComplex.mapBifunctorReg` and
`HomologicalComplex.mapBifunctorMapReg` as objects and morphisms.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackHomComplexMap`: the comparison.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.pullbackHomComplexMap_adjoint`: its transpose is
  the Tag 01CD monoidality comparison followed by `h^*` of the cochain-level evaluation.  The
  currying bijection being a bijection, this pins the comparison down, so it cannot be satisfied
  by a degenerate map.
* `Stacks.Cohomology.DerivedInternalHomPullback.curryHomEquivPair_naturality_source`: Tag 08J8 in
  its source variable for the cochain-level currying bijection, in the shape
  `Transpose.TensorHomEquivNaturalLeft` is stated at.

## Nothing here is tagged

The map built here is a step of the *proof* of Tag 0GM7, not a clause of any published statement;
the published map is the derived one, `derivedPullbackSheafHomMap`, which already carries the
registration of Tag 08I3.  So no declaration below carries a tag, and in particular none of the
three
clauses of Tag 0GM7 is proved or weakened here.

## What is still owed to Tag 0GM7 clause (1)

Three things, in order:

1. *The model description of the map of Tag 08I3.*  The equation displayed in the implementation
   notes of `…InternalHomPullbackComplexMap` — that `derivedPullbackSheafHomMap h (QE) (QF)`, at a
   strictly perfect `E` and a K-flat `F`, is the derived image of the cochain-level comparison,
   read through the two Tag 08DM identifications and the comparison `Lh^*Q ⟶ Q h^*`.  With the
   comparison below in hand that equation typechecks; it is not proved here.  Both sides are
   determined by their transposes, by `Transpose.homComparison_adjoint` on the derived level and
   `pullbackHomComplexMap_adjoint` on this one, and the two inputs the equation then needs
   are `Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedCurryIso` and
   `AlgebraicGeometry.RingedSite.derivedApplication_eq_cochainEvaluation`.
2. *Invertibility of the comparison below at a strictly perfect `E`.*  This is the source's own
   last sentence, that `h^*𝓗om(ℰ, ℱ) = 𝓗om(h^*ℰ, ℱ)` whenever `ℰ` is a direct summand of a
   finite free `𝒪`-module, combined with the finite direct-sum description of the terms of the
   Hom complex, which is Tag 08DM — `Stacks.SheafOfModules.strictlyPerfectHomDegreeIso`.
3. *The local-to-global step*, the source's "the question is local on `Y`".  Perfectness
   (Stacks 08CM) gives a strictly perfect model only locally.  Note that this is where a
   cochain-level comparison earns its keep: invertibility of a morphism of `D(𝒪_Y)` has no
   restriction compatibility in this development, while quasi-isomorphy of a morphism of
   complexes is local, by `AlgebraicGeometry.RingedSite.quasiIso_of_coversTop`.  That is the
   shape in which the companion Tag 0G40 is proved, by
   `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_coversTop`.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPullbackTensor

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

-- The pullback development names the structure sheaf of a ringed space by `structureSheafRing`
-- and the tensor-product development by `Stacks.SheafOfModules.Tensor.ringSheaf`, while the
-- ringed-site vocabulary of Tag 0A8Z names it `(ringedSite Z).ringSheaf`.  All three are the
-- same sheaf of rings by `rfl`, and every statement here mixes them; the two Mathlib definitions
-- that bridge the explicit-constructor reduct of the first to the `(sheafCompose _ _).obj`
-- reduct of the second have to unfold at `implicit` transparency for the mixed statements to be
-- type-correct there, and at `instances` transparency for the additivity instances below to be
-- recognised as applicable: those are stated over a space and a sheaf of rings on it, so the
-- module category they name is `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Rc)`,
-- while the statements here name the same category as `…KFlatDerivedPullback.Modules Z`, through
-- `Z.sheaf`.  `instance_reducible` gives both, being the stronger of the two settings;
-- `structureSheafRing` carries it globally already.
attribute [local instance_reducible] StacksDraft.KFlat.modulePullback
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

-- The three instances of the total tensor complex on a ringed space — the additivity of
-- `⊗_{𝒪_Z}` in each variable and the existence of the total complexes — are the ones
-- `Stacks.Topology.SheafTensorAdditiveOnOpens` states for the open-cover site of a space,
-- reused rather than restated and re-attributed section by section below.  Each is stated there
-- with its site and every universe written out rather than left to synthesis: over `Opens Z` the
-- universe of the site and the universe of the sections of `𝒪_Z` coincide, and instance search
-- then has to solve `max ?u ?v =?= u` with both unknown.

/-! ### The comparison -/

section Comparison

-- No sheafify binder appears here.  `HasWeakSheafify` and `WEqualsLocallyBijective` for the
-- open-cover topology of a ringed space are global instances of this development
-- (`Stacks.Topology.RingedSpaceSheafifyOpens`), and carrying them as binders as well would
-- create a second spelling of each for instance search to pick wrongly.  Indeed, the
-- declarations below elaborate with the four binders dropped.
variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

attribute [local instance 10000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The cochain-level comparison of Hom complexes at the Tag 0A8Z spelling**,

`h^*𝓗om^•_{𝒪_Y}(E, F) ⟶ 𝓗om^•_{𝒪_X}(h^*E, h^*F)`,

for a morphism of ringed spaces `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and cochain complexes `E`, `F` of
`𝒪_Y`-modules.

It is the abstract transpose construction of Tag 08I3,
`Transpose.homComparison`, instantiated at the internal Hom complex bifunctor of Tag 0A8Z, the
currying bijection of Tag 0A90 in the transpose-ready shape
`AlgebraicGeometry.RingedSite.curryHomEquivPair`, and the monoidality comparison of Tag 01CD on
total tensor complexes, `pullbackTensorComplexNatIso`.  Nothing is assumed of `E` or `F`. -/
def pullbackHomComplexMap
    (E F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackComplex h).obj
        ((AlgebraicGeometry.RingedSite.sheafHomComplex
          (AlgebraicGeometry.RingedSpace.ringedSite Y) E F).obj) ⟶
      (AlgebraicGeometry.RingedSite.sheafHomComplex
        (AlgebraicGeometry.RingedSpace.ringedSite X) ((pullbackComplex h).obj E)
        ((pullbackComplex h).obj F)).obj :=
  Transpose.homComparison (pullbackComplex h)
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y).sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (pullbackTensorComplexNatIso h) E F

/-- **The transpose of the comparison is the transpose datum**: the monoidality comparison of
Tag 01CD followed by `h^*` of the cochain-level evaluation `𝓗om^•(E, F) ⊗ E ⟶ F`.

The currying bijection of Tag 0A90 being a bijection, this pins `pullbackHomComplexMap` down: it
is the unique morphism with that transpose.  So the construction above is not satisfiable by a
degenerate map, and in particular not by zero unless the datum itself is zero.

This is `Transpose.homComparison_adjoint` at the Tag 0A8Z data. -/
theorem pullbackHomComplexMap_adjoint
    (E F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    AlgebraicGeometry.RingedSite.curryHomEquivPair
        (AlgebraicGeometry.RingedSpace.ringedSite X)
        ((pullbackComplex h).obj
          ((AlgebraicGeometry.RingedSite.sheafHomComplex
            (AlgebraicGeometry.RingedSpace.ringedSite Y) E F).obj))
        ((pullbackComplex h).obj E) ((pullbackComplex h).obj F)
        (pullbackHomComplexMap h E F) =
      Transpose.homComparisonDatum (pullbackComplex h)
        (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
          (AlgebraicGeometry.RingedSpace.ringedSite Y))
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y).sheaf))
        (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf))
        (AlgebraicGeometry.RingedSite.curryHomEquivPair
          (AlgebraicGeometry.RingedSpace.ringedSite Y))
        (pullbackTensorComplexNatIso h) E F :=
  Transpose.homComparison_adjoint (pullbackComplex h)
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y).sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (pullbackTensorComplexNatIso h) E F

end Comparison

/-! ### Tag 08J8 in its source variable, at the cochain level -/

section Naturality

variable (Z : RingedSpace.{u, u})

attribute [local instance 10000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- Naturality of the cochain-level currying bijection in its source variable, in the shape of
`Transpose.TensorHomEquivNaturalLeft`: the transpose of `φ ≫ ψ` is the transpose of `ψ`
precomposed with `φ ⊗ 1`, for the uncurried total tensor complex. -/
theorem curryHomEquivPair_naturality_source
    (A A' B C : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (φ : A ⟶ A')
    (ψ : A' ⟶ ((AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Z)).obj (op B)).obj C) :
    AlgebraicGeometry.RingedSite.curryHomEquivPair
        (AlgebraicGeometry.RingedSpace.ringedSite Z) A B C (φ ≫ ψ) =
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z).sheaf)).map
          (φ ×ₘ 𝟙 B) ≫
        AlgebraicGeometry.RingedSite.curryHomEquivPair
          (AlgebraicGeometry.RingedSpace.ringedSite Z) A' B C ψ := by
  rw [CategoryTheory.uncurry_map_mkHom_id
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z).sheaf).map₂HomologicalComplexReg
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) φ B]
  exact AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_source
    (AlgebraicGeometry.RingedSpace.ringedSite Z) φ B C ψ

end Naturality

end Stacks.Cohomology.DerivedInternalHomPullback

end
