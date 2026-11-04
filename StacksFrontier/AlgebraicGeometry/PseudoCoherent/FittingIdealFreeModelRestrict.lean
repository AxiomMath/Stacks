module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealDerivedModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# Restricting a finite free model to a smaller open

`AlgebraicGeometry.DerivedFreeModel K U` records a bounded-above finite free model, over the open
`U`, of a complex `K` of `𝒪_X`-modules: a complex `model` which over `U` is free of finite rank in
each degree (`isFree`), a chosen basis of its sections over `U` in each degree (`basis`), and an
isomorphism in `D(𝒪_U)` between the two restrictions (`derivedIso`). The Fitting ideal sheaf of
[Stacks, Tag 0ESP] is `Scheme.IdealSheafData.ofIdeals` applied to the family of ideals of minors of
all such models, so it comes with an upper bound for free and with *no* lower bound; a lower bound
means producing a genuine quasi-coherent ideal sheaf, hence knowing how the family behaves on
passing from an affine open `U` to a standard open `D(f) ⊆ U`, hence having a model over `D(f)`
built from one over `U`.

This file supplies two of the fields of such a restriction: the trivialization and the
isomorphism in the derived category both restrict to a smaller open. What remains is the `basis`
field, which is *data independent of* `isFree` and so is not produced by the transported
trivialization; the implementation notes record exactly what it needs, and
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/FittingIdealFreeModelBasis.lean` assembles it.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nonempty_restrictFunctor_iso_free_of_le`: a trivialization of
  an `𝒪_X`-module over an open `U` restricts to a trivialization over any smaller open.
* `AlgebraicGeometry.DerivedFreeModel.isFree_of_le`: the `isFree` field of a finite free model over
  `U`, read on a smaller open.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesHomology`: restriction along an open
  immersion preserves homology, being exact.
* `AlgebraicGeometry.Scheme.Modules.isoOverOpen_of_le`: an isomorphism in `D(𝒪_U)` of the
  restrictions of two complexes restricts to one in `D(𝒪_V)` for `V ≤ U`.
* `AlgebraicGeometry.DerivedFreeModel.derivedIso_of_le`: the `derivedIso` field of a finite free
  model over `U`, read on a smaller open.

## Implementation notes

Restriction to `V ≤ U` factors through restriction to `U`: that is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` along `AlgebraicGeometry.Scheme.homOfLE`,
whose composite with `U.ι` is `V.ι` by `AlgebraicGeometry.Scheme.homOfLE_ι`, the discrepancy being
absorbed by `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`. Both halves below are that
factorization followed by a transport: for the trivialization, along
`AlgebraicGeometry.Scheme.Modules.restrictFreeIso` (restriction sends a free module to a free
module on the same index type); for the isomorphism in the derived category, along
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the restriction from `U` to `V`, which is
exact.

A `AlgebraicGeometry.DerivedFreeModel K V` built from a `AlgebraicGeometry.DerivedFreeModel K U`
still needs the `basis` field, a `Module.Basis (Fin (rank i)) Γ(X, V) Γ(model.X i, V)`, and then
the identification of its matrix with the entrywise image of
`AlgebraicGeometry.DerivedFreeModel.matrix` under `X.presheaf.map (homOfLE _).op`, which is
assembled from:

* `Stacks.SheafOfModules.freeSheafBasis` with `Stacks.SheafOfModules.freeSheafBasis_apply` and
  `Stacks.SheafOfModules.freeSheafBasis_natural` give the basis of the sections of a finite free
  sheaf of modules over an open, and its naturality under restriction;
* `Stacks.Eta.Sections.restrictionMatrix` and `Stacks.Eta.Sections.restrictionMatrix_comm` give
  the matrix over `Γ(X, V)` of the restriction map on sections and the intertwining of the two
  matrix complexes, which collapses to the entrywise image exactly when the basis over `V` is the
  restriction of the basis over `U`;
* `Stacks.FittingComplex.FreeData.map_fittingIdeal` then identifies the two ideals of minors, and
  `Stacks.FittingComplex.FreeData.fittingIdeal_eq_of_units_mul_mul` absorbs the change of basis
  between the restricted basis and the chosen one.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Scheme.Modules

/-- **A trivialization of an `𝒪_X`-module over an open `U` restricts to a trivialization over any
smaller open.** Restriction to `V` factors through restriction to `U`, and the restriction of a
free module is free on the same index type. This is the `isFree` field of
`AlgebraicGeometry.DerivedFreeModel` transported along an inclusion of opens. -/
theorem nonempty_restrictFunctor_iso_free_of_le {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U)
    (M : X.Modules) (I : Type u)
    (h : Nonempty ((restrictFunctor U.ι).obj M ≅
      SheafOfModules.free (R := (U.toScheme).ringCatSheaf) I)) :
    Nonempty ((restrictFunctor V.ι).obj M ≅
      SheafOfModules.free (R := (V.toScheme).ringCatSheaf) I) := by
  obtain ⟨e⟩ := h
  exact ⟨((restrictFunctorCongr (X.homOfLE_ι hVU)).app M).symm ≪≫
    (restrictFunctorComp (X.homOfLE hVU) U.ι).app M ≪≫
    (restrictFunctor (X.homOfLE hVU)).mapIso e ≪≫
    (restrictFreeIso (X.homOfLE hVU) I).symm⟩

/-- **Restriction of sheaves of modules along an open immersion preserves homology**: it is
additive, preserves finite limits (`restrictFunctor_preservesFiniteLimits`) and, being a left
adjoint, preserves finite colimits, hence is exact. -/
instance restrictFunctor_preservesHomology {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).PreservesHomology :=
  haveI : PreservesFiniteColimits (restrictFunctor f) := inferInstance
  Functor.preservesHomologyOfExact (restrictFunctor f)

end Scheme.Modules

namespace DerivedFreeModel

variable {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ} {U : X.Opens}

/-- The `isFree` field of a finite free model over `U`, read on a smaller open `V ≤ U`: in each
degree the model is still free of the same rank over `V`. -/
theorem isFree_of_le (M : DerivedFreeModel K U) {V : X.Opens} (hVU : V ≤ U) (i : ℤ) :
    Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj (M.model.X i) ≅
      SheafOfModules.free (R := (V.toScheme).ringCatSheaf) (ULift.{u} (Fin (M.rank i)))) :=
  Scheme.Modules.nonempty_restrictFunctor_iso_free_of_le hVU _ _ (M.isFree i)

end DerivedFreeModel

/-! ### Transporting an isomorphism over an open to a smaller open -/

namespace Scheme.Modules

/-- The composite of the restriction to `U` and the restriction to `V ≤ U` is the restriction to
`V`: `Scheme.Modules.restrictFunctorComp` along `AlgebraicGeometry.Scheme.homOfLE`, whose
composite with `U.ι` is `V.ι` by `AlgebraicGeometry.Scheme.homOfLE_ι`. -/
noncomputable def restrictFunctorLEIso {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    restrictFunctor U.ι ⋙ restrictFunctor (X.homOfLE hVU) ≅ restrictFunctor V.ι :=
  (restrictFunctorComp (X.homOfLE hVU) U.ι).symm ≪≫ restrictFunctorCongr (X.homOfLE_ι hVU)

/-- The same on cochain complexes: restricting a complex to `U` and then to `V ≤ U` is restricting
it to `V`. -/
noncomputable def restrictComplexLEIso {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U)
    (C : CochainComplex X.Modules ℤ) :
    ((restrictFunctor (X.homOfLE hVU)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (restrictComplex C U) ≅ restrictComplex C V :=
  (NatIso.mapHomologicalComplex (restrictFunctorLEIso hVU) (ComplexShape.up ℤ)).app C

/-- **An isomorphism in `D(𝒪_U)` restricts to one in `D(𝒪_V)` for `V ≤ U`.** Restriction from `U`
to `V` is exact, so it descends to the derived categories, and the composite of the two
restrictions is the restriction to `V`. -/
theorem isoOverOpen_of_le {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U)
    {C D : CochainComplex X.Modules ℤ} (h : IsoOverOpen U C D) : IsoOverOpen V C D := by
  let := HasDerivedCategory.standard (U.toScheme).Modules
  let := HasDerivedCategory.standard (V.toScheme).Modules
  obtain ⟨e⟩ := h
  have key : ∀ A : CochainComplex X.Modules ℤ,
      DerivedCategory.Q.obj (restrictComplex A V) ≅
        (restrictFunctor (X.homOfLE hVU)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj (restrictComplex A U)) := fun A =>
    DerivedCategory.Q.mapIso (restrictComplexLEIso hVU A).symm ≪≫
      ((restrictFunctor (X.homOfLE hVU)).mapDerivedCategoryFactors.app
        (restrictComplex A U)).symm
  exact ⟨key C ≪≫ (restrictFunctor (X.homOfLE hVU)).mapDerivedCategory.mapIso e ≪≫
    (key D).symm⟩

end Scheme.Modules

namespace DerivedFreeModel

variable {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ} {U : X.Opens}

/-- The `derivedIso` field of a finite free model over `U`, read on a smaller open `V ≤ U`: the
model still represents `K` over `V`. -/
theorem derivedIso_of_le (M : DerivedFreeModel K U) {V : X.Opens} (hVU : V ≤ U) :
    Scheme.Modules.IsoOverOpen V M.model K :=
  Scheme.Modules.isoOverOpen_of_le hVU M.derivedIso

end DerivedFreeModel

end AlgebraicGeometry
