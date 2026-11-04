module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Locality

/-!
# The projection formula at a finite locally free module on the target

For a morphism of ringed spaces `f : Z ⟶ X`,
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/Basic.lean` builds the canonical map

`Stacks.AffineProjectionFormula.projectionFormulaMap f 𝒢 ℋ : f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)`

and `ProjectionFormula/Locality.lean` proves it invertible, for a morphism of schemes and with no
hypothesis on `𝒢`, whenever `ℋ` is isomorphic on each member of an open covering of `X` to the
restriction of a finite biproduct of copies of `𝒪_X`.  This file states the same conclusion from
the hypothesis in the shape [Stacks, Tag 01C6] gives it — each point of `X` has a neighbourhood
`V` on which `ℋ|_V` is isomorphic to a **free** sheaf of modules `SheafOfModules.free I` on a
finite index type.  The `q = 0` clause of [Stacks, Tag 01E8] for an arbitrary morphism of ringed
spaces is `isIso_projectionFormulaMap_of_isFiniteLocallyFree_class_ringedSpace`.

## The argument

Two identifications turn the local free model into the finite biproduct that
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_biproduct_structureModule` handles.

* On one ringed space, `SheafOfModules.free I` for a finite `I` *is* a finite biproduct of copies
  of the structure sheaf: it is the coproduct of `I` copies of the unit, a finite coproduct is a
  biproduct (`CategoryTheory.Limits.biproduct.isoCoproduct`), and the index type is transported
  to `Fin (Nat.card I)` by `CategoryTheory.Limits.Sigma.whiskerEquiv`, which crosses universes.
  So the projection-formula map is invertible at `SheafOfModules.free I` for an arbitrary
  morphism of ringed spaces and a finite `I`.
* The free sheaf restricts to the free sheaf on the same index type.  This is
  `RingedSpaceModuleAdjunction.modulePullbackObjFreeIso`, the inverse image of a free module
  along an arbitrary morphism of ringed spaces, read at the restriction functor of a scheme via
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

With those, the locality argument of `Locality.lean` applies verbatim with the free sheaf
`SheafOfModules.free I` on `X` in the role its `freeStructureModule` played; the transport lemma
is restated here for an arbitrary comparison module, which is the only change its proof needs.

## Main definitions

* `Stacks.AffineProjectionFormula.freeIsoBiproductStructureModule`: a free sheaf of modules on a
  finite index type is a finite biproduct of copies of the structure sheaf.
* `Stacks.AffineProjectionFormula.openRestrictFreeIso`: the restriction of a free sheaf of
  modules to an open of a scheme is the free sheaf of modules on the same index type.

## Main results

* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_free`: the projection formula at a
  free module of finite rank on the target, for an arbitrary morphism of ringed spaces.
* `Stacks.AffineProjectionFormula.isIso_openRestrictHom_projectionFormulaMap_of_isIso`: the
  transport of `Locality.lean`, with the comparison module arbitrary rather than a finite
  biproduct of copies of `𝒪_X`.
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree`: the
  projection formula at a finite locally free module, for a morphism of schemes.

## Implementation notes

*The hypothesis is `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`, written out.*  That
definition — for every point an open neighbourhood `V`, a finite `I : Type u` and an isomorphism
`ℋ|_V ≅ SheafOfModules.free I` — is the one this file's hypothesis spells, in the same order and
with the same `SheafOfModules.free`.  It is not referred to by name because the file it lives in,
`StacksFrontier/RingTheory/Module/LocallyFree/SheafBridge.lean`, carries a long list of unrelated
Mathlib imports (analysis, number theory) that have no business under `ProjectionFormula/`.

*The tag's conclusion is read with the two tensor factors exchanged.*  [Stacks, Tag 01E8] asserts
`ℰ ⊗_{𝒪_Y} R^q f_*ℱ ≅ R^q f_*(f^*ℰ ⊗_{𝒪_X} ℱ)`, while `projectionFormulaMap f 𝒢 ℋ` goes
`f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)`; the two differ by the symmetry of the tensor product on
each side, which is an isomorphism of the source with the source and of the target with the
target.

*`IsIso` is supplied in argument position, never as an instance binder*, as in the three files
this one builds on: `projectionFormulaMap` is a semireducible definition, so
`IsIso (projectionFormulaMap …)` never matches `IsIso (?f ≫ ?g)` during instance search.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01E7](https://stacks.math.columbia.edu/tag/01E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry

namespace Stacks.AffineProjectionFormula

universe u

/-! ### A finite free module is a finite biproduct of copies of the structure sheaf -/

/-- **A free sheaf of modules on a finite index type is a finite biproduct of copies of the
structure sheaf.**  The free sheaf is the coproduct of `I` copies of the unit; reindexing it
along `I ≃ Fin (Nat.card I)` brings the index type down to `Type`, where the coproduct is a
biproduct. -/
def freeIsoBiproductStructureModule (W : AlgebraicGeometry.RingedSpace.{u, u}) (I : Type u)
    [Finite I] :
    SheafOfModules.free.{u} (R := structureRingSheaf W) I ≅
      freeStructureModule W (Fin (Nat.card I)) :=
  (Sigma.whiskerEquiv (Finite.equivFin I) (fun _ => Iso.refl (structureModule W)) :
      (∐ fun _ : I => structureModule W) ≅
        ∐ fun _ : Fin (Nat.card I) => structureModule W) ≪≫
    (biproduct.isoCoproduct fun _ : Fin (Nat.card I) => structureModule W).symm

/-- **The projection formula at a free module of finite rank on the target**, for an arbitrary
morphism of ringed spaces and with no hypothesis on `𝒢`. -/
theorem isIso_projectionFormulaMap_free {X Z : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X)
    (G : SheafOfModules.{u} (structureRingSheaf Z)) (I : Type u) [Finite I] :
    IsIso (projectionFormulaMap f G (SheafOfModules.free.{u} (R := structureRingSheaf X) I)) :=
  isIso_projectionFormulaMap_of_iso f G (freeIsoBiproductStructureModule X I).symm
    (isIso_projectionFormulaMap_biproduct_structureModule f G (Fin (Nat.card I)))

/-! ### The restriction of a free module to an open -/

/-- **The restriction of a free sheaf of modules to an open of a scheme is the free sheaf of
modules on the same index type.**  Restriction is the inverse image
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), and the inverse image of a free
module along an arbitrary morphism of ringed spaces is free
(`RingedSpaceModuleAdjunction.modulePullbackObjFreeIso`). -/
def openRestrictFreeIso {X : Scheme.{u}} (V : X.Opens) (I : Type u) :
    openRestrictModule V
        (SheafOfModules.free.{u} (R := structureRingSheaf X.toRingedSpace) I) ≅
      SheafOfModules.free.{u}
        (R := structureRingSheaf (V : Scheme.{u}).toRingedSpace) I :=
  (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
      (show X.Modules from SheafOfModules.free.{u} I) ≪≫
    modulePullbackObjFreeIso V.ι.toLRSHom.toShHom I

/-! ### The projection formula at a finite locally free module -/

section Locality

variable {Z X : Scheme.{u}} (f : Z ⟶ X)
  (G : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace))
  (H : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))

/-- **The restriction of the projection-formula map to an open on which the module on the target
agrees with one at which the map is already invertible is invertible.**  This is
`Stacks.AffineProjectionFormula.isIso_openRestrictHom_projectionFormulaMap` with the comparison
module arbitrary: the three transports along
`Stacks.AffineProjectionFormula.isIso_pullback_projectionFormulaMap_congr` never used that it was
a finite biproduct of copies of `𝒪_X`, only that the projection-formula map was invertible
there. -/
theorem isIso_openRestrictHom_projectionFormulaMap_of_isIso (V : X.Opens)
    (E : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (hE : IsIso (projectionFormulaMap f.toLRSHom.toShHom G E))
    (e : openRestrictModule V E ≅ openRestrictModule V H) :
    IsIso (openRestrictHom V (projectionFormulaMap f.toLRSHom.toShHom G H)) := by
  refine (isIso_openRestrictHom_iff V _).mpr ?_
  have c0 : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      (projectionFormulaMap f.toLRSHom.toShHom G E)) :=
    ((pullbackFunctor V.ι.toLRSHom.toShHom).mapIso
      (@asIso _ _ _ _ (projectionFormulaMap f.toLRSHom.toShHom G E) hE)).isIso_hom
  have c1 := (isIso_pullback_projectionFormulaMap_congr f V G (openRestrictUnit V E)
    (isIso_pullback_openRestrictUnit V E)).mp c0
  have hk2 := ((pullbackFunctor V.ι.toLRSHom.toShHom).mapIso
    ((Scheme.Modules.pushforward V.ι).mapIso e)).isIso_hom
  have c2 := (isIso_pullback_projectionFormulaMap_congr f V G _ hk2).mp c1
  exact (isIso_pullback_projectionFormulaMap_congr f V G (openRestrictUnit V H)
    (isIso_pullback_openRestrictUnit V H)).mpr c2

/-- **The projection formula for a morphism of schemes at a module on the target which is free of
finite rank on each member of an open covering**, in the free-sheaf spelling: the canonical map
`f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` is an isomorphism, with no hypothesis on `𝒢` and none on
`f`. -/
theorem isIso_projectionFormulaMap_of_restrict_free
    (I : X.carrier → Type u) [∀ x, Finite (I x)]
    (V : X.carrier → X.Opens) (hx : ∀ x, x ∈ V x)
    (e : ∀ x, openRestrictModule (V x) H ≅ SheafOfModules.free.{u} (I x)) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom G H) := by
  refine AffineBaseChange.isIso_of_isIso_restrict
    (show (show X.Modules from _) ⟶ (show X.Modules from _) from
      projectionFormulaMap f.toLRSHom.toShHom G H) V (IsOpenCover.mk ?_) fun x =>
    isIso_openRestrictHom_projectionFormulaMap_of_isIso f G H (V x)
      (SheafOfModules.free.{u} (I x))
      (isIso_projectionFormulaMap_free f.toLRSHom.toShHom G (I x))
      (openRestrictFreeIso (V x) (I x) ≪≫ (e x).symm)
  refine le_antisymm le_top ?_
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- **The projection formula for a morphism of schemes at a finite locally free module on the
target**: for `𝒢` an arbitrary `𝒪_Z`-module and `ℋ` an `𝒪_X`-module such that every point of `X`
has a neighbourhood on which `ℋ` is free of finite rank, the canonical map
`f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` is an isomorphism.

The condition on `ℋ` is `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree ℋ` written out,
which is the finite local freeness of [Stacks, Tag 01C6]. -/
theorem isIso_projectionFormulaMap_of_isFiniteLocallyFree
    (hH : ∀ x : X.carrier, ∃ (V : X.Opens) (_ : x ∈ V) (I : Type u) (_ : Finite I),
      Nonempty (openRestrictModule V H ≅ SheafOfModules.free.{u} I)) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom G H) := by
  choose V hV I hI e using hH
  exact isIso_projectionFormulaMap_of_restrict_free f G H I V hV fun x => (e x).some

end Locality

end Stacks.AffineProjectionFormula

end
