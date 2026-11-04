module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidStack
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Descent.SubPseudofunctorStack

/-!
# Cutting the finite locally free objects out of the stack of Frobenius-colimit modules

`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidStack` carries the
descent properties of `AlgebraicGeometry.frobeniusColimitModulePseudofunctor` — the pseudofunctor
of *all* sheaves of `colim_F 𝒪_U`-modules — to its fibrewise maximal subgroupoid
`AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor`.  The pseudofunctor Stacks Tag 0EXE is
actually about is one step further: it is
`AlgebraicGeometry.frobeniusVectorBundleGroupoidPseudofunctor`, the full subcategory of the coring
cut out by finite local freeness.  This file supplies that step, which nothing in the development
did: the stack condition passes from the coring to the full subcategory as soon as finite local
freeness can be *detected* on the covering family.

## Main results

* `AlgebraicGeometry.isStackFor_frobeniusVectorBundleGroupoidPseudofunctor`: **the pseudofunctor in
  groupoids of finite locally free Frobenius-colimit modules is a stack for a family as soon as the
  pseudofunctor of all Frobenius-colimit modules is, provided finite local freeness is detected on
  that family.**

## Implementation notes

The step is `Stacks.Descent.isStackFor_fullsubcategory` applied to the object property
`AlgebraicGeometry.frobeniusColimitCoreFiniteLocallyFree`, whose
`CategoryTheory.Pseudofunctor.ObjectProperty.IsClosedUnderMapObj` instance is already available
where the property is defined.  Two things are supplied here.

The closure of the property under isomorphism.  The objects of a fibre of the coring are the
objects of the corresponding fibre of the pseudofunctor of all modules, and an isomorphism of
`CategoryTheory.Core` is an isomorphism of the underlying category, so this is finite local
freeness being an isomorphism-invariant of a sheaf of modules.  That invariance is
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso`, which is stated for the parallel class
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`; the two classes have the same single field, so the
crossing is `⟨·.exists_isFiniteLocallyFreeData⟩` in both directions.  The
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` spellings of `of_iso` in the development are
for `X.Modules` over a scheme and do not apply to the ring sheaf `colim_F 𝒪_U` on the site of
opens.

The detection hypothesis `hP`, phrased on the underlying sheaves of modules rather than on the
objects of the coring, because that is the form a geometric input has.  Its translation into the
form `Stacks.Descent.isStackFor_fullsubcategory` wants is definitional: the transition functor of
the coring is the core of the transition functor of all modules, and
`CategoryTheory.Functor.core` acts on objects as the functor does.

The index type of the family is left in its own universe `t`, as it is in
`Stacks.Descent.isStackFor_fullsubcategory`.  This is not cosmetic: the families the Zariski and
the h topology of the big h category over `S` are generated from are
`CategoryTheory.PreZeroHypercover.{u + 1}` families — see
`AlgebraicGeometry.BigHOver.zariskiPrecoverage` — so they are indexed by a type of `Type (u + 1)`,
and a statement whose index type is confined to `Type u` does not apply to a single one of them.

**Why the hypothesis is not discharged here.**  `hP` is a descent statement for finite local
freeness along the family, and for an arbitrary family of the big h site it is not available —
indeed for a family that is not flat it is not expected.  It is an input the criterion that
consumes this lemma has to supply per family, which is why it is left as a hypothesis of a general
statement rather than specialised; this is the same shape as the `hP` of
`Stacks.Descent.isStackFor_fullsubcategory` itself.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe t u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-- Finite local freeness is invariant under isomorphism of sheaves of `colim_F 𝒪_U`-modules, so
the object property `AlgebraicGeometry.frobeniusColimitCoreFiniteLocallyFree` is closed under
isomorphism in every fibre.

An isomorphism of `CategoryTheory.Core` is an isomorphism of the underlying category, and the
invariance of finite local freeness is `Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso`,
reached across the two parallel classes' common single field. -/
instance isClosedUnderIsomorphisms_frobeniusColimitCoreFiniteLocallyFree :
    (frobeniusColimitCoreFiniteLocallyFree B S hS p hpS).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms U :=
    { of_iso := fun {M N} e hM ↦ by
        have hM' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M.of :=
          ⟨hM.exists_isFiniteLocallyFreeData⟩
        have hN' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} N.of :=
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso
            ((Core.inclusion _).mapIso e) (h := hM')
        exact ⟨hN'.exists_isFiniteLocallyFreeData⟩ }

/-- **The pseudofunctor in groupoids of finite locally free Frobenius-colimit modules is a stack
for a family as soon as the pseudofunctor of all Frobenius-colimit modules is**, provided finite
local freeness is detected on that family: a sheaf of `colim_F 𝒪_U`-modules all of whose scalar
extensions along the members of the family are finite locally free is itself finite locally free.

This is the step from `AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor` to the
pseudofunctor `AlgebraicGeometry.frobeniusVectorBundleGroupoidPseudofunctor` that Stacks Tag 0EXE
is about: the coring is handled by
`AlgebraicGeometry.isStackFor_frobeniusColimitModuleCorePseudofunctor` and the full subcategory by
`Stacks.Descent.isStackFor_fullsubcategory`. -/
theorem isStackFor_frobeniusVectorBundleGroupoidPseudofunctor {ι : Type t}
    {U : BigHOver B S hS} {X : ι → BigHOver B S hS} (f : ∀ i, X i ⟶ U)
    (hP : ∀ M : _root_.SheafOfModules.{u} (bigHFrobeniusColimitRingSheaf B S hS p hpS U),
      (∀ i, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          ((bigHFrobeniusColimitPullback B S hS p hpS (f i).op).obj M)) →
        SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hR : (frobeniusColimitModulePseudofunctor B S hS p hpS).IsStackFor
      (Presieve.ofArrows X f)) :
    (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).IsStackFor
      (Presieve.ofArrows X f) :=
  Stacks.Descent.isStackFor_fullsubcategory
    (frobeniusColimitCoreFiniteLocallyFree B S hS p hpS) f
    (fun M hM ↦ hP M.of hM)
    (isStackFor_frobeniusColimitModuleCorePseudofunctor B S hS p hpS _ hR)

end AlgebraicGeometry

end
