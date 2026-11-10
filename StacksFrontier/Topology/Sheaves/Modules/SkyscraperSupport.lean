module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.Topology.Sheaves.Modules.Skyscraper
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of a skyscraper sheaf of modules

Let `(X, 𝒪)` be a ringed space, `x` a point of `X` and `M` a module over the stalk `𝒪_x`.  The
skyscraper sheaf `AlgebraicGeometry.SheafOfModules.skyscraperObj 𝒪 x M` has no sections over an
open set missing `x`, so its stalk vanishes at every point `y` admitting an open neighbourhood
missing `x` — that is, at every `y` outside the closure of `{x}`.  Consequently the complex with
the skyscraper in degree zero has its cohomology supported on `closure {x}`, in the sense of
`AlgebraicGeometry.CohomologySupportedOn` ([Stacks, Tag 08DA]).

For a closed point `x` the closure is `{x}` itself, which is the form in which Case I of
[Stacks, Tag 0G0R] uses this: the source takes `z` to be a closed point of the fibre and needs
the skyscraper at `z` to have support disjoint from the diagonal.

## Main results

* `AlgebraicGeometry.SheafOfModules.isZero_stalk_skyscraperObj_of_notMem_closure`: the stalk of
  the skyscraper at `x` vanishes at every point outside `closure {x}`.
* `AlgebraicGeometry.SheafOfModules.cohomologySupportedOn_singleFunctor_skyscraperObj`: hence the
  skyscraper, placed in degree zero, has its cohomology supported on `closure {x}`.

## Implementation notes

*The stalk.*  A point `y` outside `closure {x}` has an open neighbourhood `V` with `x ∉ V`, and
`Mathlib`'s `TopCat.Presheaf.exists_le_germ_eq` writes any element of the stalk at `y` as the germ
of a section over an open `U ≤ V`.  Over such a `U` the skyscraper has only the zero section,
because `AlgebraicGeometry.SheafOfModules.isZero_skyscraperEval` says evaluation of the skyscraper
at an open set missing `x` is the zero functor; so the germ is zero.

*The cohomology.*  In degree zero the cohomology sheaf of the complex is the skyscraper itself,
by `CategoryTheory.DerivedCategory.singleFunctorCompHomologyFunctorIso`; in the other degrees the
cohomology sheaf vanishes outright, by
`HomologicalComplex.isZero_single_obj_homology`.  Support is measured on the underlying presheaf
of abelian groups, which `ExtensionByZeroModules.toAb` produces, so the second case needs that
forgetful functor to preserve zero morphisms — it is a composite of two functors that do.  This is
the same argument as
`AlgebraicGeometry.cohomologySupportedOn_singleFunctor_pushforward_unit` in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.ClosedImmersionStructureSheaf`, with the
skyscraper in place of the direct image of the structure sheaf.

No `stacks` attribute is carried: [Stacks, Tag 08DA] is the *definition* of cohomological support,
already registered on `AlgebraicGeometry.CohomologySupportedOn`, and the statements here are not
clauses of a tagged result.

## References

* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

attribute [local instance] skyscraperModule

/-- A point outside the closure of `{x}` has an open neighbourhood missing `x`. -/
theorem exists_opens_mem_notMem_of_notMem_closure (y : X)
    (hy : y ∉ closure ({x} : Set X)) :
    ∃ V : Opens X, y ∈ V ∧ x ∉ V := by
  rw [mem_closure_iff] at hy
  push Not at hy
  obtain ⟨o, ho, hyo, hno⟩ := hy
  rw [Set.eq_empty_iff_forall_notMem] at hno
  exact ⟨⟨o, ho⟩, hyo, fun hx => hno x ⟨hx, rfl⟩⟩

/-- **A skyscraper has no sections over an open set missing its point.**  This is
`AlgebraicGeometry.SheafOfModules.isZero_skyscraperEval` read at one value. -/
theorem subsingleton_skyscraperObj_sections
    (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
    (V : (Opens X)ᵒᵖ) (hxV : x ∉ V.unop) :
    Subsingleton (ToType ((skyscraperObj O x M).val.presheaf.obj V)) := by
  have h := (isZero_skyscraperEval O x V hxV).obj M
  rwa [ModuleCat.isZero_iff_subsingleton] at h

/-- **The stalk of a skyscraper vanishes outside the closure of its point.**  A point `y` outside
`closure {x}` has an open neighbourhood missing `x`; every element of the stalk at `y` is the germ
of a section over an open subset of that neighbourhood, and the skyscraper has only the zero
section there. -/
@[ega "IV 21.9.1" "partial"]
theorem isZero_stalk_skyscraperObj_of_notMem_closure
    (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
    (y : X) (hy : y ∉ closure ({x} : Set X)) :
    IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
      (skyscraperObj O x M).val.presheaf y) := by
  obtain ⟨V, hyV, hxV⟩ := exists_opens_mem_notMem_of_notMem_closure x y hy
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun a => ?_
  obtain ⟨U, hUV, hyU, s, hs⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (skyscraperObj O x M).val.presheaf a hyV
  have hzero : s = 0 :=
    (subsingleton_skyscraperObj_sections O x M (op U) fun hx => hxV (hUV hx)).elim s 0
  rw [← hs, hzero]
  exact map_zero _

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **A skyscraper in degree zero has its cohomology supported on the closure of its point.**
In degree zero the cohomology sheaf is the skyscraper, whose stalk vanishes off `closure {x}`; in
every other degree the cohomology sheaf vanishes.

For a closed point `x` this reads `CohomologySupportedOn 𝒪 {x}`, which is the form Case I of
[Stacks, Tag 0G0R] uses. -/
theorem cohomologySupportedOn_singleFunctor_skyscraperObj
    (M : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)) :
    AlgebraicGeometry.CohomologySupportedOn O (closure ({x} : Set X))
      ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} O) 0).obj
        (skyscraperObj O x M)) := by
  intro n y hy
  rcases eq_or_ne n 0 with rfl | hn
  · refine (isZero_stalk_skyscraperObj_of_notMem_closure O x M y hy).of_iso ?_
    exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((ExtensionByZeroModules.toAb O).mapIso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _))
  · let _ : HasZeroMorphisms (TopCat.Presheaf AddCommGrpCat.{u} X) :=
      inferInstanceAs (HasZeroMorphisms ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    have hpres : (ExtensionByZeroModules.toAb O).PreservesZeroMorphisms := by
      change (_root_.SheafOfModules.forget O ⋙
        PresheafOfModules.toPresheaf O.obj).PreservesZeroMorphisms
      infer_instance
    let _ := hpres
    refine Functor.map_isZero _ (Functor.map_isZero (ExtensionByZeroModules.toAb O) ?_)
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ n).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _))
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors _ n).app _)
    exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn

end Derived

end AlgebraicGeometry.SheafOfModules

end
