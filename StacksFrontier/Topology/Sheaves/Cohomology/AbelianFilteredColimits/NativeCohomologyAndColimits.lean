module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen

/-!
# Native cohomology of abelian sheaves and filtered colimits over a quasi-compact open

Stacks 01FF says that cohomology over a quasi-compact open commutes with filtered colimits. This
file runs its induction directly for abelian sheaves on the site of opens and Mathlib's native
cohomology `Sheaf.H'`, rather than for sheaves of modules and the cohomology functor
`(secF R U).rightDerived q` of
`Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact`. The induction has three
inputs:

* the `δ`-functor structure: the corepresentation of sections,
  `ModuleSheafCohomology.evaluationRepresentation`, is stated for `Sheaf J AddCommGrpCat`, so
  `ModuleSheafCohomology.selfDerivedDeltaFunctor` transports the `δ`-functor structure of `Ext`
  onto `fun n => ((sheafSections _ _).obj (op U)).rightDerived n` directly;
* the degree-zero input, Stacks 009F for abelian sheaves,
  `Stacks.Cohomology.Sections.preservesColimitsOfShape_sheafSections_of_isCompact`;
* the vanishing input `Hⁿ⁺¹(U, colimᵢ Iᵢ) = 0` for a filtered system of injective abelian
  sheaves, which is taken as a hypothesis here.

## Main definitions

* `abSections` is sections over `U` of an abelian sheaf, as a functor on abelian sheaves.
* `H'functor` is `Sheaf.H' · q U` read as a functor in the sheaf variable; it is *definitionally*
  `Abelian.extFunctorObj (freeOfOpen U) q`.
* `cohomologyDeltaFunctor` is the `δ`-functor on abelian sheaves whose degree-`n` component is
  literally `(abSections U).rightDerived n`.

## Main results

* `nonempty_H'functor_iso_rightDerived`: the functor-level form of
  `Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections`, which is what lets the
  statement be moved between the `Sheaf.H'` and the right-derived spellings.
* `isIso_colimit_post_rightDerived_of_isZero` and `isIso_colimit_post_H'functor_of_isCompact`:
  Stacks 01FF for abelian sheaves, modulo the vanishing input, in the right-derived and in
  the `Sheaf.H'` spelling respectively.

## Implementation notes

The universes are all equal, as in the module spelling.

`preservesColimitsOfShape_sheafSections_of_isCompact` is a `theorem` and not an instance, since
`hBasis`, `hInter` and `hU` cannot be inferred; `isIso_colimit_post_rightDerived_of_isZero`
accordingly takes `PreservesColimitsOfShape I (abSections U)` as an instance binder and
`isIso_colimit_post_H'functor_of_isCompact` discharges it with a `have`.

`abSections U` is spelled through `sheafSections (Opens.grothendieckTopology X) AddCommGrpCat`
rather than as `Stacks.Cohomology.SpectralLimit.sections X U`, and the ambient space as a
`Type u` with a topology rather than as a `TopCat`.  Both are forced by instance resolution:
`TopCat.Sheaf` is a semireducible `def` over `Sheaf (Opens.grothendieckTopology X)`, so the
`IsGrothendieckAbelian`, `HasExt` and `HasExactColimitsOfShape` instances that
`CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero` and
`ModuleSheafCohomology.selfDerivedDeltaFunctor` require are not found at the `X.Sheaf` spelling,
and the degree-zero input is stated for a plain topological space.  A consumer holding
`X : TopCat` applies these to `(X : Type u)`.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Abelian
open ModuleSheafCohomology
open Stacks.Cohomology.Sections

universe u

namespace Stacks.Cohomology.AbelianColimit

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-! ### Sections, the free abelian sheaf on an open, and native cohomology as a functor -/

/-- Sections over `U` of an abelian sheaf on the site of opens of `X`, as a functor on abelian
sheaves.  This is `Stacks.Cohomology.SpectralLimit.sections X U` at the spelling of the site
rather than of a `TopCat`. -/
abbrev abSections (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)

/-- The free abelian sheaf on `yoneda.obj U`: the sheafification of the free abelian presheaf on
the presheaf of sets `yoneda.obj U`.  This is the object Mathlib's native cohomology over `U`
takes `Ext` out of, and the object corepresenting sections over `U`. -/
abbrev freeOfOpen (U : Opens X) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- Mathlib's native cohomology `Sheaf.H' · q U` read as a functor in the sheaf variable: the
cohomology presheaf functor followed by evaluation at `U`.  By construction of
`Sheaf.cohomologyPresheafFunctor` this is definitionally the `Ext`-functor out of
`freeOfOpen U`, which is what `H'functor_eq_extFunctorObj` records. -/
abbrev H'functor (U : Opens X) (q : ℕ) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) q ⋙
    (evaluation ((Opens X)ᵒᵖ) AddCommGrpCat.{u}).obj (op U)

/-- The value of `H'functor` is native sheaf cohomology. -/
theorem H'functor_obj (U : Opens X) (q : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (H'functor U q).obj F = Sheaf.H'.{u, u, u} F q U :=
  rfl

/-- **Native cohomology over `U` is the `Ext`-functor out of the free abelian sheaf on
`yoneda.obj U`**, by definitional unfolding of `Sheaf.cohomologyPresheafFunctor`.  This is the
step that makes the comparison with right-derived sections available at the level of functors
rather than only object by object. -/
theorem H'functor_eq_extFunctorObj (U : Opens X) (q : ℕ) :
    H'functor U q = extFunctorObj (freeOfOpen U) q :=
  rfl

/-- Sections over an open subset are left exact: the functor is evaluation of the underlying
presheaf, so this is left exactness of the inclusion of sheaves into presheaves followed by left
exactness of evaluation in a functor category. -/
instance preservesFiniteLimits_abSections (U : Opens X) :
    PreservesFiniteLimits (abSections U) :=
  inferInstanceAs <| PreservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation ((Opens X)ᵒᵖ) AddCommGrpCat.{u}).obj (op U))

/-- **Native sheaf cohomology is right-derived sections, as functors.**  Sections over `U` of an
abelian sheaf are corepresented by `freeOfOpen U`, so the general comparison
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived` applies.  This is the
functor-level form of `Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections`; as
there, only existence of the comparison is asserted. -/
theorem nonempty_H'functor_iso_rightDerived (U : Opens X) (q : ℕ) :
    Nonempty (H'functor U q ≅ (abSections U).rightDerived q) :=
  nonempty_extFunctorObj_iso_rightDerived (abSections U) _
    (evaluationRepresentation (Opens.grothendieckTopology X) U) q

/-! ### The long exact sequence -/

/-- **The long exact cohomology sequence over an open, for abelian sheaves.**  The `δ`-functor on
abelian sheaves whose degree-`n` component is `(abSections U).rightDerived n`, obtained by
transporting the `δ`-functor structure of `Ext` along the corepresentation
`ModuleSheafCohomology.evaluationRepresentation` of sections over `U`.

This is the abelian analogue of `Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor`. -/
def cohomologyDeltaFunctor (U : Opens X) :
    DeltaFunctor (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) AddCommGrpCat.{u} :=
  selfDerivedDeltaFunctor (abSections U) _
    (evaluationRepresentation (Opens.grothendieckTopology X) U)

/-- The components of `cohomologyDeltaFunctor` are the right-derived functors of sections. -/
theorem cohomologyDeltaFunctor_functor (U : Opens X) (n : ℕ) :
    (cohomologyDeltaFunctor U).functor n = (abSections U).rightDerived n :=
  rfl

/-- **`cohomologyDeltaFunctor` is universal** (Stacks 010S): `Ext` out of any object vanishes in
positive degree against an injective object. -/
instance cohomologyDeltaFunctor_isUniversal (U : Opens X) :
    (cohomologyDeltaFunctor U).IsUniversal :=
  selfDerivedDeltaFunctor_isUniversal _ _ _

/-! ### Stacks 01FF for abelian sheaves, modulo the vanishing input -/

/-- **Cohomology over `U` commutes with filtered colimits, given the vanishing input.** Let `U`
be an open of `X` over which sections of abelian sheaves preserve `I`-colimits — Stacks 009F,
available when `U` is quasi-compact and `X` has a basis of quasi-compact opens closed under
binary intersection — and assume `Hⁿ⁺¹(U, colimᵢ Eᵢ) = 0` for every filtered system `E` of
injective abelian sheaves. Then `colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` is an isomorphism in every
degree.

This is Stacks 01FF for abelian sheaves, modulo its vanishing input. -/
theorem isIso_colimit_post_rightDerived_of_isZero
    {I : Type u} [SmallCategory I] [IsFiltered I] (U : Opens X)
    [PreservesColimitsOfShape I (abSections U)]
    (hvan : ∀ E : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      (∀ i, Injective (E.obj i)) → ∀ n : ℕ,
      IsZero (((abSections U).rightDerived (n + 1)).obj (colimit E)))
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (colimit.post F ((abSections U).rightDerived q)) :=
  DeltaFunctor.isIso_colimit_post_of_isIso_zero (cohomologyDeltaFunctor U)
    (fun G =>
      have : PreservesColimit G (abSections U) := PreservesColimitsOfShape.preservesColimit
      isIso_colimit_post_of_natIso G (abSections U).rightDerivedZeroIsoSelf)
    (fun Y hY n => have := hY; (abSections U).isZero_rightDerived_obj_injective_succ n Y)
    hvan q F

/-- **Native cohomology over a quasi-compact open commutes with filtered colimits, given the
vanishing input.** Let `X` have a basis of quasi-compact opens whose binary intersections are
quasi-compact, let `U` be a quasi-compact open, and assume `Sheaf.H' (colimᵢ Eᵢ) (n + 1) U = 0`
for every filtered system `E` of injective abelian sheaves. Then for every filtered system `F`
of abelian sheaves and every degree `q` the canonical map
`colimᵢ Sheaf.H' Fᵢ q U ⟶ Sheaf.H' (colimᵢ Fᵢ) q U` is an isomorphism.

This is Stacks 01FF for abelian sheaves in the `Sheaf.H'` spelling, modulo its vanishing input;
Stacks 009F for abelian sheaves supplies the degree-zero input. -/
theorem isIso_colimit_post_H'functor_of_isCompact
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X))
    (hvan : ∀ E : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      (∀ i, Injective (E.obj i)) → ∀ n : ℕ,
      IsZero (Sheaf.H'.{u, u, u} (colimit E) (n + 1) U))
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (colimit.post F (H'functor U q)) :=
  have : PreservesColimitsOfShape I (abSections U) :=
    preservesColimitsOfShape_sheafSections_of_isCompact hBasis hInter U hU
  have hvan' : ∀ E : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      (∀ i, Injective (E.obj i)) → ∀ n : ℕ,
      IsZero (((abSections U).rightDerived (n + 1)).obj (colimit E)) :=
    fun E hE n => (hvan E hE n).of_iso
      (((nonempty_H'functor_iso_rightDerived U (n + 1)).some.app (colimit E)).symm)
  have : IsIso (colimit.post F ((abSections U).rightDerived q)) :=
    isIso_colimit_post_rightDerived_of_isZero U hvan' F q
  isIso_colimit_post_of_natIso F (nonempty_H'functor_iso_rightDerived U q).some

end Stacks.Cohomology.AbelianColimit

end
