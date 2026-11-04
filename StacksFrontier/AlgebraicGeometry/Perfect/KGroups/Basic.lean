module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory

/-!
# Perfect complexes supported on a closed subscheme

For a closed subscheme `Z` of a scheme `X`, the supported perfect derived category is the
strictly full subcategory of perfect derived objects whose cohomology sheaves are supported
on the underlying closed subset of `Z`.

## Main definitions

* `AlgebraicGeometry.supportedPerfectDerivedCategory` is this full subcategory of the derived
  category of sheaves of modules on `X`.

## Main results

* `AlgebraicGeometry.isClosedUnderIsomorphisms_supportedPerfect`: the supported perfect objects
  form a strictly full subcategory.
* `AlgebraicGeometry.isTriangulated_supportedPerfect`: they form a triangulated subcategory, so
  that the `K`-group of `D_{Z, perf}(O_X)` is available for every closed subscheme.

## Implementation notes

The closed subscheme is represented by a closed immersion, and its underlying closed subset
is the range of the map on points. Support uses the stalkwise support of categorical sheaves
of modules. The abbreviation keeps the ambient full subcategory API available to later
constructions.

The three conditions of `CategoryTheory.ObjectProperty.IsTriangulated` are each the conjunction
of a statement about perfectness and a statement about supports. The perfectness halves are
those of `Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect`. For the
support halves: the cohomology sheaves of a zero object are zero, hence have empty support; the
`n`-th cohomology sheaf of `K⟦m⟧` is the `(m + n)`-th cohomology sheaf of `K`, by the shift
sequence of the homology functor, so the support condition merely shifts degree; and a
distinguished triangle gives an exact sequence `H^n(E₁) → H^n(E₂) → H^n(E₃)` of cohomology
sheaves, whence `supp H^n(E₂) ⊆ supp H^n(E₁) ∪ supp H^n(E₃)`.

## References

* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
-/

@[expose] public section

open CategoryTheory StrictlyPerfect

universe u d

namespace AlgebraicGeometry

/-- The strictly full subcategory of perfect derived objects whose every cohomology sheaf
is set-theoretically supported on a closed subscheme. -/
@[stacks 0FDN "supported_perfect_definition"]
public abbrev supportedPerfectDerivedCategory {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [HasDerivedCategory.{d} (OXMod.{u} X.toRingedSpace)] :=
  ObjectProperty.FullSubcategory (fun K : DerivedCategory (OXMod.{u} X.toRingedSpace) =>
    RingedSpace.IsPerfect K ∧
      ∀ n : ℤ, SheafOfModules.supp
        ((DerivedCategory.homologyFunctor (OXMod.{u} X.toRingedSpace) n).obj K) ⊆
          Set.range i.base)

end AlgebraicGeometry

open CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- **Supported perfect objects form a strictly full subcategory.** Perfectness only depends on
the isomorphism class, and an isomorphism of derived objects induces an isomorphism of each
cohomology sheaf, which has no effect on its support. -/
@[stacks 0FDN "strict fullness of the supported perfect subcategory"]
instance isClosedUnderIsomorphisms_supportedPerfect {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (show ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) from
        fun K => RingedSpace.IsPerfect K ∧
          ∀ n : ℤ, SheafOfModules.supp
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) ⊆
              Set.range i.base) where
  of_iso e hK :=
    ⟨Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.of_iso e hK.1,
      fun n => (SheafOfModules.supp_eq_of_iso ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} X.toRingedSpace) n).mapIso e)).symm.subset.trans (hK.2 n)⟩

/-- **Perfect complexes supported on a closed subscheme form a triangulated subcategory** of the
derived category of `O_X`-modules: the subcategory `D_{Z, perf}(O_X)` contains a zero object, is
stable under all shifts, and the middle object of a distinguished triangle whose other two
objects are perfect and supported on `Z` is again perfect and supported on `Z`.

Saturation, the remaining adjective of the source, is
`AlgebraicGeometry.isSaturated_supportedPerfect`; its perfect half is Tag 08CS. -/
@[stacks 0FDN "triangulatedness of the supported perfect subcategory",
  sga "6 I 5.8.4" "5.8.4 a), special case"]
instance isTriangulated_supportedPerfect {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)] :
    ObjectProperty.IsTriangulated
      (show ObjectProperty (DerivedCategory (OXMod.{u, u} X.toRingedSpace)) from
        fun K => RingedSpace.IsPerfect K ∧
          ∀ n : ℤ, SheafOfModules.supp
            ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) ⊆
              Set.range i.base) where
  toContainsZero := ⟨⟨0, isZero_zero _,
    Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_zero, fun n =>
      (SheafOfModules.supp_eq_empty_of_isZero
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).map_isZero
          (isZero_zero _))).subset.trans (Set.empty_subset _)⟩⟩
  toIsStableUnderShift := ⟨fun m => ⟨fun K hK =>
    ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hK.1 m, fun n =>
      (SheafOfModules.supp_eq_of_iso (show (DerivedCategory.homologyFunctor
          (OXMod.{u, u} X.toRingedSpace) n).obj (K⟦m⟧) ≅
            (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) (m + n)).obj K from
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).shiftIso m n (m + n)
            rfl).app K)).subset.trans (hK.2 (m + n))⟩⟩⟩
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ =>
      ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished T hT h₁.1 h₃.1,
        fun n => (SheafOfModules.supp_subset_union_of_exact _
          (DerivedCategory.HomologySequence.exact₂ T hT n)).trans
            (Set.union_subset (h₁.2 n) (h₃.2 n))⟩)

end AlgebraicGeometry
