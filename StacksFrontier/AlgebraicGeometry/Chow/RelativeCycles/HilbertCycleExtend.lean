module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertCycleClass
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic

/-!
# Extending a member of `Hilb` along a closed immersion over an open immersion of the base

Let `q : Y ⟶ T` and `f : X ⟶ S` be morphisms fitting into a commutative square
`j ≫ f = q ≫ i` in which `j : Y ⟶ X` is a closed immersion and `i : T ⟶ S` is a quasi-compact
open immersion. A closed subscheme of `Y` flat and of finite presentation over `T`, of relative
dimension at most `r` — that is, a member of `Hilb(Y/T, r)` in the sense of
[Tag 0H6V](https://stacks.math.columbia.edu/tag/0H6V) — pushes forward along `j` to a closed
subscheme of `X`, and that closed subscheme is a member of `Hilb(X/S, r)`.

This is used in the coproduct step of [Tag 0H59](https://stacks.math.columbia.edu/tag/0H59), for
a coproduct injection `T₁ ⟶ T₁ ⨿ T₂`, which is both a closed and an open immersion.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.mapSubschemeIso` — pushing an ideal sheaf forward along
  a closed immersion does not change the closed subscheme it cuts out: the canonical morphism
  `I.subscheme ⟶ (I.map j).subscheme` is an isomorphism.
* `Stacks.Chow.HilbertCycleDatum.extend` — **the extension**: a member of `Hilb(Y/T, r)` read as a
  member of `Hilb(X/S, r)` through the square above.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.mapSubschemeIso_hom_subschemeι` — the comparison
  isomorphism is compatible with the two closed immersions into `X`.
* `Stacks.Chow.HilbertCycleDatum.extend_ideal` — the ideal sheaf of the extension is the
  pushforward of the original one.
* `Stacks.Chow.HilbertCycleDatum.map_subschemeι_comp` — the factorisation of the structure
  morphism of the pushforward through the comparison isomorphism.
* `Stacks.Chow.HilbertCycleDatum.isPullback_map_subschemeι` — the closed subscheme of the
  extension is the base change along `i` of the closed subscheme of the original datum.

## Implementation notes

The three morphism-property fields of `Stacks.Chow.HilbertCycleDatum` — flatness, local finite
presentation and quasi-compactness of the structure morphism — are obtained by rewriting
`(I.map j).subschemeι ≫ f` as `e.inv ≫ (I.subschemeι ≫ q) ≫ i` along
`AlgebraicGeometry.Scheme.IdealSheafData.mapSubschemeIso`, where the three factors have the
property for, respectively, trivial, hypothesised and open-immersion reasons. `i` is required to
be quasi-compact because an open immersion need not be; in the application `i` is a coproduct
injection, which is also a closed immersion and therefore quasi-compact.

The relative dimension field of `Stacks.Chow.HilbertCycleDatum` carries a `letI` supplying the
`LocallyOfFiniteType` instance from the two preceding fields. To avoid having to reproduce that
`letI` chain, the bound is proved as
`Stacks.Chow.HilbertCycleDatum.topologicalKrullDimAt_map_subschemeι_comp_le`, which is stated as
the bare local Krull dimension inequality with no instance argument at all, and
`Stacks.Chow.HilbertCycleDatum.extend` is then built in term mode so that
`Stacks.Chow.HilbertCycleDatum.extend_ideal` holds by `rfl`.

Instance search for `IsIso f.toImage` of a closed immersion `f` does not terminate in the
presence of this file's imports, although the instance exists in Mathlib and is found in a file
importing less; `AlgebraicGeometry.Scheme.IdealSheafData.mapSubschemeIso` therefore passes
`AlgebraicGeometry.IsClosedImmersion.instIsIsoSchemeToImage` explicitly.

The relative dimension bound is transported along
`AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback`, for which the square has to be
recognised as a pullback. It is one because its top edge is an isomorphism and its bottom edge a
monomorphism, which is `CategoryTheory.IsPullback.of_horiz_isIso_mono`.

## Scope

This file supplies the extension of a *datum*. The behaviour of the resulting *cycle* under
restriction is `Stacks.Chow.HilbertCycleDatum.restrictedFamily_cycleFamily_extend` and
`Stacks.Chow.HilbertCycleDatum.restrictedFamily_cycleFamily_eq_zero_of_disjoint`, in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleClassFacet`; the coproduct clause of
Tag 0H59 assembled from them is `Stacks.Chow.pullbackInCycleClassImage_coprod_desc`.

## References

* [Stacks Project, Section 0H6V](https://stacks.math.columbia.edu/tag/0H6V)
* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Definition 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (I : Y.IdealSheafData) (j : Y ⟶ X) [IsClosedImmersion j]

/-- **Pushing an ideal sheaf forward along a closed immersion does not change the closed
subscheme it cuts out.** The isomorphism from `I.subscheme` onto the scheme-theoretic image of
`I.subscheme ⟶ Y ⟶ X`, which is the closed subscheme cut out by `I.map j`. -/
def mapSubschemeIso : I.subscheme ≅ (I.map j).subscheme :=
  @asIso Scheme.{u} _ _ _ (I.subschemeι ≫ j).toImage
    (IsClosedImmersion.instIsIsoSchemeToImage (I.subschemeι ≫ j))

/-- The comparison isomorphism of
`AlgebraicGeometry.Scheme.IdealSheafData.mapSubschemeIso` is compatible with the two closed
immersions into the ambient scheme. -/
@[reassoc]
theorem mapSubschemeIso_hom_subschemeι :
    (mapSubschemeIso I j).hom ≫ (I.map j).subschemeι = I.subschemeι ≫ j :=
  (I.subschemeι ≫ j).toImage_imageι

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Chow.HilbertCycleDatum

variable {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (j : Y ⟶ X) [IsClosedImmersion j]
  (i : T ⟶ S) (r : ℕ) (Z : HilbertCycleDatum q r)

/-- The structure morphism of the pushed-forward closed subscheme factors through the comparison
isomorphism as `e.inv`, followed by the structure morphism of the given datum, followed by `i`. -/
theorem map_subschemeι_comp (h : j ≫ f = q ≫ i) :
    (Z.ideal.map j).subschemeι ≫ f =
      (Scheme.IdealSheafData.mapSubschemeIso Z.ideal j).inv ≫
        (Z.ideal.subschemeι ≫ q) ≫ i := by
  rw [Iso.eq_inv_comp, Scheme.IdealSheafData.mapSubschemeIso_hom_subschemeι_assoc, h,
    Category.assoc]

/-- **The closed subscheme of the pushforward is the base change along `i` of the closed
subscheme of the given datum.** -/
theorem isPullback_map_subschemeι [Mono i] (h : j ≫ f = q ≫ i) :
    IsPullback (Scheme.IdealSheafData.mapSubschemeIso Z.ideal j).hom
      (Z.ideal.subschemeι ≫ q) ((Z.ideal.map j).subschemeι ≫ f) i :=
  IsPullback.of_horiz_isIso_mono ⟨by
    rw [Scheme.IdealSheafData.mapSubschemeIso_hom_subschemeι_assoc, h, Category.assoc]⟩

/-- The pushed-forward closed subscheme is flat over `S`. -/
theorem flat_map_subschemeι_comp [IsOpenImmersion i] (h : j ≫ f = q ≫ i) :
    Flat ((Z.ideal.map j).subschemeι ≫ f) := by
  have := Z.flat
  rw [map_subschemeι_comp f q j i r Z h]
  infer_instance

/-- The pushed-forward closed subscheme is locally of finite presentation over `S`. -/
theorem locallyOfFinitePresentation_map_subschemeι_comp [IsOpenImmersion i]
    (h : j ≫ f = q ≫ i) :
    LocallyOfFinitePresentation ((Z.ideal.map j).subschemeι ≫ f) := by
  have := Z.locallyFinitePresentation
  rw [map_subschemeι_comp f q j i r Z h]
  infer_instance

/-- The pushed-forward closed subscheme is quasi-compact over `S`. -/
theorem quasiCompact_map_subschemeι_comp [QuasiCompact i] (h : j ≫ f = q ≫ i) :
    QuasiCompact ((Z.ideal.map j).subschemeι ≫ f) := by
  have := Z.quasiCompact
  rw [map_subschemeι_comp f q j i r Z h]
  infer_instance

/-- The local Krull dimension bound of Tag 02NJ at a point of the pushed-forward closed
subscheme, stated without a `LocallyOfFiniteType` instance argument. -/
theorem topologicalKrullDimAt_map_subschemeι_comp_le [IsOpenImmersion i] [QuasiCompact i]
    (h : j ≫ f = q ≫ i) (x : (Z.ideal.map j).subscheme) :
    topologicalKrullDimAt (((Z.ideal.map j).subschemeι ≫ f).fiber
        (((Z.ideal.map j).subschemeι ≫ f) x))
      (((Z.ideal.map j).subschemeι ≫ f).asFiber x) ≤ (r : WithBot ℕ∞) := by
  have := Z.flat
  have := Z.locallyFinitePresentation
  have := Z.quasiCompact
  have := flat_map_subschemeι_comp f q j i r Z h
  have := locallyOfFinitePresentation_map_subschemeι_comp f q j i r Z h
  have := quasiCompact_map_subschemeι_comp f q j i r Z h
  have hft : LocallyOfFiniteType ((Z.ideal.map j).subschemeι ≫ f) := inferInstance
  obtain ⟨z, rfl⟩ : ∃ z, (Scheme.IdealSheafData.mapSubschemeIso Z.ideal j).hom z = x := by
    refine ⟨(Scheme.IdealSheafData.mapSubschemeIso Z.ideal j).inv x, ?_⟩
    change ((Scheme.IdealSheafData.mapSubschemeIso Z.ideal j).inv ≫
      (Scheme.IdealSheafData.mapSubschemeIso Z.ideal j).hom) x = x
    rw [Iso.inv_hom_id]
    rfl
  rw [← topologicalKrullDimAt_fiber_eq_of_isPullback
    (isPullback_map_subschemeι f q j i r Z h) z]
  exact Z.relativeDimensionLE z

/-- **The extension of a member of `Hilb(Y/T, r)` to a member of `Hilb(X/S, r)`** along a closed
immersion `j : Y ⟶ X` over a quasi-compact open immersion `i : T ⟶ S` of the base. Its ideal
sheaf is the pushforward along `j` of the ideal sheaf of the given datum. -/
def extend [IsOpenImmersion i] [QuasiCompact i] (h : j ≫ f = q ≫ i) :
    HilbertCycleDatum f r :=
  ⟨Z.ideal.map j, flat_map_subschemeι_comp f q j i r Z h,
    locallyOfFinitePresentation_map_subschemeι_comp f q j i r Z h,
    quasiCompact_map_subschemeι_comp f q j i r Z h,
    fun x ↦ topologicalKrullDimAt_map_subschemeι_comp_le f q j i r Z h x⟩

/-- The ideal sheaf of the extension is the pushforward along `j` of the ideal sheaf of the given
datum. -/
@[simp]
theorem extend_ideal [IsOpenImmersion i] [QuasiCompact i] (h : j ≫ f = q ≫ i) :
    (extend f q j i r Z h).ideal = Z.ideal.map j := rfl

end Stacks.Chow.HilbertCycleDatum

end
