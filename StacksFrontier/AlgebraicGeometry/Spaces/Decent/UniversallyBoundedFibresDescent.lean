module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedFlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FieldFibreDegreeBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Descent of universally bounded fibres to a morphism towards an algebraic space

A morphism from a scheme to an algebraic space can inherit a bound on the degrees of its
field-valued fibres from a second morphism related to it. Two such descents are recorded.

Stacks 03JP descends along a flat surjection: if `U ⟶ V` is a surjective flat morphism of
schemes over an algebraic space `X`, then a bound for `U ⟶ X` is a bound for `V ⟶ X`.

Stacks 03JO descends along a base change: if `g : Y ⟶ X` is a morphism of algebraic spaces,
`f : U ⟶ X` is a morphism from a scheme whose image on points is contained in the image of
`g`, and the base change of `f` along `g` is a scheme with universally bounded fibres over
`Y`, then the fibres of `f` are universally bounded.

## Main results

* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_comp_of_surjective_flat`:
  **Stacks 03JP**.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_baseChange_of_range_subset`:
  **Stacks 03JO**.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_isPullback_of_isoFieldSpec`: a rank
  descends along a field extension of the base, by Stacks 02VO.

## Implementation notes

A field-valued fibre of a morphism to the algebraic space `X` is given by a cartesian square
of presheaves whose upper left corner is represented by an object of the site, as in
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`. In both statements the fibre of the
morphism whose bound is wanted is produced by the representability of that morphism, which
follows from the representability of the diagonal of `X`; the fibre of the morphism whose
bound is given then maps to it, and the two are compared there.

For Stacks 03JP the comparison morphism is a base change of `U ⟶ V`, hence again flat and
surjective, so the scheme-level descent
`AlgebraicGeometry.boundsFiberDegrees_of_comp_of_surjective_flat` of Stacks 03JB applies to
it. That descent produces a bound on the degrees of the fibres rather than a rank of the
morphism itself; over the spectrum of a field the two are the same thing, because the base
change of a morphism along the identity of its target is the morphism itself, which is
`AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange` of Stacks 03J5 read at the
identity.

For Stacks 03JO the comparison is only available after a field extension: the source states
that a field-valued point of `X` in the image of `|U|` lifts to `Y` after extending the
field, which here is `AlgebraicGeometry.Space.exists_point_of_isPullback` of Stacks 03H4
applied to the given cartesian square, followed by the choice of a field-valued point of the
fibre product of the two charts over `U`. The rank obtained over the extension descends
because the morphism of field spectra realising the extension is flat, surjective and
quasi-compact, hence a one-element fpqc covering, and being finite locally free of a fixed
rank is fpqc local on the base by Stacks 02VO.

## References

* [Stacks Project, Tag 03JO](https://stacks.math.columbia.edu/tag/03JO)
* [Stacks Project, Tag 03JP](https://stacks.math.columbia.edu/tag/03JP)
* [Stacks Project, Tag 03JB](https://stacks.math.columbia.edu/tag/03JB)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-! ### Degree bounds over the spectrum of a field -/

/-- Composing with an isomorphism of the target does not change a bound on the degrees of the
fibres: the composite is a base change of the original morphism. -/
private theorem boundsFiberDegrees_comp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) {n : ℤ}
    (h : BoundsFiberDegrees f n) : BoundsFiberDegrees (f ≫ e.hom) n :=
  boundsFiberDegrees_of_isPullback
    (show IsPullback (𝟙 X) (f ≫ e.hom) f e.inv from IsPullback.of_horiz_isIso ⟨by simp⟩) h

/-- A morphism whose target is isomorphic to the spectrum of a field is finite locally free of
some rank bounded by any bound on the degrees of its fibres. -/
private theorem exists_rank_le_of_boundsFiberDegrees_of_isoFieldSpec {k : Type u} [Field k]
    {Z W : Scheme.{u}} (g : Z ⟶ W) (e : W ≅ Spec (CommRingCat.of k)) {n : ℤ}
    (h : BoundsFiberDegrees g n) :
    ∃ r : ℕ, (r : ℤ) ≤ n ∧ IsFiniteLocallyFreeOfRank g r := by
  obtain ⟨r, hr, hrank⟩ :=
    (boundsFiberDegrees_iff_field_baseChange (g ≫ e.hom) n).mp
      (boundsFiberDegrees_comp_iso g e h) k (𝟙 _)
  have hsq : IsPullback (pullback.fst (𝟙 (Spec (CommRingCat.of k))) (g ≫ e.hom))
      (pullback.snd (𝟙 (Spec (CommRingCat.of k))) (g ≫ e.hom))
      (𝟙 (Spec (CommRingCat.of k))) (g ≫ e.hom) := IsPullback.of_hasPullback _ _
  have : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of k))) (g ≫ e.hom)) := hsq.isIso_snd_of_isIso
  have h₁ : IsFiniteLocallyFreeOfRank.property r
      (pullback.snd (𝟙 (Spec (CommRingCat.of k))) (g ≫ e.hom) ≫ (g ≫ e.hom)) := by
    rw [← hsq.w]
    simpa using hrank
  exact ⟨r, hr, ((IsFiniteLocallyFreeOfRank.property r).cancel_right_of_respectsIso g e.hom).mp
    (((IsFiniteLocallyFreeOfRank.property r).cancel_left_of_respectsIso _ _).mp h₁)⟩

namespace Space

/-! ### Descent along a flat surjection -/

set_option synthInstance.maxHeartbeats 200000 in
-- instance synthesis over the slices `BigFppfOver B S hS` of the big fppf site is expensive here
/-- **Stacks 03JP.** Let `X` be an algebraic space over `S`, let `U ⟶ V` be a morphism of
schemes over `S` and let `V ⟶ X` be a morphism over `S`. If the fibres of the composite
`U ⟶ X` are universally bounded and `U ⟶ V` is surjective and flat, then the fibres of
`V ⟶ X` are universally bounded, with the same bound. -/
@[stacks 03JP]
theorem hasUniversallyBoundedFibers_of_comp_of_surjective_flat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U V : BigFppfOver B S hS} (φ : U ⟶ V) (h : yoneda.obj V ⟶ X)
    [AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map φ)]
    [AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map φ)]
    (hU : HasUniversallyBoundedFibers B S hS U (yoneda.map φ ≫ h)) :
    HasUniversallyBoundedFibers B S hS V h := by
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : yoneda.relativelyRepresentable h :=
    (Functor.relativelyRepresentable.diag_iff).1 hX.diagonal_representable h
  obtain ⟨n, hn⟩ := hU
  refine ⟨n, fun k _ A hA ξ ↦ ?_⟩
  obtain ⟨W, p, i, r, hr, hrank, hpull⟩ := hn k A hA ξ
  have hPsq : IsPullback (yoneda.map (hrep.fst' ξ)) (yoneda.map (hrep.snd ξ)) h ξ :=
    hrep.isPullback' ξ
  -- The comparison morphism from the fibre of `U ⟶ X` to the fibre of `V ⟶ X`.
  have hc : (i ≫ yoneda.map φ) ≫ h = yoneda.map p ≫ ξ := by
    simpa [Category.assoc] using hpull.w
  have hqV : yoneda.map (hrep.lift (i ≫ yoneda.map φ) p hc) ≫ yoneda.map (hrep.fst' ξ) =
      i ≫ yoneda.map φ := by
    rw [hrep.map_fst' ξ]
    exact hrep.lift_fst (i ≫ yoneda.map φ) p hc
  have hqA : hrep.lift (i ≫ yoneda.map φ) p hc ≫ hrep.snd ξ = p :=
    hrep.lift_snd (i ≫ yoneda.map φ) p hc
  have hcompare : IsPullback i (yoneda.map (hrep.lift (i ≫ yoneda.map φ) p hc))
      (yoneda.map φ) (yoneda.map (hrep.fst' ξ)) :=
    IsPullback.of_bot (by rwa [← Functor.map_comp, hqA]) hqV.symm hPsq
  -- It is a base change of `U ⟶ V` in the site, hence surjective and flat.
  have hsite : IsPullback (yoneda.preimage i) (hrep.lift (i ≫ yoneda.map φ) p hc) φ
      (hrep.fst' ξ) := by
    refine IsPullback.of_map_of_faithful yoneda ?_
    simpa [yoneda.map_preimage i] using hcompare
  have hscheme := hsite.map (BigFppfOver.toScheme B S hS)
  have : AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hrep.lift (i ≫ yoneda.map φ) p hc)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Surjective) hscheme inferInstance
  have : AlgebraicGeometry.Flat
      ((BigFppfOver.toScheme B S hS).map (hrep.lift (i ≫ yoneda.map φ) p hc)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Flat) hscheme inferInstance
  -- The bound descends along it, and over a field spectrum a bound is a rank.
  have : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map p) r := hrank
  have hcomp : BoundsFiberDegrees
      ((BigFppfOver.toScheme B S hS).map (hrep.lift (i ≫ yoneda.map φ) p hc) ≫
        (BigFppfOver.toScheme B S hS).map (hrep.snd ξ)) (r : ℤ) := by
    rw [← Functor.map_comp, hqA]
    exact boundsFiberDegrees_of_isFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map p) r
  obtain ⟨r', hr', hrank'⟩ := exists_rank_le_of_boundsFiberDegrees_of_isoFieldSpec
    ((BigFppfOver.toScheme B S hS).map (hrep.snd ξ)) hA
    (boundsFiberDegrees_of_comp_of_surjective_flat _ _ (r : ℤ) hcomp)
  exact ⟨hrep.pullback ξ, hrep.snd ξ, yoneda.map (hrep.fst' ξ), r',
    hr'.trans hr, hrank', hPsq⟩

/-! ### Descent from a base change dominating the image on points -/

/-- A cartesian square of the site whose right-hand column is a morphism between two objects
with field spectra for underlying schemes transports the rank of its left-hand column to its
right-hand column: that column is a flat, surjective and quasi-compact morphism of schemes, so
it is a one-element fpqc covering, and being finite locally free of a fixed rank is fpqc local
on the base by Stacks 02VO. -/
theorem isFiniteLocallyFreeOfRank_of_isPullback_of_isoFieldSpec
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {k L : Type u} [Field k] [Field L] {A D W P : BigFppfOver B S hS}
    (hA : (BigFppfOver.toScheme B S hS).obj A ≅ Spec (CommRingCat.of k))
    (hD : (BigFppfOver.toScheme B S hS).obj D ≅ Spec (CommRingCat.of L))
    {j : W ⟶ P} {pW : W ⟶ D} {pA : P ⟶ A} {τ : D ⟶ A} (hsq : IsPullback j pW pA τ) (r : ℕ)
    (hrank : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map pW) r) :
    IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map pA) r := by
  have hscheme := hsq.map (BigFppfOver.toScheme B S hS)
  have hpb : IsFiniteLocallyFreeOfRank.property r
      (pullback.snd ((BigFppfOver.toScheme B S hS).map pA)
        ((BigFppfOver.toScheme B S hS).map τ)) :=
    ((IsFiniteLocallyFreeOfRank.property r).cancel_left_of_respectsIso
      hscheme.isoPullback.hom _).mp (by rwa [hscheme.isoPullback_hom_snd])
  have hfactor : (BigFppfOver.toScheme B S hS).map τ =
      hD.hom ≫ (hD.inv ≫ (BigFppfOver.toScheme B S hS).map τ ≫ hA.hom) ≫ hA.inv := by simp
  have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map τ) ∧
      AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map τ) ∧
      AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map τ) := by
    rw [hfactor]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨_, _, _⟩ := this
  refine (IsFiniteLocallyFreeOfRank.property_iff _ r).mp
    (MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := IsFiniteLocallyFreeOfRank.property.{u} r)
      ((BigFppfOver.toScheme B S hS).map τ).singleton_mem_fpqcPrecoverage ?_)
  rintro _ _ _ ⟨⟩
  exact hpb

/-- Stacks 03H4 read off a cartesian square of presheaves all of whose corners are algebraic
spaces: a point of `Z` and a point of `X` with the same image in `Y` are the two images of a
point of `W`. -/
private theorem exists_point_of_isPullback_of_isAlgebraicSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {a : W ⟶ Z} {b : W ⟶ X} {c : Z ⟶ Y} {e : X ⟶ Y} (sq : IsPullback a b c e)
    (z : points B S hS Z) (x : points B S hS X)
    (h : pointsMap B S hS Z c z = pointsMap B S hS X e x) :
    ∃ w : points B S hS W,
      pointsMap B S hS W a w = z ∧ pointsMap B S hS W b w = x :=
  exists_point_of_isPullback B S hS
    (W := ⟨W, hW⟩) (Z := ⟨Z, hZ⟩) (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩)
    (p := ObjectProperty.homMk a) (q := ObjectProperty.homMk b)
    (g := ObjectProperty.homMk c) (f := ObjectProperty.homMk e)
    (IsPullback.of_map_of_faithful (ObjectProperty.ι (algebraicSpaceProperty B S hS)) sq) z x h

/-- Under the hypotheses of Stacks 03JO, a point of a fibre of `f` above a field-valued point
`ξ` of `X` produces a field spectrum in the site through which `ξ` factors into `Y`.

Stacks 03H4 produces a point of `|h_V|` above the image of the given point in `|h_U|`, using
that the latter image in `|X|` lies in the image of `|Y| → |X|`. The two points then have the
same image in the scheme `U`, so the fibre product `V ×_U P` has a point, hence a field-valued
point in the sense of Stacks 03BU. Its field of definition is the required field: the
field spectrum maps to `V`, hence to `Y`, and to `P`, hence to `A`, compatibly over `X`. -/
private theorem exists_isoFieldSpec_factorisation_of_range_subset
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (g : Y ⟶ X)
    {U V : BigFppfOver B S hS} {f : yoneda.obj U ⟶ X} {iV : V ⟶ U} {p : yoneda.obj V ⟶ Y}
    (hcart : IsPullback (yoneda.map iV) p f g)
    (himage : Set.range (pointsMap B S hS (yoneda.obj U) f) ⊆
      Set.range (pointsMap B S hS Y g))
    {A P : BigFppfOver B S hS} {ξ : yoneda.obj A ⟶ X} {pU : P ⟶ U} {pA : P ⟶ A}
    (hP : IsPullback (yoneda.map pU) (yoneda.map pA) f ξ)
    (xP : (BigFppfOver.toScheme B S hS).obj P) :
    ∃ (L : Type u) (_ : Field L) (D : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj D ≅ Spec (CommRingCat.of L))
      (τ : D ⟶ A) (β : yoneda.obj D ⟶ Y), β ≫ g = yoneda.map τ ≫ ξ := by
  classical
  obtain ⟨y, hy⟩ := himage (Set.mem_range_self (pointsMap B S hS (yoneda.obj P) (yoneda.map pU)
    ((pointsEquivScheme B S hS P).symm xP)))
  obtain ⟨w, -, hwi⟩ := exists_point_of_isPullback_of_isAlgebraicSpace B S hS
    (isAlgebraicSpace_yoneda B S hS V) hY (isAlgebraicSpace_yoneda B S hS U) hX
    hcart.flip y _ hy
  -- The two points have the same image in the scheme `U`.
  have hpt : ((BigFppfOver.toScheme B S hS).map iV).base (pointsEquivScheme B S hS V w) =
      ((BigFppfOver.toScheme B S hS).map pU).base xP := by
    have h₁ := pointsEquivScheme_pointsMap_yoneda B S hS iV w
    have h₂ := pointsEquivScheme_pointsMap_yoneda B S hS pU
      ((pointsEquivScheme B S hS P).symm xP)
    rw [Equiv.apply_symm_apply] at h₂
    rw [← h₁, ← h₂, hwi]
  -- Hence the fibre product `V ×_U P` has a point, and so a field-valued point in the site.
  obtain ⟨zQ, -, -⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback iV pU).map (BigFppfOver.toScheme B S hS)) _ _ hpt
  obtain ⟨c, -⟩ := Quot.exists_rep
    ((pointsEquivScheme B S hS (Limits.pullback iV pU)).symm zQ)
  refine ⟨c.carrier, c.field, c.siteObject B S hS (yoneda.obj (Limits.pullback iV pU)),
    Iso.refl _, c.value ≫ Limits.pullback.snd iV pU ≫ pA,
    yoneda.map (c.value ≫ Limits.pullback.fst iV pU) ≫ p, ?_⟩
  calc (yoneda.map (c.value ≫ Limits.pullback.fst iV pU) ≫ p) ≫ g
      = yoneda.map ((c.value ≫ Limits.pullback.fst iV pU) ≫ iV) ≫ f := by
        rw [Category.assoc, ← hcart.w, Functor.map_comp, Category.assoc]
        simp [Functor.map_comp]
    _ = yoneda.map ((c.value ≫ Limits.pullback.snd iV pU) ≫ pU) ≫ f := by
        rw [Category.assoc, Category.assoc, Limits.pullback.condition]
    _ = yoneda.map (c.value ≫ Limits.pullback.snd iV pU ≫ pA) ≫ ξ := by
        rw [Functor.map_comp, Category.assoc, hP.w]
        simp [Functor.map_comp]

/-- **Stacks 03JO.** Let `g : Y ⟶ X` be a morphism of algebraic spaces over `S`, let
`f : h_U ⟶ X` be a morphism from a scheme over `S`, and let `h_V ⟶ Y` be a base change of `f`
along `g`. If the image of `|h_U| → |X|` is contained in the image of `|Y| → |X|` and the
fibres of `h_V ⟶ Y` are universally bounded, then the fibres of `f` are universally
bounded, with the same bound. -/
@[stacks 03JO]
theorem hasUniversallyBoundedFibers_of_baseChange_of_range_subset
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (g : Y ⟶ X)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X)
    (himage : Set.range (pointsMap B S hS (yoneda.obj U) f) ⊆
      Set.range (pointsMap B S hS Y g))
    {V : BigFppfOver B S hS} {i : yoneda.obj V ⟶ yoneda.obj U} {p : yoneda.obj V ⟶ Y}
    (hcart : IsPullback i p f g) (hp : HasUniversallyBoundedFibers B S hS V p) :
    HasUniversallyBoundedFibers B S hS U f := by
  classical
  obtain ⟨iV, rfl⟩ := yoneda.map_surjective i
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrepf : yoneda.relativelyRepresentable f :=
    (Functor.relativelyRepresentable.diag_iff).1 hX.diagonal_representable f
  obtain ⟨n, hbound⟩ := hp
  refine ⟨max n 0, fun k _ A hA ξ ↦ ?_⟩
  obtain ⟨P, pA, pU₀, hP⟩ := hrepf ξ
  obtain ⟨pU, rfl⟩ := yoneda.map_surjective pU₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := IsAffine.of_isIso hA.hom
  by_cases hPe : IsEmpty ((BigFppfOver.toScheme B S hS).obj P)
  · have := hPe
    exact ⟨P, pA, yoneda.map pU, 0, by simp,
      isFiniteLocallyFreeOfRank_zero_of_isEmpty ((BigFppfOver.toScheme B S hS).map pA), hP⟩
  -- A point of the nonempty fibre, and the field extension it produces.
  obtain ⟨z⟩ := not_isEmpty_iff.mp hPe
  obtain ⟨L, _, D, hD, τ, β, hcompat⟩ := exists_isoFieldSpec_factorisation_of_range_subset
    B S hS hX hY g hcart himage hP z
  -- The fibre of `h_V ⟶ Y` above the lifted point is a fibre of `f` above `ξ` after the
  -- field extension, so its rank descends to the fibre of `f`.
  obtain ⟨W, pW, iW, r, hr, hrankW, hsqW⟩ := hbound L D hD β
  have houter : IsPullback (iW ≫ yoneda.map iV) (yoneda.map pW) f (yoneda.map τ ≫ ξ) := by
    rw [← hcompat]
    exact hsqW.paste_horiz hcart
  have hlift : (iW ≫ yoneda.map iV) ≫ f = (yoneda.map pW ≫ yoneda.map τ) ≫ ξ :=
    houter.w.trans (Category.assoc _ _ _).symm
  have htop : IsPullback (hP.lift (iW ≫ yoneda.map iV) (yoneda.map pW ≫ yoneda.map τ) hlift)
      (yoneda.map pW) (yoneda.map pA) (yoneda.map τ) :=
    IsPullback.of_right (by rwa [hP.lift_fst]) (hP.lift_snd _ _ _) hP
  have hsiteJ : IsPullback (yoneda.preimage
      (hP.lift (iW ≫ yoneda.map iV) (yoneda.map pW ≫ yoneda.map τ) hlift)) pW pA τ :=
    IsPullback.of_map_of_faithful yoneda (by rwa [yoneda.map_preimage])
  exact ⟨P, pA, yoneda.map pU, r, le_trans hr (le_max_left n 0),
    isFiniteLocallyFreeOfRank_of_isPullback_of_isoFieldSpec B S hS hA hD hsiteJ r hrankW, hP⟩

end Space

end AlgebraicGeometry

end
