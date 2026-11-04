module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ClosedStratumChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalDegreeFibreBound
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeClosedStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification

/-!
# A fibre-degree bound holding over a dense set of points holds everywhere

Let `g : h_W ⟶ X` be an étale separated morphism from the presheaf represented by an object of
the big fppf site to an algebraic space, with universally bounded fibres, and let `D` be a
**topologically dense** set of points of `X`. If every field-valued fibre of `g` whose point of
`X` lies in `D` is finite locally free of degree strictly below `d`, then *every* field-valued
fibre of `g` is finite locally free of degree strictly below `d`.

This is the second half of the fibre-degree drop of the inductive step of [Stacks, Tag 09YB].
There `g` is the complementary summand `W ⟶ Y` of the splitting `U ×_X Y = U ⨿ W` and `D` is the
image of the quasi-compact open immersion `j : U ⟶ Y` of the relative compactification, dense by
`AlgebraicGeometry.Space.exists_isSchemeTheoreticallyDense_isIntegralHom_factorization`. The
graph of `j` supplies the omitted point of each fibre over `j(U)` — that is the first half, and
is `AlgebraicGeometry.Space.exists_notMem_range_pointsMap_ι_of_mem_range_pointsMap` — so the
degree drops there; this file carries the drop to the points `Y` adds.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.subset_closedChain_of_lt_of_mem`: a point over which some presentation
  of the fibre has degree `r < d` lies in the stratum `Z d` of the degree stratification.
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_dense`: **the carry.** The
  degree bound spreads from a dense set of points of the base to all of it.
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOfRank_lt_of_denseRange`: the same with the
  dense set presented as the image of a morphism, which is the shape the inductive step of
  [Stacks, Tag 09YB] produces it in.

## Implementation notes

**This is closedness of a stratum, not semicontinuity.** The chain `Z` of
`AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank` — [Stacks, Tag 07S8] —
consists of *closed* sets, is monotone, starts at `∅` and exhausts the point set; and for
`r ≤ n` the base change of `g` along a morphism into `X` is finite locally free of degree `r`
exactly when the image of that morphism lies in `Z (r + 1) ∖ Z r`. So `Z d` is precisely the
locus where the degree is below `d`, it is closed, and a closed set containing a dense set is
everything. No lower semicontinuity of the fibre degree is developed or used here; the scheme-level
counterpart `Stacks.MoreMorphisms.boundsFiberDegrees_of_dense_of_forall_mem` does phrase the same
step through `AlgebraicGeometry.isClosed_fiber_rank_lt`, but at the level of algebraic spaces the
closedness is already in the stratification.

**Why the stratum index rather than the given degree.** The characterisation `hZchar` is
available only for `r ≤ n`, and the hypothesis supplies a degree bounded by `d`, which need not
be bounded by `n`. The proof therefore never uses `hZchar` in the forward direction at the
supplied degree: it reads the *stratum index* of the point in question off the chain with
`Nat.find`, which is at most `n` by exhaustiveness, obtains the degree there from `hZchar`
backwards, and only then identifies the two degrees — by uniqueness of the relative fibre degree,
`AlgebraicGeometry.Space.eq_of_presheaf_isFiniteLocallyFreeOfRank`. This is the device of the
third clause of `AlgebraicGeometry.Space.exists_minimalDegreeOpen_and_fibre_le_degree`.

**Étaleness rather than the four separate hypotheses.** [Stacks, Tag 07S8] asks for flatness,
local finite presentation, separatedness and local quasi-finiteness. Three of the four come free
from étaleness, and the application has an étale morphism, so étaleness and separatedness are
what is assumed; separatedness does not follow and is kept.

## What is and is not proved

Nothing here carries a Stacks attribute and no part of [Stacks, Tag 09YB] is registered. The
degree stratification itself is [Stacks, Tag 07S8] and is used as a black box. The induction on
the degree which this feeds is not performed here, and neither is the derivation of the
hypothesis `hon` from the graph splitting.

## References

* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point of a field-valued fibre lies in a stratum `Z (m + 1) ∖ Z m` whose degree `m` is that
of the given presentation `q`. -/
private theorem exists_stratum_of_isPullback
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X)
    (n : ℕ) (Z : ℕ → Set (points B S hS X)) (hZ0 : Z 0 = ∅) (hZtop : Z (n + 1) = Set.univ)
    (hZchar : ∀ r : ℕ, r ≤ n → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X),
      IsAlgebraicSpace B S hS T →
      ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
        IsPullback pr₁ pr₂ g hm →
        ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
            (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
          Set.range (pointsMap B S hS T hm) ⊆ Z (r + 1) \ Z r))
    {K : Type u} [Field K] (T : BigFppfOver B S hS)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
    (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
    (i : yoneda.obj Vf ⟶ yoneda.obj W) (hsq : IsPullback i (yoneda.map q) g ξ) :
    ∃ (x : points B S hS X) (m : ℕ), (∀ z, pointsMap B S hS (yoneda.obj T) ξ z = x) ∧
      x ∈ Z (m + 1) ∧ x ∉ Z m ∧ (MorphismProperty.inverseImage
        (IsFiniteLocallyFreeOfRank.property.{u} m) (BigFppfOver.toScheme B S hS)).presheaf
          (yoneda.map q) := by
  classical
  -- the point set of `T` is a nonempty subsingleton, so `ξ` has a single point as its image
  have hsub : Subsingleton (points B S hS (yoneda.obj T)) :=
    subsingleton_points_yoneda_of_isoSpec_toScheme B S hS T eT
  obtain ⟨t₀⟩ := nonempty_points_yoneda_of_isoSpec_toScheme B S hS T eT
  set x : points B S hS X := pointsMap B S hS (yoneda.obj T) ξ t₀ with hxdef
  have hxall : ∀ z, pointsMap B S hS (yoneda.obj T) ξ z = x := fun z ↦ by
    rw [hsub.elim z t₀]
  -- the least stratum containing that point, which exists because the chain is exhaustive
  have hex : ∃ m : ℕ, x ∈ Z (m + 1) := ⟨n, by rw [hZtop]; exact Set.mem_univ x⟩
  have hsle : Nat.find hex ≤ n := Nat.find_le (by rw [hZtop]; exact Set.mem_univ x)
  have hsmem : x ∈ Z (Nat.find hex + 1) := Nat.find_spec hex
  have hsnot : x ∉ Z (Nat.find hex) := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, hZ0]; exact Set.notMem_empty x
    · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      rw [hk]
      exact Nat.find_min hex (by omega)
  -- the degree of the given presentation at the stratum of that point
  have hflf : (MorphismProperty.inverseImage
      (IsFiniteLocallyFreeOfRank.property.{u} (Nat.find hex))
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) :=
    (hZchar (Nat.find hex) hsle (yoneda.obj T) ξ (isAlgebraicSpace_yoneda B S hS T)
      (yoneda.obj Vf) i (yoneda.map q) hsq).2 (by
        rintro y ⟨z, rfl⟩
        rw [hxall z]
        exact ⟨hsmem, hsnot⟩)
  exact ⟨x, Nat.find hex, hxall, hsmem, hsnot, hflf⟩

/-- **A point over which the fibre has degree below `d` lies in the stratum `Z d`.**

The data is the degree stratification of [Stacks, Tag 07S8]: a monotone chain of closed sets
starting at `∅` and exhausting the point set at index `n + 1`, whose consecutive difference
`Z (r + 1) ∖ Z r` is, for `r ≤ n`, exactly the locus over which the base change of `g` is finite
locally free of degree `r`.

The stratum index of the point — the least `m` with the point in `Z (m + 1)` — is at most `n`,
so the characterisation applies there and gives the degree `m` of the base change at the point.
That base change also has the supplied degree `r`, so `m = r` by uniqueness of the relative fibre
degree, and the point lies in `Z (r + 1)`, hence in `Z d` because `r < d` and the chain is
monotone. -/
theorem subset_closedChain_of_lt_of_mem
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X)
    (n d : ℕ) (Z : ℕ → Set (points B S hS X)) (hZ0 : Z 0 = ∅) (hZmono : Monotone Z)
    (hZtop : Z (n + 1) = Set.univ)
    (hZchar : ∀ r : ℕ, r ≤ n → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X),
      IsAlgebraicSpace B S hS T →
      ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
        IsPullback pr₁ pr₂ g hm →
        ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
            (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
          Set.range (pointsMap B S hS T hm) ⊆ Z (r + 1) \ Z r))
    {K : Type u} [Field K] (T : BigFppfOver B S hS)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
    (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
    (i : yoneda.obj Vf ⟶ yoneda.obj W) (hsq : IsPullback i (yoneda.map q) g ξ)
    (r : ℕ) (hrd : r < d)
    (hrank : IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) :
    Set.range (pointsMap B S hS (yoneda.obj T) ξ) ⊆ Z d := by
  classical
  obtain ⟨x, m, hxall, hsmem, -, hflf⟩ :=
    exists_stratum_of_isPullback B S hS W g n Z hZ0 hZtop hZchar T eT ξ Vf q i hsq
  -- the supplied degree is the same number
  have hrpre : (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) :=
    presheaf_isFiniteLocallyFreeOfRank_yoneda_map B S hS q hrank
  have heq : m = r :=
    eq_of_presheaf_isFiniteLocallyFreeOfRank B S hS hflf hrpre (𝟙 (yoneda.obj T))
      (eT.inv.base (Classical.arbitrary (Spec (CommRingCat.of K))))
  rintro y ⟨z, rfl⟩
  rw [hxall z]
  exact hZmono (show m + 1 ≤ d by omega) hsmem

/-- **The fibre-degree bound spreads from a dense set of points of the base.** Let `g : h_W ⟶ X`
be étale and separated with universally bounded fibres, and let `D` be a dense set of points of
`X`. If every presentation of a field-valued fibre of `g` over a point of `D` is finite locally
free of degree strictly below `d`, then so is every presentation of every field-valued fibre.

The locus where the degree is below `d` is the stratum `Z d` of the degree stratification of
[Stacks, Tag 07S8], which is closed; it contains `D` by
`AlgebraicGeometry.Space.subset_closedChain_of_lt_of_mem`, hence contains the closure of `D`,
which is everything. The degree at an arbitrary point is then read off the chain at the stratum
index of that point, which is below `d` because the point lies in `Z d` but outside its own
stratum. -/
theorem exists_isFiniteLocallyFreeOfRank_lt_of_dense
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) (hgEt : IsEtale B S hS g) (hsep : IsSeparated B S hS g)
    (hbound : HasUniversallyBoundedFibers B S hS W g)
    (d : ℕ) {D : Set (points B S hS X)} (hD : Dense D)
    (hon : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
      (i : yoneda.obj Vf ⟶ yoneda.obj W),
      IsPullback i (yoneda.map q) g ξ →
      Set.range (pointsMap B S hS (yoneda.obj T) ξ) ⊆ D →
        ∃ r : ℕ, r < d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) :
    ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
      (i : yoneda.obj Vf ⟶ yoneda.obj W),
      IsPullback i (yoneda.map q) g ξ →
        ∃ r : ℕ, r < d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r := by
  classical
  -- the degree stratification of Stacks 07S8
  obtain ⟨n, Z, hZ0, hZcl, hZmono, hZtop, hZchar⟩ :=
    exists_closedChain_isFiniteLocallyFreeOfRank B S hS X W g hX
      (isFlat_of_isEtale B S hS hgEt)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hgEt) hsep
      (isLocallyQuasiFinite_of_isEtale B S hS hX hgEt) hbound
  -- `Z d` contains `D`, hence its closure, hence everything
  have hDsub : D ⊆ Z d := by
    intro x hxD
    obtain ⟨p, hp⟩ := Quot.exists_rep x
    set ξ₀ : yoneda.obj p.siteObject ⟶ X := yonedaEquiv.symm p.value with hξ₀
    have hxval : ∀ z, pointsMap B S hS (yoneda.obj p.siteObject) ξ₀ z = x := fun z ↦
      (FieldValuedPoint.pointsMap_eq_class B S hS p z).trans hp
    have hrange : Set.range (pointsMap B S hS (yoneda.obj p.siteObject) ξ₀) ⊆ D := by
      rintro y ⟨z, rfl⟩
      rw [hxval z]
      exact hxD
    -- the canonical presentation of the fibre, which étaleness of `g` provides
    have hgp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g :=
      (isEtale_iff_presheaf_of_yoneda B S hS g).1 hgEt
    have hsq : IsPullback (yoneda.map (hgp.rep.fst' ξ₀)) (yoneda.map (hgp.rep.snd ξ₀)) g ξ₀ :=
      hgp.rep.isPullback' ξ₀
    obtain ⟨r, hrd, hrank⟩ := hon p.carrier p.field p.siteObject (Iso.refl _) ξ₀
      (hgp.rep.pullback ξ₀) (hgp.rep.snd ξ₀) (yoneda.map (hgp.rep.fst' ξ₀)) hsq hrange
    have hsubset := subset_closedChain_of_lt_of_mem B S hS W g n d Z hZ0 hZmono hZtop hZchar
      (K := p.carrier) p.siteObject (Iso.refl _) ξ₀ (hgp.rep.pullback ξ₀) (hgp.rep.snd ξ₀)
      (yoneda.map (hgp.rep.fst' ξ₀)) hsq r hrd hrank
    obtain ⟨z⟩ := nonempty_points_yoneda_of_isoSpec_toScheme B S hS p.siteObject
      (K := p.carrier) (Iso.refl _)
    have := hsubset ⟨z, rfl⟩
    rwa [hxval z] at this
  have hZduniv : Z d = Set.univ := by
    have hcl : closure D ⊆ Z d := (hZcl d).closure_subset_iff.mpr hDsub
    rw [hD.closure_eq] at hcl
    exact Set.eq_univ_of_univ_subset hcl
  -- the degree at an arbitrary field-valued point, read off at its own stratum
  intro K hK T eT ξ Vf q i hsq
  obtain ⟨x, m, hxall, hsmem, hsnot, hflf⟩ :=
    exists_stratum_of_isPullback B S hS W g n Z hZ0 hZtop hZchar T eT ξ Vf q i hsq
  -- the stratum index is below `d`: the point lies in `Z d` but outside its own stratum
  have hlt : m < d := by
    by_contra hge
    exact hsnot (hZmono (show d ≤ m by omega) (by rw [hZduniv]; exact Set.mem_univ x))
  have hid : IsPullback (𝟙 (yoneda.obj Vf))
      (yoneda.map q) (yoneda.map q) (𝟙 (yoneda.obj T)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  exact ⟨m, hlt,
    isFiniteLocallyFreeOfRank_of_presheaf B S hS hflf (𝟙 _) (𝟙 _) q hid⟩

/-- **The carry, with the dense set presented as the image of a morphism.** This is the shape in
which the inductive step of [Stacks, Tag 09YB] has its dense set: the image of the quasi-compact
open immersion `j : U ⟶ Y` of the relative compactification, whose density is the last clause of
`AlgebraicGeometry.Space.exists_isSchemeTheoreticallyDense_isIntegralHom_factorization`. -/
theorem exists_isFiniteLocallyFreeOfRank_lt_of_denseRange
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) (hgEt : IsEtale B S hS g) (hsep : IsSeparated B S hS g)
    (hbound : HasUniversallyBoundedFibers B S hS W g)
    (d : ℕ) (j : U ⟶ X) (hj : DenseRange (pointsMap B S hS U j))
    (hon : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
      (i : yoneda.obj Vf ⟶ yoneda.obj W),
      IsPullback i (yoneda.map q) g ξ →
      Set.range (pointsMap B S hS (yoneda.obj T) ξ) ⊆
        Set.range (pointsMap B S hS U j) →
        ∃ r : ℕ, r < d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) :
    ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
      (i : yoneda.obj Vf ⟶ yoneda.obj W),
      IsPullback i (yoneda.map q) g ξ →
        ∃ r : ℕ, r < d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r :=
  exists_isFiniteLocallyFreeOfRank_lt_of_dense B S hS W g hX hgEt hsep hbound d hj hon

end AlgebraicGeometry.Space

end
