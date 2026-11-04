module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartFibreComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FibreRankUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# The minimal fibre degree bounds every fibre, and the lifts of a point are then exhausted

The construction of [Stacks, Tag 089J] forms the complement of the diagonals in the `d`-fold
self-product of an étale chart, where `d` is the degree of the chart over the open stratum where
that degree is largest. Two things must hold of the same `d`: over the stratum a point must have
`d` pairwise distinct lifts to the chart, so that it lifts to the complement of the diagonals;
and *everywhere* a point must have at most `d` lifts, so that `d` pairwise distinct lifts are all
of them — which is the hypothesis `hmatch` of
`AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom`, the fibre-exhaustion
clause used in the valuative criterion.

Both hold for the `d` of the degree stratification of Stacks 07S8, because its chain of closed
strata reaches the whole point set at index `d + 1`: every point lies in some stratum of index at
most `d`, so the fibre degree at every point is at most `d`. This file extracts that bound
alongside the two clauses about the open stratum which the rest of the construction consumes,
all from the one chain, so that the `d` is the same in all three.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.subsingleton_points_yoneda_of_isoSpec_toScheme` and
  `AlgebraicGeometry.Space.nonempty_points_yoneda_of_isoSpec_toScheme`: the point set of the
  presheaf represented by an object of the site whose underlying scheme is the spectrum of a
  field is a nonempty subsingleton.
* `AlgebraicGeometry.Space.exists_minimalDegreeOpen_and_fibre_le_degree`: **the minimal-degree
  open together with the bound on every fibre.** For a separated étale affine chart of a
  reasonable algebraic space with at least one point there is a degree `d` and a nonempty open
  `U` of the point set such that the chart base change has degree `d` exactly over `U`, has
  degree strictly less than `d` over a morphism missing `U`, and, at every field-valued point of
  the space, has *some* degree at most `d` on every representable presentation of its fibre.
* `AlgebraicGeometry.Space.exists_eq_of_minimalDegreeOpen`: **the fibre-exhaustion clause of
  [Stacks, Tag 089J]**, in the shape
  `AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom` takes it: `d` pairwise
  distinct lifts of a field-valued point to the chart exhaust the lifts.

## Implementation notes

The three clauses are read off the chain of
`AlgebraicGeometry.Space.exists_minimal_closedChain_isFiniteLocallyFreeOfRank` rather than from
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'`, which packages
the first two only: the bound needs `Z (d + 1) = Set.univ`, which that packaging discards, and
all three must speak about one and the same `d`.

For the bound, the degree at a field-valued point is produced in the shape of a *scheme* morphism
rather than of `CategoryTheory.MorphismProperty.presheaf`, because that is what
`AlgebraicGeometry.Space.exists_eq_of_isFiniteLocallyFreeOfRank_fibre` consumes; the passage is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_presheaf` applied to the identity base
change. The presentation of the fibre is an *argument* of that clause rather than part of its
conclusion, because a consumer which has already built the fibre — as the complement stratum of
[Stacks, Tag 089J] has, from its own chart — needs the degree of that presentation and not of
some other one. The characterisation of the strata holds for every presentation, so this costs
nothing.

`AlgebraicGeometry.Space.subsingleton_points_yoneda_of_isoSpec_toScheme` re-derives a lemma which
is `private` in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Radicial.lean`; under the Lean
module system a `private` declaration may not occur in the exposed body of a public one, so it is
restated here under a different name rather than reused. No existing declaration is touched.

## What is and is not proved

[Stacks, Tag 089J] is **not** proved here and no declaration in this file carries a Stacks
attribute. The degree stratification is Stacks 07S8, carried by
`AlgebraicGeometry.Space.exists_minimal_closedChain_isFiniteLocallyFreeOfRank`; the universal
fibre bound of a reasonable space is Stacks 03JL, carried by
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`; the count of sections of a finite locally
free morphism to the spectrum of a field is
`Stacks.Morphisms.exists_eq_of_isFiniteLocallyFreeOfRank`.

Nothing is said here about the complement of the minimal-degree open as an algebraic space, nor
about the chart it inherits, nor is the induction on `d` performed.

## References

* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The point set of a field spectrum in the site -/

/-- **The point set of the presheaf represented by an object of the site whose underlying scheme
is the spectrum of a field is a subsingleton.** The point set of the presheaf is the point set of
the underlying scheme by `AlgebraicGeometry.Space.pointsEquivScheme`, and the prime spectrum of a
field has one point. -/
theorem subsingleton_points_yoneda_of_isoSpec_toScheme (T : BigFppfOver B S hS)
    {K : Type u} [Field K]
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K)) :
    Subsingleton (points B S hS (yoneda.obj T)) := by
  have h1 : Subsingleton (Spec (CommRingCat.of K)) := by
    show Subsingleton (PrimeSpectrum K); infer_instance
  have h2 : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) :=
    ⟨fun x y ↦ eT.hom.injective (h1.elim _ _)⟩
  exact (pointsEquivScheme B S hS T).subsingleton

/-- **The point set of the presheaf represented by an object of the site whose underlying scheme
is the spectrum of a field is nonempty.** The prime spectrum of a field has a point, namely its
zero ideal. -/
theorem nonempty_points_yoneda_of_isoSpec_toScheme (T : BigFppfOver B S hS)
    {K : Type u} [Field K]
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K)) :
    Nonempty (points B S hS (yoneda.obj T)) :=
  ⟨(pointsEquivScheme B S hS T).symm
    (eT.inv.base (Classical.arbitrary (Spec (CommRingCat.of K))))⟩

/-! ### The minimal-degree open, with the bound on every fibre -/

/-- **The minimal-degree open of a separated étale affine chart, with the strict drop of the
degree on its complement and a bound on every fibre degree.**

The first two clauses are those of
`AlgebraicGeometry.Space.exists_isOpen_isFiniteLocallyFreeOfRank_and_degree_lt'`: the chart base
change along a morphism into `X` is finite locally free of degree `d` exactly when the image of
that morphism lies in `U`, and it is of degree strictly less than `d` whenever the image misses
`U` altogether.

The third clause is the one this file adds: at *every* field-valued point of `X`, whether in `U`
or not, each representable presentation of the fibre of the chart is finite locally free of some
degree at most `d`. It holds because the chain of closed strata of Stacks 07S8 reaches the whole
point set at index `d + 1`, so the least index at which a given point appears is at most `d`; the
characterisation of the strata then identifies the degree there, and it does so for every
presentation of the fibre, which is why the presentation is an argument rather than an output.

All three clauses speak about the same `d` and `U`, which is why they are produced together. -/
theorem exists_minimalDegreeOpen_and_fibre_le_degree
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
    (g : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hR : IsReasonableSpace B S hS X)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hgEt : IsEtale B S hS g) (hsep : IsSeparated B S hS g)
    (hne : Nonempty (points B S hS X)) :
    ∃ (d : ℕ) (U : Set (points B S hS X)), IsOpen U ∧ U.Nonempty ∧
      (∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X), IsAlgebraicSpace B S hS T →
        ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm →
          ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} d)
              (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
            Set.range (pointsMap B S hS T hm) ⊆ U)) ∧
      (∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X)
        (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm → points B S hS T →
            Set.range (pointsMap B S hS T hm) ⊆ Uᶜ →
              ∀ r : ℕ,
                (MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
                  (BigFppfOver.toScheme B S hS)).presheaf pr₂ → r < d) ∧
      ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
        (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
        (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
        (i : yoneda.obj Vf ⟶ yoneda.obj W),
        IsPullback i (yoneda.map q) g ξ →
          ∃ r : ℕ, r ≤ d ∧
            IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r := by
  classical
  obtain ⟨d, Z, hZ0, hZcl, -, hZtop, hZd, hZchar⟩ :=
    exists_minimal_closedChain_isFiniteLocallyFreeOfRank B S hS X W g hX
      (isFlat_of_isEtale B S hS hgEt) (isLocallyOfFinitePresentation_of_isEtale B S hS hgEt)
      hsep (isLocallyQuasiFinite_of_isEtale B S hS hX hgEt)
      (hR W hW g ((isEtale_iff_presheaf_of_yoneda B S hS g).1 hgEt)) hne
  refine ⟨d, (Z d)ᶜ, (hZcl d).isOpen_compl, Set.nonempty_compl.2 hZd, ?_, ?_, ?_⟩
  · intro T hm hT Pp pr₁ pr₂ hsq
    have h := hZchar d le_rfl T hm hT Pp pr₁ pr₂ hsq
    rw [hZtop] at h
    rwa [Set.compl_eq_univ_sdiff]
  · intro T hm Pp pr₁ pr₂ hsq t hTsub r hflf
    exact lt_of_presheaf_isFiniteLocallyFreeOfRank_of_range_subset B S hS W g d Z hZ0 hZchar
      T hm Pp pr₁ pr₂ hsq t (by rwa [compl_compl] at hTsub) r hflf
  · intro K hK T eT ξ Vf q i hsq
    -- the point set of `T` is a nonempty subsingleton, so `ξ` has a single point as its image
    have hsub : Subsingleton (points B S hS (yoneda.obj T)) :=
      subsingleton_points_yoneda_of_isoSpec_toScheme B S hS T eT
    obtain ⟨t₀⟩ := nonempty_points_yoneda_of_isoSpec_toScheme B S hS T eT
    set x : points B S hS X := pointsMap B S hS (yoneda.obj T) ξ t₀ with hxdef
    have hxall : ∀ z, pointsMap B S hS (yoneda.obj T) ξ z = x := fun z ↦ by
      rw [hsub.elim z t₀]
    -- the least stratum containing that point, which exists because the chain is exhaustive
    have hxd : x ∈ Z (d + 1) := by rw [hZtop]; exact Set.mem_univ x
    have hex : ∃ m : ℕ, x ∈ Z (m + 1) := ⟨d, hxd⟩
    have hsle : Nat.find hex ≤ d := Nat.find_le hxd
    have hsmem : x ∈ Z (Nat.find hex + 1) := Nat.find_spec hex
    have hsnot : x ∉ Z (Nat.find hex) := by
      rcases h : Nat.find hex with _ | k
      · rw [hZ0]; exact Set.notMem_empty x
      · exact Nat.find_min hex (by omega)
    -- the degree of the given presentation of the fibre, read off at the stratum of that point
    have hflf : (MorphismProperty.inverseImage
        (IsFiniteLocallyFreeOfRank.property.{u} (Nat.find hex))
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) :=
      (hZchar (Nat.find hex) hsle (yoneda.obj T) ξ (isAlgebraicSpace_yoneda B S hS T)
        (yoneda.obj Vf) i (yoneda.map q) hsq).2 (by
          rintro y ⟨z, rfl⟩
          rw [hxall z]
          exact ⟨hsmem, hsnot⟩)
    have hid : IsPullback (𝟙 (yoneda.obj Vf))
        (yoneda.map q) (yoneda.map q) (𝟙 (yoneda.obj T)) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    exact ⟨Nat.find hex, hsle,
      isFiniteLocallyFreeOfRank_of_presheaf B S hS hflf (𝟙 _) (𝟙 _) q hid⟩

/-! ### The fibre-exhaustion clause -/

/-- **The fibre-exhaustion clause of [Stacks, Tag 089J].** If every field-valued fibre of the
chart has degree at most `d`, then `d` pairwise distinct lifts of a field-valued point of `X` to
the chart are *all* the lifts of that point.

The hypothesis `hbd` is the third clause of
`AlgebraicGeometry.Space.exists_minimalDegreeOpen_and_fibre_le_degree`; the presentation of the
fibre it needs is the canonical one of
`CategoryTheory.Functor.relativelyRepresentable.pullback`, which étaleness of the chart
provides. The conclusion is the hypothesis `hmatch` of
`AlgebraicGeometry.Space.isProper_and_isHQuasiProjective_chowCoverHom`. The proof is
`AlgebraicGeometry.Space.exists_eq_of_isFiniteLocallyFreeOfRank_fibre`, which counts the
sections of a finite locally free morphism to the spectrum of a field, with the bound `d`
supplied by `hbd` at the point in question. -/
theorem exists_eq_of_minimalDegreeOpen
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X)
    (hgEt : IsEtale B S hS g) (d : ℕ)
    (hbd : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (Vf : BigFppfOver B S hS) (q : Vf ⟶ T)
      (i : yoneda.obj Vf ⟶ yoneda.obj W),
      IsPullback i (yoneda.map q) g ξ →
        ∃ r : ℕ, r ≤ d ∧
          IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) r) :
    ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (w : Fin d → (T ⟶ W)),
      (∀ k, yoneda.map (w k) ≫ g = ξ) → Function.Injective w →
        ∀ v : T ⟶ W, yoneda.map v ≫ g = ξ → ∃ k, v = w k := by
  intro K hK T eT ξ w hw hwinj v hv
  have hgp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g :=
    (isEtale_iff_presheaf_of_yoneda B S hS g).1 hgEt
  have hsq : IsPullback (yoneda.map (hgp.rep.fst' ξ)) (yoneda.map (hgp.rep.snd ξ)) g ξ :=
    hgp.rep.isPullback' ξ
  obtain ⟨r, hrle, hrank⟩ := hbd K hK T eT ξ (hgp.rep.pullback ξ) (hgp.rep.snd ξ)
    (yoneda.map (hgp.rep.fst' ξ)) hsq
  exact exists_eq_of_isFiniteLocallyFreeOfRank_fibre B S hS W g T eT ξ (hgp.rep.pullback ξ)
    (hgp.rep.snd ξ) (yoneda.map (hgp.rep.fst' ξ)) r d hrank hsq hrle w hw hwinj v hv

end AlgebraicGeometry.Space

end
