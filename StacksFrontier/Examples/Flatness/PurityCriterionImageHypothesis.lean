module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.Examples.Flatness.PureNotUniversallyPure

/-!
# The purity criterion with hypothesis (5) read on all of `X'`

Tag 05L4 assumes, as its hypothesis (5), that `g(X')` contains `Ass_{X_s}(ℱ_s)`. Read literally,
with no condition on where in `S'` the points of `X'` hitting `Ass_{X_s}(ℱ_s)` lie, the lemma is
false. Let `S` be any scheme with a point `s₀`, let `X = S`, `f = 𝟙`, `ℱ = 𝒪_S`, let
`S' = S ⨿ S` with the codiagonal and `s'` the copy of `s₀` in the first summand, and let `X' = S`
map to the second summand, with `g = 𝟙`. Every hypothesis of the lemma holds: `g^*ℱ` is pure along
`X'_{s'}` because no point of `X'` lies over a generalization of `s'`, and `g` is surjective. The
module `ℱ` is pure along `X_s`, `f` being an isomorphism. But the point `s'` of
`X ×_S S' = S'` is in the relative assassin and is not in the image of `X'`, which is the second
summand.

The proof of the lemma in the source replaces `S` by `S'` at its first step and from then on uses
hypothesis (5) for the fibre over `s'`; with (5) in that form the lemma holds, and that is the
form of
`AlgebraicGeometry.isPureAlong_iff_relativeAssassin_specializing_mem_range_of_associatedPoints`.

## Main results

* `Stacks.Examples.not_forall_isPureAlong_iff_of_associatedPoints_subset_range`: the literal
  reading of Tag 05L4 is false.

## References

* [Stacks Project, Tag 05L4](https://stacks.math.columbia.edu/tag/05L4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Examples

/-- The codiagonal `S ⨿ S ⟶ S` is étale: on each summand of the open cover by the two summands
it is the identity. -/
theorem etale_coprodDesc_id (S : Scheme.{u}) : Etale (coprod.desc (𝟙 S) (𝟙 S)) := by
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  refine IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) (coprodOpenCover.{u, 0} S S) ?_
  have : Etale (𝟙 S) := inferInstance
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · exact (coprod.inl_desc (𝟙 S) (𝟙 S)).symm ▸ this
  · exact (coprod.inr_desc (𝟙 S) (𝟙 S)).symm ▸ this

/-- The codiagonal `S ⨿ S ⟶ S`, pointed at the copy of `s₀` in the first summand, is an étale
neighbourhood of its image. -/
abbrev coprodNeighborhood (S : Scheme.{u}) (s₀ : S) :
    EtaleNeighborhood S (coprod.desc (𝟙 S) (𝟙 S) ((coprod.inl : S ⟶ S ⨿ S) s₀)) where
  scheme := S ⨿ S
  point := (coprod.inl : S ⟶ S ⨿ S) s₀
  toBase := coprod.desc (𝟙 S) (𝟙 S)
  etale_toBase := etale_coprodDesc_id S
  map_point := rfl

/-- The codiagonal neighbourhood is elementary: the first summand is an open subscheme on which
the codiagonal is the identity. -/
theorem isElementary_coprodNeighborhood (S : Scheme.{u}) (s₀ : S) :
    (coprodNeighborhood S s₀).IsElementary := by
  rw [EtaleNeighborhood.isElementary_iff]
  change IsIso ((coprod.desc (𝟙 S) (𝟙 S)).residueFieldMap ((coprod.inl : S ⟶ S ⨿ S) s₀))
  have h := Scheme.Hom.residueFieldMap_congr (coprod.inl_desc (𝟙 S) (𝟙 S)) s₀
  rw [Scheme.residueFieldMap_comp] at h
  have _ : IsIso ((coprod.inl : S ⟶ S ⨿ S).residueFieldMap s₀) := inferInstance
  refine (isIso_comp_right_iff _ ((coprod.inl : S ⟶ S ⨿ S).residueFieldMap s₀)).mp ?_
  rw [h]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) inferInstance

/-- The inclusion of the second summand of `S ⨿ S` is a closed immersion, its image being the
complement of the open image of the first summand. -/
theorem isClosedImmersion_coprod_inr (S : Scheme.{u}) :
    IsClosedImmersion (coprod.inr : S ⟶ S ⨿ S) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [← (isCompl_range_inl_inr S S).compl_eq]
  exact (coprod.inl : S ⟶ S ⨿ S).opensRange.isOpen.isClosed_compl

/-- Purity of the structure sheaf along every fibre of an isomorphism: after a base change the
morphism stays an isomorphism, so every point specializes into the fibre over every
specialization of its image. -/
theorem isPureAlong_id_unit (S : Scheme.{u}) (s : S) :
    IsPureAlong
      ({ S := S
         X := S
         f := 𝟙 S
         F := SheafOfModules.unit S.ringCatSheaf
         isFiniteType := structureSheaf_isFiniteType S
         isQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S
         s := s } : PrePureSituation.{u}) := by
  intro D _ _ hD
  have : IsIso D.toT := D.isPullback.isIso_snd_of_isIso
  obtain ⟨y, hy⟩ := D.toT.surjective D.t
  have hspec : D.xi ⤳ y := by
    refine D.toT.homeomorph.isInducing.specializes_iff.mp ?_
    rw [Scheme.Hom.homeomorph_apply, Scheme.Hom.homeomorph_apply, hy, D.xi_liesOver]
    exact D.specializes
  have hmem : y ∈ closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) :=
    ⟨specializes_iff_mem_closure.mp hspec, by rw [D.toT.range_fiberι]; exact hy⟩
  rwa [hD.2] at hmem

/-- **Tag 05L4 with hypothesis (5) read on all of `X'` is false.** The statement below is Tag
05L4 with hypothesis (5) in the form `g(X') ⊇ Ass_{X_s}(ℱ_s)`, and it fails for `X = S`,
`ℱ = 𝒪_S`, the codiagonal neighbourhood `S ⨿ S ⟶ S` of the copy of a point in the first
summand, and `X' = S` mapping to the second summand. -/
theorem not_forall_isPureAlong_iff_of_associatedPoints_subset_range :
    ¬ ∀ {X S X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
      (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
      (s : S) (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (p : X' ⟶ U.scheme) [LocallyOfFiniteType p] [QuasiCompact p]
      (g : X' ⟶ X) [Etale g] (hcomm : g ≫ f = p ≫ U.toBase),
      (∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) →
      IsPureAlong
        ({ S := U.scheme
           X := X'
           f := p
           F := (Scheme.Modules.pullback g).obj F
           isFiniteType := SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F
           isQuasicoherent := by
             have hF : F.IsQuasicoherent := inferInstance
             exact @SheafOfModules.modulePullback_isQuasicoherent X'.toRingedSpace
               X.toRingedSpace g.toLRSHom.toShHom F hF
           s := U.point } : PrePureSituation.{u}) →
      (∀ z : f.fiber s,
        z ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) →
          f.fiberι s z ∈ Set.range g) →
      (IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) ↔
        ∀ x : pullback (C := Scheme.{u}) f U.toBase,
          x ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
              ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) →
            pullback.snd f U.toBase x ⤳ U.point →
              x ∈ Set.range (pullback.lift g p hcomm)) := by
  intro H
  let S : Scheme.{u} := Spec (.of (ULift.{u} ℤ))
  obtain ⟨s₀⟩ : Nonempty S := inferInstanceAs (Nonempty (PrimeSpectrum (ULift.{u} ℤ)))
  let O := SheafOfModules.unit S.ringCatSheaf
  have : O.IsFiniteType := structureSheaf_isFiniteType S
  have : O.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S
  have := isClosedImmersion_coprod_inr S
  let U := coprodNeighborhood S s₀
  have : LocallyOfFiniteType (coprod.inr : S ⟶ U.scheme) :=
    inferInstanceAs (LocallyOfFiniteType (coprod.inr : S ⟶ S ⨿ S))
  have : QuasiCompact (coprod.inr : S ⟶ U.scheme) :=
    inferInstanceAs (QuasiCompact (coprod.inr : S ⟶ S ⨿ S))
  have hcomm : 𝟙 S ≫ 𝟙 S = (coprod.inr : S ⟶ S ⨿ S) ≫ U.toBase := by
    change 𝟙 S ≫ 𝟙 S = coprod.inr ≫ coprod.desc (𝟙 S) (𝟙 S)
    rw [coprod.inr_desc, Category.comp_id]
  have hflat : ∀ x : (𝟙 S : S ⟶ S).fiber (U.toBase U.point),
      IsFlatOverAt (𝟙 S : S ⟶ S).toLRSHom.toShHom O ((𝟙 S : S ⟶ S).fiberι _ x) := fun x =>
    (isFlatOverAt_unit_iff_isFlatAt (𝟙 S) _).mpr
      ((Flat.iff_flat_stalkMap (𝟙 S : S ⟶ S)).mp inferInstance _)
  have hpure' : IsPureAlong
      ({ S := U.scheme
         X := S
         f := (coprod.inr : S ⟶ U.scheme)
         F := (Scheme.Modules.pullback (𝟙 S)).obj O
         isFiniteType := SheafOfModules.pullback_isFiniteType (𝟙 S : S ⟶ S).toLRSHom.toShHom O
         isQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent S.toRingedSpace
             S.toRingedSpace (𝟙 S : S ⟶ S).toLRSHom.toShHom O
             (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S)
         s := U.point } : PrePureSituation.{u}) := by
    intro D _ _ _
    have hgen : D.g D.t' ⤳ (coprod.inl : S ⟶ S ⨿ S) s₀ := by
      have h := D.specializes.map D.g.continuous
      rwa [D.mapsToChosenPoint] at h
    obtain ⟨a, ha⟩ := hgen.mem_open (coprod.inl : S ⟶ S ⨿ S).opensRange.isOpen ⟨s₀, rfl⟩
    have hw := congrArg (fun k : D.X_T ⟶ U.scheme => k D.xi) D.isPullback.w
    simp only [Scheme.Hom.comp_apply, D.xi_liesOver] at hw
    exact inl_ne_inr S S a (D.toX D.xi) (ha.trans hw.symm)
  have hass : ∀ z : (𝟙 S : S ⟶ S).fiber (U.toBase U.point),
      z ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback ((𝟙 S : S ⟶ S).fiberι (U.toBase U.point))).obj O) →
        (𝟙 S : S ⟶ S).fiberι (U.toBase U.point) z ∈ Set.range (𝟙 S : S ⟶ S) :=
    fun z _ => by simp
  have key := (H (𝟙 S) O (U.toBase U.point) U (isElementary_coprodNeighborhood S s₀)
    (coprod.inr : S ⟶ U.scheme) (𝟙 S) hcomm hflat hpure' hass).mp (isPureAlong_id_unit S _)
  let x : pullback (C := Scheme.{u}) (𝟙 S) U.toBase :=
    (pullback.snd (𝟙 S) U.toBase).homeomorph.symm U.point
  have hx : pullback.snd (𝟙 S) U.toBase x = U.point :=
    (pullback.snd (𝟙 S) U.toBase).homeomorph.apply_symm_apply U.point
  have : IsIso ((pullback.snd (𝟙 S) U.toBase).fiberToSpecResidueField U.point) :=
    inferInstanceAs (IsIso (pullback.snd (pullback.snd (𝟙 S) U.toBase)
      (U.scheme.fromSpecResidueField U.point)))
  have hrel : x ∈ Stacks.Divisors.relativeAssassin (pullback.snd (𝟙 S) U.toBase)
      ((Scheme.Modules.pullback (pullback.fst (𝟙 S) U.toBase)).obj O) :=
    mem_relativeAssassin_of_fiberToSpecResidueField_isIso (pullback.snd (𝟙 S) U.toBase) _
      (Scheme.Modules.pullbackUnitIso (pullback.fst (𝟙 S) U.toBase)) U.point x hx
  obtain ⟨y, hy⟩ := key x hrel (specializes_of_eq hx)
  have h1 := congrArg (fun k : S ⟶ U.scheme => k y)
    (pullback.lift_snd (𝟙 S) (coprod.inr : S ⟶ U.scheme) hcomm)
  simp only [Scheme.Hom.comp_apply, hy, hx] at h1
  exact inr_ne_inl S S s₀ y h1.symm

end Stacks.Examples

end
