module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitLocalFactorization
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover

/-!
# Representable étale morphisms of fppf sheaves, from étale affine points of bounded size

Let `S` be a scheme contained in a big fppf site `B` and let `Φ : X ⟶ Z` be a morphism of fppf
sheaves over `S`. Suppose that the base change of `Φ` along every point of `Z` out of an
*affine* object `U` of the site is represented by an object `W` of the site étale over `U`,
with `size W ≤ g (size U)` for a monotone `g` sending cardinals below the cutoff of the site to
cardinals below it. Then `Φ` is representable by algebraic spaces and étale.

This is `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_openImmersion_over_affinePoints`
with the open immersions replaced by étale morphisms of controlled size: the representing
objects over the affine opens of an arbitrary test object `T` are glued as a coproduct inside the
site, which the uniform bound `g (size T)` makes possible.

## Main results

* `AlgebraicGeometry.FormalSpace.DependentProduct.isRepresentableEtale_of_etale_over_affinePoints`:
  the criterion.

## References

* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The hypothesis of the criterion: over every affine point the base change is represented by
an étale object of size at most `g` of the size of the point. -/
abbrev EtaleAffinePullbackBounded {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z)
    (g : Cardinal.{u} → Cardinal.{u}) : Prop :=
  ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ Z,
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U)
      (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
      IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
      Etale ((BigFppfOver.toScheme B S hS).map p) ∧
      ((BigFppfOver.toScheme B S hS).obj W).size ≤ g ((BigFppfOver.toScheme B S hS).obj U).size

theorem exists_representable_etale_pullback_of_etale_over_affinePoints
    {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z)
    {g : Cardinal.{u} → Cardinal.{u}} (hgm : Monotone g) (hgc : ∀ c, c < B.cutoff → g c < B.cutoff)
    (h : EtaleAffinePullbackBounded B S hS Φ g)
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj) :
    ∃ (V : BigFppfOver B S hS) (q : V ⟶ T) (Wt : BigFppfOver B S hS) (m : Wt ⟶ V)
      (e : (uliftYoneda.{u + 1}).obj Wt ≅ pullback ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map m) ∧
      e.hom ≫ pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom =
        (uliftYoneda.{u + 1}).map m := by
  classical
  let J := BigFppfOver.topology B S hS
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨ι, Xf, V, j, q, hXaff, hjopen, hιsize, hXsize, hqsurj, hqetale, -, ⟨hsheaf⟩⟩ :=
    BigFppfOver.exists_affineOpens_surjective_etale_sigma' B S hS T
  set ξV : J.uliftYoneda.{u + 1}.obj V ⟶ Z := ⟨(uliftYoneda.{u + 1}).map q ≫ ξ⟩ with hξV
  choose W p r hpb hopen hsz using fun i =>
    h (Xf i) (hXaff i) (J.uliftYoneda.{u + 1}.map (j i) ≫ ξV)
  -- the representing objects are bounded by `g` of the size of the point
  set μ := max ((BigFppfOver.toScheme B S hS).obj T).size
    (g ((BigFppfOver.toScheme B S hS).obj T).size) with hμ
  have hμc : μ < B.cutoff := max_lt T.left.property (hgc _ T.left.property)
  have hWsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤ μ :=
    fun i => ((hsz i).trans (hgm (hXsize i))).trans (le_max_right _ _)
  obtain ⟨Wt, jw, hjwopen, hjwcov, -, ⟨hWsite⟩, ⟨hWsheaf⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS W hμc
      (hιsize.trans (le_max_left _ _)) hWsize
  set m : Wt ⟶ V := Cofan.IsColimit.desc hWsite (fun i => p i ≫ j i) with hm
  have hmfac : ∀ i, jw i ≫ m = p i ≫ j i := fun i => Cofan.IsColimit.fac hWsite _ i
  -- `m` is étale, étaleness being Zariski local on the source
  have hmet : Etale ((BigFppfOver.toScheme B S hS).map m) := by
    let 𝒰 : ((BigFppfOver.toScheme B S hS).obj Wt).OpenCover.{u} :=
      { I₀ := ι
        X := fun i => (BigFppfOver.toScheme B S hS).obj (W i)
        f := fun i => (BigFppfOver.toScheme B S hS).map (jw i)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hjwcov, hjwopen⟩ }
    have _ : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    have hfac : 𝒰.f i ≫ (BigFppfOver.toScheme B S hS).map m =
        (BigFppfOver.toScheme B S hS).map (p i) ≫
          (BigFppfOver.toScheme B S hS).map (j i) := by
      change (BigFppfOver.toScheme B S hS).map (jw i) ≫ _ = _
      rw [← Functor.map_comp, ← Functor.map_comp, hmfac i]
    rw [hfac]
    have _ : Etale ((BigFppfOver.toScheme B S hS).map (p i)) := hopen i
    have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i)) := hjopen i
    infer_instance
  -- the fibre product over `V` is the coproduct of the fibre products over the affine opens
  have ht : IsPullback (pullback.snd ξV Φ) (pullback.fst ξV Φ) Φ ξV :=
    (IsPullback.of_hasPullback ξV Φ).flip
  have hleft := fun i => IsPullback.of_right' (hpb i) ht
  obtain ⟨hPcol⟩ := Sheaf.nonempty_isColimit_cofanMk_of_isPullback J
    (fun i => J.uliftYoneda.{u + 1}.map (j i)) hsheaf (pullback.fst ξV Φ) _
    (fun i => J.uliftYoneda.{u + 1}.map (p i)) hleft
  set eW := IsColimit.coconePointUniqueUpToIso hWsheaf hPcol with heW
  have hfstm : eW.hom ≫ pullback.fst ξV Φ = J.uliftYoneda.{u + 1}.map m := by
    refine Cofan.IsColimit.hom_ext hWsheaf _ _ fun i => ?_
    have h1 := IsColimit.comp_coconePointUniqueUpToIso_hom hWsheaf hPcol ⟨i⟩
    have h2 : J.uliftYoneda.{u + 1}.map (jw i) ≫ eW.hom ≫ pullback.fst ξV Φ =
        J.uliftYoneda.{u + 1}.map (p i) ≫ J.uliftYoneda.{u + 1}.map (j i) := by
      rw [← Category.assoc]
      rw [show J.uliftYoneda.{u + 1}.map (jw i) ≫ eW.hom =
        (Cofan.mk (pullback ξV Φ)
          fun k ↦ ht.lift (r k) (J.uliftYoneda.{u + 1}.map (p k) ≫
            J.uliftYoneda.{u + 1}.map (j k))
            (by rw [(hpb k).w, Category.assoc])).ι.app ⟨i⟩ from h1]
      exact (hleft i).w
    have h3 : J.uliftYoneda.{u + 1}.map (jw i) ≫ J.uliftYoneda.{u + 1}.map m =
        J.uliftYoneda.{u + 1}.map (p i) ≫ J.uliftYoneda.{u + 1}.map (j i) := by
      rw [← Functor.map_comp, ← Functor.map_comp, hmfac i]
    change J.uliftYoneda.{u + 1}.map (jw i) ≫ eW.hom ≫ pullback.fst ξV Φ =
      J.uliftYoneda.{u + 1}.map (jw i) ≫ J.uliftYoneda.{u + 1}.map m
    rw [h2, h3]
  -- read the sheaf-level square at the level of presheaves
  have hPpre := (IsPullback.of_hasPullback ξV Φ).map (sheafToPresheaf J (Type (u + 1)))
  refine ⟨V, q, Wt, m,
    (sheafToPresheaf J (Type (u + 1))).mapIso eW ≪≫ hPpre.isoPullback,
    hqsurj, hqetale, hmet, ?_⟩
  have h4 : eW.hom.hom ≫ (pullback.fst ξV Φ).hom = (uliftYoneda.{u + 1}).map m :=
    congrArg (fun t : J.uliftYoneda.{u + 1}.obj Wt ⟶ J.uliftYoneda.{u + 1}.obj V ↦ t.hom) hfstm
  have h5 : hPpre.isoPullback.hom ≫ pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom =
      (pullback.fst ξV Φ).hom := hPpre.isoPullback_hom_fst
  change eW.hom.hom ≫ hPpre.isoPullback.hom ≫
      pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom = (uliftYoneda.{u + 1}).map m
  rw [h5]
  exact h4

/-- **Representable étale morphisms from étale affine points of bounded size.** A morphism of
fppf sheaves whose base change along every affine point of its target is represented by an
étale object of the site of size at most `g` of the size of the point is representable by
algebraic spaces and étale, for any monotone `g` preserving the bound by the cutoff. -/
theorem isRepresentableEtale_of_etale_over_affinePoints
    {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z)
    {g : Cardinal.{u} → Cardinal.{u}} (hgm : Monotone g)
    (hgc : ∀ c, c < B.cutoff → g c < B.cutoff)
    (h : EtaleAffinePullbackBounded B S hS Φ g) :
    IsRepresentableEtale B S hS Φ := by
  classical
  have hkey := exists_representable_etale_pullback_of_etale_over_affinePoints
    B S hS Φ hgm hgc h
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS Φ.hom := by
    refine isRepresentable_of_forall_surjective_etale_cover B S hS Φ fun T ξ ↦ ?_
    obtain ⟨V, q, Wt, m, e, hqs, hqe, -, -⟩ := hkey T ξ
    exact ⟨V, q, hqs, hqe, Space.isAlgebraicSpaceULift_of_iso B S hS e
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Wt)⟩
  refine ⟨hrep, ?_⟩
  intro T ξ
  obtain ⟨V, q, Wt, m, e, hqs, hqe, hme, hfst⟩ := hkey T ξ
  -- the base change of `Φ` along the point is étale over the chart `V`
  have hVet : Space.IsEtaleULift.{u + 1} B S hS
      (pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom) := by
    have hmet : Space.IsEtaleULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).map m) :=
      (Space.isEtaleULift_uliftYoneda_map_iff.{u + 1} B S hS m).mpr hme
    have hpre := isEtaleULift_precomp_iso B S hS e.symm _ hmet
    rw [Iso.symm_hom, ← hfst, Iso.inv_hom_id_assoc] at hpre
    exact hpre
  refine isEtaleULift_of_targetChart B S hS
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T)
    (pullback.fst ξ Φ.hom) V ((uliftYoneda.{u + 1}).map q)
    (Space.relative_uliftYoneda_map B S hS _ q hqs)
    (Space.relative_uliftYoneda_map B S hS _ q hqe) ?_
  have hpre := isEtaleULift_precomp_iso B S hS
    (pullbackRightPullbackFstIso ξ Φ.hom ((uliftYoneda.{u + 1}).map q)) _ hVet
  rwa [pullbackRightPullbackFstIso_hom_fst] at hpre

end AlgebraicGeometry.FormalSpace.DependentProduct

end
