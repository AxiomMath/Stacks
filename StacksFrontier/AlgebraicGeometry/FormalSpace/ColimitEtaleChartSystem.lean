module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitLocalFactorization
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover

/-!
# Charts of a directed colimit: étale charts with a uniform size bound

Let `S` be a scheme contained in a big fppf site `B`. A morphism of fppf sheaves over `S` whose
base change along every affine point `U` of its target is represented by an object of the site
étale over `U`, of size at most `f (size U)` for one monotone function `f` of cardinals sending
cardinals below the cutoff of the site to cardinals below the cutoff, is representable by
algebraic spaces and étale. Consequently a directed colimit of fppf sheaves with monomorphic
transition morphisms and an étale chart system with such a bound is a formal algebraic space.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_etale_over_affinePoints`: a morphism
  of fppf sheaves whose base change along every affine point `U` of its target is represented by
  an object of the site étale over `U`, of size at most `f (size U)` for one monotone `f`
  preserving the cardinals below the cutoff, is representable by algebraic spaces and étale.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleChartSystem`: a directed colimit
  with monomorphic transitions and an étale chart system with such a bound is a formal algebraic
  space.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal
open AlgebraicGeometry.FormalSpace.CartesianColimit (equifibered_colimit_isPullback)

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A functor preserves a commuting square of morphisms. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- **Representability and étaleness are local on the test object, for étale base changes with a
uniform size bound.** Let `Φ : X ⟶ Z` be a morphism of fppf sheaves over `S` and `f` a monotone
function of cardinals sending cardinals below the cutoff of the site to cardinals below the
cutoff. Suppose that the base change of `Φ` along every point of `Z` out of an affine object `U`
of the site is represented by an object `W` of the site, étale over `U`, with
`size W ≤ f (size U)`. Then `Φ` is representable by algebraic spaces and étale. -/
theorem isRepresentableEtale_of_etale_over_affinePoints
    {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z) (f : Cardinal.{u} → Cardinal.{u})
    (hfmono : Monotone f) (hf : ∀ s < B.cutoff, f s < B.cutoff)
    (h : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ Z,
      ∃ (W : BigFppfOver B S hS) (p : W ⟶ U)
        (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
        IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
        Etale ((BigFppfOver.toScheme B S hS).map p) ∧
        ((BigFppfOver.toScheme B S hS).obj W).size ≤
          f ((BigFppfOver.toScheme B S hS).obj U).size) :
    IsRepresentableEtale B S hS Φ := by
  classical
  have hkey : ∀ (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj),
      ∃ (V : BigFppfOver B S hS) (q : V ⟶ T) (Wt : BigFppfOver B S hS) (m : Wt ⟶ V)
        (e : (uliftYoneda.{u + 1}).obj Wt ≅ pullback ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom),
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        Etale ((BigFppfOver.toScheme B S hS).map m) ∧
        e.hom ≫ pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom =
          (uliftYoneda.{u + 1}).map m := by
    intro T ξ
    classical
    let J := BigFppfOver.topology B S hS
    have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
    obtain ⟨ι, Xf, V, j, q, hXaff, hjopen, hιsize, hXsize, hqsurj, hqetale, -, ⟨hsheaf⟩⟩ :=
      BigFppfOver.exists_affineOpens_surjective_etale_sigma' B S hS T
    set ξV : J.uliftYoneda.{u + 1}.obj V ⟶ Z := ⟨(uliftYoneda.{u + 1}).map q ≫ ξ⟩ with hξV
    choose W p r hpb hpet hpsize using fun i =>
      h (Xf i) (hXaff i) (J.uliftYoneda.{u + 1}.map (j i) ≫ ξV)
    have hWsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤
        max ((BigFppfOver.toScheme B S hS).obj T).size
          (f ((BigFppfOver.toScheme B S hS).obj T).size) := fun i =>
      (hpsize i).trans ((hfmono (hXsize i)).trans (le_max_right _ _))
    obtain ⟨Wt, jw, hjwopen, hjwcov, -, ⟨hWsite⟩, ⟨hWsheaf⟩⟩ :=
      BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS W
        (max_lt T.left.property (hf _ T.left.property))
        (hιsize.trans (le_max_left _ _)) hWsize
    set m : Wt ⟶ V := Cofan.IsColimit.desc hWsite (fun i => p i ≫ j i) with hm
    have hmfac : ∀ i, jw i ≫ m = p i ≫ j i := fun i => Cofan.IsColimit.fac hWsite _ i
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
      rw [show 𝒰.f i ≫ (BigFppfOver.toScheme B S hS).map m = _ from
        map_comp_eq_map_comp (BigFppfOver.toScheme B S hS) (hmfac i)]
      have _ : Etale ((BigFppfOver.toScheme B S hS).map (p i)) := hpet i
      have _ : _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (j i)) := hjopen i
      infer_instance
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
      have h3 := map_comp_eq_map_comp J.uliftYoneda.{u + 1} (hmfac i)
      show J.uliftYoneda.{u + 1}.map (jw i) ≫ eW.hom ≫ pullback.fst ξV Φ =
        J.uliftYoneda.{u + 1}.map (jw i) ≫ J.uliftYoneda.{u + 1}.map m
      rw [h2, h3]
    have hPpre := (IsPullback.of_hasPullback ξV Φ).map (sheafToPresheaf J (Type (u + 1)))
    refine ⟨V, q, Wt, m,
      (sheafToPresheaf J (Type (u + 1))).mapIso eW ≪≫ hPpre.isoPullback,
      hqsurj, hqetale, hmet, ?_⟩
    have h4 : eW.hom.hom ≫ (pullback.fst ξV Φ).hom = (uliftYoneda.{u + 1}).map m :=
      congrArg (fun t : J.uliftYoneda.{u + 1}.obj Wt ⟶ J.uliftYoneda.{u + 1}.obj V ↦ t.hom) hfstm
    have h5 : hPpre.isoPullback.hom ≫ pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom =
        (pullback.fst ξV Φ).hom := hPpre.isoPullback_hom_fst
    show eW.hom.hom ≫ hPpre.isoPullback.hom ≫
        pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) Φ.hom = (uliftYoneda.{u + 1}).map m
    rw [h5]
    exact h4
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS Φ.hom := by
    refine isRepresentable_of_forall_surjective_etale_cover B S hS Φ fun T ξ ↦ ?_
    obtain ⟨V, q, Wt, m, e, hqs, hqe, -, -⟩ := hkey T ξ
    exact ⟨V, q, hqs, hqe, Space.isAlgebraicSpaceULift_of_iso B S hS e
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Wt)⟩
  refine ⟨hrep, ?_⟩
  intro T ξ
  obtain ⟨V, q, Wt, m, e, hqs, hqe, hme, hfst⟩ := hkey T ξ
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

/-- **A directed colimit with an étale chart system bounded uniformly is a formal algebraic
space.** Let `E : Λ ⥤ FppfSheaf B S hS` be a directed diagram with monomorphic transition
morphisms and `α k : G k ⟶ E` a family of equifibered chart diagrams whose colimits are affine
formal algebraic spaces and which cover each stage. Suppose that for each chart `k` there is a
monotone function `f k` of cardinals, sending cardinals below the cutoff of the site to
cardinals below the cutoff, such that the base change of every `(α k).app i` along a point of
`E.obj i` out of an affine object `U` of the site is represented by an object of the site étale
over `U` of size at most `f k (size U)`. Then a sheaf `Z ≅ colim E` satisfying
`SatisfiesSetTheoreticCondition` is a formal algebraic space. -/
theorem isFormalAlgebraicSpace_of_etaleChartSystem
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hmono : ∀ ⦃i j : Λ⦄ (f : i ⟶ j), Mono (E.map f))
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (colimit (G k)))
    (f : I → Cardinal.{u} → Cardinal.{u}) (hfmono : ∀ k, Monotone (f k))
    (hf : ∀ k, ∀ s < B.cutoff, f k s < B.cutoff)
    (hαet : ∀ (k : I) (i : Λ) (U : BigFppfOver B S hS),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ E.obj i,
      ∃ (W : BigFppfOver B S hS) (pr : W ⟶ U)
        (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ (G k).obj i),
        IsPullback c ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr)
          ((α k).app i) ξ ∧
        Etale ((BigFppfOver.toScheme B S hS).map pr) ∧
        ((BigFppfOver.toScheme B S hS).obj W).size ≤
          f k ((BigFppfOver.toScheme B S hS).obj U).size)
    (hα : ∀ k, (α k).Equifibered)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ i : Λ, Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i)))
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨eZ⟩ := hZ
  have hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i) := by
    intro k i
    have _ : IsConnected (Under i) := IsFiltered.isConnected _
    exact equifibered_colimit_isPullback (α k) (hα k) i
  refine ⟨hZset, I, (fun k ↦ colimit (G k)), (fun k ↦ colimMap (α k) ≫ eZ.inv), haff, ?_, ?_⟩
  · intro k
    refine isRepresentableEtale_of_etale_over_affinePoints B S hS
      (colimMap (α k) ≫ eZ.inv) (f k) (hfmono k) (hf k) fun U hU ξ ↦ ?_
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
    have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
    obtain ⟨i, ξ', hξ'⟩ :=
      exists_factor_through_stage_of_compact B S hS E hmono U (ξ ≫ eZ.hom)
    obtain ⟨W, pr, c, hpb, het, hsize⟩ := hαet k i U hU ξ'
    refine ⟨W, pr, c ≫ colimit.ι (G k) i, ?_, het, hsize⟩
    have hpaste : IsPullback (c ≫ colimit.ι (G k) i)
        ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr) (colimMap (α k))
        (ξ' ≫ colimit.ι E i) :=
      hpb.paste_horiz (hsq k i)
    rw [← hξ'] at hpaste
    refine hpaste.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eZ.symm
      (by simp) (by simp) (by simp) (by simp)
  · rw [Sheaf.isLocallySurjective_iff_epi]
    refine ⟨?_⟩
    intro T k l hkl
    have hζkl : ∀ m : I, (colimMap (α m) ≫ eZ.inv) ≫ k = (colimMap (α m) ≫ eZ.inv) ≫ l := by
      intro m
      have h := congrArg (fun t ↦ Sigma.ι (fun m : I ↦ colimit (G m)) m ≫ t) hkl
      simpa using h
    have hcolim : eZ.inv ≫ k = eZ.inv ≫ l := by
      refine colimit.hom_ext (fun i ↦ ?_)
      have hepi : Epi (Sigma.desc (fun m ↦ (α m).app i)) :=
        (Sheaf.isLocallySurjective_iff_epi _).mp (hcov i)
      refine (cancel_epi (Sigma.desc (fun m ↦ (α m).app i))).1 (Sigma.hom_ext _ _ (fun m ↦ ?_))
      have hm := hζkl m
      simp only [Category.assoc] at hm
      have hm2 := congrArg (fun t ↦ colimit.ι (G m) i ≫ t) hm
      simp only [ι_colimMap_assoc] at hm2
      simpa using hm2
    exact (cancel_epi eZ.inv).1 hcolim

end AlgebraicGeometry.FormalSpace

end
