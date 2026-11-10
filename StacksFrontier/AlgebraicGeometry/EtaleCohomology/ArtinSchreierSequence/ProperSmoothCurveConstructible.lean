module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.HigherDirectImageZModAffine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.HigherDirectImageEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ZModConstructibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ModuleSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionCoefficientsDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback

/-!
# [Stacks, Tag 0GKV] in characteristic `p`: `R^q f_* 𝐙/p` for a family of curves

Let `S` be a Noetherian scheme of characteristic `p` and `f : X ⟶ S` proper and smooth with
geometrically connected fibres of dimension at most `1`. Then every `R^q f_* 𝐙/p` is a
constructible sheaf of `𝔽_p`-modules.

Constructibility is Zariski local on `S` ([Stacks, Tag 095F]). Near a point of `S`, inside an
affine open `Spec A`, there is `g ∉ p` such that the Čech model of `RΓ(X_{A_g}, 𝒪)` has free
cohomology of finite rank ([Stacks, Tag 0GKA], `exists_away_free_homology_of_smooth`). Over
`Spec A_g` the higher direct images of `𝐙/p` are then the kernels of `F - 1` for Frobenius matrices
on `𝐆_a^r`, which are constructible by [Stacks, Tag 0GKU]
(`isConstructibleAbelianSheaf_rightDerived_constantZMod_of_free`). The higher direct images
commute with restriction to `Spec A_g` (`rightDerivedDirectImageEtaleRestrictIso`) and with
forgetting the `𝔽_p`-module structure, and a sheaf of `𝔽_p`-modules is constructible when its
underlying abelian sheaf is (`isConstructibleEtaleModule_zmod_of_forget`).

## Main results

* `Stacks.ArtinSchreier.isConstructibleEtaleModule_rightDerivedConstantUnit_of_charP`:
  [Stacks, Tag 0GKV] case `ℓ = p`, over a Noetherian base; the tag allows any base `S`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace Stacks.CategoryTheory.CechComplex

universe u

namespace Stacks.ArtinSchreier

section Fibre

/-- **A bound on the dimension of the fibres passes to a base change along an open immersion.**
If every fibre of `f` has dimension at most `n`, so does every fibre of `pullback.snd f ι`. -/
theorem topologicalKrullDim_fiber_pullbackSnd_le {X S W : Scheme.{u}} (f : X ⟶ S) (ι : W ⟶ S)
    [IsOpenImmersion ι] {n : WithBot ℕ∞} (h : ∀ s, topologicalKrullDim (f.fiber s) ≤ n)
    (w : W) : topologicalKrullDim ((pullback.snd f ι).fiber w) ≤ n := by
  let φ : (pullback.snd f ι).base ⁻¹' {w} → f.base ⁻¹' {ι.base w} := fun x =>
    ⟨(pullback.fst f ι).base x.1, by
      change (pullback.fst f ι ≫ f).base x.1 = ι.base w
      rw [pullback.condition, Scheme.Hom.comp_apply, x.2]⟩
  have hφ : IsHomeomorph φ := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨(pullback.fst f ι).isOpenEmbedding.isEmbedding.restrict
      (fun x hx => (φ ⟨x, hx⟩).2), fun y => ?_⟩
    obtain ⟨x, hx⟩ : y.1 ∈ Set.range (pullback.fst f ι).base := by
      rw [IsOpenImmersion.range_pullbackFst]
      change f.base y.1 ∈ Set.range ι.base
      rw [show f.base y.1 = ι.base w from y.2]
      exact Set.mem_range_self _
    have hxw : (pullback.snd f ι).base x = w := by
      apply ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hx]
      exact y.2
    exact ⟨⟨x, hxw⟩, Subtype.ext hx⟩
  rw [((pullback.snd f ι).fiberHomeo w).isHomeomorph.topologicalKrullDim_eq,
    hφ.topologicalKrullDim_eq, ← (f.fiberHomeo (ι.base w)).isHomeomorph.topologicalKrullDim_eq]
  exact h _

end Fibre

/-- A quasi-compact scheme has a finite cover by affine opens. -/
theorem exists_fin_affine_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ i, IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => (V : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  refine ⟨t.card, fun i => (t.equivFin.symm i).1.1, fun i => (t.equivFin.symm i).1.2,
    top_unique fun x _ => ?_⟩
  obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨t.equivFin ⟨V, hV⟩, by simpa using hxV⟩

section Main

attribute [local instance] moduleCat_hasLimitsOfSize SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **Restricting `R^q f_* 𝐙/p` along an étale map `t`, as an abelian sheaf**: for a pullback
square of `f` along `t` with étale top map, the underlying abelian sheaf of `t^{-1} R^q f_* 𝐙/p`
is `R^q f'_* 𝐙/p`. -/
private def etaleModuleForgetInverseImageRightDerivedConstantUnitIso {X S T P : Scheme.{u}}
    (f : X ⟶ S) (t : T ⟶ S) (g' : P ⟶ X) (f' : P ⟶ T) [Etale t] [Etale g']
    (sq : IsPullback g' f' f t) (p q : ℕ) :
    (etaleModuleForgetAb.{u, 0} (ZMod p) T).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod p) t).obj (rightDerivedConstantUnit f q (ZMod p))) ≅
      ((etaleAbelianDirectImage.{u, 0} f').rightDerived q).obj
        ((constantSheaf P.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))) :=
  ((etaleModuleForgetInverseImageIso (ZMod p) t).app
      (rightDerivedConstantUnit f q (ZMod p))).symm ≪≫
    (etaleAbelianInverseImage.{u, 0} t).mapIso
      ((rightDerivedEtaleModuleDirectImageForgetIso (ZMod p) f q).app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p))).obj
            (ModuleCat.of (ZMod p) (ULift.{u + 1} (ZMod p)))) ≪≫
        ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).mapIso
          ((Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod p)
            X.smallEtaleTopology).app (ModuleCat.of (ZMod p) (ULift.{u + 1} (ZMod p))))) ≪≫
    rightDerivedDirectImageEtaleRestrictIso f t g' f' sq sq.w q _ ≪≫
    ((etaleAbelianDirectImage.{u, 0} f').rightDerived q).mapIso
      ((etaleAbelianInverseImageConstantIso.{u, 0} g').app _)

variable (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
  [GeometricallyConnected f] (hdim : ∀ s : S.obj, topologicalKrullDim (f.fiber s) ≤ 1)
  [IsNoetherian S.obj] (p : ℕ) [Fact p.Prime] (hp : ((p : ℕ) : ↑(S.obj.presheaf.obj (op ⊤))) = 0)
  (q : ℕ)

include hdim hp in
/-- **Near every point of `S`, `R^q f_* 𝐙/p` is constructible.** -/
theorem exists_isOpenImmersion_isConstructibleEtaleModule_rightDerivedConstantUnit
    (s : S.obj) :
    ∃ (T : B.Scheme) (j : T ⟶ S), IsOpenImmersion (B.inclusion.map j) ∧
      s ∈ Set.range (B.inclusion.map j).base ∧
      IsBigSiteConstructibleEtaleModule B T (ZMod p)
        ((etaleModuleInverseImage.{u, 0} (ZMod p) (B.inclusion.map j)).obj
          (rightDerivedConstantUnit f q (ZMod p))) := by
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := s) trivial
  have hLN : IsLocallyNoetherian S.obj := IsNoetherian.toIsLocallyNoetherian
  have : IsNoetherianRing ↑(S.obj.presheaf.obj (op W)) :=
    @AlgebraicGeometry.IsLocallyNoetherian.component_noetherian S.obj hLN ⟨W, hW⟩
  let ιW := hW.fromSpec
  obtain ⟨sW, hsW'⟩ : s ∈ Set.range ιW := by rwa [hW.range_fromSpec]
  let fW := pullback.snd f ιW
  obtain ⟨n, U, hUa, hUtop⟩ := exists_fin_affine_cover (pullback f ιW)
  have hU' : (⊤ : (pullback f ιW).Opens) = ⨆ i, liftCover U i :=
    le_antisymm (hUtop ▸ iSup_le fun i => le_iSup (fun j : ULift.{u} (Fin n) => U j.down) ⟨i⟩)
      le_top
  have haff : ∀ (r : ℕ) (x : Fin (r + 1) → ULift.{u} (Fin n)),
      IsAffineOpen (⨅ k, liftCover U (x k)) := fun r x =>
    Stacks.Cech.inter_isAffineOpen fW (liftCover U) (fun i => hUa i.down) x
  have hdimW : ∀ x, topologicalKrullDim (fW.fiber x) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_pullbackSnd_le f ιW (fun s => by exact_mod_cast hdim s)
  obtain ⟨g, hg, hfree⟩ :=
    Stacks.AlgebraicGeometry.CurveCechCohomology.exists_away_free_homology_of_smooth
      fW (liftCover U) hU' hdimW (fun i => hUa i.down) haff sW.asIdeal
  let φ := algebraMap ↑(S.obj.presheaf.obj (op W)) (Localization.Away g)
  let tA : Spec (.of (Localization.Away g)) ⟶ Spec ↑(S.obj.presheaf.obj (op W)) :=
    Spec.map (CommRingCat.ofHom φ)
  obtain ⟨sT, hsT⟩ : sW ∈ Set.range tA := by
    change sW ∈ (tA.opensRange : Set _)
    rwa [Scheme.Hom.opensRange_localizationAway g]
  have hsq := IsPullback.of_hasPullback fW tA
  have hT : B.Contains (Spec (.of (Localization.Away g))) :=
    Scheme.size_lt_of_isOpenImmersion (tA ≫ ιW) S.property
  let TB := B.obj (Spec (.of (Localization.Away g))) hT
  let j : TB ⟶ S := ObjectProperty.homMk (tA ≫ ιW)
  refine ⟨TB, j, inferInstanceAs (IsOpenImmersion (tA ≫ ιW)), ⟨sT, ?_⟩, ?_⟩
  · change ιW (tA sT) = s
    rw [hsT, hsW']
  let gT := pullback.fst fW tA
  let fT := pullback.snd fW tA
  let U' : Fin n → (pullback fW tA).Opens := fun i => gT ⁻¹ᵁ U i
  have hU'' : ⨆ i, U' i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hUtop, Scheme.Hom.preimage_top]
  have hUaff' : ∀ (r : ℕ) (x : Fin (r + 1) → Fin n), IsAffineOpen (inter U' x) := fun r x => by
    rw [inter_eq_iInf]
    exact Stacks.AlgebraicGeometry.ProperFlatGlobalSections.iInf_preimage_isAffineOpen φ hsq
      (liftCover U) (fun i => hUa i.down) r (ULift.up ∘ x)
  have hK := isConstructibleAbelianSheaf_rightDerived_constantZMod_of_free fT U' hU'' hUaff'
    Fact.out (natCast_eq_zero_of_hom (tA ≫ ιW) hp) B hT q fun m =>
      free_finite_homology_baseCech_of_isPullback φ hsq U hU' hUa m (hfree m).1 (hfree m).2
  exact isConstructibleEtaleModule_zmod_of_forget B TB p _ _
    (etaleModuleForgetInverseImageRightDerivedConstantUnitIso f (tA ≫ ιW)
      (gT ≫ pullback.fst f ιW) fT (hsq.paste_horiz (IsPullback.of_hasPullback f ιW)) p q) hK

include hdim hp in
/-- **[Stacks, Tag 0GKV], case `ℓ = p`, over a Noetherian base** (the tag's statement has no
Noetherian hypothesis on `S`). Let `S` be a Noetherian scheme on which the prime `p` vanishes and
`f : X ⟶ S` proper and smooth with geometrically connected fibres of dimension at most `1`. Then
`R^q f_* 𝐙/p` is a constructible sheaf of `𝔽_p`-modules for every `q`. -/
theorem isConstructibleEtaleModule_rightDerivedConstantUnit_of_charP :
    IsBigSiteConstructibleEtaleModule B S (ZMod p) (rightDerivedConstantUnit f q (ZMod p)) := by
  have := fun (S T : B.Scheme) (f : T ⟶ S) =>
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B (ZMod p) f
  have := SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B (ZMod p)
  choose T j hj hs hc using
    exists_isOpenImmersion_isConstructibleEtaleModule_rightDerivedConstantUnit B f hdim p hp q
  exact isConstructibleModuleSheaf_of_openCover B (ZMod p) S _ T j hj
    (Set.eq_univ_of_forall fun s => Set.mem_iUnion.2 ⟨s, hs s⟩).symm fun s =>
    isConstructibleModuleSheaf_congr B (ZMod p) (T s)
      (etaleModulesToSmallEtalePullbackIso B (ZMod p) (j s) _) (hc s)

end Main

end Stacks.ArtinSchreier

end
