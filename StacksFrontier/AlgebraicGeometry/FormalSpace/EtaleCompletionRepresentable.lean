module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFormalSpectrumRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleModWeakIdeal

/-!
# The completion of an étale algebra is representable étale

Let `S` be a scheme contained in a big fppf site `B`, let `A` be a weakly admissible topological
ring over `S` and let `f : A →+* C` be an étale ring map. The forward direction of
**Stacks 0AN8** says that `Spf C^∧ ⟶ Spf A` is representable by algebraic spaces and étale,
where `C^∧ = lim_J C / JC` is the completion of `C` over `A`.

## Main results

* `AlgebraicGeometry.FormalSpace.isEtaleULift_pullback_fst_formalSpectrumMap_of_etale`: the base
  change of `Spf C^∧ ⟶ Spf A` along any scheme-valued point of `Spf A` is étale over that point.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_formalSpectrumMap_of_etale`:
  `Spf C^∧ ⟶ Spf A` is representable étale.
* `AlgebraicGeometry.FormalSpace.isCountablyAdicStar_completionOver`: the completion over a
  ring of `WAdm^{adic*}` with countably generated topology is again such a ring.

## Implementation notes

Representability is Stacks 0AN5, the implication from tautness,
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut`,
applied to the canonical map `A → C^∧`, which is taut by Stacks 0AN6
(`TopologicalRing.isTaut_canonicalMap`); the site condition of Stacks 0AIF on `Spf C^∧` is
`AlgebraicGeometry.FormalSpace.hasLargeSite_completionOver_of_finiteType` of Stacks 0ANM.

For étaleness, let `T` be an object of the site with a point `ξ : T ⟶ Spf A`, and let
`φ : U' ⟶ T ×_{Spf A} Spf C^∧` be étale from an object `U'` of the site; the composite
`h : U' ⟶ T` has to be étale. This is Zariski local on `T`, so it may be checked over each
member `Tᵢ` of the affine open cover of `T`. A point of `Spf A` out of the quasi-compact `Tᵢ`
factors through a stage `Spec (A ⧸ I)` (Stacks 0AIA), over which the base change of
`Spf C^∧ ⟶ Spf A` is the base change `Vᵢ = Tᵢ ×_{Spec (A ⧸ I)} Spec (C^∧ ⧸ K)` of the stage map,
with `K` the closure of `I C^∧`. That stage map is étale by the first step of the proof of
Stacks 0AN8 (`TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap`), since `K` is the
kernel of the projection `C^∧ → C ⧸ IC` (Stacks 0AN6), so `Vᵢ ⟶ Tᵢ` is étale. Finally
`U' ×_T Tᵢ` is the base change of `φ` along `Vᵢ ⟶ T ×_{Spf A} Spf C^∧`, so it is étale over `Vᵢ`,
and therefore over `Tᵢ`.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Etale

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- For an étale ring map `f : A →+* C` and a weak ideal of definition `I` of `A`, the map of
stages `A ⧸ I → C^∧ ⧸ K` induced by the canonical map is étale, where `K` is the closure of
`I C^∧`: that closure is the kernel of the projection `C^∧ → C ⧸ IC`. -/
private theorem etale_quotientMap_of_eq_closure {f : A →+* C} (hf : f.Etale)
    (I : TopologicalRing.WeakIdealOfDefinitionIndex A)
    {φ : A →+* TopologicalRing.CompletionOver f}
    (hφ : φ = TopologicalRing.CompletionOver.canonicalMap f)
    {K : Ideal (TopologicalRing.CompletionOver f)} (hK : K = (I.1.map φ).closure)
    (h : I.1 ≤ Ideal.comap φ K) : (Ideal.quotientMap K φ h).Etale := by
  subst hφ
  rw [← TopologicalRing.CompletionOver.ker_projection_eq_closure] at hK
  subst hK
  exact TopologicalRing.CompletionOver.etale_quotientMap_canonicalMap hf I

/-- **The base change over a point factoring through a stage is étale.** Let `f : A →+* C` be
étale and let `g : Spf C^∧ ⟶ Spf A` be the formal spectrum of the canonical map. The base change
of `g` along a point `U ⟶ Spf A` which factors through a stage `Spec (A ⧸ I)` is represented by
an object `V` of the site, étale over `U`. -/
private theorem exists_isPullback_etale_of_factorsThroughStage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    {f : A →+* C} (hf : f.Etale) (Q : QuotientSystem B S hS (TopologicalRing.CompletionOver f))
    (g : ContinuousHom D Q) (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (U : BigFppfOver B S hS) (t : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum D)
    (ha : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t ≫
      formalSpectrumInclusion D I = a) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ formalSpectrum Q),
      IsPullback q ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        (formalSpectrumMap hA g) a ∧
      Etale ((BigFppfOver.toScheme B S hS).map p) := by
  classical
  subst ha
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  let _ : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  have htaut : RingHom.IsTaut g.toRingHom := hg ▸ TopologicalRing.isTaut_canonicalMap f hA.1
  obtain ⟨K, hK, hIK, hsq⟩ := isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA
    (TopologicalRing.completionOver_isWeaklyAdmissible f hA) D Q g htaut I
  refine ⟨pullback (T.map (g.stageMap I K hIK)) t, pullback.snd _ _,
    F.map (pullback.fst (T.map (g.stageMap I K hIK)) t) ≫ formalSpectrumInclusion Q K,
    ((IsPullback.of_hasPullback (T.map (g.stageMap I K hIK)) t).map F).paste_horiz hsq, ?_⟩
  have hs : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (T.map (g.stageMap I K hIK)) := by
    show Etale (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 g.toRingHom hIK)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact etale_quotientMap_of_eq_closure hf I hg hK hIK
  exact MorphismProperty.pullback_snd _ _ hs

/-- **The base change over a point out of a quasi-compact object is étale.** A point of `Spf A`
out of a quasi-compact object `U` of the site factors through a stage by Stacks 0AIA, so the
previous lemma applies to it. The statement is in terms of the universe-lifted Yoneda
embedding into sheaves, as in
`AlgebraicGeometry.FormalSpace.exists_isPullback_size_le_formalSpectrumMap_of_compactSpace`. -/
private theorem exists_isPullback_etale_of_compactSpace
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    {f : A →+* C} (hf : f.Etale) (Q : QuotientSystem B S hS (TopologicalRing.CompletionOver f))
    (g : ContinuousHom D Q) (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (U : BigFppfOver B S hS) (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ formalSpectrum D) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ U)
      (q : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶ formalSpectrum Q),
      IsPullback q ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p)
        (formalSpectrumMap hA g) ξ ∧
      Etale ((BigFppfOver.toScheme B S hS).map p) := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let ε := Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨I, t, ht⟩ :=
    exists_factorsThroughStage_of_compactSpace hA.1 D U hU (ε.inv.app U ≫ ξ)
  obtain ⟨V, p, c, hpb, hp⟩ :=
    exists_isPullback_etale_of_factorsThroughStage B S hS hA D hf Q g hg I U t _ ht
  refine ⟨V, p, ε.hom.app V ≫ c, ?_, hp⟩
  refine hpb.of_iso' (ε.app V) (Iso.refl _) (ε.app U) (Iso.refl _) (by simp)
    (ε.hom.naturality p).symm (by simp) ?_
  rw [← Iso.app_inv, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]

/-- **Étaleness in Stacks 0AN8.** Let `f : A →+* C` be étale and let `g : Spf C^∧ ⟶ Spf A` be
the formal spectrum of the canonical map. The base change of `g` along any scheme-valued point
`ξ` of `Spf A` is étale over the source of `ξ`.

The source of an étale point `φ : U' ⟶ T ×_{Spf A} Spf C^∧` maps to `T` by a morphism `h`
which is checked to be étale over the affine open cover `{Tᵢ}` of `T`: over `Tᵢ` the base change
of `g` is represented by an object `Vᵢ` étale over `Tᵢ`
(`exists_isPullback_etale_of_compactSpace`), and `U' ×_T Tᵢ` is the base change of `φ` along
`Vᵢ ⟶ T ×_{Spf A} Spf C^∧`, hence étale over `Vᵢ`. -/
theorem isEtaleULift_pullback_fst_formalSpectrumMap_of_etale
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    {f : A →+* C} (hf : f.Etale) (Q : QuotientSystem B S hS (TopologicalRing.CompletionOver f))
    (g : ContinuousHom D Q) (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f)
    (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ (formalSpectrum D).obj) :
    Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ (formalSpectrumMap hA g).hom) := by
  classical
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let Sch := BigFppfOver.toScheme B S hS
  let J := BigFppfOver.topology B S hS
  let L := sheafToPresheaf J (Type (u + 1))
  let a := (formalSpectrumMap hA g).hom
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have hpres : PreservesLimitsOfShape WalkingCospan Sch := by
    dsimp [Sch, BigFppfOver.toScheme]
    infer_instance
  intro U' φ hφ
  obtain ⟨h, hh⟩ := Y.map_surjective (φ ≫ pullback.fst ξ a)
  show (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Sch).relative
    Y (φ ≫ pullback.fst ξ a)
  rw [← hh, Space.relative_etale_uliftYoneda_map_iff]
  have : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u}) (Q := RingHom.Etale)
  apply IsZariskiLocalAtTarget.of_openCover (P := @Etale.{u}) (Sch.obj T).affineCover
  intro i
  -- the member `Tᵢ` of the affine open cover of `T`, as an object of the site
  have hTi : B.Contains ((Sch.obj T).affineCover.X i) :=
    Scheme.size_lt_of_isOpenImmersion ((Sch.obj T).affineCover.f i) T.left.property
  let e : B.obj hTi ⟶ T.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj hTi) ⟶ B.inclusion.obj T.left from
        (Sch.obj T).affineCover.f i)
  let Ti : BigFppfOver B S hS := Over.mk (e ≫ T.hom)
  let ai : Ti ⟶ T := Over.homMk e (by simp [Ti])
  have hai : Sch.map ai = (Sch.obj T).affineCover.f i := B.inclusion.map_preimage _
  have hcpt : CompactSpace (Sch.obj Ti) := by
    show CompactSpace ((Sch.obj T).affineCover.X i)
    infer_instance
  -- the base change of `g` over `Tᵢ`
  obtain ⟨V, p, c, hpb, hp⟩ := exists_isPullback_etale_of_compactSpace B S hS hA D hf Q g hg
    Ti hcpt ⟨Y.map ai ≫ ξ⟩
  let c' : Y.obj V ⟶ (formalSpectrum Q).obj := c.hom
  have hpbP : IsPullback c' (Y.map p) a (Y.map ai ≫ ξ) := hpb.map L
  -- the map from `Vᵢ` to the base change over `T`
  obtain ⟨gm, hgm₁, hgm₂⟩ : ∃ gm : Y.obj V ⟶ pullback ξ a,
      gm ≫ pullback.fst ξ a = Y.map p ≫ Y.map ai ∧ gm ≫ pullback.snd ξ a = c' :=
    ⟨pullback.lift (Y.map p ≫ Y.map ai) c' ((Category.assoc _ _ _).trans hpbP.w.symm),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have ht : IsPullback (Y.map p) gm (Y.map ai) (pullback.fst ξ a) := by
    refine IsPullback.of_bot ?_ hgm₁.symm (IsPullback.of_hasPullback ξ a)
    rw [hgm₂]
    exact hpbP.flip
  -- the map from `U' ×_T Tᵢ` to `Vᵢ`
  have hcond : (Y.map (pullback.fst h ai) ≫ φ ≫ pullback.snd ξ a) ≫ a =
      Y.map (pullback.snd h ai) ≫ Y.map ai ≫ ξ := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc φ, ← hh,
      ← Category.assoc, ← Category.assoc, ← Y.map_comp, ← Y.map_comp, pullback.condition]
  obtain ⟨q, hq⟩ := Y.map_surjective (hpbP.lift _ _ hcond)
  have hqp : Y.map q ≫ Y.map p = Y.map (pullback.snd h ai) := by
    rw [hq]
    exact hpbP.lift_snd _ _ hcond
  have hs : IsPullback (Y.map q ≫ Y.map p) (Y.map (pullback.fst h ai)) (Y.map ai)
      (φ ≫ pullback.fst ξ a) := by
    rw [hqp, ← hh]
    exact ((IsPullback.of_hasPullback h ai).map Y).flip
  have hcomm : Y.map q ≫ gm = Y.map (pullback.fst h ai) ≫ φ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgm₁, ← Category.assoc, hqp, Category.assoc, ← hh,
        ← Y.map_comp, ← Y.map_comp, pullback.condition]
    · rw [Category.assoc, hgm₂, hq, Category.assoc]
      exact hpbP.lift_fst _ _ hcond
  have hqe : Etale (Sch.map q) :=
    hφ.property gm (Y.map (pullback.fst h ai)) q (IsPullback.of_right hs hcomm ht).flip
  have hsnd : Etale (Sch.map (pullback.snd h ai)) := by
    have hqp' : q ≫ p = pullback.snd h ai := Y.map_injective (by rw [Y.map_comp, hqp])
    rw [← hqp', Sch.map_comp]
    infer_instance
  -- back to the fibre product of schemes
  let hsq := (IsPullback.of_hasPullback h ai).map Sch
  show Etale (pullback.snd (Sch.map h) ((Sch.obj T).affineCover.f i))
  rw [← hai]
  rw [← hsq.isoPullback_hom_snd] at hsnd
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale.{u}) _ _).mp hsnd

/-- **Stacks 0AN8, the forward direction.** Let `A` be a weakly admissible topological ring
over `S` with `Spf A` an affine formal algebraic space, and let `f : A →+* C` be étale. Then
`Spf C^∧ ⟶ Spf A`, the formal spectrum of the canonical map to the completion of `C` over `A`,
is representable by algebraic spaces and étale.

Representability is Stacks 0AN5 for the canonical map, which is taut by Stacks 0AN6; étaleness
is `isEtaleULift_pullback_fst_formalSpectrumMap_of_etale`. -/
theorem isRepresentableEtale_formalSpectrumMap_of_etale
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (hD : D.HasLargeSite) (f : A →+* C) (hf : f.Etale)
    (Q : QuotientSystem B S hS (TopologicalRing.CompletionOver f)) (g : ContinuousHom D Q)
    (hg : g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f) :
    IsRepresentableEtale B S hS (formalSpectrumMap hA g) := by
  have hfin : let : Algebra A C := f.toAlgebra; Algebra.FiniteType A C := by
    let : Algebra A C := f.toAlgebra
    have : Algebra.Etale A C := hf
    infer_instance
  have htaut : RingHom.IsTaut g.toRingHom := hg ▸ TopologicalRing.isTaut_canonicalMap f hA.1
  exact ⟨isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut B S hS hA
    (TopologicalRing.completionOver_isWeaklyAdmissible f hA) D Q
    (hasLargeSite_completionOver_of_finiteType B S hS f hfin hD Q) g htaut,
    isEtaleULift_pullback_fst_formalSpectrumMap_of_etale B S hS hA D hf Q g hg⟩

end Etale

/-- The completion of `C` over a ring `A` of `WAdm^{adic*}` with countably generated topology is
again such a ring, for an arbitrary ring map `A →+* C`: it is weakly admissible by Stacks 0AN6,
its topology is countably generated and defined by a finitely generated ideal because the
canonical map `A → C^∧` is taut (Stacks 0ANB). -/
theorem isCountablyAdicStar_completionOver
    {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing C] (hA : IsCountablyAdicStar A) (f : A →+* C) :
    IsCountablyAdicStar (TopologicalRing.CompletionOver f) :=
  ⟨⟨TopologicalRing.completionOver_isWeaklyAdmissible f hA.1.1,
    TopologicalRing.completionOver_isCountablyGenerated_nhds_zero f hA.1.1 hA.1.2⟩,
    TopologicalRing.completionOver_exists_fg_isAdic f hA.1.1 hA.2⟩

end AlgebraicGeometry.FormalSpace

end
