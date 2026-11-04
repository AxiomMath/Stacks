module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient

/-!
# The quotient of an étale equivalence relation on a representable algebraic space

Let `s, t : R ⟶ Y` be étale morphisms of algebraic spaces over `S` whose underlying presheaves are
representable, forming an equivalence relation of presheaves. Then there is an algebraic space
`Q` with an étale surjective morphism `e : Y ⟶ Q` of which `(t, s)` is the kernel pair. This is
**Stacks 02WW** (and the kernel-pair property **Stacks 02WV**) read on algebraic spaces whose
presheaves are only isomorphic to represented ones.

It is the quotient `U' = ∐ U'_k / ∐ U'_{kk'}` of the source's proof of Stacks 0CJU.

## Main results

* `CategoryTheory.EquivalenceRelation.compIso`: an equivalence relation stays one after
  composing both legs with an isomorphism.
* `AlgebraicGeometry.Space.exists_etaleQuotient_of_isEquivalenceRelation`: the quotient above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- **An equivalence relation stays one after composing both legs with an isomorphism.** -/
theorem IsEquivalenceRelation.comp_iso {C : Type*} [Category C] {R X X' : C} {p₁ p₂ : R ⟶ X}
    (h : IsEquivalenceRelation p₁ p₂) (e : X ≅ X') :
    IsEquivalenceRelation (p₁ ≫ e.hom) (p₂ ≫ e.hom) := by
  obtain ⟨E⟩ := h.nonempty_equivalenceRelation
  have hc : E.c.fst ≫ p₂ ≫ e.hom = E.c.snd ≫ p₁ ≫ e.hom := by
    rw [← Category.assoc, E.c.condition, Category.assoc]
  have hlim : IsLimit (PullbackCone.mk E.c.fst E.c.snd hc) :=
    PullbackCone.IsLimit.mk hc (fun c => PullbackCone.IsLimit.lift E.isLimit c.fst c.snd
        (by simpa using c.condition))
      (fun c => PullbackCone.IsLimit.lift_fst _ _ _ _)
      (fun c => PullbackCone.IsLimit.lift_snd _ _ _ _)
      (fun c m h₁ h₂ => PullbackCone.IsLimit.hom_ext E.isLimit
        (by rw [PullbackCone.IsLimit.lift_fst]; exact h₁)
        (by rw [PullbackCone.IsLimit.lift_snd]; exact h₂))
  exact ⟨⟨{ right_cancellation := fun _ f g h₁ h₂ =>
               E.right_cancellation f g (by simpa using h₁) (by simpa using h₂),
             r := e.inv ≫ E.r,
             reflexivity₁ := by simp,
             reflexivity₂ := by simp,
             s := E.s,
             symmetry₁ := by rw [← Category.assoc, E.symmetry₁],
             symmetry₂ := by rw [← Category.assoc, E.symmetry₂],
             c := PullbackCone.mk E.c.fst E.c.snd hc,
             isLimit := hlim,
             t := E.t,
             transitivity₁ := (Category.assoc _ _ _).symm.trans
               ((congrArg (· ≫ e.hom) E.transitivity₁).trans (Category.assoc _ _ _)),
             transitivity₂ := (Category.assoc _ _ _).symm.trans
               ((congrArg (· ≫ e.hom) E.transitivity₂).trans (Category.assoc _ _ _)) }⟩⟩

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quotient of an étale equivalence relation on a representable algebraic space** (Stacks
02WW and 02WV). -/
theorem exists_etaleQuotient_of_isEquivalenceRelation {R Y : AlgebraicSpaces B S hS}
    (hR : R.obj.IsRepresentable) (hY : Y.obj.IsRepresentable) (s t : R ⟶ Y)
    (hs : IsEtale B S hS s.hom) (ht : IsEtale B S hS t.hom)
    (hrel : IsEquivalenceRelation t.hom s.hom) :
    ∃ (Q : AlgebraicSpaces B S hS) (e : Y ⟶ Q), IsPullback t s e e ∧
      IsEtale B S hS e.hom ∧ IsSurjective B S hS e.hom := by
  let Y₀ := Y.obj.reprX
  let R₀ := R.obj.reprX
  let iY : yoneda.obj Y₀ ≅ Y.obj := Y.obj.reprW
  let iR : yoneda.obj R₀ ≅ R.obj := R.obj.reprW
  let t₀ : R₀ ⟶ Y₀ := yoneda.preimage (iR.hom ≫ t.hom ≫ iY.inv)
  let s₀ : R₀ ⟶ Y₀ := yoneda.preimage (iR.hom ≫ s.hom ≫ iY.inv)
  have ht₀ : yoneda.map t₀ = iR.hom ≫ t.hom ≫ iY.inv := yoneda.map_preimage _
  have hs₀ : yoneda.map s₀ = iR.hom ≫ s.hom ≫ iY.inv := yoneda.map_preimage _
  have hE := isMultiplicative_presheaf_etale B S hS
  have etale₀ : ∀ g : R ⟶ Y, IsEtale B S hS g.hom →
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (yoneda.preimage (iR.hom ≫ g.hom ≫ iY.inv)) := by
    intro g hg
    refine (presheaf_yoneda_map_etale_iff B S hS _).1 ?_
    rw [yoneda.map_preimage]
    have h₁ : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (iR.hom ≫ g.hom) :=
      (isEtale_iff_presheaf_of_yoneda B S hS _).1 (fun U φ hφ => by
        rw [← Category.assoc]
        exact hg U _ (MorphismProperty.comp_mem _ _ _ hφ (presheaf_etale_of_iso B S hS iR)))
    rw [← Category.assoc]
    exact MorphismProperty.comp_mem _ _ _ h₁ (presheaf_etale_of_iso B S hS iY.symm)
  have hrel' : IsEquivalenceRelation (iR.symm.hom ≫ yoneda.map t₀)
      (iR.symm.hom ≫ yoneda.map s₀) := by
    have h := hrel.comp_iso iY.symm
    rw [ht₀, hs₀]
    simpa using h
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS s₀ t₀) :=
    isEtaleEquivalenceRelation_of_yoneda B S hS s₀ t₀ iR.symm hrel' (etale₀ t ht) (etale₀ s hs)
  let Q : AlgebraicSpaces B S hS := ⟨_, isAlgebraicSpace_quotient_unconditional B S hS s₀ t₀⟩
  let π := quotientMap B S hS s₀ t₀
  refine ⟨Q, ObjectProperty.homMk (iY.inv ≫ π), ?_, ?_, ?_⟩
  · have hk := quotientMap_isPullback B S hS s₀ t₀
    refine isPullback_of_isPullback_hom B S hS (fst := t) (snd := s) ?_
    refine hk.of_iso iR iY iY (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [ht₀]; simp
    · rw [hs₀]; simp
    all_goals exact (Category.comp_id _).trans (iY.hom_inv_id_assoc π).symm
  · exact isEtale_of_presheafEtaleProperty B S hS _ (MorphismProperty.comp_mem _ _ _
      (presheaf_etale_of_iso B S hS iY.symm) (quotientMap_etale_unconditional B S hS s₀ t₀))
  · exact isSurjective_comp B S hS (isSurjective_of_isIso B S hS iY.inv)
      (isSurjective_of_presheafSurjective B S hS _
        (quotientMap_surjective_unconditional B S hS s₀ t₀))

end AlgebraicGeometry.Space
