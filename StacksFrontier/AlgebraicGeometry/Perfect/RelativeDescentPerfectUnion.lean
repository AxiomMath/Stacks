module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentUnion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentReindex
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectInduction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectAffineCase
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentSituationIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChangeTor
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.PullbackCoherence

/-!
# The union step of the essential-surjectivity half of Stacks 0DI8

In the relative descent situation of Stacks 0DI6, an isomorphism over the limit between the
pullbacks of two objects at a stage `i`, for which the comparison of derived morphism sets out of
the colimit over the stages `k ≥ i` is bijective in all four directions, is the pullback of an
isomorphism at some stage `k ≥ i`.

Together with the glueing of Stacks 08DG this gives the union step of the induction of
Stacks 08DR for the essential-surjectivity half of Stacks 0DI8: if every object perfect relative
to `S` on the restrictions to two quasi-compact opens `U₀`, `V₀` of `X₀` descends to a stage, and
derived morphism sets between objects perfect at a stage descend, then every object perfect
relative to `S` on the restriction to `U₀ ∪ V₀` descends to a stage.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.exists_iso_homComparisonAt`: an isomorphism over
  the limit descends to an isomorphism at a stage.
* `AlgebraicGeometry.RelativeDescentSituation.exists_isPerfectAt_iso_of_cover`: the glueing step.
* `AlgebraicGeometry.RelativeDescentSituation.perfectEssentiallySurjectiveCanonical_of_cover`,
  `restrictPerfectEssentiallySurjective_sup`: the union step.
* `perfectEssentiallySurjectiveCanonical_of_fullyFaithful`: the essential-surjectivity half of
  Stacks 0DI8 from the descent of derived morphism sets between objects perfect at a stage.

## References

* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Lemma 20.45.1 (Tag 08DG)](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Lemma 30.4.1 (Tag 08DR)](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedPullback

variable {X Y Z : Scheme.{u}}

/-- The map on derived morphism sets attached to a factorisation is compatible with
composition. -/
theorem schemeFactorHom_comp_comp (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj K ⟶ (derivedPullback g.toLRSHom.toShHom).obj L)
    (ψ : (derivedPullback g.toLRSHom.toShHom).obj L ⟶
      (derivedPullback g.toLRSHom.toShHom).obj M) :
    schemeFactorHom f g k h K M (φ ≫ ψ) =
      schemeFactorHom f g k h K L φ ≫ schemeFactorHom f g k h L M ψ :=
  (congrArg (((schemeFactorIso f g k h).app K).homCongr ((schemeFactorIso f g k h).app M))
    ((derivedPullback f.toLRSHom.toShHom).map_comp φ ψ)).trans
    (Iso.homCongr_comp _ _ _ _ _)

/-- The map on derived morphism sets attached to a factorisation sends identities to
identities. -/
theorem schemeFactorHom_id_obj (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    schemeFactorHom f g k h K K (𝟙 _) = 𝟙 _ :=
  (congrArg (((schemeFactorIso f g k h).app K).homCongr ((schemeFactorIso f g k h).app K))
    ((derivedPullback f.toLRSHom.toShHom).map_id _)).trans
    ((congrArg (fun t => ((schemeFactorIso f g k h).app K).inv ≫ t) (Category.id_comp _)).trans
      (Iso.inv_hom_id _))

end Stacks.DerivedPullback

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)
  (i : D.LaterIndex)

section At

variable (K L M : DerivedCategory (SheafOfModules.{u}
  (structureSheafRing (D.schemeAt i).toRingedSpace)))

/-- The comparison maps out of the stages `k ≥ i` are compatible with the transition maps. -/
theorem homComparisonAt_homTransitionAt {k l : (D.reindex i).LaterIndex} (h : k.1 ≤ l.1)
    (φ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L) :
    D.homComparisonAt i K L l (D.homTransitionAt i K L h φ) = D.homComparisonAt i K L k φ :=
  Stacks.DerivedPullback.schemeFactorHom_comp (D.projection (D.reindexLater i l))
    (D.transition (i := D.reindexLater i k) (j := D.reindexLater i l) h)
    (D.reindexTransition i k) (D.reindexTransition i l) (D.projection (D.reindexLater i k))
    (D.projection i) (D.transition_comp_transition k.2 h) (D.projection_comp_transition h)
    (D.projection_comp_transition k.2) (D.projection_comp_transition l.2) K L φ

/-- The transition maps of the stages `k ≥ i` compose. -/
theorem homTransitionAt_homTransitionAt {k l m : (D.reindex i).LaterIndex} (h : k.1 ≤ l.1)
    (h' : l.1 ≤ m.1)
    (φ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L) :
    D.homTransitionAt i K L h' (D.homTransitionAt i K L h φ) =
      D.homTransitionAt i K L (h.trans h') φ :=
  Stacks.DerivedPullback.schemeFactorHom_comp
    (D.transition (i := D.reindexLater i l) (j := D.reindexLater i m) h')
    (D.transition (i := D.reindexLater i k) (j := D.reindexLater i l) h)
    (D.reindexTransition i k) (D.reindexTransition i l)
    (D.transition (i := D.reindexLater i k) (j := D.reindexLater i m) (h.trans h'))
    (D.reindexTransition i m) (D.transition_comp_transition k.2 h)
    (D.transition_comp_transition h h') (D.transition_comp_transition k.2 (h.trans h'))
    (D.transition_comp_transition l.2 h') K L φ

/-- The transition maps of the stages `k ≥ i` are compatible with composition. -/
theorem homTransitionAt_comp {k l : (D.reindex i).LaterIndex} (h : k.1 ≤ l.1)
    (φ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L)
    (ψ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj M) :
    D.homTransitionAt i K M h (φ ≫ ψ) =
      D.homTransitionAt i K L h φ ≫ D.homTransitionAt i L M h ψ :=
  Stacks.DerivedPullback.schemeFactorHom_comp_comp _ _ _ _ K L M φ ψ

/-- The comparison maps out of the stages `k ≥ i` are compatible with composition. -/
theorem homComparisonAt_comp (k : (D.reindex i).LaterIndex)
    (φ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L)
    (ψ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj M) :
    D.homComparisonAt i K M k (φ ≫ ψ) =
      D.homComparisonAt i K L k φ ≫ D.homComparisonAt i L M k ψ :=
  Stacks.DerivedPullback.schemeFactorHom_comp_comp _ _ _ _ K L M φ ψ

/-- The transition maps of the stages `k ≥ i` send identities to identities. -/
theorem homTransitionAt_id {k l : (D.reindex i).LaterIndex} (h : k.1 ≤ l.1) :
    D.homTransitionAt i K K h (𝟙 _) = 𝟙 _ :=
  Stacks.DerivedPullback.schemeFactorHom_id_obj _ _ _ _ K

/-- The comparison maps out of the stages `k ≥ i` send identities to identities. -/
theorem homComparisonAt_id (k : (D.reindex i).LaterIndex) :
    D.homComparisonAt i K K k (𝟙 _) = 𝟙 _ :=
  Stacks.DerivedPullback.schemeFactorHom_id_obj _ _ _ _ K

end At

/-- Two stages of the reindexed situation have a common later stage. -/
theorem exists_reindex_ge_ge (k l : (D.reindex i).LaterIndex) :
    ∃ m : (D.reindex i).LaterIndex, k.1 ≤ m.1 ∧ l.1 ≤ m.1 := by
  obtain ⟨m, hkm, hlm⟩ := directed_of (· ≤ ·) k.1 l.1
  exact ⟨⟨m, k.2.trans hkm⟩, hkm, hlm⟩

variable {i} {K L : DerivedCategory (SheafOfModules.{u}
  (structureSheafRing (D.schemeAt i).toRingedSpace))}

/-- Two morphisms at a stage which are mutually inverse over the limit become mutually inverse
at a later stage. -/
theorem exists_comp_eq_id_homTransitionAt (hKK : D.HomDescentAt i K K)
    {k : (D.reindex i).LaterIndex}
    (φ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L)
    (ψ : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K)
    (h : D.homComparisonAt i K L k φ ≫ D.homComparisonAt i L K k ψ = 𝟙 _) :
    ∃ (l : (D.reindex i).LaterIndex) (hkl : k.1 ≤ l.1),
      ∀ (m : (D.reindex i).LaterIndex) (hlm : l.1 ≤ m.1),
        D.homTransitionAt i K L (hkl.trans hlm) φ ≫ D.homTransitionAt i L K (hkl.trans hlm) ψ =
          𝟙 _ := by
  have e : D.homComparisonAt i K K k (φ ≫ ψ) = D.homComparisonAt i K K k (𝟙 _) :=
    (D.homComparisonAt_comp i K L K k φ ψ).trans (h.trans (D.homComparisonAt_id i K k).symm)
  obtain ⟨l, hkl, hl⟩ := hKK.2 k _ _ e
  refine ⟨l, hkl, fun m hlm => ?_⟩
  have t₁ := D.homTransitionAt_comp i K L K (hkl.trans hlm) φ ψ
  have t₂ := D.homTransitionAt_homTransitionAt i K K hkl hlm (φ ≫ ψ)
  have t₃ := D.homTransitionAt_homTransitionAt i K K hkl hlm (𝟙 _)
  have t₄ := congrArg (D.homTransitionAt i K K hlm) hl
  exact t₁.symm.trans (t₂.symm.trans (t₄.trans (t₃.trans (D.homTransitionAt_id i K _))))

/-- **An isomorphism over the limit descends to a stage.** If the comparison out of the colimit
of derived morphism sets over the stages `k ≥ i` is bijective for the four pairs formed from `K`
and `L`, then every isomorphism `Lfᵢ^*K ≅ Lfᵢ^*L` over the limit is the image of an isomorphism
`Lf_{ki}^*K ≅ Lf_{ki}^*L` at some stage `k ≥ i`. -/
theorem exists_iso_homComparisonAt (hKL : D.HomDescentAt i K L) (hLK : D.HomDescentAt i L K)
    (hKK : D.HomDescentAt i K K) (hLL : D.HomDescentAt i L L)
    (θ : (derivedPullback (D.projection i).toLRSHom.toShHom).obj K ≅
      (derivedPullback (D.projection i).toLRSHom.toShHom).obj L) :
    ∃ (k : (D.reindex i).LaterIndex)
      (c : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ≅
        (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L),
      D.homComparisonAt i K L k c.hom = θ.hom := by
  have t₁ := hKL.1 θ.hom
  obtain ⟨k₁, φ, hφ⟩ := t₁
  have t₂ := hLK.1 θ.inv
  obtain ⟨k₂, ψ, hψ⟩ := t₂
  have t₃ := D.exists_reindex_ge_ge i k₁ k₂
  obtain ⟨k₃, h₁, h₂⟩ := t₃
  have hφ₃ : D.homComparisonAt i K L k₃ (D.homTransitionAt i K L h₁ φ) = θ.hom :=
    (D.homComparisonAt_homTransitionAt i K L h₁ φ).trans hφ
  have hψ₃ : D.homComparisonAt i L K k₃ (D.homTransitionAt i L K h₂ ψ) = θ.inv :=
    (D.homComparisonAt_homTransitionAt i L K h₂ ψ).trans hψ
  have u₁ := D.exists_comp_eq_id_homTransitionAt hKK (D.homTransitionAt i K L h₁ φ)
    (D.homTransitionAt i L K h₂ ψ) ((congrArg₂ (· ≫ ·) hφ₃ hψ₃).trans θ.hom_inv_id)
  obtain ⟨l₁, hl₁, hu₁⟩ := u₁
  have u₂ := D.exists_comp_eq_id_homTransitionAt hLL (D.homTransitionAt i L K h₂ ψ)
    (D.homTransitionAt i K L h₁ φ) ((congrArg₂ (· ≫ ·) hψ₃ hφ₃).trans θ.inv_hom_id)
  obtain ⟨l₂, hl₂, hu₂⟩ := u₂
  have t₄ := D.exists_reindex_ge_ge i l₁ l₂
  obtain ⟨m, hm₁, hm₂⟩ := t₄
  refine ⟨m, ⟨D.homTransitionAt i K L (hl₁.trans hm₁) (D.homTransitionAt i K L h₁ φ),
    D.homTransitionAt i L K (hl₁.trans hm₁) (D.homTransitionAt i L K h₂ ψ),
    hu₁ m hm₁, hu₂ m hm₂⟩, ?_⟩
  exact (D.homComparisonAt_homTransitionAt i K L (hl₁.trans hm₁) _).trans hφ₃

/-! ### The cover of a stage by the stages of two restricted situations -/

section Cover

attribute [local implicit_reducible] restrict

variable (A B : D.X₀.left.Opens) (hA : IsCompact (A : Set D.X₀.left))
  (hB : IsCompact (B : Set D.X₀.left)) (hC : IsCompact ((A ⊓ B : D.X₀.left.Opens) : Set D.X₀.left))

/-- At a stage, the stage of the situation restricted to `A ∩ B` is the intersection of the
stages of the situations restricted to `A` and to `B`. -/
theorem isPullback_restrictToLarger_inf (j : D.LaterIndex) :
    IsPullback (D.restrictToLarger A hA (A ⊓ B) hC inf_le_left j)
      (D.restrictToLarger B hB (A ⊓ B) hC inf_le_right j) (D.restrictToAmbient A hA j)
      (D.restrictToAmbient B hB j) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [D.restrictToLarger_comp_restrictToAmbient, D.restrictToLarger_comp_restrictToAmbient]
  · rw [D.opensRange_restrictToAmbient A hA j,
      D.opensRange_restrictToLarger B hB (A ⊓ B) hC inf_le_right j, ← Scheme.Hom.comp_preimage,
      D.restrictToAmbient_comp_toFixedStage B hB j, Scheme.Hom.comp_preimage,
      Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]

/-- At the limit, the limit of the situation restricted to `A ∩ B` is the intersection of the
limits of the situations restricted to `A` and to `B`. -/
theorem isPullback_restrictToLargerLimit_inf :
    IsPullback (D.restrictToLargerLimit A hA (A ⊓ B) hC inf_le_left)
      (D.restrictToLargerLimit B hB (A ⊓ B) hC inf_le_right) (D.restrictToAmbientLimit A hA)
      (D.restrictToAmbientLimit B hB) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [D.restrictToLargerLimit_comp_restrictToAmbientLimit,
      D.restrictToLargerLimit_comp_restrictToAmbientLimit]
  · rw [D.opensRange_restrictToAmbientLimit A hA,
      D.opensRange_restrictToLargerLimit B hB (A ⊓ B) hC inf_le_right, ← Scheme.Hom.comp_preimage,
      D.restrictToAmbientLimit_comp_limitToFixedStage B hB, Scheme.Hom.comp_preimage,
      Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]

/-- If `A` and `B` cover `X₀`, the stages of the two restricted situations cover a stage. -/
theorem range_restrictToAmbient_union (hAB : A ⊔ B = ⊤) (j : D.LaterIndex) :
    Set.range (D.restrictToAmbient A hA j).base ∪ Set.range (D.restrictToAmbient B hB j).base =
      Set.univ := by
  have hA' := congrArg (fun U : (D.schemeAt j).Opens => (U : Set (D.schemeAt j)))
    (D.opensRange_restrictToAmbient A hA j)
  have hB' := congrArg (fun U : (D.schemeAt j).Opens => (U : Set (D.schemeAt j)))
    (D.opensRange_restrictToAmbient B hB j)
  simp only [Scheme.Hom.coe_opensRange] at hA' hB'
  rw [hA', hB']
  have := congrArg (fun U : D.X₀.left.Opens => (D.toFixedStage j ⁻¹ᵁ U : Set (D.schemeAt j))) hAB
  simpa [Scheme.Hom.preimage_sup] using this

/-- If `A` and `B` cover `X₀`, the limits of the two restricted situations cover the limit. -/
theorem range_restrictToAmbientLimit_union (hAB : A ⊔ B = ⊤) :
    Set.range (D.restrictToAmbientLimit A hA).base ∪
        Set.range (D.restrictToAmbientLimit B hB).base = Set.univ := by
  have hA' := congrArg (fun U : D.limitScheme.Opens => (U : Set D.limitScheme))
    (D.opensRange_restrictToAmbientLimit A hA)
  have hB' := congrArg (fun U : D.limitScheme.Opens => (U : Set D.limitScheme))
    (D.opensRange_restrictToAmbientLimit B hB)
  simp only [Scheme.Hom.coe_opensRange] at hA' hB'
  rw [hA', hB']
  have := congrArg (fun U : D.X₀.left.Opens =>
    (D.limitToFixedStage ⁻¹ᵁ U : Set D.limitScheme)) hAB
  simpa [Scheme.Hom.preimage_sup] using this

end Cover

end AlgebraicGeometry.RelativeDescentSituation

/-- A pullback square of schemes along an open immersion is a pullback square of the underlying
ringed spaces. -/
theorem AlgebraicGeometry.Scheme.isPullback_toShHom {W U V X : Scheme.{u}} {iU : W ⟶ U}
    {iV : W ⟶ V} {jU : U ⟶ X} {jV : V ⟶ X} [IsOpenImmersion jU] (h : IsPullback iU iV jU jV) :
    IsPullback iU.toLRSHom.toShHom iV.toLRSHom.toShHom jU.toLRSHom.toShHom
      jV.toLRSHom.toShHom :=
  (h.map Scheme.forgetToLocallyRingedSpace).map LocallyRingedSpace.forgetToSheafedSpace

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

/-- Relative perfectness of an object at a stage, relative to that stage of the base, at the
canonical certificates. -/
abbrev IsPerfectAt (i : D.LaterIndex)
    (K : DerivedCategory (OXMod.{u, u} (D.schemeAt i).toRingedSpace)) : Prop :=
  let : Flat D.X₀.hom := D.flat
  let : LocallyOfFinitePresentation D.X₀.hom := D.finitePresentation.locallyOfFinitePresentation
  (D.structureMapAt i).IsPerfectRelativeTo (D.canonicalStageCertificates i) K

/-- The structure map of the base of a relative descent situation is flat. -/
private instance flat_X₀_hom (D : RelativeDescentSituation.{u, u} I) : Flat D.X₀.hom := D.flat

/-- The structure map of the base of a relative descent situation is locally of finite
presentation. -/
private instance locallyOfFinitePresentation_X₀_hom (D : RelativeDescentSituation.{u, u} I) :
    LocallyOfFinitePresentation D.X₀.hom :=
  D.finitePresentation.locallyOfFinitePresentation

/-! ### Relative perfectness along the restricted situations -/

section Perfect

/-- The restriction to `U₀` of an object of `D(𝒪_X)` perfect relative to `S` is perfect relative
to `S`. -/
theorem isPerfectRelativeTo_restrictToAmbientLimit (U₀ : D.X₀.left.Opens)
    (hU₀ : IsCompact (U₀ : Set D.X₀.left))
    (E : DerivedCategory (OXMod.{u, u} D.limitScheme.toRingedSpace))
    (hE : letI : Flat D.X₀.hom := D.flat
      letI : LocallyOfFinitePresentation D.X₀.hom :=
        D.finitePresentation.locallyOfFinitePresentation
      D.structureMapLimit.IsPerfectRelativeTo D.canonicalLimitCertificates E) :
    letI : Flat (D.restrict U₀ hU₀).X₀.hom := (D.restrict U₀ hU₀).flat
    letI : LocallyOfFinitePresentation (D.restrict U₀ hU₀).X₀.hom :=
      (D.restrict U₀ hU₀).finitePresentation.locallyOfFinitePresentation
    (D.restrict U₀ hU₀).structureMapLimit.IsPerfectRelativeTo
      (D.restrict U₀ hU₀).canonicalLimitCertificates
      ((derivedPullback (D.restrictToAmbientLimit U₀ hU₀).toLRSHom.toShHom).obj E) := by
  exact (Scheme.Hom.isPerfectRelativeTo_canonical_congr
    (D.restrictToAmbientLimit_comp_snd U₀ hU₀) _).1
    (Scheme.Hom.isPerfectRelativeTo_comp_openImmersion D.structureMapLimit
      (D.restrictToAmbientLimit U₀ hU₀) E hE)

/-- The restriction to a smaller quasi-compact open of an object perfect at a stage is perfect at
that stage. -/
theorem isPerfectAt_restrictToLarger (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
    (V₀ : D.X₀.left.Opens) (hV₀ : IsCompact (V₀ : Set D.X₀.left)) (hVU : V₀ ≤ U₀)
    (i : D.LaterIndex)
    (F : DerivedCategory (OXMod.{u, u} ((D.restrict U₀ hU₀).schemeAt i).toRingedSpace))
    (hF : (D.restrict U₀ hU₀).IsPerfectAt i F) :
    (D.restrict V₀ hV₀).IsPerfectAt i
      ((derivedPullback (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).toLRSHom.toShHom).obj F) := by
  exact (Scheme.Hom.isPerfectRelativeTo_canonical_congr
    (D.restrictToLarger_comp_snd U₀ hU₀ V₀ hV₀ hVU i) _).1
    (Scheme.Hom.isPerfectRelativeTo_comp_openImmersion ((D.restrict U₀ hU₀).structureMapAt i)
      (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i) F hF)

/-- An object at a stage whose restrictions to the stages of the situations restricted to two
quasi-compact opens covering `X₀` are perfect, is perfect. -/
theorem isPerfectAt_of_cover (A B : D.X₀.left.Opens) (hA : IsCompact (A : Set D.X₀.left))
    (hB : IsCompact (B : Set D.X₀.left)) (hAB : A ⊔ B = ⊤) (k : D.LaterIndex)
    (G : DerivedCategory (OXMod.{u, u} (D.schemeAt k).toRingedSpace))
    (hGA : (D.restrict A hA).IsPerfectAt k
      ((derivedPullback (D.restrictToAmbient A hA k).toLRSHom.toShHom).obj G))
    (hGB : (D.restrict B hB).IsPerfectAt k
      ((derivedPullback (D.restrictToAmbient B hB k).toLRSHom.toShHom).obj G)) :
    D.IsPerfectAt k G := by
  exact Scheme.Hom.isPerfectRelativeTo_of_two_openImmersions (D.structureMapAt k)
    (D.restrictToAmbient A hA k) (D.restrictToAmbient B hB k)
    (D.range_restrictToAmbient_union A B hA hB hAB k) G
    ((Scheme.Hom.isPerfectRelativeTo_canonical_congr
      (D.restrictToAmbient_comp_snd A hA k).symm _).1 hGA)
    ((Scheme.Hom.isPerfectRelativeTo_canonical_congr
      (D.restrictToAmbient_comp_snd B hB k).symm _).1 hGB)

end Perfect

/-! ### The union step -/

/-- A commutative square of morphisms of schemes is a commutative square of ringed spaces. -/
theorem toShHom_comp_eq_comp {X Y Y' Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'}
    {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') :
    f.toLRSHom.toShHom ≫ g.toLRSHom.toShHom = f'.toLRSHom.toShHom ≫ g'.toLRSHom.toShHom :=
  congrArg (fun m => m.toLRSHom.toShHom) h

/-- A factorisation of morphisms of schemes is a factorisation of ringed spaces. -/
theorem toShHom_comp_eq {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    (h : f ≫ g = k) : f.toLRSHom.toShHom ≫ g.toLRSHom.toShHom = k.toLRSHom.toShHom :=
  congrArg (fun m => m.toLRSHom.toShHom) h

section Union

open Stacks.Cohomology.GlueingComplexes Stacks.DerivedPullback

/-- The comparison map out of a stage `k ≥ i`, written through the comparison isomorphism of the
factorisation of the projection. -/
theorem homComparisonAt_eq_iff (i : D.LaterIndex)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (D.schemeAt i).toRingedSpace))}
    (k : (D.reindex i).LaterIndex)
    (c : (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.reindexTransition i k).toLRSHom.toShHom).obj L)
    (ψ : (derivedPullback (D.projection i).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.projection i).toLRSHom.toShHom).obj L) :
    D.homComparisonAt i K L k c = ψ ↔
      (factorIso (D.projection (D.reindexLater i k)).toLRSHom.toShHom
          (D.reindexTransition i k).toLRSHom.toShHom (D.projection i).toLRSHom.toShHom
          (toShHom_comp_eq (D.projection_comp_transition k.2))).inv.app K ≫
        (derivedPullback (D.projection (D.reindexLater i k)).toLRSHom.toShHom).map c ≫
        (factorIso (D.projection (D.reindexLater i k)).toLRSHom.toShHom
          (D.reindexTransition i k).toLRSHom.toShHom (D.projection i).toLRSHom.toShHom
          (toShHom_comp_eq (D.projection_comp_transition k.2))).hom.app L = ψ :=
  Iff.rfl

variable (A B : D.X₀.left.Opens) (hA : IsCompact (A : Set D.X₀.left))
  (hB : IsCompact (B : Set D.X₀.left)) (hC : IsCompact ((A ⊓ B : D.X₀.left.Opens) : Set D.X₀.left))

/-- **The glueing step of the union step of Stacks 0DI8.** Let `A` and `B` be quasi-compact opens
covering `X₀`, and suppose the comparison out of the colimit of derived morphism sets is bijective
for objects perfect at a stage of the situation restricted to `A ∩ B`. Given objects `FA`, `FB`
perfect at a stage `i` of the situations restricted to `A` and to `B`, whose pullbacks to the
limits are identified with the restrictions of an object `E` of `D(𝒪_X)`, there is an object
perfect at some stage of `D` whose pullback to the limit is isomorphic to `E`. -/
theorem exists_isPerfectAt_iso_of_cover (hAB : A ⊔ B = ⊤)
    (hFF : ∀ (i : D.LaterIndex)
      (K L : DerivedCategory (OXMod.{u, u} ((D.restrict (A ⊓ B) hC).schemeAt i).toRingedSpace)),
      (D.restrict (A ⊓ B) hC).IsPerfectAt i K → (D.restrict (A ⊓ B) hC).IsPerfectAt i L →
        (D.restrict (A ⊓ B) hC).HomDescentAt i K L)
    (E : DerivedCategory (OXMod.{u, u} D.limitScheme.toRingedSpace)) (i : D.LaterIndex)
    (FA : DerivedCategory (OXMod.{u, u} ((D.restrict A hA).schemeAt i).toRingedSpace))
    (hFA : (D.restrict A hA).IsPerfectAt i FA)
    (FB : DerivedCategory (OXMod.{u, u} ((D.restrict B hB).schemeAt i).toRingedSpace))
    (hFB : (D.restrict B hB).IsPerfectAt i FB)
    (a : (derivedPullback ((D.restrict A hA).projection i).toLRSHom.toShHom).obj FA ≅
      (derivedPullback (D.restrictToAmbientLimit A hA).toLRSHom.toShHom).obj E)
    (b : (derivedPullback ((D.restrict B hB).projection i).toLRSHom.toShHom).obj FB ≅
      (derivedPullback (D.restrictToAmbientLimit B hB).toLRSHom.toShHom).obj E) :
    ∃ (k : D.LaterIndex) (G : DerivedCategory (OXMod.{u, u} (D.schemeAt k).toRingedSpace)),
      D.IsPerfectAt k G ∧
        Nonempty ((derivedPullback (D.projection k).toLRSHom.toShHom).obj G ≅ E) := by
  have hGA := D.isPerfectAt_restrictToLarger A hA (A ⊓ B) hC inf_le_left i FA hFA
  have hGB := D.isPerfectAt_restrictToLarger B hB (A ⊓ B) hC inf_le_right i FB hFB
  have t := (D.restrict (A ⊓ B) hC).exists_iso_homComparisonAt (hFF i _ _ hGA hGB)
    (hFF i _ _ hGB hGA) (hFF i _ _ hGA hGA) (hFF i _ _ hGB hGB)
    (overlapComparison _ _ _ _
      (toShHom_comp_eq_comp (D.restrictToLarger_projection A hA (A ⊓ B) hC inf_le_left i)) _ _ _
      (toShHom_comp_eq_comp (D.restrictToLarger_projection B hB (A ⊓ B) hC inf_le_right i)) _ _
      (Scheme.isPullback_toShHom (D.isPullback_restrictToLargerLimit_inf A B hA hB hC)).w
      FA FB E a b)
  obtain ⟨k, c₀, hc₀⟩ := t
  have : SheafedSpace.IsOpenImmersion (D.restrictToAmbientLimit A hA).toLRSHom.toShHom :=
    (inferInstance : IsOpenImmersion (D.restrictToAmbientLimit A hA))
  have : SheafedSpace.IsOpenImmersion (D.restrictToAmbientLimit B hB).toLRSHom.toShHom :=
    (inferInstance : IsOpenImmersion (D.restrictToAmbientLimit B hB))
  have : SheafedSpace.IsOpenImmersion (D.restrictToAmbient A hA
      ((D.restrict (A ⊓ B) hC).reindexLater i k)).toLRSHom.toShHom :=
    (inferInstance : IsOpenImmersion (D.restrictToAmbient A hA _))
  have : SheafedSpace.IsOpenImmersion (D.restrictToAmbient B hB
      ((D.restrict (A ⊓ B) hC).reindexLater i k)).toLRSHom.toShHom :=
    (inferInstance : IsOpenImmersion (D.restrictToAmbient B hB _))
  have t' := exists_glueing_derivedRestrict_iso_of_homCongr _ _ _
    (toShHom_comp_eq ((D.restrict (A ⊓ B) hC).projection_comp_transition k.2)) _ _ _ _ _ _
    (toShHom_comp_eq ((D.restrict A hA).projection_comp_transition k.2))
    (toShHom_comp_eq_comp (D.restrictToLarger_transition A hA (A ⊓ B) hC inf_le_left k.2).symm)
    (toShHom_comp_eq_comp (D.restrictToLarger_projection A hA (A ⊓ B) hC inf_le_left
      ((D.restrict (A ⊓ B) hC).reindexLater i k)))
    (toShHom_comp_eq_comp (D.restrictToLarger_projection A hA (A ⊓ B) hC inf_le_left i))
    _ _ _ _ _ _
    (toShHom_comp_eq ((D.restrict B hB).projection_comp_transition k.2))
    (toShHom_comp_eq_comp (D.restrictToLarger_transition B hB (A ⊓ B) hC inf_le_right k.2).symm)
    (toShHom_comp_eq_comp (D.restrictToLarger_projection B hB (A ⊓ B) hC inf_le_right
      ((D.restrict (A ⊓ B) hC).reindexLater i k)))
    (toShHom_comp_eq_comp (D.restrictToLarger_projection B hB (A ⊓ B) hC inf_le_right i))
    _ _ FA FB E a b c₀
    (Scheme.isPullback_toShHom (D.isPullback_restrictToLarger_inf A B hA hB hC
      ((D.restrict (A ⊓ B) hC).reindexLater i k)))
    (Scheme.isPullback_toShHom (D.isPullback_restrictToLargerLimit_inf A B hA hB hC))
    (D.range_restrictToAmbientLimit_union A B hA hB hAB)
    (toShHom_comp_eq_comp (D.restrictToAmbient_projection A hA
      ((D.restrict (A ⊓ B) hC).reindexLater i k)).symm)
    (toShHom_comp_eq_comp (D.restrictToAmbient_projection B hB
      ((D.restrict (A ⊓ B) hC).reindexLater i k)).symm) hc₀
  obtain ⟨G, ⟨f⟩, ⟨g⟩, hG⟩ := t'
  refine ⟨(D.restrict (A ⊓ B) hC).reindexLater i k, G,
    D.isPerfectAt_of_cover A B hA hB hAB _ G ?_ ?_, hG⟩
  · exact Scheme.Hom.isPerfectRelativeTo_canonical_of_iso _ f.symm
      ((D.restrict A hA).isPerfectRelativeTo_transition k.2 FA hFA)
  · exact Scheme.Hom.isPerfectRelativeTo_canonical_of_iso _ g.symm
      ((D.restrict B hB).isPerfectRelativeTo_transition k.2 FB hFB)

/-- **The union step of the essential-surjectivity half of Stacks 0DI8, for a cover by two
opens.** Let `A` and `B` be quasi-compact opens covering `X₀`. If every object of `D(𝒪_X)`
perfect relative to `S` is, after restriction to `A` and to `B`, the pullback of an object
perfect at some stage, and the comparison out of the colimit of derived morphism sets is bijective
for objects perfect at a stage of the situation restricted to `A ∩ B`, then every object of
`D(𝒪_X)` perfect relative to `S` is the pullback of an object perfect at some stage. -/
theorem perfectEssentiallySurjectiveCanonical_of_cover (hAB : A ⊔ B = ⊤)
    (hFF : ∀ (i : D.LaterIndex)
      (K L : DerivedCategory (OXMod.{u, u} ((D.restrict (A ⊓ B) hC).schemeAt i).toRingedSpace)),
      (D.restrict (A ⊓ B) hC).IsPerfectAt i K → (D.restrict (A ⊓ B) hC).IsPerfectAt i L →
        (D.restrict (A ⊓ B) hC).HomDescentAt i K L)
    (hPA : D.RestrictPerfectEssentiallySurjective A hA)
    (hPB : D.RestrictPerfectEssentiallySurjective B hB) :
    D.PerfectEssentiallySurjectiveCanonical := by
  unfold RestrictPerfectEssentiallySurjective PerfectEssentiallySurjectiveCanonical
    PerfectEssentiallySurjective at hPA hPB
  unfold PerfectEssentiallySurjectiveCanonical PerfectEssentiallySurjective
  intro E hE
  obtain ⟨iA, FA, hFA, ⟨aA⟩⟩ := hPA _ (D.isPerfectRelativeTo_restrictToAmbientLimit A hA E hE)
  obtain ⟨iB, FB, hFB, ⟨aB⟩⟩ := hPB _ (D.isPerfectRelativeTo_restrictToAmbientLimit B hB E hE)
  obtain ⟨i, hiA, hiB⟩ := D.exists_laterIndex_ge_ge iA iB
  exact D.exists_isPerfectAt_iso_of_cover A B hA hB hC hAB hFF E i _
    ((D.restrict A hA).isPerfectRelativeTo_transition hiA FA hFA) _
    ((D.restrict B hB).isPerfectRelativeTo_transition hiB FB hFB)
    ((factorIso _ _ _ (toShHom_comp_eq ((D.restrict A hA).projection_comp_transition hiA))).app FA
      ≪≫ aA)
    ((factorIso _ _ _ (toShHom_comp_eq ((D.restrict B hB).projection_comp_transition hiB))).app FB
      ≪≫ aB)

end Union

/-- **The union step of the essential-surjectivity half of Stacks 0DI8.** If the comparison out
of the colimit of derived morphism sets is bijective for objects perfect at a stage of every
relative descent situation, then essential surjectivity for the situations restricted to
quasi-compact opens `U₀` and `V₀` of `X₀` gives it for the situation restricted to `U₀ ∪ V₀`. -/
theorem restrictPerfectEssentiallySurjective_sup (U₀ V₀ : D.X₀.left.Opens)
    (hU₀ : IsCompact (U₀ : Set D.X₀.left)) (hV₀ : IsCompact (V₀ : Set D.X₀.left))
    (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
    (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
    (hFF : ∀ (D' : RelativeDescentSituation.{u, u} I) (i : D'.LaterIndex)
      (K L : DerivedCategory (OXMod.{u, u} (D'.schemeAt i).toRingedSpace)),
      D'.IsPerfectAt i K → D'.IsPerfectAt i L → D'.HomDescentAt i K L)
    (hU : D.RestrictPerfectEssentiallySurjective U₀ hU₀)
    (hV : D.RestrictPerfectEssentiallySurjective V₀ hV₀) :
    D.RestrictPerfectEssentiallySurjective (U₀ ⊔ V₀) hsupc := by
  have hA := isCompact_preimage_ι hU₀ (le_sup_left : U₀ ≤ U₀ ⊔ V₀)
  have hB := isCompact_preimage_ι hV₀ (le_sup_right : V₀ ≤ U₀ ⊔ V₀)
  have hC : IsCompact ((D.restrictSupOpenLeft U₀ V₀ ⊓ D.restrictSupOpenRight U₀ V₀ :
      (U₀ ⊔ V₀ : D.X₀.left.Opens).toScheme.Opens) : Set (U₀ ⊔ V₀ : D.X₀.left.Opens).toScheme) :=
    isCompact_preimage_ι hinf ((inf_le_left.trans le_sup_left : U₀ ⊓ V₀ ≤ U₀ ⊔ V₀))
  exact (D.restrict (U₀ ⊔ V₀) hsupc).perfectEssentiallySurjectiveCanonical_of_cover
    (D.restrictSupOpenLeft U₀ V₀) (D.restrictSupOpenRight U₀ V₀) hA hB hC
    (D.restrictSupOpenLeft_sup_restrictSupOpenRight U₀ V₀)
    (hFF ((D.restrict (U₀ ⊔ V₀) hsupc).restrict _ hC))
    ((D.restrictPerfectEssentiallySurjective_restrict_iff hU₀ hsupc hA le_sup_left).2 hU)
    ((D.restrictPerfectEssentiallySurjective_restrict_iff hV₀ hsupc hB le_sup_right).2 hV)

/-- **The essential-surjectivity half of Stacks 0DI8, from full faithfulness.** If the comparison
out of the colimit of derived morphism sets is bijective for objects perfect at a stage of every
relative descent situation, then every object of `D(𝒪_X)` perfect relative to `S` is the pullback
of an object perfect at some stage. The induction of Stacks 08DR runs from the affine case over
affine opens of the base, `restrictPerfectEssentiallySurjective_of_isAffineOpenOverAffine`,
through the union step `restrictPerfectEssentiallySurjective_sup`. -/
theorem perfectEssentiallySurjectiveCanonical_of_fullyFaithful
    (hFF : ∀ (D' : RelativeDescentSituation.{u, u} I) (i : D'.LaterIndex)
      (K L : DerivedCategory (OXMod.{u, u} (D'.schemeAt i).toRingedSpace)),
      D'.IsPerfectAt i K → D'.IsPerfectAt i L → D'.HomDescentAt i K L) :
    D.PerfectEssentiallySurjectiveCanonical :=
  (D.perfectEssentiallySurjectiveCanonical_restrict_top_iff D.isCompact_top_X₀).1
    (D.restrictPerfectEssentiallySurjective_top
      (fun V₀ hV₀ hQ => D.restrictPerfectEssentiallySurjective_of_isAffineOpenOverAffine V₀ hV₀ hQ)
      (fun U₀ V₀ hU₀ hV₀ _ hinf hsupc hU hV _ =>
        D.restrictPerfectEssentiallySurjective_sup U₀ V₀ hU₀ hV₀.isCompact hinf hsupc hFF hU hV)
      D.isCompact_top_X₀)

end AlgebraicGeometry.RelativeDescentSituation

end
