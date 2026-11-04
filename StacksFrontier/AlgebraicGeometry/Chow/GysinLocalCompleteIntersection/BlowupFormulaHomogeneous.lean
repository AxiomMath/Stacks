module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BlowupFormula
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedHomogeneousComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionCompleted
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseCommute
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedProductRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed

/-!
# The blow up formula in a single degree

Let `i : Z ⟶ X` be a regular closed immersion of schemes locally of finite type over the base,
`b : X' ⟶ X` the blowing up with centre `Z`, `E = X' ×_X Z` with `j : E ⟶ X'` and `π : E ⟶ Z`,
and `𝓕 = Ker(π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'})`. The blow up formula of Stacks 0FVA,
`res(b^!) = c_top(𝓕^∨) ∘ π^*` in `A^*(E ⟶ Z)^∧`
(`Stacks.Chow.completedBivariantRestriction_lciGysinMap_blowUpToBase`), is an identity of completed
classes. When `𝓕` has constant rank `s` and `π` constant relative dimension `s` (the situation of
Lemma 0FIH, with `s = r - 1` for a centre of pure codimension `r`), both sides are concentrated in
degree `0`, and the identity reads, in `A^0(E ⟶ Z)`,

  `res((b^!)_0) = c_s(𝓕^∨) ∘ π^*`.

## Main results

* `Stacks.Chow.bivariantRestriction_lciGysinClass_blowUpToBase`: the identity above.

## References

* [Stacks Project, Tag 0FVA](https://stacks.math.columbia.edu/tag/0FVA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The sequence of a transported completed class is the transported sequence. -/
theorem completedBivariantSequenceOfInvertible_copy_heq {W Y : Scheme.{u}} {sW : W ⟶ C.S}
    [LocallyOfFiniteType sW] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] [IsLocallyNoetherian W]
    [IsLocallyNoetherian Y] {f f' : W ⟶ Y}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sW)
    (hf' : f' ≫ sY = sW) (c : completedBivariantGroup C (gysinSystemOfInvertible C) sW sY f hf)
    (n : ℤ) :
    completedBivariantSequenceOfInvertible C sW sY f' hf'
        (completedBivariantGroup.copy C hff hf hf' c) n ≍
      completedBivariantSequenceOfInvertible C sW sY f hf c n := by
  subst hff
  rfl

/-- **Stacks 0FVA in degree `0`.** If `𝓕^∨` has rank `s` on every connected component of `E` and
`π : E ⟶ Z` has relative dimension `s`, then the restriction along `i` of the degree-`0` term of
the Gysin map `b^!` of the blowing up is `c_s(𝓕^∨) ∘ π^*`. -/
theorem bivariantRestriction_lciGysinClass_blowUpToBase (hi : IsRegularImmersion i)
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsLocallyNoetherian (Stacks.Blowup.blowUp i.ker)]
    [IsLocallyNoetherian (pullback (Stacks.Blowup.blowUpToBase i.ker) i)]
    (hG : GysinMapExists (Stacks.Blowup.blowUpToBase i.ker)) (s : ℕ)
    (hF : haveI := isFiniteLocallyFree_blowupExcessConormal i hi hG
          haveI := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
          ∀ a, Scheme.Modules.rankOnConnectedComponent (dualSheaf (blowupExcessConormal i)) a = s)
    (hπ : haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
      AlgebraicGeometry.RelativeDimension
        (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) s) :
    haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
    haveI := isFiniteLocallyFree_blowupExcessConormal i hi hG
    haveI := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
    bivariantRestriction C (gysinSystemOfInvertible C) (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
        (Stacks.Blowup.blowUpToBase i.ker) rfl i 0
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (completedBivariantSequenceOfInvertible C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
          (Stacks.Blowup.blowUpToBase i.ker) rfl
          (lciGysinMap C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX rfl
            (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi) hG) 0) =
      BivariantClass.copy C (gysinSystemOfInvertible C) _ _ (Category.id_comp _) _
        (pullbackSnd_comp_structureMorphism_eq C _ sX _ rfl i) (by ring : (s : ℤ) + -(s : ℤ) = 0)
        (bivariantCompositeOfInvertible C
          (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫
            Stacks.Blowup.blowUpToBase i.ker ≫ sX)
          (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫
            Stacks.Blowup.blowUpToBase i.ker ≫ sX)
          (i ≫ sX) (𝟙 _) (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C _ sX _ rfl i) (s : ℤ) (-(s : ℤ))
          (totalChernOfFiniteLocallyFree C _ (dualSheaf (blowupExcessConormal i)) s)
          (flatPullbackBivariantClassOfInvertible C _ (i ≫ sX)
            (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i)
            (pullbackSnd_comp_structureMorphism_eq C _ sX _ rfl i) s hπ)) := by
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  have := isFiniteLocallyFree_blowupExcessConormal i hi hG
  have := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
  have h := congrArg (fun c ↦ completedBivariantSequenceOfInvertible C _ _ _ _ c 0)
    (completedBivariantRestriction_lciGysinMap_blowUpToBase C i hi sX hG)
  rw [completedBivariantSequenceOfInvertible_completedBivariantRestriction] at h
  rw [h]
  refine eq_of_heq ((completedBivariantSequenceOfInvertible_copy_heq C _ _ _ _ 0).trans ?_)
  rw [topChernClassOfInvertible_eq_toCompleted C _ _ s hF,
    completedFlatPullbackOfSmooth_eq_toCompleted C _ _ _ _ s hπ,
    completedBivariantCompositeOfInvertible_toCompleted C _ _ _ _ _ _ _
      (by ring : (s : ℤ) + -(s : ℤ) = 0),
    completedBivariantSequenceOfInvertible_toCompleted_self]
  exact (BivariantClass.copy_heq _ _ _ _ _).trans (BivariantClass.copy_heq _ _ _ _ _).symm

section Cap

/-- Proper pushforward along equal morphisms, from equal structure morphisms and in equal degrees,
of heterogeneously equal classes. -/
theorem properChowPushforward_heq_of_morphism_eq {A B : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sB : B ⟶ C.S} [LocallyOfFiniteType sB]
    (u u' : A ⟶ B) [IsProper u] [IsProper u'] (huu : u = u') (hsA : sA = sA')
    (hu : u ≫ sB = sA) (hu' : u' ≫ sB = sA') {k k' : ℤ} (hk : k = k')
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB u' hu' k')
    {α : chowGroup C sA k} {α' : chowGroup C sA' k'} (hα : α ≍ α') :
    properChowPushforward C sA sB u hu k hfac α ≍
      properChowPushforward C sA' sB u' hu' k' hfac' α' := by
  subst huu hsA hk
  obtain rfl := eq_of_heq hα
  rfl

/-- The fundamental class does not depend on how the structure morphism is written. -/
theorem fundamentalChowClass_congr_heq {T : Scheme.{u}} {sT sT' : T ⟶ C.S} [LocallyOfFiniteType sT]
    [LocallyOfFiniteType sT'] (h : sT = sT') (k : ℤ) :
    fundamentalChowClass C sT k ≍ fundamentalChowClass C sT' k := by
  subst h
  rfl

variable {E Z' : Scheme.{u}} (sE : E ⟶ C.S) [LocallyOfFiniteType sE] (sZ : Z' ⟶ C.S)
  [LocallyOfFiniteType sZ] (π : E ⟶ Z') [LocallyOfFiniteType π] [AlgebraicGeometry.Flat π]
  (hπ : π ≫ sZ = sE) (s : ℕ) (hrel : AlgebraicGeometry.RelativeDimension π s)

/-- **`(x ∘ π^*) ∩ [Z']_e = x ∩ [E]_{e+s}`.** For a flat `π : E ⟶ Z'` of relative dimension `s`
and `x ∈ A^s(E)`, the degree-`0` class `x ∘ π^* ∈ A^0(E ⟶ Z')` caps the fundamental class of
`Z'` in dimension `e ≥ dim Z'` to `x ∩ [E]_{e+s}`, since `π^*[Z']_e = [E]_{e+s}`. -/
theorem capTarget_bivariantCompositeOfInvertible_flatPullback_fundamentalChowClass
    (x : chowCohomologyComponent C (gysinSystemOfInvertible C) sE (s : ℤ)) (e : ℤ)
    (hdim : schemeDeltaDimension C sZ ≤ (e : EInt)) :
    (BivariantClass.copy C (gysinSystemOfInvertible C) sE sZ (Category.id_comp π) _ hπ
        (by ring : (s : ℤ) + -(s : ℤ) = 0)
        (bivariantCompositeOfInvertible C sE sE sZ (𝟙 E) π (Category.id_comp sE) hπ (s : ℤ)
          (-(s : ℤ)) x (flatPullbackBivariantClassOfInvertible C sE sZ π hπ s hrel))).capTarget
        C (gysinSystemOfInvertible C) sE sZ π hπ 0 e (fundamentalChowClass C sZ e) ≍
      chowCohomologyCap C (gysinSystemOfInvertible C) sE (s : ℤ) x (e + s)
        (fundamentalChowClass C sE (e + s)) := by
  rw [BivariantClass.capTarget]
  set φ := pullback.fst π (𝟙 Z')
  have hφiso : (pullbackIdIso π).inv = φ := pullbackIdIso_inv_eq_fst π
  have : IsIso φ := hφiso ▸ inferInstance
  have hP : schemeDeltaDimension C (𝟙 Z' ≫ sZ) ≤ (e : EInt) := by
    have key : ∀ (t : Z' ⟶ C.S) [LocallyOfFiniteType t], t = sZ →
        schemeDeltaDimension C t ≤ (e : EInt) := by
      rintro t _ rfl; exact hdim
    exact key _ (Category.id_comp sZ)
  -- `π^* [Z']_e = [P]_{e+s}`, `P = E ×_{Z'} Z'`
  have hpb : (flatPullbackBivariantClassOfInvertible C sE sZ π hπ s hrel).cap (𝟙 Z') e
      (chowGroupCongr C (Category.id_comp sZ).symm e (fundamentalChowClass C sZ e)) ≍
      fundamentalChowClass C (φ ≫ sE) (e + s) := by
    refine (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ _ _ _ _) _ e _).trans ?_
    have hc : chowGroupCongr C (Category.id_comp sZ).symm e (fundamentalChowClass C sZ e) =
        fundamentalChowClass C (𝟙 Z' ≫ sZ) e :=
      chowGroupCongr_fundamentalChowClass C _ e
    rw [hc, flatPullbackChow_fundamentalChowClass C _ _ _ _ s _ e _ hP]
  -- the cap of the composite is the operation of `x` on `π^* [Z']_e`
  have hA := ((BivariantClass.copy_cap C _ sE sZ (Category.id_comp π) _ hπ
      (by ring : (s : ℤ) + -(s : ℤ) = 0) _ (𝟙 Z') e
      (chowGroupCongr C (Category.id_comp sZ).symm e (fundamentalChowClass C sZ e))).trans
    (BivariantClass.id_bivariantCompositeOfInvertible_cap_heq x
      (flatPullbackBivariantClassOfInvertible C sE sZ π hπ s hrel) (𝟙 Z') e _)).trans
    (BivariantClass.idRule_heq_of_heq x φ (by ring : e - -(s : ℤ) = e + s) hpb)
  -- the operation of `x` commutes with pushforward along the isomorphism `φ : P ≅ E`
  have hB := BivariantClass.idRule_chowPushforwardOfIso_heq x (𝟙 E) φ φ (Category.comp_id φ)
    (sT := 𝟙 E ≫ sE) rfl (sT' := φ ≫ 𝟙 E ≫ sE) rfl (e + s)
    (fundamentalChowClass C (φ ≫ 𝟙 E ≫ sE) (e + s))
    (chowGroupCongr C (Category.id_comp sE).symm (e + s) (fundamentalChowClass C sE (e + s)))
    (by
      rw [chowPushforwardOfIso_fundamentalChowClass]
      exact heq_of_eq (chowGroupCongr_fundamentalChowClass C _ _))
    (fundamentalChowClass C (φ ≫ sE) (e + s))
    (fundamentalChowClass_congr_heq C (by rw [Category.id_comp]) _)
  refine HEq.trans ?_ (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sE (s : ℤ) x (e + s)
    (fundamentalChowClass C sE (e + s))).symm
  refine HEq.trans ?_ hB.symm
  exact chowPushforwardOfIso_heq_of_eq C _ _ hφiso _ _ rfl (Category.id_comp sE).symm (by ring) hA

/-- **The blow up formula on the fundamental class of the centre.** If `Z` has dimension at most
`e`, `𝓕^∨` has constant rank `s` and `π` constant relative dimension `s`, then the degree-`0` term
of the Gysin map `b^!` of the blowing up, capped at the test scheme `i : Z ⟶ X` with `[Z]_e`, is
`c_s(𝓕^∨) ∩ [E]_{e+s}` on `E = X' ×_X Z`. -/
theorem cap_lciGysinClass_blowUpToBase_fundamentalChowClass (hi : IsRegularImmersion i)
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsLocallyNoetherian (Stacks.Blowup.blowUp i.ker)]
    [IsLocallyNoetherian (pullback (Stacks.Blowup.blowUpToBase i.ker) i)]
    (hG : GysinMapExists (Stacks.Blowup.blowUpToBase i.ker)) (s : ℕ)
    (hF : haveI := isFiniteLocallyFree_blowupExcessConormal i hi hG
          haveI := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
          ∀ a, Scheme.Modules.rankOnConnectedComponent (dualSheaf (blowupExcessConormal i)) a = s)
    (hπ : haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
      AlgebraicGeometry.RelativeDimension
        (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) s)
    (e : ℤ) (hdim : schemeDeltaDimension C (i ≫ sX) ≤ (e : EInt)) :
    haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
    haveI := isFiniteLocallyFree_blowupExcessConormal i hi hG
    haveI := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
    (completedBivariantSequenceOfInvertible C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
        (Stacks.Blowup.blowUpToBase i.ker) rfl
        (lciGysinMap C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX rfl
          (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi) hG) 0).cap i e
        (fundamentalChowClass C (i ≫ sX) e) ≍
      chowCohomologyCap C (gysinSystemOfInvertible C)
        (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫ Stacks.Blowup.blowUpToBase i.ker ≫ sX)
        (s : ℤ) (totalChernOfFiniteLocallyFree C _ (dualSheaf (blowupExcessConormal i)) s) (e + s)
        (fundamentalChowClass C _ (e + s)) := by
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  have := isFiniteLocallyFree_blowupExcessConormal i hi hG
  have := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
  rw [← bivariantRestriction_capTarget (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C),
    bivariantRestriction_lciGysinClass_blowUpToBase C i hi sX hG s hF hπ]
  exact capTarget_bivariantCompositeOfInvertible_flatPullback_fundamentalChowClass C _ _ _ _ s hπ
    _ e hdim

/-- **`b^!(i_*[Z]_e) = j_*(c_s(𝓕^∨) ∩ [E]_{e+s})`.** The degree-`0` term of the Gysin map of the
blowing up, capped on `X'` with the class of the centre pushed into `X`, is the pushforward along
`j : E ⟶ X'` of `c_s(𝓕^∨) ∩ [E]_{e+s}`: a bivariant class commutes with proper pushforward
(Stacks 0B76 (1)) and the blow up formula computes the cap at the test scheme `Z`. -/
theorem capTarget_lciGysinClass_blowUpToBase_pushforward (hi : IsRegularImmersion i)
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsLocallyNoetherian (Stacks.Blowup.blowUp i.ker)]
    [IsLocallyNoetherian (pullback (Stacks.Blowup.blowUpToBase i.ker) i)]
    (hG : GysinMapExists (Stacks.Blowup.blowUpToBase i.ker)) (s : ℕ)
    (hF : haveI := isFiniteLocallyFree_blowupExcessConormal i hi hG
          haveI := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
          ∀ a, Scheme.Modules.rankOnConnectedComponent (dualSheaf (blowupExcessConormal i)) a = s)
    (hπ : haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
      AlgebraicGeometry.RelativeDimension
        (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) s)
    (e : ℤ) (hdim : schemeDeltaDimension C (i ≫ sX) ≤ (e : EInt)) :
    haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
    haveI := isFiniteLocallyFree_blowupExcessConormal i hi hG
    haveI := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
    (completedBivariantSequenceOfInvertible C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
        (Stacks.Blowup.blowUpToBase i.ker) rfl
        (lciGysinMap C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX rfl
          (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi) hG) 0).capTarget
        C (gysinSystemOfInvertible C) (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
        (Stacks.Blowup.blowUpToBase i.ker) rfl 0 e
        (properChowPushforward C (i ≫ sX) sX i rfl e (properPushforwardDescends C _ _ _ _ _)
          (fundamentalChowClass C (i ≫ sX) e)) ≍
      properChowPushforward C
        (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫ Stacks.Blowup.blowUpToBase i.ker ≫ sX)
        (Stacks.Blowup.blowUpToBase i.ker ≫ sX)
        (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i) rfl ((e + s) - s)
        (properPushforwardDescends C _ _ _ _ _)
        (chowCohomologyCap C (gysinSystemOfInvertible C)
          (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫ Stacks.Blowup.blowUpToBase i.ker ≫
            sX)
          (s : ℤ) (totalChernOfFiniteLocallyFree C _ (dualSheaf (blowupExcessConormal i)) s)
          (e + s) (fundamentalChowClass C _ (e + s))) := by
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  have := isFiniteLocallyFree_blowupExcessConormal i hi hG
  have := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
  set b := Stacks.Blowup.blowUpToBase i.ker
  set c := completedBivariantSequenceOfInvertible C (b ≫ sX) sX b rfl
    (lciGysinMap C (b ≫ sX) sX rfl
      (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi) hG) 0
  have hcap := cap_lciGysinClass_blowUpToBase_fundamentalChowClass C i hi sX hG s hF hπ e hdim
  set h' := baseChangeMapOfEq b (𝟙 X) i i (Category.comp_id i)
  have hsq := isPullback_baseChangeMapOfEq b (𝟙 X) i i (Category.comp_id i)
  have hfst := baseChangeMapOfEq_fst b (𝟙 X) i i (Category.comp_id i)
  have : IsProper h' := MorphismProperty.of_isPullback hsq (P := @IsProper) inferInstance
  -- `c` commutes with the pushforward along `i`
  have hnat := c.proper_naturality_of_test_eq (𝟙 X) i i (Category.comp_id i) h' hsq hfst e
    (by rw [Category.id_comp]) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (fundamentalChowClass C (i ≫ sX) e)
  rw [BivariantClass.capTarget,
    properChowPushforward_chowGroupCongr C rfl (Category.id_comp sX).symm i rfl
      (by rw [Category.id_comp]) e _ (properPushforwardDescends C _ _ _ _ _)]
  rw [show chowGroupCongr C (rfl : i ≫ sX = i ≫ sX) e (fundamentalChowClass C (i ≫ sX) e) =
    fundamentalChowClass C (i ≫ sX) e from rfl, hnat]
  have hv : (pullbackIdIso b).inv = pullback.fst b (𝟙 X) := pullbackIdIso_inv_eq_fst b
  have hj : h' ≫ (pullbackIdIso b).inv = pullback.fst b i := by rw [hv, hfst]
  rw [chowPushforwardOfIso, ← AddMonoidHom.comp_apply, properChowPushforward_comp]
  exact properChowPushforward_heq_of_morphism_eq C _ _ hj rfl _ _ (by ring) _ _ hcap

end Cap

end Stacks.Chow

end
