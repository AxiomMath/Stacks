module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimensionParts
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupGysinFundamental

/-!
# The blow up formula on an arbitrary class of the centre

Let `i : Z ⟶ X` be a regular closed immersion, `b : X' ⟶ X` the blowing up with centre `Z`,
`j : E ⟶ X'` the exceptional divisor, `π : E ⟶ Z`, and `𝓕` the excess bundle of Tag 0FVA. When
`𝓕^∨` has constant rank `s` and `π` constant relative dimension `s`, the blow up formula reads

  `b^!(i_*β) = j_*(c_s(𝓕^∨) ∩ π^*β)`

for **every** class `β` of `Z`. For `β = [Z]_e` and `Z` of dimension at most `e` this is
`Stacks.Chow.capTarget_lciGysinClass_blowUpToBase_pushforward`; no bound on the dimension of `Z`
is needed here, since `π^*β` is not rewritten as a fundamental class. This is what the proof of
[Stacks, Tag 0FIH] needs when `X` is not equidimensional.

## Main results

* `Stacks.Chow.capTarget_bivariantCompositeOfInvertible_flatPullback`: `(x ∘ π^*) ∩ β = x ∩ π^*β`.
* `Stacks.Chow.capTarget_lciGysinClass_blowUpToBase_pushforward_flatPullback`:
  `b^!(i_*β) = j_*(c_s(𝓕^∨) ∩ π^*β)`.
* `capTarget_smoothGysinClass_blowupHom_of_codimension` (in the namespace
  `Stacks.WeilCohomology.SmoothProjectiveScheme`): the same for smooth projective schemes,
  with `Z` of pure codimension `r ≥ 1` and `s = r - 1`.

## References

* [Stacks Project, Tag 0FVA](https://stacks.math.columbia.edu/tag/0FVA)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-- Flat pullback depends on the structure morphisms of source and target, and on the class, only
up to equality and heterogeneous equality. -/
theorem flatPullbackChow_heq_of_heq_of_eq {A W : Scheme.{u}} {sA sA' : A ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] {sW sW' : W ⟶ C.S}
    [LocallyOfFiniteType sW] [LocallyOfFiniteType sW'] (f : A ⟶ W) [LocallyOfFiniteType f]
    [Flat f] (hsA : sA = sA') (hsW : sW = sW') (hf : f ≫ sW = sA) (hf' : f ≫ sW' = sA') (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sW f hf r hr k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA' sW' f hf' r hr k)
    {α : chowGroup C sW k} {α' : chowGroup C sW' k} (h : α ≍ α') :
    flatPullbackChow C sA sW f hf r hr k hfac α ≍
      flatPullbackChow C sA' sW' f hf' r hr k hfac' α' := by
  subst hsA hsW
  obtain rfl := eq_of_heq h
  rfl

variable {E Z' : Scheme.{u}} (sE : E ⟶ C.S) [LocallyOfFiniteType sE] (sZ : Z' ⟶ C.S)
  [LocallyOfFiniteType sZ] (π : E ⟶ Z') [LocallyOfFiniteType π] [AlgebraicGeometry.Flat π]
  (hπ : π ≫ sZ = sE) (s : ℕ) (hrel : AlgebraicGeometry.RelativeDimension π s)

/-- **`(x ∘ π^*) ∩ β = x ∩ π^*β`.** For a flat `π : E ⟶ Z'` of relative dimension `s` and
`x ∈ A^s(E)`, the degree-`0` class `x ∘ π^* ∈ A^0(E ⟶ Z')` caps a class `β ∈ A_e(Z')` to
`x ∩ π^*β ∈ A_e(E)`. -/
theorem capTarget_bivariantCompositeOfInvertible_flatPullback
    (x : chowCohomologyComponent C (gysinSystemOfInvertible C) sE (s : ℤ)) (e : ℤ)
    (β : chowGroup C sZ e) :
    (BivariantClass.copy C (gysinSystemOfInvertible C) sE sZ (Category.id_comp π) _ hπ
        (by ring : (s : ℤ) + -(s : ℤ) = 0)
        (bivariantCompositeOfInvertible C sE sE sZ (𝟙 E) π (Category.id_comp sE) hπ (s : ℤ)
          (-(s : ℤ)) x (flatPullbackBivariantClassOfInvertible C sE sZ π hπ s hrel))).capTarget
        C (gysinSystemOfInvertible C) sE sZ π hπ 0 e β ≍
      chowCohomologyCap C (gysinSystemOfInvertible C) sE (s : ℤ) x (e + s)
        (flatPullbackChow C sE sZ π hπ s hrel e (flatPullbackDescends C sE sZ π hπ s hrel e)
          β) := by
  rw [BivariantClass.capTarget]
  set φ := pullback.fst π (𝟙 Z')
  have hφiso : (pullbackIdIso π).inv = φ := pullbackIdIso_inv_eq_fst π
  have : IsIso φ := hφiso ▸ inferInstance
  have hφπ : φ ≫ π = pullback.snd π (𝟙 Z') := by
    rw [pullback.condition, Category.comp_id]
  -- `π^*β` at the test scheme `𝟙 Z'` is the flat pullback along `P = E ×_{Z'} Z' ⟶ Z'`
  have hpb := IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
    (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sE sZ π hπ s hrel) (𝟙 Z') e
    (chowGroupCongr C (Category.id_comp sZ).symm e β)
  -- the cap of the composite is the operation of `x` on that pullback
  have hA := ((BivariantClass.copy_cap C _ sE sZ (Category.id_comp π) _ hπ
      (by ring : (s : ℤ) + -(s : ℤ) = 0) _ (𝟙 Z') e
      (chowGroupCongr C (Category.id_comp sZ).symm e β)).trans
    (BivariantClass.id_bivariantCompositeOfInvertible_cap_heq x
      (flatPullbackBivariantClassOfInvertible C sE sZ π hπ s hrel) (𝟙 Z') e _)).trans
    (BivariantClass.idRule_heq_of_heq x φ (by ring : e - -(s : ℤ) = e + s) hpb)
  -- the flat pullback along `P ⟶ Z'`, pushed forward along `φ : P ≅ E`, is `π^*β`
  have hsnd : pullback.snd π (𝟙 Z') ≫ sZ = φ ≫ sE := by rw [← hφπ, Category.assoc, hπ]
  have hrel' : AlgebraicGeometry.RelativeDimension (pullback.snd π (𝟙 Z')) s :=
    relativeDimension_pullbackSnd π hrel (𝟙 Z')
  have hiso := chowPushforwardOfIso_flatPullbackChow_eq_of_comp C (φ ≫ sE) sE sE sZ
    (pullback.snd π (𝟙 Z')) hsnd π hπ φ rfl (𝟙 E) (Category.id_comp sE) π hφπ
    (Category.id_comp π) s hrel' hrel e (flatPullbackDescends C _ _ _ _ _ _ e)
    (flatPullbackDescends C _ _ _ _ _ _ e) β
  rw [chowPushforwardOfIso_id] at hiso
  have hB := BivariantClass.idRule_chowPushforwardOfIso_heq x (𝟙 E) φ φ (Category.comp_id φ)
    (sT := 𝟙 E ≫ sE) rfl (sT' := φ ≫ 𝟙 E ≫ sE) rfl (e + s)
    (flatPullbackChow C (φ ≫ 𝟙 E ≫ sE) (𝟙 Z' ≫ sZ) (pullback.snd π (𝟙 Z'))
      (by rw [Category.id_comp, Category.id_comp, hsnd]) s hrel' e
      (flatPullbackDescends C _ _ _ _ _ _ e) (chowGroupCongr C (Category.id_comp sZ).symm e β))
    (chowGroupCongr C (Category.id_comp sE).symm (e + s)
      (flatPullbackChow C sE sZ π hπ s hrel e (flatPullbackDescends C sE sZ π hπ s hrel e) β))
    (by
      refine (chowGroupCongr_heq C _ _ _).trans ?_
      rw [hiso]
      exact chowPushforwardOfIso_heq_of_eq C _ _ rfl _ _ (by rw [Category.id_comp])
        (Category.id_comp sE).symm rfl
        (flatPullbackChow_heq_of_heq_of_eq C (pullback.snd π (𝟙 Z')) (by rw [Category.id_comp])
          (Category.id_comp sZ).symm _ _ s hrel' e (flatPullbackDescends C _ _ _ _ _ _ e)
          (flatPullbackDescends C _ _ _ _ _ _ e) (chowGroupCongr_heq C _ e β).symm))
    (flatPullbackChow C (φ ≫ sE) (𝟙 Z' ≫ sZ) (pullback.snd π (𝟙 Z'))
      (by rw [Category.id_comp, hsnd]) s hrel' e
      (flatPullbackDescends C _ _ _ _ _ _ e) (chowGroupCongr C (Category.id_comp sZ).symm e β))
    (flatPullbackChow_heq_of_heq_of_eq C (pullback.snd π (𝟙 Z')) (by rw [Category.id_comp]) rfl
      _ _ s hrel' e (flatPullbackDescends C _ _ _ _ _ _ e) (flatPullbackDescends C _ _ _ _ _ _ e)
      HEq.rfl)
  refine HEq.trans ?_ (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sE (s : ℤ) x (e + s) _).symm
  refine HEq.trans ?_ hB.symm
  exact chowPushforwardOfIso_heq_of_eq C _ _ hφiso _ _ rfl (Category.id_comp sE).symm (by ring) hA

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The blow up formula on an arbitrary class of the centre.** If `𝓕^∨` has constant rank `s`
and `π` constant relative dimension `s`, the degree-`0` term of the Gysin map `b^!` of the blowing
up, capped at the test scheme `i : Z ⟶ X` with `β ∈ A_e(Z)`, is `c_s(𝓕^∨) ∩ π^*β` on
`E = X' ×_X Z`. -/
theorem cap_lciGysinClass_blowUpToBase_flatPullback (hi : IsRegularImmersion i)
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
    (e : ℤ) (β : chowGroup C (i ≫ sX) e) :
    haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
    haveI := isFiniteLocallyFree_blowupExcessConormal i hi hG
    haveI := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
    (completedBivariantSequenceOfInvertible C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
        (Stacks.Blowup.blowUpToBase i.ker) rfl
        (lciGysinMap C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX rfl
          (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi) hG) 0).cap i e
        β ≍
      chowCohomologyCap C (gysinSystemOfInvertible C)
        (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫ Stacks.Blowup.blowUpToBase i.ker ≫ sX)
        (s : ℤ) (totalChernOfFiniteLocallyFree C _ (dualSheaf (blowupExcessConormal i)) s) (e + s)
        (flatPullbackChow C _ (i ≫ sX) (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i)
          (pullbackSnd_comp_structureMorphism_eq C _ sX _ rfl i) s hπ e
          (flatPullbackDescends C _ _ _ _ _ _ e) β) := by
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  have := isFiniteLocallyFree_blowupExcessConormal i hi hG
  have := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
  rw [← bivariantRestriction_capTarget (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C),
    bivariantRestriction_lciGysinClass_blowUpToBase C i hi sX hG s hF hπ]
  exact capTarget_bivariantCompositeOfInvertible_flatPullback C _ _ _ _ s hπ _ e β

/-- **`b^!(i_*β) = j_*(c_s(𝓕^∨) ∩ π^*β)`** for every class `β ∈ A_e(Z)`, when `𝓕^∨` has
constant rank `s` and `π` constant relative dimension `s`: a bivariant class commutes with proper
pushforward (Stacks 0B76 (1)) and the blow up formula computes the cap at the test scheme `Z`. -/
theorem capTarget_lciGysinClass_blowUpToBase_pushforward_flatPullback (hi : IsRegularImmersion i)
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
    (e : ℤ) (β : chowGroup C (i ≫ sX) e) :
    haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
    haveI := isFiniteLocallyFree_blowupExcessConormal i hi hG
    haveI := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
    (completedBivariantSequenceOfInvertible C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
        (Stacks.Blowup.blowUpToBase i.ker) rfl
        (lciGysinMap C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX rfl
          (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi) hG) 0).capTarget
        C (gysinSystemOfInvertible C) (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
        (Stacks.Blowup.blowUpToBase i.ker) rfl 0 e
        (properChowPushforward C (i ≫ sX) sX i rfl e (properPushforwardDescends C _ _ _ _ _) β) ≍
      properChowPushforward C
        (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫ Stacks.Blowup.blowUpToBase i.ker ≫ sX)
        (Stacks.Blowup.blowUpToBase i.ker ≫ sX)
        (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i) rfl ((e + s) - s)
        (properPushforwardDescends C _ _ _ _ _)
        (chowCohomologyCap C (gysinSystemOfInvertible C)
          (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫ Stacks.Blowup.blowUpToBase i.ker ≫
            sX)
          (s : ℤ) (totalChernOfFiniteLocallyFree C _ (dualSheaf (blowupExcessConormal i)) s)
          (e + s)
          (flatPullbackChow C _ (i ≫ sX) (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i)
            (pullbackSnd_comp_structureMorphism_eq C _ sX _ rfl i) s hπ e
            (flatPullbackDescends C _ _ _ _ _ _ e) β)) := by
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  have := isFiniteLocallyFree_blowupExcessConormal i hi hG
  have := isFiniteLocallyFree_dualSheaf (blowupExcessConormal i) this
  set b := Stacks.Blowup.blowUpToBase i.ker
  set c := completedBivariantSequenceOfInvertible C (b ≫ sX) sX b rfl
    (lciGysinMap C (b ≫ sX) sX rfl
      (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi) hG) 0
  have hcap := cap_lciGysinClass_blowUpToBase_flatPullback C i hi sX hG s hF hπ e β
  set h' := baseChangeMapOfEq b (𝟙 X) i i (Category.comp_id i)
  have hsq := isPullback_baseChangeMapOfEq b (𝟙 X) i i (Category.comp_id i)
  have hfst := baseChangeMapOfEq_fst b (𝟙 X) i i (Category.comp_id i)
  have : IsProper h' := MorphismProperty.of_isPullback hsq (P := @IsProper) inferInstance
  -- `c` commutes with the pushforward along `i`
  have hnat := c.proper_naturality_of_test_eq (𝟙 X) i i (Category.comp_id i) h' hsq hfst e
    (by rw [Category.id_comp]) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) β
  rw [BivariantClass.capTarget,
    properChowPushforward_chowGroupCongr C rfl (Category.id_comp sX).symm i rfl
      (by rw [Category.id_comp]) e _ (properPushforwardDescends C _ _ _ _ _)]
  rw [show chowGroupCongr C (rfl : i ≫ sX = i ≫ sX) e β = β from rfl, hnat]
  have hv : (pullbackIdIso b).inv = pullback.fst b (𝟙 X) := pullbackIdIso_inv_eq_fst b
  have hj : h' ≫ (pullbackIdIso b).inv = pullback.fst b i := by rw [hv, hfst]
  rw [chowPushforwardOfIso, ← AddMonoidHom.comp_apply, properChowPushforward_comp]
  exact properChowPushforward_heq_of_morphism_eq C _ _ hj rfl _ _ (by ring) _ _ hcap

end Stacks.Chow

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

open Stacks.Chow

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left] {r : ℕ}
  (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
    Order.coheight (i.hom.left z) = r)

include hr in
/-- **The blow up formula `b^!(i_*β) = j_*(c_{r-1}(𝓕^∨) ∩ π^*β)`** for a closed immersion
`i : Z ⟶ X` of smooth projective schemes over `k` whose components all have codimension `r ≥ 1`,
`X` not necessarily equidimensional, and every class `β ∈ CH_e(Z)`: the degree-`0` Gysin class of
the blowing up `b` (Stacks 0FF3) capped with `i_*β` (Tag 0FVA, with `𝓕^∨` of rank `r - 1` and
`π` of relative dimension `r - 1`). -/
theorem capTarget_smoothGysinClass_blowupHom_of_codimension (hr0 : 0 < r) (e : ℤ)
    (β : chowGroup (fieldChowSituation k) Z.obj.hom e) :
    (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
        (Over.w (blowupHom i).hom) 0).capTarget (fieldChowSituation k)
        (gysinSystemOfInvertible _) _ _ _ _ 0 e
        (properChowPushforward (fieldChowSituation k) Z.obj.hom X.obj.hom i.hom.left (Over.w i.hom)
          e (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _) β) ≍
      properChowPushforward (fieldChowSituation k) (exceptionalObj i).obj.hom
        (blowupObj i).obj.hom (exceptionalHom i).hom.left (Over.w (exceptionalHom i).hom)
        ((e + ((r - 1 : ℕ) : ℤ)) - ((r - 1 : ℕ) : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _)
          (exceptionalObj i).obj.hom ((r - 1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) (exceptionalObj i).obj.hom
            (dualSheaf (excessConormal i)) (r - 1)) (e + ((r - 1 : ℕ) : ℤ))
          (flatPullbackChow (fieldChowSituation k) (exceptionalObj i).obj.hom Z.obj.hom
            (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom) (r - 1)
            (relativeDimension_exceptionalProj_of_codimension i hr hr0) e
            (flatPullbackDescends _ _ _ _ _ _ _ e) β)) := by
  have hi := isRegularImmersion_of_isClosedImmersion i
  have hG := gysinMapExists_blowupHom i
  have : IsLocallyNoetherian (Stacks.Blowup.blowUp i.hom.left.ker) :=
    isLocallyNoetherian (blowupObj i)
  have : IsLocallyNoetherian
      (Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) :=
    isLocallyNoetherian (exceptionalObj i)
  have hFr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (excessConormal i) (r - 1) := isFiniteLocallyFreeOfRank_excessConormal_of_codimension i hr hr0
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    (excessConormal i) (r - 1) hFr
  have hF : ∀ a, Scheme.Modules.rankOnConnectedComponent
      (dualSheaf (excessConormal i)) a = r - 1 :=
    fun a ↦ Scheme.Modules.rankOnConnectedComponent_eq_of_isFiniteLocallyFreeOfRank _ _ a
  have hπ : RelativeDimension
      (pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) (r - 1) :=
    relativeDimension_exceptionalProj_of_codimension i hr hr0
  have hβ : chowGroupCongr (fieldChowSituation k) (Over.w i.hom).symm e β ≍ β :=
    chowGroupCongr_heq _ _ _ _
  have h := capTarget_lciGysinClass_blowUpToBase_pushforward_flatPullback (fieldChowSituation k)
    i.hom.left hi X.obj.hom hG (r - 1) hF hπ e
    (chowGroupCongr (fieldChowSituation k) (Over.w i.hom).symm e β)
  have hL : ∀ (q : Z.obj.left ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType q]
      (hq : i.hom.left ≫ X.obj.hom = q) (y : chowGroup (fieldChowSituation k) q e)
      (y' : chowGroup (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) e) (_ : y ≍ y') hd hd',
      (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
          (Over.w (blowupHom i).hom) 0).capTarget (fieldChowSituation k)
          (gysinSystemOfInvertible _) _ _ _ _ 0 e
          (properChowPushforward (fieldChowSituation k) q X.obj.hom i.hom.left hq e hd y) ≍
        (smoothGysinClass (fieldChowSituation k) (blowupObj i).obj.hom X.obj.hom
          (Over.w (blowupHom i).hom) 0).capTarget (fieldChowSituation k)
          (gysinSystemOfInvertible _) _ _ _ _ 0 e
          (properChowPushforward (fieldChowSituation k) (i.hom.left ≫ X.obj.hom) X.obj.hom
            i.hom.left rfl e hd' y') := by
    rintro q _ rfl y y' hy hd hd'
    cases hy
    rfl
  refine (hL _ (Over.w i.hom) β _ hβ.symm _ _).trans (h.trans ?_)
  have hsE : pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left ≫
      Stacks.Blowup.blowUpToBase i.hom.left.ker ≫ X.obj.hom = (exceptionalObj i).obj.hom := by
    change _ = pullback.snd _ _ ≫ Z.obj.hom
    rw [pullback.condition_assoc, Over.w i.hom]
  have : LocallyOfFiniteType
      (X := Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
      (Y := (fieldChowSituation k).S) (exceptionalObj i).obj.hom :=
    (inferInstance : LocallyOfFiniteType (exceptionalObj i).obj.hom)
  have : IsProper (X := Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
      (Y := (blowupObj i).obj.left)
      (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) :=
    (inferInstance : IsProper (exceptionalHom i).hom.left)
  refine properChowPushforward_heq_of_morphism_eq (fieldChowSituation k)
    (A := Limits.pullback (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
    (B := (blowupObj i).obj.left) (sB := (blowupObj i).obj.hom)
    (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left)
    (pullback.fst (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) rfl hsE _ _ rfl
    _ _ ?_
  have key : ∀ (q : (exceptionalObj i).obj.left ⟶ (fieldChowSituation k).S)
      [LocallyOfFiniteType q] (_ : q = (exceptionalObj i).obj.hom)
      (y : chowGroup (fieldChowSituation k) q (e + ((r - 1 : ℕ) : ℤ)))
      (y' : chowGroup (fieldChowSituation k) (exceptionalObj i).obj.hom (e + ((r - 1 : ℕ) : ℤ)))
      (_ : y ≍ y'),
      chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _) q ((r - 1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) q (dualSheaf (excessConormal i))
            (r - 1)) (e + ((r - 1 : ℕ) : ℤ)) y ≍
        chowCohomologyCap (fieldChowSituation k) (gysinSystemOfInvertible _)
          (exceptionalObj i).obj.hom ((r - 1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) (exceptionalObj i).obj.hom
            (dualSheaf (excessConormal i)) (r - 1)) (e + ((r - 1 : ℕ) : ℤ)) y' := by
    rintro q _ rfl y y' hy
    cases hy
    rfl
  refine @key _ (show LocallyOfFiniteType (pullback.fst (Stacks.Blowup.blowUpToBase
      i.hom.left.ker) i.hom.left ≫ Stacks.Blowup.blowUpToBase i.hom.left.ker ≫ X.obj.hom) from
    inferInstance) hsE _ _ ?_
  exact flatPullbackChow_heq_of_heq_of_eq (fieldChowSituation k)
    (pullback.snd (Stacks.Blowup.blowUpToBase i.hom.left.ker) i.hom.left) hsE (Over.w i.hom) _ _
    (r - 1) hπ e _ _ hβ

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
