module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityComparison

/-!
# The class at infinity is unchanged by a proper modification

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `b : W ⟶ 𝐏¹_X` be a proper morphism which is an isomorphism over
`𝐀¹_X`. Stacks 0F9J attaches to `b` a canonical class `C ∈ A⁰(W_∞ ⟶ X)`, where `W_∞ ⊆ W` is the
inverse image of the divisor at infinity: on a test scheme `t : T ⟶ X` it sends `α ∈ A_k(T)` to
`i_∞^*β`, for any `β ∈ A_{k+1}(W ×_X T)` whose restriction over `b^{-1}(𝐀¹_X)` is the flat
pullback of `α`.

Stacks 0FAQ compares two such classes. Let `g : W' ⟶ W` be proper and an isomorphism over
`𝐀¹_X`, so that `b' = b ∘ g` satisfies the hypotheses of Stacks 0F9J as well, and let
`C' ∈ A⁰(W'_∞ ⟶ X)` be its class. Then

  `g_{∞,*} ∘ C' = C`  in  `A⁰(W_∞ ⟶ X)`,

the left side being the proper pushforward of bivariant classes of Stacks 0EPK along the
restriction `g_∞ : W'_∞ ⟶ W_∞` of `g`.

The proof is the source's. On a test scheme `T`, lift `α` to `β'` on `W' ×_X T`; then
`g_{T,*} β'` lifts `α` on `W ×_X T`, so `C ∩ α = i_∞^*(g_{T,*} β')`, and Stacks 02TA turns that
into `g_{∞,T,*}((i'_∞)^*β') = g_{∞,T,*}(C' ∩ α)`, which is the cap operation of `g_{∞,*} ∘ C'`.
Both steps are the case `φ = g_T` of `Stacks.Chow.gysinCapOfLift_comparison`.

## Main definitions

* `Stacks.Chow.modificationFibreAtInfinityMap` — the restriction `g_∞ : W'_∞ ⟶ W_∞` of `g`.
* `Stacks.Chow.modificationMapBaseChange` — the base change `W' ×_X T ⟶ W ×_X T` of `g`.

## Main results

* `Stacks.Chow.isIso_pullbackSnd_comp_projectiveLineAffineChart` — if `b` and `g` are
  isomorphisms over `𝐀¹_X`, so is `b ∘ g`.
* `Stacks.Chow.gysinAtInfinityClass_properPushforward` — **Stacks 0FAQ**: `g_{∞,*} ∘ C' = C`.

## Implementation notes

The class `C'` is a class for `W'_∞ ⟶ X`, the structure morphism of the fibre at infinity of
`b ∘ g`; the pushforward of Stacks 0EPK along `g_∞` takes a class for the composite
`W'_∞ ⟶ W_∞ ⟶ X`. These two morphisms are equal and not the same term, and
`Stacks.Chow.BivariantClass.congrHom` reads `C'` as a class for the second.

## References

* [Stacks Project, Tag 0FAQ](https://stacks.math.columbia.edu/tag/0FAQ)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The geometry of a further modification -/

section Geometry

variable {X S W W' : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : W' ⟶ W)

/-- If `b` is an isomorphism over `𝐀¹_X` and `g` is an isomorphism over `b^{-1}(𝐀¹_X)`, then
`b ∘ g` is an isomorphism over `𝐀¹_X`. -/
theorem isIso_pullbackSnd_comp_projectiveLineAffineChart
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
    (hg : IsIso (pullback.snd g (pullback.fst b (projectiveLineAffineChart f)))) :
    IsIso (pullback.snd (g ≫ b) (projectiveLineAffineChart f)) := by
  rw [← Iso.inv_hom_id_assoc (pullbackRightPullbackFstIso b (projectiveLineAffineChart f) g)
    (pullback.snd (g ≫ b) (projectiveLineAffineChart f)), pullbackRightPullbackFstIso_hom_snd]
  infer_instance

/-- The restriction `g_∞ : W'_∞ ⟶ W_∞` of `g : W' ⟶ W` to the fibres at infinity of `b ∘ g` and
of `b`. -/
def modificationFibreAtInfinityMap :
    modificationFibreAtInfinity f (g ≫ b) ⟶ modificationFibreAtInfinity f b :=
  pullback.map (g ≫ b) (infinitySection f) b (infinitySection f) g (𝟙 X) (𝟙 _) (by simp)
    (by simp)

/-- `g_∞` lies over `g` under the inclusions of the fibres at infinity. -/
@[reassoc (attr := simp)]
theorem modificationFibreAtInfinityMap_fst :
    modificationFibreAtInfinityMap f b g ≫ modificationInclusionAtInfinity f b =
      modificationInclusionAtInfinity f (g ≫ b) ≫ g :=
  pullback.lift_fst _ _ _

/-- `g_∞` is the base change of `g` along `i_∞`. -/
theorem modificationFibreAtInfinityMap_eq :
    modificationFibreAtInfinityMap f b g =
      (pullbackRightPullbackFstIso b (infinitySection f) g).inv ≫ pullback.snd _ _ := by
  rw [Iso.eq_inv_comp]
  refine pullback.hom_ext ?_ ?_
  · simp [modificationFibreAtInfinityMap, pullback.condition]
  · simp [modificationFibreAtInfinityMap]

/-- If `g` is proper, then so is `g_∞`. -/
instance isProper_modificationFibreAtInfinityMap [IsProper g] :
    IsProper (modificationFibreAtInfinityMap f b g) := by
  rw [modificationFibreAtInfinityMap_eq]
  haveI : IsProper (pullback.snd g (modificationInclusionAtInfinity f b)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback g _) (P := @IsProper) inferInstance
  infer_instance

/-- The structure morphism of `W'_∞` over `X` factors through `g_∞`. -/
theorem modificationProjectionAtInfinity_comp_eq :
    modificationProjectionAtInfinity f (g ≫ b) =
      modificationFibreAtInfinityMap f b g ≫ modificationProjectionAtInfinity f b := by
  simp [modificationProjectionAtInfinity, modificationProjection]

/-- `g_∞` is a morphism over the base. -/
theorem modificationFibreAtInfinityMap_comp_over :
    modificationFibreAtInfinityMap f b g ≫ (modificationProjectionAtInfinity f b ≫ f) =
      modificationProjectionAtInfinity f (g ≫ b) ≫ f := by
  rw [modificationProjectionAtInfinity_comp_eq f b g]
  exact (Category.assoc _ _ _).symm

variable {T : Scheme.{u}} (t : T ⟶ X)

/-- The base change `W' ×_X T ⟶ W ×_X T` of `g : W' ⟶ W` along a test scheme `t : T ⟶ X`. -/
def modificationMapBaseChange :
    modificationBaseChange f (g ≫ b) t ⟶ modificationBaseChange f b t :=
  pullback.map (modificationProjection f (g ≫ b)) t (modificationProjection f b) t g (𝟙 T) (𝟙 X)
    (by simp [modificationProjection]) (by simp)

/-- The base change of `g` lies over `g` under the first projections. -/
@[reassoc (attr := simp)]
theorem modificationMapBaseChange_fst :
    modificationMapBaseChange f b g t ≫ pullback.fst (modificationProjection f b) t =
      pullback.fst (modificationProjection f (g ≫ b)) t ≫ g :=
  pullback.lift_fst _ _ _

/-- The base change of `g` is a morphism over `T`. -/
@[reassoc (attr := simp)]
theorem modificationMapBaseChange_snd :
    modificationMapBaseChange f b g t ≫ pullback.snd (modificationProjection f b) t =
      pullback.snd (modificationProjection f (g ≫ b)) t := by
  simp [modificationMapBaseChange]

/-- The base change of `g` is the comparison of the two spellings of `W' ⟶ X` followed by the
base change of `g` of Stacks 0EPK. -/
theorem modificationMapBaseChange_eq :
    modificationMapBaseChange f b g t =
      (pullback.congrHom (Category.assoc g b _) rfl).hom ≫
        bivariantPushforwardBaseChange g (modificationProjection f b) t := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- If `g` is proper, then so is its base change `W' ×_X T ⟶ W ×_X T`. -/
instance isProper_modificationMapBaseChange [IsProper g] :
    IsProper (modificationMapBaseChange f b g t) := by
  rw [modificationMapBaseChange_eq]
  infer_instance

/-- The base change of `g` is compatible with the maps to `𝐏¹_S`. -/
theorem modificationMapBaseChange_toRelativeLine :
    modificationMapBaseChange f b g t ≫ modificationBaseChangeToRelativeLine f b t =
      modificationBaseChangeToRelativeLine f (g ≫ b) t := by
  simp [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine]

/-- The morphism of base-changed fibres at infinity induced by `g`: the comparison of the two
spellings of `W'_∞ ⟶ X` followed by the base change of `g_∞` of Stacks 0EPK. -/
abbrev modificationInfinityMapBaseChange :
    pullback (modificationProjectionAtInfinity f (g ≫ b)) t ⟶
      pullback (modificationProjectionAtInfinity f b) t :=
  (pullback.congrHom (modificationProjectionAtInfinity_comp_eq f b g) rfl).hom ≫
    bivariantPushforwardBaseChange (modificationFibreAtInfinityMap f b g)
      (modificationProjectionAtInfinity f b) t

/-- The morphism of base-changed fibres at infinity is compatible with the base change of `g`. -/
theorem modificationInfinityMapBaseChange_comp :
    modificationInfinityMapBaseChange f b g t ≫ modificationInfinityBaseChange f b t =
      modificationInfinityBaseChange f (g ≫ b) t ≫ modificationMapBaseChange f b g t := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, modificationInfinityBaseChange_comp_fst,
      modificationMapBaseChange_fst]
    rw [← Category.assoc (modificationInfinityBaseChange f (g ≫ b) t),
      modificationInfinityBaseChange_comp_fst]
    simp
  · simp only [Category.assoc, modificationInfinityBaseChange_comp_snd,
      modificationMapBaseChange_snd]
    simp

end Geometry

/-! ### Stacks 0FAQ -/

section Specialization

variable (C : ChowSituation.{u}) {X W W' : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (g : W' ⟶ W) [IsProper g]
  (hg : IsIso (pullback.snd g (pullback.fst b (projectiveLineAffineChart f))))

/-- **Stacks 0FAQ.** Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, and let
`g : W' ⟶ W` be proper and an isomorphism over `𝐀¹_X`. Let `C' ∈ A⁰(W'_∞ ⟶ X)` and
`C ∈ A⁰(W_∞ ⟶ X)` be the classes of Stacks 0F9J for `b ∘ g` and for `b`
(`Stacks.Chow.gysinAtInfinityClass`). Then `g_{∞,*} ∘ C' = C`, the left side being the proper
pushforward of Stacks 0EPK along `g_∞ : W'_∞ ⟶ W_∞`. -/
@[stacks 0FAQ "g_{∞,*} ∘ C' = C for the canonical classes of Lemma 0F9J"]
theorem gysinAtInfinityClass_properPushforward :
    bivariantProperPushforwardOfInvertible C (modificationProjectionAtInfinity f (g ≫ b) ≫ f)
        (modificationProjectionAtInfinity f b ≫ f) f (modificationFibreAtInfinityMap f b g)
        (modificationProjectionAtInfinity f b) (modificationFibreAtInfinityMap_comp_over f b g)
        rfl 0
        ((gysinAtInfinityClass C f (g ≫ b)
            (isIso_pullbackSnd_comp_projectiveLineAffineChart f b g hA hg)).congrHom
          (modificationProjectionAtInfinity_comp_eq f b g)
          (comp_comp_structureMorphism_eq (modificationFibreAtInfinityMap_comp_over f b g) rfl)) =
      gysinAtInfinityClass C f b hA := by
  have hA' := isIso_pullbackSnd_comp_projectiveLineAffineChart f b g hA hg
  refine BivariantClass.ext C _ (modificationProjectionAtInfinity f b ≫ f) f
    (modificationProjectionAtInfinity f b) rfl 0 ?_
  intro T t _ k α
  rw [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply,
    BivariantClass.congrHom_cap, gysinAtInfinityClass_cap, gysinAtInfinityClass_cap]
  have hT : t ≫ f = t ≫ f := rfl
  have hφover := comp_modificationBaseChangeOver_of_comp_snd (modificationMapBaseChange f b g t) hT
    (modificationMapBaseChange_snd f b g t)
  have hInf := comp_modificationInfinityBaseChangeOver_of_comp
    (modificationMapBaseChange f b g t) hφover (modificationInfinityMapBaseChange f b g t)
    (modificationInfinityMapBaseChange_comp f b g t)
  have key := gysinCapOfLift_comparison C (modificationMapBaseChange f b g t)
    (modificationInfinityMapBaseChange f b g t) hT hA' hA (modificationMapBaseChange_snd f b g t)
    (modificationMapBaseChange_toRelativeLine f b g t)
    (modificationInfinityMapBaseChange_comp f b g t) k α
  change gysinCapAtInfinity C f b hA t k α = _ at key
  rw [key]
  refine eq_of_heq ?_
  refine (properChowPushforward_heq_congr C _ _ _ _ (sub_zero k) _
    (properPushforwardDescends C _ _ _ _ _) _
    (chowPushforwardOfIso C _ _ _
      (pullback_congrHom_hom_comp_fst_comp (modificationProjectionAtInfinity_comp_eq f b g) t) k
      (gysinCapAtInfinity C f (g ≫ b) hA' t k α)) ?_).trans ?_
  · exact properChowPushforward_heq_congr C _ _ _ _ (sub_zero k) _ _ _ _
      (chowGroupDegreeEquiv_heq C _ _ _)
  · refine (heq_of_eq (properChowPushforward_comp_apply C _ _ _ _ _
      (modificationInfinityMapBaseChange f b g t) rfl _ _ hInf k _ _
      (properPushforwardDescends C _ _ _ _ _) _).symm).trans ?_
    exact (chowGroupDegreeEquiv_heq C _ _ _).symm

end Specialization

end Stacks.Chow

end
