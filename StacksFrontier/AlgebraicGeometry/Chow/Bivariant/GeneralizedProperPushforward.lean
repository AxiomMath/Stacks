module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Generalized
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction

/-!
# Proper pushforward as a generalized bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X₂ ⟶ X₁` be a
proper morphism of schemes locally of finite type over `S`. Stacks 0FDU closes by observing that
`f_*` is not a bivariant class in the sense of Stacks 0B76, but that it is one in the generalized
sense of that remark:

  `f_* ∈ A^0(X₁ ⟶ X₁ ⟵ X₂)`.

Concretely, for the diagram `X₁ --id--> X₁ <--f-- X₂` a test scheme `z' : Z' ⟶ X₁` has
`X' = X₁ ×_{X₁} Z'` and `Y' = Z' ×_{X₁} X₂`, and the cap operation is proper pushforward
`A_k(Z' ×_{X₁} X₂) ⟶ A_k(X₁ ×_{X₁} Z')` along the base change of `f`. That element, at the Gysin
system of the first Chern class rule `Stacks.Chow.gysinSystemOfInvertible`, is
`Stacks.Chow.properPushforwardGeneralizedBivariantClass`.

## Main definitions

* `Stacks.Chow.generalizedProperPushforwardMap` — the base change
  `Z' ×_{X₁} X₂ ⟶ X₁ ×_{X₁} Z'` of `f` along a test scheme `z' : Z' ⟶ X₁`; it is proper.
* `Stacks.Chow.generalizedProperPushforwardCap` — proper pushforward along it on Chow groups, read
  in degree `k - 0`.
* `Stacks.Chow.properPushforwardGeneralizedBivariantClass` — **Stacks 0FDU**, the element
  `f_* ∈ A^0(X₁ ⟶ X₁ ⟵ X₂)`.

## Main results

* `Stacks.Chow.generalizedProperPushforwardCap_proper_naturality`,
  `Stacks.Chow.generalizedProperPushforwardCap_flat_naturality` and
  `Stacks.Chow.generalizedProperPushforwardCap_gysin_naturality` — the three compatibilities of
  Stacks 0FDU for the rule `α ↦ f'_* α`.
* `Stacks.Chow.properPushforwardGeneralizedBivariantClass_cap` — the class caps by proper
  pushforward along the base change of `f`.

## Implementation notes

Proper pushforward on Chow groups is taken with the descent of Stacks 02S2, the theorem
`Stacks.Chow.properPushforwardDescends`, and flat pullback with that of Stacks 02S1,
`Stacks.Chow.flatPullbackDescends`.

The cap operation of a generalized bivariant class of degree `0` lands in degree `k - 0`, which is
`k` as an integer but not as a term, so the pushforward is followed by
`Stacks.Chow.chowGroupDegreeEquiv`.

The remark's other assertion, that `f_*` is *not* a bivariant class in the sense of Stacks 0B76,
is a statement about the shape of the operation rather than a proposition: a class of
`A^0(X₂ ⟶ X₁)` maps `A_k(Z')` to `A_k(Z' ×_{X₁} X₂)`, the opposite direction to `f_*`, and there
is no morphism `X₁ ⟶ X₂` to read `f_*` against.

## References

* [Stacks Project, Tag 0FDU](https://stacks.math.columbia.edu/tag/0FDU)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The base change of the proper morphism along a test scheme -/

section Map

variable {X₁ X₂ : Scheme.{u}} (f : X₂ ⟶ X₁)

/-- The base change `Z' ×_{X₁} X₂ ⟶ X₁ ×_{X₁} Z'` of `f : X₂ ⟶ X₁` along a test scheme
`z' : Z' ⟶ X₁`. -/
def generalizedProperPushforwardMap {Z' : Scheme.{u}} (z' : Z' ⟶ X₁) :
    pullback z' f ⟶ pullback (𝟙 X₁) z' :=
  pullback.lift (pullback.snd z' f ≫ f) (pullback.fst z' f) (by simp [pullback.condition])

/-- The base change of `f` followed by the first projection of `X₁ ×_{X₁} Z'` is the projection
`Z' ×_{X₁} X₂ ⟶ X₂` followed by `f`. -/
@[reassoc (attr := simp)]
theorem generalizedProperPushforwardMap_fst {Z' : Scheme.{u}} (z' : Z' ⟶ X₁) :
    generalizedProperPushforwardMap f z' ≫ pullback.fst (𝟙 X₁) z' = pullback.snd z' f ≫ f :=
  pullback.lift_fst _ _ _

/-- The base change of `f` followed by the second projection of `X₁ ×_{X₁} Z'` is the projection
`Z' ×_{X₁} X₂ ⟶ Z'`. -/
@[reassoc (attr := simp)]
theorem generalizedProperPushforwardMap_snd {Z' : Scheme.{u}} (z' : Z' ⟶ X₁) :
    generalizedProperPushforwardMap f z' ≫ pullback.snd (𝟙 X₁) z' = pullback.fst z' f :=
  pullback.lift_snd _ _ _

/-- The base change of `f` is the projection `Z' ×_{X₁} X₂ ⟶ Z'` followed by the inverse of the
isomorphism `X₁ ×_{X₁} Z' ⟶ Z'`. -/
theorem generalizedProperPushforwardMap_eq {Z' : Scheme.{u}} (z' : Z' ⟶ X₁) :
    generalizedProperPushforwardMap f z' =
      pullback.fst z' f ≫ inv (pullback.snd (𝟙 X₁) z') := by
  rw [IsIso.eq_comp_inv, generalizedProperPushforwardMap_snd]

/-- The base change of a proper morphism along a test scheme is proper. -/
instance isProper_generalizedProperPushforwardMap [IsProper f] {Z' : Scheme.{u}}
    (z' : Z' ⟶ X₁) : IsProper (generalizedProperPushforwardMap f z') := by
  rw [generalizedProperPushforwardMap_eq]
  infer_instance

/-- The base changes of `f` along `h ≫ z'` and along `z'` commute with any two comparison
morphisms of the base changes of `h : Z'' ⟶ Z'`. -/
theorem generalizedProperPushforwardMap_comp {Z' Z'' : Scheme.{u}} (z' : Z' ⟶ X₁)
    (h : Z'' ⟶ Z') (hX' : pullback (𝟙 X₁) (h ≫ z') ⟶ pullback (𝟙 X₁) z')
    (hX'fst : hX' ≫ pullback.fst (𝟙 X₁) z' = pullback.fst (𝟙 X₁) (h ≫ z'))
    (hX'snd : hX' ≫ pullback.snd (𝟙 X₁) z' = pullback.snd (𝟙 X₁) (h ≫ z') ≫ h)
    (hY' : pullback (h ≫ z') f ⟶ pullback z' f)
    (hY'fst : hY' ≫ pullback.fst z' f = pullback.fst (h ≫ z') f ≫ h)
    (hY'snd : hY' ≫ pullback.snd z' f = pullback.snd (h ≫ z') f) :
    hY' ≫ generalizedProperPushforwardMap f z' =
      generalizedProperPushforwardMap f (h ≫ z') ≫ hX' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, generalizedProperPushforwardMap_fst, reassoc_of% hY'snd, Category.assoc,
      hX'fst, generalizedProperPushforwardMap_fst]
  · rw [Category.assoc, generalizedProperPushforwardMap_snd, hY'fst, Category.assoc, hX'snd,
      generalizedProperPushforwardMap_snd_assoc]

/-- The square formed by the base changes of `f` along `h ≫ z'` and along `z'` and by two
comparison morphisms of the base changes of `h : Z'' ⟶ Z'` is cartesian. -/
theorem isPullback_generalizedProperPushforwardMap {Z' Z'' : Scheme.{u}} (z' : Z' ⟶ X₁)
    (h : Z'' ⟶ Z') (hX' : pullback (𝟙 X₁) (h ≫ z') ⟶ pullback (𝟙 X₁) z')
    (sqX : IsPullback (pullback.snd (𝟙 X₁) (h ≫ z')) hX' h (pullback.snd (𝟙 X₁) z'))
    (hfstX : hX' ≫ pullback.fst (𝟙 X₁) z' = pullback.fst (𝟙 X₁) (h ≫ z'))
    (hY' : pullback (h ≫ z') f ⟶ pullback z' f)
    (sqY : IsPullback (pullback.fst (h ≫ z') f) hY' h (pullback.fst z' f))
    (hsndY : hY' ≫ pullback.snd z' f = pullback.snd (h ≫ z') f) :
    IsPullback hY' (generalizedProperPushforwardMap f (h ≫ z'))
      (generalizedProperPushforwardMap f z') hX' := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd (𝟙 X₁) (h ≫ z'))
    (v₂₂ := pullback.snd (𝟙 X₁) z') ?_
    (generalizedProperPushforwardMap_comp f z' h hX' hfstX sqX.w.symm hY' sqY.w.symm hsndY)
    sqX.flip
  rw [generalizedProperPushforwardMap_snd, generalizedProperPushforwardMap_snd]
  exact sqY.flip

end Map

/-! ### The cap operation and its three compatibilities -/

section Cap

variable (C : ChowSituation.{u}) {X₁ X₂ : Scheme.{u}} (s₁ : X₁ ⟶ C.S) [LocallyOfFiniteType s₁]
  (s₂ : X₂ ⟶ C.S) [LocallyOfFiniteType s₂] (f : X₂ ⟶ X₁) [IsProper f] (hf : f ≫ s₁ = s₂)

omit [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂] [IsProper f] in
include hf in
/-- The base change of `f` commutes with the structure morphisms over the base. -/
theorem generalizedProperPushforwardMap_comp_structure {Z' : Scheme.{u}} (z' : Z' ⟶ X₁) :
    generalizedProperPushforwardMap f z' ≫ (pullback.fst (𝟙 X₁) z' ≫ s₁) =
      pullback.snd z' f ≫ s₂ := by
  rw [generalizedProperPushforwardMap_fst_assoc, hf]

/-- The cap operation of `f_* ∈ A^0(X₁ ⟶ X₁ ⟵ X₂)` on a test scheme `z' : Z' ⟶ X₁`: proper
pushforward `A_k(Z' ×_{X₁} X₂) ⟶ A_k(X₁ ×_{X₁} Z')` along the base change of `f`, read in degree
`k - 0`. -/
def generalizedProperPushforwardCap {Z' : Scheme.{u}} (z' : Z' ⟶ X₁) [LocallyOfFiniteType z']
    (k : ℤ) :
    chowGroup C (pullback.snd z' f ≫ s₂) k →+ chowGroup C (pullback.fst (𝟙 X₁) z' ≫ s₁) (k - 0) :=
  (chowGroupDegreeEquiv C (pullback.fst (𝟙 X₁) z' ≫ s₁) (sub_zero k).symm).toAddMonoidHom.comp
    (properChowPushforward C (pullback.snd z' f ≫ s₂) (pullback.fst (𝟙 X₁) z' ≫ s₁)
      (generalizedProperPushforwardMap f z')
      (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf z') k
      (properPushforwardDescends C _ _ _ _ _))

/-- The cap operation of `f_*` sends a cycle class `α` to its proper pushforward along the base
change of `f`, transported to degree `k - 0`. -/
theorem generalizedProperPushforwardCap_apply {Z' : Scheme.{u}} (z' : Z' ⟶ X₁)
    [LocallyOfFiniteType z'] (k : ℤ)
    (α : chowGroup C (pullback.snd z' f ≫ s₂) k) :
    generalizedProperPushforwardCap C s₁ s₂ f hf z' k α =
      chowGroupDegreeEquiv C (pullback.fst (𝟙 X₁) z' ≫ s₁) (sub_zero k).symm
        (properChowPushforward C (pullback.snd z' f ≫ s₂) (pullback.fst (𝟙 X₁) z' ≫ s₁)
          (generalizedProperPushforwardMap f z')
          (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf z') k
          (properPushforwardDescends C _ _ _ _ _) α) :=
  rfl

/-- **Stacks 0FDU (1) for `f_*`.** The cap operation `α ↦ f'_* α` commutes with proper
pushforward along a proper `h : Z'' ⟶ Z'`. -/
theorem generalizedProperPushforwardCap_proper_naturality {Z' Z'' : Scheme.{u}} (z' : Z' ⟶ X₁)
    [LocallyOfFiniteType z'] (h : Z'' ⟶ Z') [IsProper h]
    (hX' : pullback (𝟙 X₁) (h ≫ z') ⟶ pullback (𝟙 X₁) z')
    (sqX : IsPullback (pullback.snd (𝟙 X₁) (h ≫ z')) hX' h (pullback.snd (𝟙 X₁) z'))
    (hfstX : hX' ≫ pullback.fst (𝟙 X₁) z' = pullback.fst (𝟙 X₁) (h ≫ z'))
    (hY' : pullback (h ≫ z') f ⟶ pullback z' f)
    (sqY : IsPullback (pullback.fst (h ≫ z') f) hY' h (pullback.fst z' f))
    (hsndY : hY' ≫ pullback.snd z' f = pullback.snd (h ≫ z') f) (k : ℤ) :
    letI : IsProper hX' := MorphismProperty.of_isPullback sqX (P := @IsProper) inferInstance
    letI : IsProper hY' := MorphismProperty.of_isPullback sqY (P := @IsProper) inferInstance
    ∀ (hfacY : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.snd (h ≫ z') f ≫ s₂) (pullback.snd z' f ≫ s₂) hY'
        (by rw [← Category.assoc, hsndY]) k)
      (hfacX : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (𝟙 X₁) (h ≫ z') ≫ s₁) (pullback.fst (𝟙 X₁) z' ≫ s₁) hX'
        (by rw [← Category.assoc, hfstX]) (k - 0))
      (α : chowGroup C (pullback.snd (h ≫ z') f ≫ s₂) k),
      generalizedProperPushforwardCap C s₁ s₂ f hf z' k
          (properChowPushforward C (pullback.snd (h ≫ z') f ≫ s₂) (pullback.snd z' f ≫ s₂) hY'
            (by rw [← Category.assoc, hsndY]) k hfacY α) =
        properChowPushforward C (pullback.fst (𝟙 X₁) (h ≫ z') ≫ s₁)
          (pullback.fst (𝟙 X₁) z' ≫ s₁) hX' (by rw [← Category.assoc, hfstX]) (k - 0) hfacX
          (generalizedProperPushforwardCap C s₁ s₂ f hf (h ≫ z') k α) := by
  have : IsProper hX' := MorphismProperty.of_isPullback sqX (P := @IsProper) inferInstance
  have : IsProper hY' := MorphismProperty.of_isPullback sqY (P := @IsProper) inferInstance
  intro hfacY hfacX α
  rw [generalizedProperPushforwardCap_apply, generalizedProperPushforwardCap_apply,
    properChowPushforward_chowGroupDegreeEquiv C _ _ hX' _ (sub_zero k).symm
      (properPushforwardDescends C _ _ _ _ _) hfacX]
  exact congrArg (chowGroupDegreeEquiv C _ _)
    (properChowPushforward_comp_eq C _ _ _ _ hY' (generalizedProperPushforwardMap f z')
      (generalizedProperPushforwardMap f (h ≫ z')) hX'
      (generalizedProperPushforwardMap_comp f z' h hX' hfstX sqX.w.symm hY' sqY.w.symm hsndY)
      _ _ _ _ k hfacY (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) α)

/-- **Stacks 0FDU (2) for `f_*`.** The cap operation `α ↦ f'_* α` commutes with flat pullback
along a flat `h : Z'' ⟶ Z'` of fixed relative dimension. -/
theorem generalizedProperPushforwardCap_flat_naturality {Z' Z'' : Scheme.{u}} (z' : Z' ⟶ X₁)
    [LocallyOfFiniteType z'] (h : Z'' ⟶ Z') [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (_hr : AlgebraicGeometry.RelativeDimension h r)
    (hX' : pullback (𝟙 X₁) (h ≫ z') ⟶ pullback (𝟙 X₁) z')
    (sqX : IsPullback (pullback.snd (𝟙 X₁) (h ≫ z')) hX' h (pullback.snd (𝟙 X₁) z'))
    (hfstX : hX' ≫ pullback.fst (𝟙 X₁) z' = pullback.fst (𝟙 X₁) (h ≫ z'))
    (hY' : pullback (h ≫ z') f ⟶ pullback z' f)
    (sqY : IsPullback (pullback.fst (h ≫ z') f) hY' h (pullback.fst z' f))
    (hsndY : hY' ≫ pullback.snd z' f = pullback.snd (h ≫ z') f) (k : ℤ) :
    letI : LocallyOfFiniteType hX' :=
      MorphismProperty.of_isPullback sqX (P := @LocallyOfFiniteType) inferInstance
    letI : Flat hX' := MorphismProperty.of_isPullback sqX (P := @Flat) inferInstance
    letI : LocallyOfFiniteType hY' :=
      MorphismProperty.of_isPullback sqY (P := @LocallyOfFiniteType) inferInstance
    letI : Flat hY' := MorphismProperty.of_isPullback sqY (P := @Flat) inferInstance
    ∀ (hrX' : AlgebraicGeometry.RelativeDimension hX' r)
      (hrY' : AlgebraicGeometry.RelativeDimension hY' r)
      (hfacY : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.snd (h ≫ z') f ≫ s₂) (pullback.snd z' f ≫ s₂) hY'
        (by rw [← Category.assoc, hsndY]) r hrY' k)
      (hfacX : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst (𝟙 X₁) (h ≫ z') ≫ s₁) (pullback.fst (𝟙 X₁) z' ≫ s₁) hX'
        (by rw [← Category.assoc, hfstX]) r hrX' (k - 0))
      (α : chowGroup C (pullback.snd z' f ≫ s₂) k),
      HEq
        (generalizedProperPushforwardCap C s₁ s₂ f hf (h ≫ z') (k + (r : ℤ))
          (flatPullbackChow C (pullback.snd (h ≫ z') f ≫ s₂) (pullback.snd z' f ≫ s₂) hY'
            (by rw [← Category.assoc, hsndY]) r hrY' k hfacY α))
        (flatPullbackChow C (pullback.fst (𝟙 X₁) (h ≫ z') ≫ s₁) (pullback.fst (𝟙 X₁) z' ≫ s₁)
          hX' (by rw [← Category.assoc, hfstX]) r hrX' (k - 0) hfacX
          (generalizedProperPushforwardCap C s₁ s₂ f hf z' k α)) := by
  have : LocallyOfFiniteType hX' :=
    MorphismProperty.of_isPullback sqX (P := @LocallyOfFiniteType) inferInstance
  have : Flat hX' := MorphismProperty.of_isPullback sqX (P := @Flat) inferInstance
  have : LocallyOfFiniteType hY' :=
    MorphismProperty.of_isPullback sqY (P := @LocallyOfFiniteType) inferInstance
  have : Flat hY' := MorphismProperty.of_isPullback sqY (P := @Flat) inferInstance
  intro hrX' hrY' hfacY hfacX α
  rw [generalizedProperPushforwardCap_apply, generalizedProperPushforwardCap_apply]
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  refine HEq.trans (heq_of_eq (properPushforwardFlatPullbackBaseChange C _ _ _ _
    (generalizedProperPushforwardMap f z')
    (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf z')
    (generalizedProperPushforwardMap f (h ≫ z'))
    (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf (h ≫ z')) hY'
    (by rw [← Category.assoc, hsndY]) hX' (by rw [← Category.assoc, hfstX])
    (isPullback_generalizedProperPushforwardMap f z' h hX' sqX hfstX hY' sqY hsndY) r hrY' hrX' k
    hfacY (flatPullbackDescends C _ _ _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) α)).symm ?_
  exact flatPullbackChow_heq_congr C _ _ hX' hX' _ _ rfl rfl hrX' hrX' (sub_zero k).symm _ hfacX
    _ _ (chowGroupDegreeEquiv_heq C _ _ _).symm

/-- **Stacks 0FDU (3) for `f_*`, the transport step.** Let `L` be an invertible module on a test
scheme `Z'` with a global section `s`. The Gysin map of the section pulled back to
`X₁ ×_{X₁} Z'`, applied to a class pushed forward along the base change of `f`, is the pushforward
along `ψ : Z(s|_{Z' ×_{X₁} X₂}) ⟶ Z(s|_{X₁ ×_{X₁} Z'})` of the Gysin map of the section pulled
back to `Z' ×_{X₁} X₂`, for any morphism `ψ` lying over the base change of `f`. -/
theorem gysinSystemOfInvertible_onChow_generalizedProperPushforwardMap {Z' : Scheme.{u}}
    (z' : Z' ⟶ X₁) [LocallyOfFiniteType z'] (L : Z'.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z'.sheaf.obj Z'.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback (𝟙 X₁) z').sheaf.obj
      (pullback (𝟙 X₁) z').ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ)
    (ψ : (Stacks.Divisors.zeroScheme (pullback z' f)
        ((Scheme.Modules.pullback (pullback.fst z' f)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.fst z' f) L s)).subscheme ⟶
      (Stacks.Divisors.zeroScheme (pullback (𝟙 X₁) z')
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s)).subscheme)
    [IsProper ψ]
    (hψ : ψ ≫ (Stacks.Divisors.zeroScheme (pullback (𝟙 X₁) z')
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s)).subschemeι =
      (Stacks.Divisors.zeroScheme (pullback z' f)
        ((Scheme.Modules.pullback (pullback.fst z' f)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.fst z' f) L s)).subschemeι ≫
        generalizedProperPushforwardMap f z')
    (hψbase : ψ ≫ ((Stacks.Divisors.zeroScheme (pullback (𝟙 X₁) z')
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s)).subschemeι ≫
          pullback.fst (𝟙 X₁) z' ≫ s₁) =
      (Stacks.Divisors.zeroScheme (pullback z' f)
        ((Scheme.Modules.pullback (pullback.fst z' f)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.fst z' f) L s)).subschemeι ≫
        pullback.snd z' f ≫ s₂)
    (α : chowGroup C (pullback.snd z' f ≫ s₂) (k + 1)) :
    (gysinSystemOfInvertible C).onChow (pullback.fst (𝟙 X₁) z' ≫ s₁)
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s) k
        (properChowPushforward C (pullback.snd z' f ≫ s₂) (pullback.fst (𝟙 X₁) z' ≫ s₁)
          (generalizedProperPushforwardMap f z')
          (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf z') (k + 1)
          (properPushforwardDescends C _ _ _ _ _) α) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme (pullback z' f)
          ((Scheme.Modules.pullback (pullback.fst z' f)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.fst z' f) L s)).subschemeι ≫
            pullback.snd z' f ≫ s₂)
        ((Stacks.Divisors.zeroScheme (pullback (𝟙 X₁) z')
          ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s)).subschemeι ≫
            pullback.fst (𝟙 X₁) z' ≫ s₁) ψ hψbase k (properPushforwardDescends C _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow (pullback.snd z' f ≫ s₂)
          ((Scheme.Modules.pullback (pullback.fst z' f)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.fst z' f) L s) k α) := by
  have hq := generalizedProperPushforwardMap_snd f z'
  have hzs := Stacks.Divisors.zeroScheme_pullback_comp_eq (generalizedProperPushforwardMap f z')
    (pullback.snd (𝟙 X₁) z') (pullback.fst z' f) hq L s
  have hj : (eqToHom (congrArg Scheme.IdealSheafData.subscheme hzs) ≫ ψ) ≫
      (Stacks.Divisors.zeroScheme (pullback (𝟙 X₁) z')
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s)).subschemeι =
      (pullbackZeroScheme (generalizedProperPushforwardMap f z')
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s)).subschemeι ≫
        generalizedProperPushforwardMap f z' := by
    rw [Category.assoc, hψ, ← Category.assoc, subschemeι_eqToHom hzs]
  have hu : eqToHom (congrArg Scheme.IdealSheafData.subscheme hzs) ≫
      ((Stacks.Divisors.zeroScheme (pullback z' f)
        ((Scheme.Modules.pullback (pullback.fst z' f)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.fst z' f) L s)).subschemeι ≫
          pullback.snd z' f ≫ s₂) =
      (pullbackZeroScheme (generalizedProperPushforwardMap f z')
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s)).subschemeι ≫
        pullback.snd z' f ≫ s₂ :=
    comp_comp_of_eq (subschemeι_eqToHom hzs) rfl
  exact (gysinSystemOfInvertible_isNaturalUnderProperPushforward C (pullback.snd z' f ≫ s₂)
        (pullback.fst (𝟙 X₁) z' ≫ s₁) (generalizedProperPushforwardMap f z')
        (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf z')
        ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s) k
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme hzs) ≫ ψ) hj
        (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _) α).trans
    ((properChowPushforward_comp_apply C _ _ _
          (eqToHom (congrArg Scheme.IdealSheafData.subscheme hzs)) ψ
          (eqToHom (congrArg Scheme.IdealSheafData.subscheme hzs) ≫ ψ) rfl hu hψbase
          (zeroSchemeSquare_comp_structureMorphism C (pullback.snd z' f ≫ s₂)
            (pullback.fst (𝟙 X₁) z' ≫ s₁) (generalizedProperPushforwardMap f z')
            (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf z')
            ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s)
            (eqToHom (congrArg Scheme.IdealSheafData.subscheme hzs) ≫ ψ) hj) k
          (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
          (properPushforwardDescends C _ _ _ _ _) _).trans
      (DFunLike.congr_arg (properChowPushforward C _ _ ψ hψbase k
          (properPushforwardDescends C _ _ _ _ _))
        (GysinSystem.onChow_pullbackComp
          (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)
          (generalizedProperPushforwardMap f z') (pullback.snd (𝟙 X₁) z') (pullback.fst z' f) hq
          (pullback.snd z' f ≫ s₂) L s k α)))

/-- **Stacks 0FDU (3) for `f_*`.** The cap operation `α ↦ f'_* α` commutes with the Gysin map of
the zero scheme `D ⊆ Z'` of a section of an invertible module on a test scheme, read through the
two identifications of the base changes of `D` with the zero schemes of the pulled-back sections.
-/
theorem generalizedProperPushforwardCap_gysin_naturality {Z' : Scheme.{u}} (z' : Z' ⟶ X₁)
    [LocallyOfFiniteType z'] (L : Z'.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z'.sheaf.obj Z'.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback (𝟙 X₁) z').sheaf.obj
      (pullback (𝟙 X₁) z').ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback z' f).sheaf.obj
      (pullback z' f).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.fst z' f)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme Z' L s
    let LX := (Scheme.Modules.pullback (pullback.snd (𝟙 X₁) z')).obj L
    let tX := AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X₁) z') L s
    let EX := Stacks.Divisors.zeroScheme (pullback (𝟙 X₁) z') LX tX
    let LY := (Scheme.Modules.pullback (pullback.fst z' f)).obj L
    let tY := AlgebraicGeometry.pullbackGlobalSections (pullback.fst z' f) L s
    let EY := Stacks.Divisors.zeroScheme (pullback z' f) LY tY
    ∀ (eX : pullback (𝟙 X₁) (D.subschemeι ≫ z') ≅ EX.subscheme)
      (_heX : eX.hom ≫ EX.subschemeι = bivariantBaseChangeMap (𝟙 X₁) z' D.subschemeι)
      (hbaseX : eX.hom ≫ (EX.subschemeι ≫ pullback.fst (𝟙 X₁) z' ≫ s₁) =
        pullback.fst (𝟙 X₁) (D.subschemeι ≫ z') ≫ s₁)
      (hfacX : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst (𝟙 X₁) (D.subschemeι ≫ z') ≫ s₁)
        (EX.subschemeι ≫ pullback.fst (𝟙 X₁) z' ≫ s₁) eX.hom hbaseX (k - 0))
      (eY : EY.subscheme ≅ pullback (D.subschemeι ≫ z') f)
      (_heY : eY.hom ≫ generalizedBivariantBaseChangeMap z' f D.subschemeι = EY.subschemeι)
      (hbaseY : eY.hom ≫ (pullback.snd (D.subschemeι ≫ z') f ≫ s₂) =
        EY.subschemeι ≫ pullback.snd z' f ≫ s₂)
      (hfacY : ProperPushforwardFactorsThroughRationalEquivalence C
        (EY.subschemeι ≫ pullback.snd z' f ≫ s₂)
        (pullback.snd (D.subschemeι ≫ z') f ≫ s₂) eY.hom hbaseY k)
      (α : chowGroup C (pullback.snd z' f ≫ s₂) (k + 1)),
      properChowPushforward C (pullback.fst (𝟙 X₁) (D.subschemeι ≫ z') ≫ s₁)
          (EX.subschemeι ≫ pullback.fst (𝟙 X₁) z' ≫ s₁) eX.hom hbaseX (k - 0) hfacX
          (generalizedProperPushforwardCap C s₁ s₂ f hf (D.subschemeι ≫ z') k
            (properChowPushforward C (EY.subschemeι ≫ pullback.snd z' f ≫ s₂)
              (pullback.snd (D.subschemeι ≫ z') f ≫ s₂) eY.hom hbaseY k hfacY
              ((gysinSystemOfInvertible C).onChow (pullback.snd z' f ≫ s₂) LY tY k α))) =
        (gysinSystemOfInvertible C).onChow (pullback.fst (𝟙 X₁) z' ≫ s₁) LX tX (k - 0)
          (Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X₁) z' ≫ s₁))
            (by omega : (k + 1) - 0 = (k - 0) + 1))
            (generalizedProperPushforwardCap C s₁ s₂ f hf z' (k + 1) α)) := by
  intro D LX tX EX LY tY EY eX heX hbaseX hfacX eY heY hbaseY hfacY α
  have hφD : generalizedProperPushforwardMap f (D.subschemeι ≫ z') ≫
      bivariantBaseChangeMap (𝟙 X₁) z' D.subschemeι =
      generalizedBivariantBaseChangeMap z' f D.subschemeι ≫ generalizedProperPushforwardMap f z' :=
    (generalizedProperPushforwardMap_comp f z' D.subschemeι _ (by simp) (by simp) _ (by simp)
      (by simp)).symm
  have hψ : (eY.hom ≫ generalizedProperPushforwardMap f (D.subschemeι ≫ z') ≫ eX.hom) ≫
      EX.subschemeι = EY.subschemeι ≫ generalizedProperPushforwardMap f z' := by
    rw [Category.assoc, Category.assoc, heX, hφD, ← Category.assoc, heY]
  have hφDbase : (generalizedProperPushforwardMap f (D.subschemeι ≫ z') ≫ eX.hom) ≫
      (EX.subschemeι ≫ pullback.fst (𝟙 X₁) z' ≫ s₁) =
      pullback.snd (D.subschemeι ≫ z') f ≫ s₂ := by
    rw [Category.assoc, hbaseX, generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf]
  have hψbase : (eY.hom ≫ generalizedProperPushforwardMap f (D.subschemeι ≫ z') ≫ eX.hom) ≫
      (EX.subschemeι ≫ pullback.fst (𝟙 X₁) z' ≫ s₁) =
      EY.subschemeι ≫ pullback.snd z' f ≫ s₂ := by
    rw [Category.assoc, hφDbase, hbaseY]
  have hdeg : Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X₁) z' ≫ s₁))
      (by omega : (k + 1) - 0 = (k - 0) + 1))
      (generalizedProperPushforwardCap C s₁ s₂ f hf z' (k + 1) α) =
      chowGroupDegreeEquiv C (pullback.fst (𝟙 X₁) z' ≫ s₁) (by omega : k + 1 = (k - 0) + 1)
        (properChowPushforward C (pullback.snd z' f ≫ s₂) (pullback.fst (𝟙 X₁) z' ≫ s₁)
          (generalizedProperPushforwardMap f z')
          (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf z') (k + 1)
          (properPushforwardDescends C _ _ _ _ _) α) := by
    refine ((chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).2 ?_).symm
    exact (chowGroupDegreeEquiv_heq C _ _ _).symm.trans (cast_heq _ _).symm
  rw [hdeg, ← GysinSystem.onChow_chowGroupDegreeEquiv _ _ _ _ (sub_zero k).symm,
    generalizedProperPushforwardCap_apply,
    properChowPushforward_chowGroupDegreeEquiv C _ _ eX.hom hbaseX (sub_zero k).symm
      (properPushforwardDescends C _ _ _ _ _) hfacX,
    gysinSystemOfInvertible_onChow_generalizedProperPushforwardMap C s₁ s₂ f hf z' L s k
      (eY.hom ≫ generalizedProperPushforwardMap f (D.subschemeι ≫ z') ≫ eX.hom) hψ hψbase α]
  refine congrArg (chowGroupDegreeEquiv C _ _) ?_
  rw [properChowPushforward_comp_apply C _ _ _ eY.hom
      (generalizedProperPushforwardMap f (D.subschemeι ≫ z') ≫ eX.hom) _ rfl hbaseY hφDbase
      hψbase k hfacY (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _),
    properChowPushforward_comp_apply C _ _ _ (generalizedProperPushforwardMap f (D.subschemeι ≫ z'))
      eX.hom _ rfl (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf _) hbaseX hφDbase k
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _)]

end Cap

/-! ### The generalized bivariant class `f_*` -/

section Class

variable (C : ChowSituation.{u}) {X₁ X₂ : Scheme.{u}} (s₁ : X₁ ⟶ C.S) [LocallyOfFiniteType s₁]
  (s₂ : X₂ ⟶ C.S) [LocallyOfFiniteType s₂] (f : X₂ ⟶ X₁) [IsProper f] (hf : f ≫ s₁ = s₂)

/-- For a proper morphism `f : X₂ ⟶ X₁` of schemes locally of finite type over the base, proper
pushforward is a generalized bivariant class of degree `0` for the diagram
`X₁ --id--> X₁ <--f-- X₂`:

  `f_* ∈ A^0(X₁ ⟶ X₁ ⟵ X₂)`.

On a test scheme `z' : Z' ⟶ X₁` its cap operation is proper pushforward
`A_k(Z' ×_{X₁} X₂) ⟶ A_k(X₁ ×_{X₁} Z')` along the base change of `f`
(`Stacks.Chow.properPushforwardGeneralizedBivariantClass_cap`). It is formed at the Gysin system of
the first Chern class rule, `Stacks.Chow.gysinSystemOfInvertible`. -/
@[stacks 0FDU "the example of the remark: for a proper f : X₂ ⟶ X₁, f_* ∈ A^0(X₁ ⟶ X₁ ⟵ X₂), \
at the canonical Gysin system gysinSystemOfInvertible, with NOTHING ASSUMED"]
def properPushforwardGeneralizedBivariantClass :
    GeneralizedBivariantClass C (gysinSystemOfInvertible C) s₁ s₂ s₁ (𝟙 X₁) f
      (Category.id_comp s₁) hf 0 where
  cap z' _ k := generalizedProperPushforwardCap C s₁ s₂ f hf z' k
  proper_naturality z' _ h _ hX' sqX hfstX hY' sqY hsndY k :=
    generalizedProperPushforwardCap_proper_naturality C s₁ s₂ f hf z' h hX' sqX hfstX hY' sqY
      hsndY k
  flat_naturality z' _ h _ _ r hr hX' sqX hfstX hY' sqY hsndY k :=
    generalizedProperPushforwardCap_flat_naturality C s₁ s₂ f hf z' h r hr hX' sqX hfstX hY' sqY
      hsndY k
  gysin_naturality z' _ L _ _ _ s k :=
    generalizedProperPushforwardCap_gysin_naturality C s₁ s₂ f hf z' L s k

/-- The cap operation of `f_* ∈ A^0(X₁ ⟶ X₁ ⟵ X₂)` on a test scheme `z' : Z' ⟶ X₁` is proper
pushforward along the base change `Z' ×_{X₁} X₂ ⟶ X₁ ×_{X₁} Z'` of `f`, read in degree `k - 0`. -/
@[stacks 0FDU "the class f_* ∈ A^0(X₁ ⟶ X₁ ⟵ X₂) caps by proper pushforward along the base \
change of f"]
theorem properPushforwardGeneralizedBivariantClass_cap {Z' : Scheme.{u}} (z' : Z' ⟶ X₁)
    [LocallyOfFiniteType z'] (k : ℤ) (α : chowGroup C (pullback.snd z' f ≫ s₂) k) :
    (properPushforwardGeneralizedBivariantClass C s₁ s₂ f hf).cap z' k α =
      chowGroupDegreeEquiv C (pullback.fst (𝟙 X₁) z' ≫ s₁) (sub_zero k).symm
        (properChowPushforward C (pullback.snd z' f ≫ s₂) (pullback.fst (𝟙 X₁) z' ≫ s₁)
          (generalizedProperPushforwardMap f z')
          (generalizedProperPushforwardMap_comp_structure C s₁ s₂ f hf z') k
          (properPushforwardDescends C _ _ _ _ _) α) :=
  rfl

end Class

end Stacks.Chow

end
