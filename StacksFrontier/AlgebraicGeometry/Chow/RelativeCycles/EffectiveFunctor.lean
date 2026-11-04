module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveRelative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescentStage
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute

/-!
# The functor of effective relative cycles

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let
`r ≥ 0`. For a scheme `S'` locally of finite type over `S` put `X' = S' ×_S X`. Base change of
families of cycles on fibres along a morphism `S'' ⟶ S'` over `S` carries effective relative
`r`-cycles on `X'/S'` to effective relative `r`-cycles on `X''/S''`, and this makes
`S' ↦ z^eff(X'/S', r)` a contravariant functor on the category of schemes locally of finite type
over `S`. It is the functor whose representability Stacks Remark 0H5Y asks about.

## Main definitions

* `Stacks.Chow.effectiveRelativeCyclesFunctor` — the presheaf `S' ↦ z^eff(X'/S', r)` on the
  category of schemes locally of finite type over `S`.

## Main results

* `Stacks.Chow.effectiveRelativeCyclesFunctor_map_coe` — the map attached to `h : S'' ⟶ S'` is
  base change of families of cycles on fibres through the cartesian square relating `X''` to
  `X'`.

## Implementation notes

The category of schemes locally of finite type over `S` is
`LocallyOfFiniteTypeOver S`, the full subcategory of `Over S` of the morphisms locally of
finite type. The total space over `S'` is Mathlib's chosen fibre product `X ×_S S'`, and the
map attached to `h : S'' ⟶ S'` is the base change through the cartesian square
`X ×_S S'' ⟶ X ×_S S'` over `h`, read by `Stacks.Chow.baseChangeFamilyOfIsPullback`; functoriality
is Tag 0H4P, part (1), read on squares, as for the system of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitColimit`.

## References

* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
* [Stacks Project, Definition 0H5R](https://stacks.math.columbia.edu/tag/0H5R)
* [Stacks Project, Tag 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The category of schemes locally of finite type over `S`: the full subcategory of `Over S`
whose objects are the morphisms locally of finite type. -/
abbrev LocallyOfFiniteTypeOver (S : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (fun T : Over S => LocallyOfFiniteType T.hom)

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The spectrum of a finitely generated algebra is locally of finite type over the base. -/
theorem locallyOfFiniteType_specMap_algebraMap (k C : Type u) [CommRing k] [CommRing C]
    [Algebra k C] [Algebra.FiniteType k C] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- A scheme locally of finite type over a locally Noetherian scheme is locally Noetherian. -/
instance isLocallyNoetherian_left_of_locallyOfFiniteTypeOver [IsLocallyNoetherian S]
    (T : LocallyOfFiniteTypeOver S) : IsLocallyNoetherian T.obj.left :=
  haveI : LocallyOfFiniteType T.obj.hom := T.property
  LocallyOfFiniteType.isLocallyNoetherian T.obj.hom

/-- The morphism `X ×_S S'' ⟶ X ×_S S'` induced by a morphism `h : S'' ⟶ S'` of schemes over
`S`. -/
abbrev overBaseChangeMap {T₁ T₂ : Over S} (h : T₂ ⟶ T₁) : pullback f T₂.hom ⟶ pullback f T₁.hom :=
  pullback.lift (pullback.fst f T₂.hom) (pullback.snd f T₂.hom ≫ h.left)
    (by rw [pullback.condition, Category.assoc, Over.w h])

/-- The square exhibiting `X ×_S S''` as the base change of `X ×_S S'` along a morphism
`h : S'' ⟶ S'` of schemes over `S`. -/
theorem isPullback_overBaseChange {T₁ T₂ : Over S} (h : T₂ ⟶ T₁) :
    IsPullback (overBaseChangeMap f h) (pullback.snd f T₂.hom) (pullback.snd f T₁.hom)
      h.left := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, Over.w h]
  exact IsPullback.of_hasPullback _ _

variable [LocallyOfFiniteType f] (r : ℕ)

/-- **Tag 0H4P, part (1), for the squares of schemes over `S`.** Base change along `g₂ : O₂ ⟶ O₁`
followed by base change along `g₁ : O₃ ⟶ O₂` is base change along `g₁ ≫ g₂`. -/
theorem baseChangeFamilyOfIsPullback_overBaseChange_comp {O₁ O₂ O₃ : Over S} (g₁ : O₃ ⟶ O₂)
    (g₂ : O₂ ⟶ O₁) (γ : FamilyOfCycles (pullback.snd f O₁.hom) r) :
    baseChangeFamilyOfIsPullback (pullback.snd f O₂.hom) (isPullback_overBaseChange f g₁) r
        (baseChangeFamilyOfIsPullback (pullback.snd f O₁.hom) (isPullback_overBaseChange f g₂) r
          γ) =
      baseChangeFamilyOfIsPullback (pullback.snd f O₁.hom)
        (isPullback_overBaseChange f (g₁ ≫ g₂)) r γ := by
  rw [baseChangeFamilyOfIsPullback_baseChangeFamilyOfIsPullback]
  refine baseChangeFamilyOfIsPullback_congr _ _ _ ?_ (by simp) r γ
  apply pullback.hom_ext
  · simp only [overBaseChangeMap, pullback.lift_fst, Category.assoc]
  · simp only [overBaseChangeMap, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc,
      Over.comp_left]

/-- Base change through a cartesian square preserves effectivity of a family of cycles on
fibres: it is a base change, which preserves effectivity (Tag 0H5S), followed by a restriction
along an isomorphism, which reads coefficients at image points. -/
theorem isEffectiveFamily_baseChangeFamilyOfIsPullback [IsLocallyNoetherian S] {T P : Scheme.{u}}
    {g : T ⟶ S} {a : P ⟶ X} {p : P ⟶ T} [LocallyOfFiniteType p] (sq : IsPullback a p f g)
    {α : FamilyOfCycles f r} (hα : IsEffectiveFamily f r α) :
    IsEffectiveFamily p r (baseChangeFamilyOfIsPullback f sq r α) := by
  intro t _
  exact isEffectiveFamily_baseChangeFamily f g r α hα t _

variable [IsLocallyNoetherian S]

/-- The map `z^eff(X ×_S S'/S', r) ⟶ z^eff(X ×_S S''/S'', r)` attached to a morphism
`h : S'' ⟶ S'` of schemes locally of finite type over `S`: base change through the cartesian
square `Stacks.Chow.isPullback_overBaseChange`. -/
def effectiveRelativeCyclesMap {T₁ T₂ : LocallyOfFiniteTypeOver S} (h : T₂ ⟶ T₁) :
    ↥(effectiveRelativeCycles (pullback.snd f T₁.obj.hom) r) →
      ↥(effectiveRelativeCycles (pullback.snd f T₂.obj.hom) r) := fun α =>
  ⟨⟨baseChangeFamilyOfIsPullback (pullback.snd f T₁.obj.hom)
      (isPullback_overBaseChange f h.hom) r α.1.1,
    isRelativeCycle_baseChangeFamilyOfIsPullback _ _ r α.1.2⟩,
    isEffectiveFamily_baseChangeFamilyOfIsPullback _ r _ α.2⟩

/-- The underlying family of cycles of the image of `α` under `effectiveRelativeCyclesMap f r h`
is the base change of the family of `α` through `Stacks.Chow.isPullback_overBaseChange`. -/
theorem effectiveRelativeCyclesMap_coe {T₁ T₂ : LocallyOfFiniteTypeOver S} (h : T₂ ⟶ T₁)
    (α : ↥(effectiveRelativeCycles (pullback.snd f T₁.obj.hom) r)) :
    (effectiveRelativeCyclesMap f r h α).1.1 =
      baseChangeFamilyOfIsPullback (pullback.snd f T₁.obj.hom)
        (isPullback_overBaseChange f h.hom) r α.1.1 :=
  rfl

/-- Base change along the identity is the identity. -/
theorem effectiveRelativeCyclesMap_id (T : LocallyOfFiniteTypeOver S) :
    effectiveRelativeCyclesMap f r (𝟙 T) = id := by
  funext α
  apply Subtype.ext
  apply Subtype.ext
  change baseChangeFamilyOfIsPullback _ _ r α.1.1 = α.1.1
  rw [baseChangeFamilyOfIsPullback_congr _ _ (IsPullback.of_id_fst (f := pullback.snd f _))
    (by apply pullback.hom_ext <;> simp [overBaseChangeMap]) (by simp)]
  exact baseChangeFamilyOfIsPullback_id _ _ r α.1.1

/-- Base change along a composite is the composite of the base changes (Tag 0H4P, part (1)). -/
theorem effectiveRelativeCyclesMap_comp {T₁ T₂ T₃ : LocallyOfFiniteTypeOver S} (h₁ : T₂ ⟶ T₁)
    (h₂ : T₃ ⟶ T₂) :
    effectiveRelativeCyclesMap f r (h₂ ≫ h₁) =
      effectiveRelativeCyclesMap f r h₂ ∘ effectiveRelativeCyclesMap f r h₁ := by
  funext α
  exact Subtype.ext <| Subtype.ext
    (baseChangeFamilyOfIsPullback_overBaseChange_comp f r h₂.hom h₁.hom α.1.1).symm

/-- The contravariant functor `S' ↦ z^eff(X'/S', r)`, `X' = S' ×_S X`, on the category of
schemes locally of finite type over `S`, the map attached to a morphism `S'' ⟶ S'` over `S` being
base change of effective relative `r`-cycles. -/
@[stacks 0H5Y "the functor S' ↦ z^eff(X'/S', r), X' = S' ×_S X, on schemes locally of finite type \
over S"]
def effectiveRelativeCyclesFunctor : (LocallyOfFiniteTypeOver S)ᵒᵖ ⥤ Type u where
  obj T := ↥(effectiveRelativeCycles (pullback.snd f T.unop.obj.hom) r)
  map h := ↾(effectiveRelativeCyclesMap f r h.unop)
  map_id T := by
    change ↾(effectiveRelativeCyclesMap f r (𝟙 T.unop)) = _
    rw [effectiveRelativeCyclesMap_id]
    rfl
  map_comp h₁ h₂ := by
    change ↾(effectiveRelativeCyclesMap f r (h₂.unop ≫ h₁.unop)) = _
    rw [effectiveRelativeCyclesMap_comp]
    rfl

/-- The underlying family of cycles of the image of `α` under the map of
`effectiveRelativeCyclesFunctor f r` attached to `h` is the base change of the family of `α`
through `Stacks.Chow.isPullback_overBaseChange`. -/
theorem effectiveRelativeCyclesFunctor_map_coe {T₁ T₂ : (LocallyOfFiniteTypeOver S)ᵒᵖ}
    (h : T₁ ⟶ T₂) (α : (effectiveRelativeCyclesFunctor f r).obj T₁) :
    ((effectiveRelativeCyclesFunctor f r).map h α).1.1 =
      baseChangeFamilyOfIsPullback (pullback.snd f T₁.unop.obj.hom)
        (isPullback_overBaseChange f h.unop.hom) r
          α.1.1 :=
  rfl

end Stacks.Chow

end
