module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceLeftExactness

/-!
# The base change of a morphism of a big fppf site carries pullback squares to pullback squares

Let `f : X ⟶ S` be a morphism of a big fppf site. The base change `T ↦ X_T` of `f` along the
`S`-schemes of the site carries a pullback square to a pullback square:

`X_{U ×_T V} = X_U ×_{X_T} X_V`.

## Main results

* `Stacks.Limits.isPullback_of_isPullback_vert` — base change preserves pullback squares, stated
  for four pullback squares sitting over one in an arbitrary category.
* `Stacks.PicardFunctor.baseChangeMap_isPullback_proj` — the square comparing the base change of
  a morphism of test schemes with the morphism itself is a pullback square.
* `Stacks.PicardFunctor.baseChangeMap_isPullback` — the base change of a pullback square of test
  schemes is a pullback square.
* `Stacks.PicardFunctor.exists_isPullback_bigFppfOver` — two morphisms of test schemes with the
  same target have a fibre product among the test schemes.
* `Stacks.PicardFunctor.exists_isPullback_baseChangeMap` — hence the fibre product of two base
  changes over `X_T` is again a base change.

## References

* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Limits

/-- **Base change preserves pullback squares.** Given a pullback square with sides `p`, `q`, `a`,
`b` and four pullback squares exhibiting `W'`, `U'`, `V'` over `W`, `U`, `V` as the base changes
along a morphism `T' ⟶ T`, the induced square upstairs is a pullback square. -/
theorem isPullback_of_isPullback_vert {C : Type*} [Category C] {W U V T W' U' V' T' : C}
    {pw : W' ⟶ W} {pu : U' ⟶ U} {pv : V' ⟶ V} {pt : T' ⟶ T}
    {p : W ⟶ U} {q : W ⟶ V} {a : U ⟶ T} {b : V ⟶ T}
    {p' : W' ⟶ U'} {q' : W' ⟶ V'} {a' : U' ⟶ T'} {b' : V' ⟶ T'}
    (hp : IsPullback p' pw pu p) (hq : IsPullback q' pw pv q)
    (ha : IsPullback a' pu pt a) (hb : IsPullback b' pv pt b)
    (h : IsPullback p q a b) (hcomm : p' ≫ a' = q' ≫ b') :
    IsPullback p' q' a' b' := by
  refine IsPullback.of_bot ?_ hcomm hb
  rw [hq.w, ha.w]
  exact hp.paste_vert h

end Stacks.Limits

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- The base change of a morphism `a : U ⟶ T` of test schemes sits in a pullback square over `a`
itself: `X_U = X_T ×_T U`. -/
theorem baseChangeMap_isPullback_proj {U T : BigFppfOver B S hS} (a : U ⟶ T) :
    IsPullback (baseChangeMap B hX hS f a) (baseChangeProj B hX hS f U)
      (baseChangeProj B hX hS f T) (B.inclusion.map a.left) := by
  have hfst : baseChangeMap B hX hS f a ≫
      pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom) =
      pullback.fst (B.inclusion.map f) (B.inclusion.map U.hom) := by
    simp only [baseChangeMap, pullback.map, pullback.lift_fst, Category.comp_id]
  have hbot : B.inclusion.map a.left ≫ B.inclusion.map T.hom = B.inclusion.map U.hom := by
    rw [← B.inclusion.map_comp, Over.w a]
  have hsnd : baseChangeMap B hX hS f a ≫ baseChangeProj B hX hS f T =
      baseChangeProj B hX hS f U ≫ B.inclusion.map a.left :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_right ?_ hsnd (IsPullback.of_hasPullback _ _)
  rw [hfst, hbot]
  exact IsPullback.of_hasPullback _ _

/-- **The base change of a pullback square of test schemes is a pullback square**:
`X_{U ×_T V} = X_U ×_{X_T} X_V`. -/
theorem baseChangeMap_isPullback {W U V T : BigFppfOver B S hS} (p : W ⟶ U) (q : W ⟶ V)
    (a : U ⟶ T) (b : V ⟶ T)
    (h : IsPullback (B.inclusion.map p.left) (B.inclusion.map q.left)
      (B.inclusion.map a.left) (B.inclusion.map b.left))
    (hw : p ≫ a = q ≫ b) :
    IsPullback (baseChangeMap B hX hS f p) (baseChangeMap B hX hS f q)
      (baseChangeMap B hX hS f a) (baseChangeMap B hX hS f b) := by
  refine Stacks.Limits.isPullback_of_isPullback_vert (baseChangeMap_isPullback_proj B hX hS f p)
    (baseChangeMap_isPullback_proj B hX hS f q) (baseChangeMap_isPullback_proj B hX hS f a)
    (baseChangeMap_isPullback_proj B hX hS f b) h ?_
  rw [← baseChangeMap_comp, ← baseChangeMap_comp, hw]

/-- Two morphisms of the underlying category of a big fppf site with the same target have a
fibre product there: the fibre product of schemes satisfies the site's size bound. -/
theorem exists_isPullback_bigFppfSite {U V T : B.Schemes} (a : U ⟶ T) (b : V ⟶ T) :
    ∃ (W : B.Schemes) (p : W ⟶ U) (q : W ⟶ V),
      IsPullback (B.inclusion.map p) (B.inclusion.map q)
        (B.inclusion.map a) (B.inclusion.map b) :=
  ⟨B.obj (Scheme.size_pullback_lt a.hom b.hom U.property V.property),
    ObjectProperty.homMk (pullback.fst a.hom b.hom),
    ObjectProperty.homMk (pullback.snd a.hom b.hom),
    IsPullback.of_hasPullback a.hom b.hom⟩

/-- Two morphisms of test schemes with the same target have a fibre product among the test
schemes. -/
theorem exists_isPullback_bigFppfOver {U V T : BigFppfOver B S hS} (a : U ⟶ T) (b : V ⟶ T) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U) (q : W ⟶ V), p ≫ a = q ≫ b ∧
      IsPullback (B.inclusion.map p.left) (B.inclusion.map q.left)
        (B.inclusion.map a.left) (B.inclusion.map b.left) := by
  obtain ⟨W₀, p₀, q₀, hpb⟩ := exists_isPullback_bigFppfSite B a.left b.left
  have hcond : p₀ ≫ a.left = q₀ ≫ b.left := B.inclusion.map_injective hpb.w
  refine ⟨Over.mk (p₀ ≫ U.hom), Over.homMk p₀, Over.homMk q₀ ?_, ?_, hpb⟩
  · show q₀ ≫ V.hom = p₀ ≫ U.hom
    rw [← Over.w a, ← Over.w b, ← Category.assoc, ← Category.assoc, hcond]
  · exact Over.OverMorphism.ext hcond

/-- **The fibre product of two base changes over `X_T` is again a base change.** -/
theorem exists_isPullback_baseChangeMap {U V T : BigFppfOver B S hS} (a : U ⟶ T) (b : V ⟶ T) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U) (q : W ⟶ V),
      IsPullback (baseChangeMap B hX hS f p) (baseChangeMap B hX hS f q)
        (baseChangeMap B hX hS f a) (baseChangeMap B hX hS f b) := by
  obtain ⟨W, p, q, hw, hpb⟩ := exists_isPullback_bigFppfOver B hS a b
  exact ⟨W, p, q, baseChangeMap_isPullback B hX hS f p q a b hpb hw⟩

end Stacks.PicardFunctor

end
