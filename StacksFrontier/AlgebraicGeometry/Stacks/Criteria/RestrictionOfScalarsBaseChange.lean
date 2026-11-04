module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalars

/-!
# Base change for restriction of scalars

Let `S` be a scheme contained in a big fppf site and let `x : X ⟶ Z`, `z : Z ⟶ Q` and
`b : Q' ⟶ Q` be morphisms of algebraic spaces over `S`; the source writes the base as `B` and
`B'`, names which here belong to the site. Set `Z' = Q' ×_Q Z` and `X' = Q' ×_Q X` and let
`x' : X' ⟶ Z'` be the base change of `x`. Then restriction of scalars commutes with base change
of the base:

```text
Res_{Z'/Q'}(X')  =  Q' ×_Q Res_{Z/Q}(X).
```

Both sides are presheaves on the big fppf site of `S`, so this is the asserted equality in the
category of fppf sheaves once both are known to be sheaves, which is Stacks 05YB and is not
proved here.

The identification is pinned down on sections: the pair of Stacks 05Y9 that a section of
`Res_{Z'/Q'}(X')` corresponds to is carried to its base change
`AlgebraicGeometry.Space.RestrictionPair.baseChange`, and the identification is compatible with
the two projections to `Q'`.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeFiberProductMap`: **Stacks 05YC**, the base change
  `Q' ×_Q X ⟶ Q' ×_Q Z` of `x : X ⟶ Z` along `b : Q' ⟶ Q`.
* `AlgebraicGeometry.Space.RestrictionPair.baseChange`: the pair of `Res_{Z/Q}(X)` underlying a
  pair of `Res_{Z'/Q'}(X')`: compose the first component with `b` and read the second component
  through the two descriptions of a fibre product over `Q`.

## Main results

* `AlgebraicGeometry.Space.restrictionOfScalars_baseChange`: **Stacks 05YC**, the restriction of
  scalars of the base-changed morphism is the base change of the restriction of scalars, stated
  for arbitrary presentations of `Z'` and `X'` as fibre products.
* `AlgebraicGeometry.Space.restrictionOfScalars_baseChange_fiberProduct`: **Stacks 05YC**, the
  same for the chosen fibre products of Stacks 02X2.
* `AlgebraicGeometry.Space.isPullback_baseChangeFiberProductMap`: the base-changed morphism
  exhibits `Q' ×_Q X` as `(Q' ×_Q Z) ×_Z X`, which is the form in which
  `AlgebraicGeometry.Space.restrictionOfScalars_baseChange` asks for the base change of `x`.
* `AlgebraicGeometry.Space.isPullback_hom_fiberProduct`: the chosen fibre product of algebraic
  spaces is a fibre product of the underlying presheaves.
* `CategoryTheory.Limits.isPullback_fst_snd_comp_of_isPullback`: the fibre product of
  `a : W ⟶ Q'` with a base change `Z' = Q' ×_Q Z` is the fibre product of `a ≫ b` with `z`.

## Implementation notes

The whole content of the lemma is one pasting of fibre products: a morphism `T ⟶ Z'` over
`a : T ⟶ Q'` is a morphism `T ⟶ Z` over `a ≫ b : T ⟶ Q`. That pasting is
`CategoryTheory.Limits.isPullback_fst_snd_comp_of_isPullback`, and every comparison of the two
base changes below is the isomorphism `CategoryTheory.Limits.IsPullback.isoPullback` it provides;
nothing has to be built by hand.

The statement is given for arbitrary presentations of `Z'` and `X'` as fibre products, that is,
for hypotheses `IsPullback z' c b z` and `IsPullback x' e c x`, rather than for the chosen fibre
products of Stacks 02X2. This is what keeps the proof free of comparison isomorphisms between
two chosen fibre products; the chosen case is recovered from
`AlgebraicGeometry.Space.isPullback_hom_fiberProduct` and
`AlgebraicGeometry.Space.isPullback_baseChangeFiberProductMap`.

`AlgebraicGeometry.Space.restrictionOfScalars_baseChange` is stated for arbitrary data
`AlgebraicGeometry.Space.RestrictionOfScalarsConstruction` rather than for
`AlgebraicGeometry.Space.restrictionOfScalars` itself, since only the specified properties of
the construction are used.

`AlgebraicGeometry.Space.RestrictionPair.baseChange` is `implicit_reducible` because the second
component of a pair lives over its first component: the type of the second component of a
base-changed pair is a fibre product over `p.base ≫ b`, and a goal about it is type-correct
only once the first component has been unfolded to that composite.

## References

* [Stacks Project, Tag 05YC](https://stacks.math.columbia.edu/tag/05YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace CategoryTheory.Limits

/-- **A fibre product over a base change is a fibre product over the base.** If `z' : Z' ⟶ Q'`
and `c : Z' ⟶ Z` exhibit `Z'` as the base change `Q' ×_Q Z` of `z : Z ⟶ Q` along `b : Q' ⟶ Q`,
then for `a : W ⟶ Q'` the fibre product `W ×_{a, Q'} Z'` is the fibre product
`W ×_{a ≫ b, Q} Z`: the first projection is unchanged and the second is the second projection
followed by `c`.

The morphism `d` to `Q` is taken as a separate argument, equal to `a ≫ b`, so that the
conclusion can be read at a morphism which is only *known* to factor through `b`. -/
theorem isPullback_fst_snd_comp_of_isPullback {C : Type w} [Category.{v} C] [HasPullbacks C]
    {W Q Q' Z Z' : C} {b : Q' ⟶ Q} {z : Z ⟶ Q} {z' : Z' ⟶ Q'} {c : Z' ⟶ Z}
    (hZ : IsPullback z' c b z) (a : W ⟶ Q') {d : W ⟶ Q} (ha : d = a ≫ b) :
    IsPullback (pullback.fst a z') (pullback.snd a z' ≫ c) d z := by
  subst ha
  exact (IsPullback.of_hasPullback a z').paste_vert hZ

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/- An algebraic space is a presheaf together with a property, and the chosen fibre product
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` is a plain definition, so the underlying
presheaf of a fibre product is the presheaf fibre product only after unfolding it. The goals
about the chosen fibre products below are therefore not type-correct at `implicit`
transparency, and `rw`, `simp` and `exact` decline to act on them; naming that unfolding here
is what lets the ordinary tactics see through it. -/
attribute [local implicit_reducible] AlgebraicGeometry.AlgebraicSpaces.fiberProduct

/-! ### The base change of a morphism of algebraic spaces -/

section FiberProduct

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05YC.** The base change `Q' ×_Q X ⟶ Q' ×_Q Z` of a morphism `x : X ⟶ Z` of
algebraic spaces over `z : Z ⟶ Q` along a morphism `b : Q' ⟶ Q`, for the chosen fibre products
of Stacks 02X2. It is the identity on the first factor and `x` on the second. -/
@[stacks 05YC "the base-changed morphism"]
noncomputable def baseChangeFiberProductMap {X Z Q Q' : AlgebraicSpaces B S hS} (x : X ⟶ Z)
    (z : Z ⟶ Q) (b : Q' ⟶ Q) :
    AlgebraicSpaces.fiberProduct B S hS b (x ≫ z) ⟶ AlgebraicSpaces.fiberProduct B S hS b z :=
  ObjectProperty.homMk
    (pullback.lift (pullback.fst b.hom (x ≫ z).hom)
      (pullback.snd b.hom (x ≫ z).hom ≫ x.hom)
      (by
        simpa only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using
          (pullback.condition :
            pullback.fst b.hom (x ≫ z).hom ≫ b.hom =
              pullback.snd b.hom (x ≫ z).hom ≫ (x ≫ z).hom)))

/-- **The chosen fibre product of algebraic spaces is a fibre product of the underlying
presheaves.** This is `AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` read in the
presheaf category, which is the form the hypotheses of
`AlgebraicGeometry.Space.restrictionOfScalars_baseChange` take. -/
theorem isPullback_hom_fiberProduct {F G H : AlgebraicSpaces B S hS} (f : F ⟶ H) (g : G ⟶ H) :
    IsPullback
      (ObjectProperty.homMk (pullback.fst f.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS f g ⟶ F).hom
      (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS f g ⟶ G).hom f.hom g.hom :=
  IsPullback.of_hasPullback f.hom g.hom

variable {X Z Q Q' : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q) (b : Q' ⟶ Q)

/-- The base-changed morphism is the identity on the first factor. -/
private theorem baseChangeFiberProductMap_hom_fst :
    (baseChangeFiberProductMap B S hS x z b).hom ≫ pullback.fst b.hom z.hom =
      pullback.fst b.hom (x ≫ z).hom :=
  pullback.lift_fst _ _ _

/-- The base-changed morphism is `x` on the second factor. -/
private theorem baseChangeFiberProductMap_hom_snd :
    (baseChangeFiberProductMap B S hS x z b).hom ≫ pullback.snd b.hom z.hom =
      pullback.snd b.hom (x ≫ z).hom ≫ x.hom :=
  pullback.lift_snd _ _ _

/-- **Stacks 05YC.** The base-changed morphism exhibits `Q' ×_Q X` as `(Q' ×_Q Z) ×_Z X`. This
is the form in which `AlgebraicGeometry.Space.restrictionOfScalars_baseChange` asks for the
base change of `x`. -/
@[stacks 05YC "the base-changed morphism as a fibre product"]
theorem isPullback_baseChangeFiberProductMap :
    IsPullback (baseChangeFiberProductMap B S hS x z b).hom
      (pullback.snd b.hom (x ≫ z).hom) (pullback.snd b.hom z.hom) x.hom := by
  refine (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback b.hom z.hom)
    (baseChangeFiberProductMap_hom_snd B S hS x z b)).1 ?_
  rw [baseChangeFiberProductMap_hom_fst]
  exact IsPullback.of_hasPullback b.hom (x ≫ z).hom

end FiberProduct

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Two restatements of the Yoneda dictionary

Each is `CategoryTheory.yonedaEquiv_comp` or
`AlgebraicGeometry.Space.RestrictionOfScalarsConstruction.projection_pairEquiv` read at an
object of the opposite category instead of at `op T`. -/

/-- Postcomposition with a morphism of presheaves, read through the Yoneda dictionary. -/
private theorem yonedaEquiv_comp_app {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (I : (BigFppfOver B S hS)ᵒᵖ) (f : F ⟶ F') (t : yoneda.obj I.unop ⟶ F) :
    f.app I (yonedaEquiv t) = yonedaEquiv (t ≫ f) :=
  (yonedaEquiv_comp t f).symm

/-- The projection of a restriction-of-scalars presheaf reads off the first component of a
pair. -/
private theorem projection_app_apply {Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS} {y : Y₁ ⟶ Y₂}
    {w : Y₂ ⟶ Y₃} (r : RestrictionOfScalarsConstruction B S hS y w)
    (I : (BigFppfOver B S hS)ᵒᵖ) (v : r.presheaf.obj I) :
    r.projection.app I v = yonedaEquiv ((r.pairEquiv I.unop v).base) :=
  r.projection_pairEquiv I.unop v

variable {X Z Q X' Z' Q' : AlgebraicSpaces B S hS} {x : X ⟶ Z} {z : Z ⟶ Q} {b : Q' ⟶ Q}
  {x' : X' ⟶ Z'} {z' : Z' ⟶ Q'} {c : Z' ⟶ Z} {e : X' ⟶ X}
  (hZ : IsPullback z'.hom c.hom b.hom z.hom) (hX : IsPullback x'.hom e.hom c.hom x.hom)

/-! ### The base change of a pair -/

/-- The pair of `Res_{Z/Q}(X)` underlying a pair of `Res_{Z'/Q'}(X')`, where `Z'` is the base
change of `z : Z ⟶ Q` along `b : Q' ⟶ Q` and `X'` is the base change of `x : X ⟶ Z` along
`c : Z' ⟶ Z`: compose the first component with `b`, and read the second component through the
identification of `T ×_{a, Q'} Z'` with `T ×_{a ≫ b, Q} Z` of
`CategoryTheory.Limits.isPullback_fst_snd_comp_of_isPullback`. -/
@[implicit_reducible]
noncomputable def RestrictionPair.baseChange {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RestrictionPair B S hS x' z' T) : RestrictionPair B S hS x z T where
  base := p.base ≫ b.hom
  lift := (isPullback_fst_snd_comp_of_isPullback hZ p.base rfl).isoPullback.inv ≫ p.lift ≫ e.hom
  over := by
    simp only [Category.assoc, ← hX.w]
    rw [← Category.assoc p.lift x'.hom c.hom, p.over]
    exact (isPullback_fst_snd_comp_of_isPullback hZ p.base rfl).isoPullback_inv_snd

/-- The first component of a base-changed pair. -/
@[simp] theorem RestrictionPair.baseChange_base {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RestrictionPair B S hS x' z' T) :
    (p.baseChange hZ hX).base = p.base ≫ b.hom :=
  rfl

/-- The second component of a base-changed pair. -/
@[simp] theorem RestrictionPair.baseChange_lift {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : RestrictionPair B S hS x' z' T) :
    (p.baseChange hZ hX).lift =
      (isPullback_fst_snd_comp_of_isPullback hZ p.base rfl).isoPullback.inv ≫ p.lift ≫ e.hom :=
  rfl

/-- The pair of `Res_{Z'/Q'}(X')` with prescribed first component `a` whose base change is a
given pair `p` of `Res_{Z/Q}(X)` with `p.base = a ≫ b`. -/
@[implicit_reducible]
private noncomputable def RestrictionPair.baseChangeInv
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q'.obj) (p : RestrictionPair B S hS x z T)
    (ha : p.base = a ≫ b.hom) : RestrictionPair B S hS x' z' T where
  base := a
  lift :=
    hX.lift (pullback.snd a z'.hom)
      ((isPullback_fst_snd_comp_of_isPullback hZ a ha).isoPullback.hom ≫ p.lift)
      (by
        rw [Category.assoc, p.over]
        exact (isPullback_fst_snd_comp_of_isPullback hZ a ha).isoPullback_hom_snd.symm)
  over := hX.lift_fst _ _ _

/-- The first component of `AlgebraicGeometry.Space.RestrictionPair.baseChangeInv`. -/
@[simp] private theorem RestrictionPair.baseChangeInv_base
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q'.obj) (p : RestrictionPair B S hS x z T)
    (ha : p.base = a ≫ b.hom) : (RestrictionPair.baseChangeInv hZ hX a p ha).base = a :=
  rfl

/-- The second component of `AlgebraicGeometry.Space.RestrictionPair.baseChangeInv`, read in
`X`. -/
private theorem RestrictionPair.baseChangeInv_lift_comp
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q'.obj) (p : RestrictionPair B S hS x z T)
    (ha : p.base = a ≫ b.hom) :
    (RestrictionPair.baseChangeInv hZ hX a p ha).lift ≫ e.hom =
      (isPullback_fst_snd_comp_of_isPullback hZ a ha).isoPullback.hom ≫ p.lift :=
  hX.lift_snd _ _ _

/-- The inverse construction does not depend on the first component beyond its value. -/
private theorem RestrictionPair.baseChangeInv_congr
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a₁ a₂ : T ⟶ Q'.obj)
    (p : RestrictionPair B S hS x z T) (h₁ : p.base = a₁ ≫ b.hom) (h₂ : p.base = a₂ ≫ b.hom)
    (ha : a₁ = a₂) :
    RestrictionPair.baseChangeInv hZ hX a₁ p h₁ = RestrictionPair.baseChangeInv hZ hX a₂ p h₂ := by
  cases ha
  rfl

/-- **The base change of the pair produced by the inverse construction is the original pair.** -/
private theorem RestrictionPair.baseChange_baseChangeInv
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Q'.obj) (p : RestrictionPair B S hS x z T)
    (ha : p.base = a ≫ b.hom) :
    (RestrictionPair.baseChangeInv hZ hX a p ha).baseChange hZ hX = p := by
  have key :
      (isPullback_fst_snd_comp_of_isPullback hZ a (rfl : a ≫ b.hom = a ≫ b.hom)).isoPullback.inv ≫
          (isPullback_fst_snd_comp_of_isPullback hZ a ha).isoPullback.hom =
        (pullback.congrHom ha.symm (rfl : z.hom = z.hom)).hom :=
    pullback.hom_ext (by simp) (by simp)
  refine RestrictionPair.ext_of_base_eq ha.symm ?_
  rw [RestrictionPair.baseChange_lift, RestrictionPair.baseChangeInv_lift_comp,
    ← Category.assoc, key]

/-- **The inverse construction applied to a base change returns the original pair.** -/
private theorem RestrictionPair.baseChangeInv_baseChange
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : RestrictionPair B S hS x' z' T) :
    RestrictionPair.baseChangeInv hZ hX p.base (p.baseChange hZ hX) rfl = p := by
  have hid : (pullback.congrHom (rfl : p.base = p.base) (rfl : z'.hom = z'.hom)).hom =
      𝟙 (pullback p.base z'.hom) :=
    pullback.hom_ext (by simp) (by simp)
  have hlift : (RestrictionPair.baseChangeInv hZ hX p.base (p.baseChange hZ hX) rfl).lift =
      p.lift := by
    refine hX.hom_ext ?_ ?_
    · exact (RestrictionPair.baseChangeInv hZ hX p.base (p.baseChange hZ hX) rfl).over.trans
        p.over.symm
    · rw [RestrictionPair.baseChangeInv_lift_comp, RestrictionPair.baseChange_lift,
        Iso.hom_inv_id_assoc]
  exact RestrictionPair.ext_of_base_eq rfl
    (by rw [hlift, hid]; exact (Category.id_comp p.lift).symm)

/-- **Two pairs with the same first component and the same base change are equal.** -/
private theorem RestrictionPair.baseChange_injective
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p₁ p₂ : RestrictionPair B S hS x' z' T)
    (hbase : p₁.base = p₂.base) (h : p₁.baseChange hZ hX = p₂.baseChange hZ hX) : p₁ = p₂ := by
  let conv := {q : RestrictionPair B S hS x z T // q.base = p₁.base ≫ b.hom}
  let c₁ : conv := ⟨p₁.baseChange hZ hX, rfl⟩
  let c₂ : conv := ⟨p₂.baseChange hZ hX, by rw [RestrictionPair.baseChange_base, hbase]⟩
  have hc : c₁ = c₂ := Subtype.ext h
  have h₁ : RestrictionPair.baseChangeInv hZ hX p₁.base c₁.1 c₁.2 = p₁ :=
    RestrictionPair.baseChangeInv_baseChange hZ hX p₁
  have h₂ : RestrictionPair.baseChangeInv hZ hX p₁.base c₂.1 c₂.2 = p₂ :=
    (RestrictionPair.baseChangeInv_congr hZ hX p₁.base p₂.base _ c₂.2
        (by rw [RestrictionPair.baseChange_base]) hbase).trans
      (RestrictionPair.baseChangeInv_baseChange hZ hX p₂)
  exact h₁.symm.trans
    ((congrArg (fun q : conv => RestrictionPair.baseChangeInv hZ hX p₁.base q.1 q.2) hc).trans h₂)

/-- **Base change of pairs preserves being a base change along a morphism of test presheaves.**
This is what makes the comparison of the two restriction-of-scalars presheaves natural. -/
private theorem RestrictionPair.isPullbackAlong_baseChange
    {T T₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T ⟶ T₀)
    {p₀ : RestrictionPair B S hS x' z' T₀} {p : RestrictionPair B S hS x' z' T}
    (h : RestrictionPair.IsPullbackAlong f p₀ p) :
    RestrictionPair.IsPullbackAlong f (p₀.baseChange hZ hX) (p.baseChange hZ hX) := by
  obtain ⟨hbase, q, hfst, hsnd, hlift⟩ := h
  have hsnd' : q ≫ pullback.snd p₀.base z'.hom ≫ c.hom =
      pullback.snd p.base z'.hom ≫ c.hom := by
    rw [← Category.assoc, hsnd]
  refine ⟨by simp only [RestrictionPair.baseChange_base, hbase, Category.assoc],
    (isPullback_fst_snd_comp_of_isPullback hZ p.base rfl).isoPullback.inv ≫ q ≫
      (isPullback_fst_snd_comp_of_isPullback hZ p₀.base rfl).isoPullback.hom, ?_, ?_, ?_⟩
  · simp [hfst]
  · simp [hsnd']
  · simp only [RestrictionPair.baseChange_lift, hlift, Category.assoc, Iso.hom_inv_id_assoc]

/-! ### The comparison of the two presheaves -/

variable (r : RestrictionOfScalarsConstruction B S hS x z)
  (r' : RestrictionOfScalarsConstruction B S hS x' z')

/-- The morphism `Res_{Z'/Q'}(X') ⟶ Res_{Z/Q}(X)` given on sections by base change of pairs. -/
private noncomputable def baseChangeMap : r'.presheaf ⟶ r.presheaf where
  app I := ↾fun v => (r.pairEquiv I.unop).symm ((r'.pairEquiv I.unop v).baseChange hZ hX)
  naturality I J f := by
    ext v
    apply (r.pairEquiv J.unop).injective
    have h₁ := RestrictionPair.isPullbackAlong_baseChange hZ hX (yoneda.map f.unop)
      (r'.natural f.unop v)
    have h₂ := r.natural f.unop
      ((r.pairEquiv I.unop).symm ((r'.pairEquiv I.unop v).baseChange hZ hX))
    rw [Equiv.apply_symm_apply] at h₂
    simpa using RestrictionPair.eq_of_isPullbackAlong h₁ h₂

/-- The pair of a section in the image of the comparison morphism is the base change of the pair
of that section. -/
@[simp] private theorem pairEquiv_baseChangeMap_app (I : (BigFppfOver B S hS)ᵒᵖ)
    (v : r'.presheaf.obj I) :
    r.pairEquiv I.unop ((baseChangeMap hZ hX r r').app I v) =
      (r'.pairEquiv I.unop v).baseChange hZ hX :=
  Equiv.apply_symm_apply _ _

/-- The comparison morphism commutes with the two projections to `Q`. -/
private theorem projection_comp_baseChangeMap :
    r'.projection ≫ b.hom = baseChangeMap hZ hX r r' ≫ r.projection := by
  ext I v
  show b.hom.app I (r'.projection.app I v) =
    r.projection.app I ((baseChangeMap hZ hX r r').app I v)
  rw [projection_app_apply r' I v,
    projection_app_apply r I ((baseChangeMap hZ hX r r').app I v),
    pairEquiv_baseChangeMap_app hZ hX r r' I v, RestrictionPair.baseChange_base,
    yonedaEquiv_comp_app]

/-- The comparison morphism `Res_{Z'/Q'}(X') ⟶ Q' ×_Q Res_{Z/Q}(X)`. -/
private noncomputable def toPullbackProjection :
    r'.presheaf ⟶ pullback b.hom r.projection :=
  pullback.lift r'.projection (baseChangeMap hZ hX r r') (projection_comp_baseChangeMap hZ hX r r')

/-- The first component of the comparison morphism. -/
private theorem toPullbackProjection_fst :
    toPullbackProjection hZ hX r r' ≫ pullback.fst b.hom r.projection = r'.projection :=
  pullback.lift_fst _ _ _

/-- The second component of the comparison morphism. -/
private theorem toPullbackProjection_snd :
    toPullbackProjection hZ hX r r' ≫ pullback.snd b.hom r.projection =
      baseChangeMap hZ hX r r' :=
  pullback.lift_snd _ _ _

/-- The first component of the comparison morphism, on a section. -/
private theorem toPullbackProjection_app_fst (I : (BigFppfOver B S hS)ᵒᵖ)
    (v : r'.presheaf.obj I) :
    (pullback.fst b.hom r.projection).app I ((toPullbackProjection hZ hX r r').app I v) =
      r'.projection.app I v :=
  congrArg (fun η => η.app I v) (toPullbackProjection_fst hZ hX r r')

/-- The second component of the comparison morphism, on a section. -/
private theorem toPullbackProjection_app_snd (I : (BigFppfOver B S hS)ᵒᵖ)
    (v : r'.presheaf.obj I) :
    (pullback.snd b.hom r.projection).app I ((toPullbackProjection hZ hX r r').app I v) =
      (baseChangeMap hZ hX r r').app I v :=
  congrArg (fun η => η.app I v) (toPullbackProjection_snd hZ hX r r')

/-- The comparison morphism is bijective on sections: injectivity is uniqueness of the inverse
construction, surjectivity is its existence. -/
private theorem bijective_toPullbackProjection_app (I : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Bijective ((toPullbackProjection hZ hX r r').app I) := by
  constructor
  · intro v₁ v₂ hv
    have key : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : pullback b.hom r.projection ⟶ F),
        g.app I ((toPullbackProjection hZ hX r r').app I v₁) =
          g.app I ((toPullbackProjection hZ hX r r').app I v₂) := fun g => congrArg _ hv
    refine (r'.pairEquiv I.unop).injective
      (RestrictionPair.baseChange_injective hZ hX _ _ ?_ ?_)
    · apply yonedaEquiv.injective
      rw [← projection_app_apply r' I v₁, ← projection_app_apply r' I v₂]
      simpa only [toPullbackProjection_app_fst] using key (pullback.fst b.hom r.projection)
    · rw [← pairEquiv_baseChangeMap_app hZ hX r r' I v₁,
        ← pairEquiv_baseChangeMap_app hZ hX r r' I v₂]
      simpa only [toPullbackProjection_app_snd] using
        congrArg (r.pairEquiv I.unop) (key (pullback.snd b.hom r.projection))
  · intro w
    have hw : b.hom.app I ((pullback.fst b.hom r.projection).app I w) =
        r.projection.app I ((pullback.snd b.hom r.projection).app I w) :=
      congrArg (fun η => η.app I w) (pullback.condition (f := b.hom) (g := r.projection))
    have ha : (r.pairEquiv I.unop ((pullback.snd b.hom r.projection).app I w)).base =
        yonedaEquiv.symm ((pullback.fst b.hom r.projection).app I w) ≫ b.hom := by
      have h1 : (r.pairEquiv I.unop ((pullback.snd b.hom r.projection).app I w)).base =
          yonedaEquiv.symm (r.projection.app I ((pullback.snd b.hom r.projection).app I w)) := by
        rw [projection_app_apply, Equiv.symm_apply_apply]
      rw [h1, ← hw, yonedaEquiv_symm_naturality_right]
    refine ⟨(r'.pairEquiv I.unop).symm (RestrictionPair.baseChangeInv hZ hX
      (yonedaEquiv.symm ((pullback.fst b.hom r.projection).app I w))
      (r.pairEquiv I.unop ((pullback.snd b.hom r.projection).app I w)) ha), ?_⟩
    apply yonedaEquiv.symm.injective
    refine pullback.hom_ext ?_ ?_
    · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right,
        toPullbackProjection_app_fst,
        projection_app_apply, Equiv.apply_symm_apply, RestrictionPair.baseChangeInv_base,
        Equiv.apply_symm_apply]
    · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right,
        toPullbackProjection_app_snd]
      refine congrArg yonedaEquiv.symm ((r.pairEquiv I.unop).injective ?_)
      rw [pairEquiv_baseChangeMap_app, Equiv.apply_symm_apply,
        RestrictionPair.baseChange_baseChangeInv]

/-! ### Base change for restriction of scalars -/

/-- **Stacks 05YC.** Let `x : X ⟶ Z` and `z : Z ⟶ Q` be morphisms of algebraic spaces over `S`
and let `b : Q' ⟶ Q` be a morphism of algebraic spaces over `S`. Let `z' : Z' ⟶ Q'`, `c : Z' ⟶ Z`
exhibit `Z'` as the base change `Q' ×_Q Z`, and let `x' : X' ⟶ Z'`, `e : X' ⟶ X` exhibit `X'` as
the base change `Z' ×_Z X`, so that `X' = Q' ×_Q X`. Then

```text
Res_{Z'/Q'}(X')  =  Q' ×_Q Res_{Z/Q}(X)
```

as presheaves on the big fppf site of `S`: there is an isomorphism compatible with the
projections to `Q'`, which on sections carries the pair of Stacks 05Y9 of a section of
`Res_{Z'/Q'}(X')` to its base change
`AlgebraicGeometry.Space.RestrictionPair.baseChange`.

For the chosen fibre products of Stacks 02X2 the two hypotheses are
`AlgebraicGeometry.Space.isPullback_hom_fiberProduct` and
`AlgebraicGeometry.Space.isPullback_baseChangeFiberProductMap`; that instance is
`AlgebraicGeometry.Space.restrictionOfScalars_baseChange_fiberProduct`. -/
@[stacks 05YC "the base-change identification"]
theorem restrictionOfScalars_baseChange :
    ∃ i : r'.presheaf ≅ pullback b.hom r.projection,
      i.hom ≫ pullback.fst b.hom r.projection = r'.projection ∧
        ∀ (T : BigFppfOver B S hS) (v : r'.presheaf.obj (op T)),
          r.pairEquiv T ((i.hom ≫ pullback.snd b.hom r.projection).app (op T) v) =
            (r'.pairEquiv T v).baseChange hZ hX := by
  have hbij : ∀ I, IsIso ((toPullbackProjection hZ hX r r').app I) := fun I =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toPullbackProjection_app hZ hX r r' I)
  have : IsIso (toPullbackProjection hZ hX r r') :=
    NatIso.isIso_of_isIso_app (toPullbackProjection hZ hX r r')
  refine ⟨asIso (toPullbackProjection hZ hX r r'), toPullbackProjection_fst hZ hX r r',
    fun T v => ?_⟩
  rw [asIso_hom, toPullbackProjection_snd]
  exact pairEquiv_baseChangeMap_app hZ hX r r' (op T) v

end BaseChange

/-! ### Base change for the chosen fibre products -/

section FiberProductBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05YC.** The form of `AlgebraicGeometry.Space.restrictionOfScalars_baseChange` for
the chosen fibre products of Stacks 02X2: with `Z' = Q' ×_Q Z` and `X' = Q' ×_Q X` those fibre
products and `x' : X' ⟶ Z'` the base-changed morphism
`AlgebraicGeometry.Space.baseChangeFiberProductMap`,

```text
Res_{Z'/Q'}(X')  =  Q' ×_Q Res_{Z/Q}(X)
```

as presheaves on the big fppf site of `S`, compatibly with the projections to `Q'`. -/
@[stacks 05YC "the base-change identification for the chosen fibre products"]
theorem restrictionOfScalars_baseChange_fiberProduct {X Z Q Q' : AlgebraicSpaces B S hS}
    (x : X ⟶ Z) (z : Z ⟶ Q) (b : Q' ⟶ Q)
    (r : RestrictionOfScalarsConstruction B S hS x z)
    (r' : RestrictionOfScalarsConstruction B S hS (baseChangeFiberProductMap B S hS x z b)
      (ObjectProperty.homMk (pullback.fst b.hom z.hom) :
        AlgebraicSpaces.fiberProduct B S hS b z ⟶ Q')) :
    ∃ i : r'.presheaf ≅ pullback b.hom r.projection,
      i.hom ≫ pullback.fst b.hom r.projection = r'.projection ∧
        ∀ (T : BigFppfOver B S hS) (v : r'.presheaf.obj (op T)),
          r.pairEquiv T ((i.hom ≫ pullback.snd b.hom r.projection).app (op T) v) =
            (r'.pairEquiv T v).baseChange (isPullback_hom_fiberProduct B S hS b z)
              (isPullback_baseChangeFiberProductMap B S hS x z b) :=
  restrictionOfScalars_baseChange _ _ r r'

end FiberProductBaseChange

end AlgebraicGeometry.Space

end
