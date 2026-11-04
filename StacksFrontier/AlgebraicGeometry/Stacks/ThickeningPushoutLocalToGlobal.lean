module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RXFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutLocalDescent
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange

/-!
# Restriction to a thickening-and-affine pushout: from local to global

Let `X ⟶ X'` be a thickening and `X ⟶ Y` an affine morphism of schemes over `S`, with pushout
`Y' = Y ⨿_X X'` (Stacks 07RT), and let `𝒳` be a stack in groupoids over the big fppf site of `S`
whose isomorphism presheaves are algebraic spaces — for instance an algebraic stack. The proof of
Stacks 07WN shows that the comparison functor

`𝒳_{Y'} ⥤ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}`

is an equivalence in two steps: it is full and faithful
(`AlgebraicGeometry.Stack.ThickeningPushout.fiberSquareComparison_full_and_faithful`), and "it
suffices to construct a preimage fppf locally on `Y'`". This file proves the second step: an
object of the two-fibre product which, after base change along a flat, locally finitely presented
and surjective morphism `Y'₁ ⟶ Y'`, comes from an object over `Y'₁`, comes from an object over
`Y'`.

The base change of the pushout square along a flat morphism `T ⟶ Y'` is again a
thickening-and-affine pushout square, by the closing paragraph of Stacks 07RX
(`Stacks.Pushout.gluingAdjunction_counit_app_isIso_of_flat`); so the comparison functor is full
and faithful after every such base change, and the generic local-to-global step
`Deformation.Artin.mem_essImage_fiberSquareComparison_of_localPreimage` applies.

## Main results

* `Stacks.Pushout.isPushout_of_isPullback_of_flat`: the base change of a thickening-and-affine
  pushout square of schemes along a flat morphism is a pushout square.
* `AlgebraicGeometry.Stack.ThickeningPushout.isGluingSquare_baseChange`: after base change along
  a flat morphism, the cartesian lifts of the square to `𝒳` form a pushout in `𝒳`.
* `AlgebraicGeometry.Stack.ThickeningPushout.mem_essImage_fiberSquareComparison_of_localPreimage`:
  the local-to-global step.
* `AlgebraicGeometry.Stack.ThickeningPushout.fiberSquareComparison_isEquivalence_of_localPreimage`:
  if every object of the two-fibre product admits a local preimage, the comparison functor is an
  equivalence.

## Implementation notes

The local data are packaged as `Deformation.Artin.LocalPreimage`: an object over `Y'₁` together
with spans in `𝒳` identifying its restrictions to `Y ×_{Y'} Y'₁` and `X' ×_{Y'} Y'₁` with those
of the two components of the given object, compatibly over `X ×_{Y'} Y'₁`. The fibre products are
those of the big fppf site of `S`, which has all of them.

No declaration here carries `@[stacks 07WN]`: the essential surjectivity of the comparison
functor also needs the construction of the local preimages, through pushouts of algebraic spaces
(Stacks 07VX, 07W3), which is not done here.

## References

* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Stacks.Pushout

open Stacks.Thickenings

variable {X X' Y Y' : Scheme.{u}}

/-- The base change of the pushout square `Y ⨿_X X'` along a flat `W' ⟶ Y ⨿_X X'`, with its
corners written as fibre products over `W'`, is a pushout square. -/
theorem isPushout_pullback_pushout_of_flat (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] [HasPushout i f] (W' : Over (pushout i f)) (hW : Flat W'.hom) :
    IsPushout (pullback.fst (pullback.snd W'.hom (pushout.inl i f)) i)
      (gluingSourceMap i f ((baseChangeFunctor i f hi).obj W'))
      (pullback.fst W'.hom (pushout.inl i f)) (pullback.fst W'.hom (pushout.inr i f)) := by
  have hc := gluingAdjunction_counit_app_isIso_of_flat i f hi W' hW
  let T₀ := (baseChangeFunctor i f hi).obj W'
  have := gluingHasPushout i f hi T₀
  let c := ((gluingAdjunction i f hi).counit.app W').left
  have hcl : IsIso c := by
    show IsIso ((Over.forget _).map ((gluingAdjunction i f hi).counit.app W'))
    infer_instance
  have hc' : c = (gluingFromPair i f hi (𝟙 T₀)).left :=
    congrArg CommaMorphism.left (gluingAdjunction_counit_app_eq i f hi W')
  have hinl : pushout.inl (pullback.fst T₀.obj.right.hom i) (gluingSourceMap i f T₀) ≫ c =
      pullback.fst W'.hom (pushout.inl i f) := by
    rw [hc', inl_comp_gluingFromPair]
    exact Category.id_comp _
  have hinr : pushout.inr (pullback.fst T₀.obj.right.hom i) (gluingSourceMap i f T₀) ≫ c =
      pullback.fst W'.hom (pushout.inr i f) := by
    rw [hc', inr_comp_gluingFromPair]
    exact Category.id_comp _
  have h₀ : IsPushout (pullback.fst T₀.obj.right.hom i) (gluingSourceMap i f T₀)
      (pullback.fst W'.hom (pushout.inl i f)) (pullback.fst W'.hom (pushout.inr i f)) :=
    (IsPushout.of_hasPushout (pullback.fst T₀.obj.right.hom i)
      (gluingSourceMap i f T₀)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (@asIso _ _ _ _ c hcl) (by simp) (by simp) (hinl.trans (Category.id_comp _).symm)
      (hinr.trans (Category.id_comp _).symm)
  exact h₀

/-- **The base change of a thickening-and-affine pushout along a flat morphism is a pushout.** Let
`Y' = Y ⨿_X X'` be the pushout of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y`,
and let `t : T ⟶ Y'` be flat. Then the base change of the square along `t`, with corners
`Y ×_{Y'} T`, `X' ×_{Y'} T` and `X ×_{Y'} T` given by any cartesian squares, is again a pushout.

This is the closing paragraph of Stacks 07RX: `T` is glued from its two base changes. -/
theorem isPushout_of_isPullback_of_flat (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (hi : IsThickening i) [IsAffineHom f] (hsq : IsPushout i f a b)
    {T TY TX' TX : Scheme.{u}} (t : T ⟶ Y') [Flat t]
    (bT : TY ⟶ T) (tY : TY ⟶ Y) (hY : IsPullback bT tY t b)
    (aT : TX' ⟶ T) (tX' : TX' ⟶ X') (hX' : IsPullback aT tX' t a)
    (iT : TX ⟶ TX') (tX : TX ⟶ X) (hX : IsPullback iT tX tX' i)
    (fT : TX ⟶ TY) (hfT : fT ≫ tY = tX ≫ f) (hw : fT ≫ bT = iT ≫ aT) :
    IsPushout iT fT aT bT := by
  have := hasPushout_of_isThickening i f hi
  let φ := hsq.isoPushout
  let W' : Over (pushout i f) := Over.mk (t ≫ φ.hom)
  let T₀ := (baseChangeFunctor i f hi).obj W'
  have hX'φ : IsPullback aT tX' W'.hom (pushout.inl i f) :=
    hX'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) φ (by simp) (by simp) (by simp [W'])
      (by simp [φ])
  have hYφ : IsPullback bT tY W'.hom (pushout.inr i f) :=
    hY.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) φ (by simp) (by simp) (by simp [W'])
      (by simp [φ])
  let e₂ := (IsPullback.of_hasPullback W'.hom (pushout.inl i f)).isoIsPullback _ _ hX'φ
  let e₃ := (IsPullback.of_hasPullback W'.hom (pushout.inr i f)).isoIsPullback _ _ hYφ
  have hXe : IsPullback (iT ≫ e₂.inv) tX (pullback.snd W'.hom (pushout.inl i f)) i :=
    hX.of_iso (Iso.refl _) e₂.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [e₂]) (by simp)
  let e₁ := (IsPullback.of_hasPullback (pullback.snd W'.hom (pushout.inl i f)) i).isoIsPullback
    _ _ hXe
  let g : pullback (pullback.snd W'.hom (pushout.inl i f)) i ⟶
      pullback W'.hom (pushout.inr i f) := gluingSourceMap i f T₀
  have h₀' : IsPushout (pullback.fst (pullback.snd W'.hom (pushout.inl i f)) i) g
      (pullback.fst W'.hom (pushout.inl i f)) (pullback.fst W'.hom (pushout.inr i f)) :=
    isPushout_pullback_pushout_of_flat i f hi W' (inferInstanceAs (Flat (t ≫ φ.hom)))
  have k₂f : e₂.hom ≫ aT = pullback.fst W'.hom (pushout.inl i f) :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have k₃f : e₃.hom ≫ bT = pullback.fst W'.hom (pushout.inr i f) :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have k₃s : e₃.hom ≫ tY = pullback.snd W'.hom (pushout.inr i f) :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have k₁f : e₁.hom ≫ iT ≫ e₂.inv = pullback.fst (pullback.snd W'.hom (pushout.inl i f)) i :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have k₁s : e₁.hom ≫ tX = pullback.snd (pullback.snd W'.hom (pushout.inl i f)) i :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have he₁ : pullback.fst (pullback.snd W'.hom (pushout.inl i f)) i ≫ e₂.hom = e₁.hom ≫ iT := by
    rw [← k₁f, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hg : g ≫ e₃.hom = e₁.hom ≫ fT := by
    refine hY.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, k₃f, hw, ← Category.assoc, ← he₁, Category.assoc, k₂f]
      exact h₀'.w.symm
    · rw [Category.assoc, Category.assoc, k₃s, hfT, ← Category.assoc, k₁s]
      exact (gluingSourceMap_isPullback i f T₀).w
  exact h₀'.of_iso e₁ e₂ e₃ (Iso.refl _) he₁ hg (by rw [Iso.refl_hom, Category.comp_id, k₂f])
    (by rw [Iso.refl_hom, Category.comp_id, k₃f])

end Stacks.Pushout

namespace AlgebraicGeometry.Stack.ThickeningPushout

open Deformation.Artin Stacks.Thickenings

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The forgetful functor from the big fppf site of `S` to schemes preserves fibre products. -/
instance preservesLimitsOfShape_walkingCospan_toScheme :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
  apply comp_preservesLimitsOfShape

variable {B S hS}

/-- The base change of a flat morphism of the big fppf site is flat. -/
lemma flat_toScheme_map_pullback_fst {T T' Z : BigFppfOver B S hS} (k : T' ⟶ Z) (q : T ⟶ Z)
    (hq : Flat ((BigFppfOver.toScheme B S hS).map q)) :
    Flat ((BigFppfOver.toScheme B S hS).map (pullback.fst k q)) :=
  MorphismProperty.of_isPullback (P := @Flat)
    ((IsPullback.of_hasPullback k q).map (BigFppfOver.toScheme B S hS)).flip hq

/-- The composite of two flat morphisms of the big fppf site is flat. -/
lemma flat_toScheme_map_comp {T T' Z : BigFppfOver B S hS} (k : T' ⟶ T) (q : T ⟶ Z)
    (hk : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hq : Flat ((BigFppfOver.toScheme B S hS).map q)) :
    Flat ((BigFppfOver.toScheme B S hS).map (k ≫ q)) := by
  rw [Functor.map_comp]
  infer_instance

variable {X X' Y Y' : BigFppfOver B S hS} {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'}

/-- The base change of the square along `t : T ⟶ Y'`: the corner `X ×_{Y'} T` is the fibre product
of `X'` and `X' ×_{Y'} T` over `X'`. -/
lemma isPullback_baseChangeTop (w : f ≫ b = i ≫ a) {T : BigFppfOver B S hS} (t : T ⟶ Y') :
    IsPullback (baseChangeTop f i b a w t) (pullback.fst (f ≫ b) t) (pullback.fst a t) i := by
  refine IsPullback.of_right (h₁₂ := pullback.snd a t) (h₂₂ := a) (v₁₃ := t) ?_
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback a t).flip
  exact (IsPullback.of_hasPullback (f ≫ b) t).flip.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (pullback.lift_snd _ _ _).symm)
    (by simp) (by simp) (by simp [w])

/-- The base change of the square along `t : T ⟶ Y'`: the corner `X ×_{Y'} T` is the fibre product
of `X` and `Y ×_{Y'} T` over `Y`. -/
lemma isPullback_baseChangeLeft {T : BigFppfOver B S hS} (t : T ⟶ Y') :
    IsPullback (baseChangeLeft f b t) (pullback.fst (f ≫ b) t) (pullback.fst b t) f := by
  refine IsPullback.of_right (h₁₂ := pullback.snd b t) (h₂₂ := b) (v₁₃ := t) ?_
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback b t).flip
  exact (IsPullback.of_hasPullback (f ≫ b) t).flip.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ((Category.comp_id _).trans (pullback.lift_snd _ _ _).symm)
    (by simp) (by simp) (by simp)

/-- **After base change along a flat morphism, the cartesian lifts of a thickening-and-affine
pushout square form a pushout in the stack.** Let `𝒳` be a category fibred in groupoids over the
big fppf site of `S` whose isomorphism presheaves are algebraic spaces, let `X ⟶ X'` be a
thickening and `X ⟶ Y` an affine morphism with pushout `Y'`, and let `t : T ⟶ Y'` be flat. Then
the base change of the square along `t` is a gluing square for `𝒳`: its base change is again a
thickening-and-affine pushout square (Stacks 07RX), so its comparison functor is full and
faithful. -/
theorem isGluingSquare_baseChange
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) (w : f ≫ b = i ≫ a)
    (hi : IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    {T : BigFppfOver B S hS} (t : T ⟶ Y') (ht : Flat ((BigFppfOver.toScheme B S hS).map t)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    IsGluingSquare 𝒳.val.p (baseChangeLeft f b t) (baseChangeTop f i b a w t)
      (pullback.snd b t) (pullback.snd a t) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let F := BigFppfOver.toScheme B S hS
  have hX := (isPullback_baseChangeTop w t).map F
  have hL := (isPullback_baseChangeLeft (f := f) (b := b) t).map F
  have hi' : IsThickening (F.map (baseChangeTop f i b a w t)) :=
    isThickening_of_isPullback hX hi
  have : IsAffineHom (F.map (baseChangeLeft f b t)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hL.flip inferInstance
  have w₀ : baseChangeTop f i b a w t ≫ pullback.snd a t =
      baseChangeLeft f b t ≫ pullback.snd b t :=
    (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hpo : IsPushout (F.map (baseChangeTop f i b a w t)) (F.map (baseChangeLeft f b t))
      (F.map (pullback.snd a t)) (F.map (pullback.snd b t)) :=
    Stacks.Pushout.isPushout_of_isPullback_of_flat (F.map i) (F.map f) (F.map a) (F.map b) hi hsq
      (F.map t) (F.map (pullback.snd b t)) (F.map (pullback.fst b t))
      ((IsPullback.of_hasPullback b t).flip.map F) (F.map (pullback.snd a t))
      (F.map (pullback.fst a t)) ((IsPullback.of_hasPullback a t).flip.map F)
      (F.map (baseChangeTop f i b a w t)) (F.map (pullback.fst (f ≫ b) t)) hX
      (F.map (baseChangeLeft f b t)) (by rw [← F.map_comp, ← F.map_comp, pullback.lift_fst])
      (by rw [← F.map_comp, ← F.map_comp, w₀])
  exact isGluingSquare_of_full_of_faithful 𝒳.val.p (baseChangeLeft f b t)
    (baseChangeTop f i b a w t) (pullback.snd b t) (pullback.snd a t) w₀.symm
    (fiberSquareComparison_full_and_faithful B S hS 𝒳 h𝒳 (baseChangeTop f i b a w t)
      (baseChangeLeft f b t) (pullback.snd a t) (pullback.snd b t) w₀ hi' hpo)

/-- **The local-to-global step of Stacks 07WN.** Let `X ⟶ X'` be a thickening and `X ⟶ Y` an
affine morphism of schemes over `S` with pushout `Y' = Y ⨿_X X'`, and let `𝒳` be a stack in
groupoids over the big fppf site of `S` whose isomorphism presheaves are algebraic spaces. Let `e`
be an object of the two-fibre product `𝒳_Y ×_{𝒳_X} 𝒳_{X'}`, and let `q : Y'₁ ⟶ Y'` be flat,
locally of finite presentation and surjective. If `e` has a local preimage along `q` — an object
over `Y'₁` whose restrictions to `Y ×_{Y'} Y'₁` and `X' ×_{Y'} Y'₁` are identified with those of
the two components of `e`, compatibly over `X ×_{Y'} Y'₁` — then `e` is in the essential image of
the comparison functor `𝒳_{Y'} ⥤ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}`. -/
theorem mem_essImage_fiberSquareComparison_of_localPreimage
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) [𝒳.val.p.IsFibered]
    (hst : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒳 : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) (w : i ≫ a = f ≫ b)
    (hi : IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    {Y'₁ : BigFppfOver B S hS} (q : Y'₁ ⟶ Y')
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q))
    (e : CategoricalPullback (𝒳.val.p.chosenPullbacks.pullbackFunctor f)
      (𝒳.val.p.chosenPullbacks.pullbackFunctor i))
    (L : LocalPreimage (p := 𝒳.val.p) (f := f) (i := i) (b := b) (a := a) w.symm e q) :
    (fiberSquareComparison 𝒳.val.p 𝒳.val.p.chosenPullbacks f i b a w.symm).essImage e := by
  have hq := Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS q hqs hqf hqp
  have hq₂ : Flat ((BigFppfOver.toScheme B S hS).map (pullback.fst q q)) :=
    flat_toScheme_map_pullback_fst q q hqf
  have ht₂ : Flat ((BigFppfOver.toScheme B S hS).map (pullback.fst q q ≫ q)) :=
    flat_toScheme_map_comp _ _ hq₂ hqf
  have ht₃ : Flat ((BigFppfOver.toScheme B S hS).map (tripleMap q)) :=
    flat_toScheme_map_comp _ _ (flat_toScheme_map_pullback_fst _ _ hq₂) ht₂
  exact Deformation.Artin.mem_essImage_fiberSquareComparison_of_localPreimage
    𝒳.isFiberedInGroupoids hst w.symm q hq (isGluingSquare_baseChange 𝒳 h𝒳 w.symm hi hsq q hqf)
    (isGluingSquare_baseChange 𝒳 h𝒳 w.symm hi hsq _ ht₂)
    (isGluingSquare_baseChange 𝒳 h𝒳 w.symm hi hsq _ ht₃) e L

/-- **The comparison functor is an equivalence once preimages exist locally.** In the situation of
`AlgebraicGeometry.Stack.ThickeningPushout.mem_essImage_fiberSquareComparison_of_localPreimage`,
if every object of the two-fibre product `𝒳_Y ×_{𝒳_X} 𝒳_{X'}` has a local preimage along some
flat, locally finitely presented and surjective morphism to `Y'`, then the comparison functor
`𝒳_{Y'} ⥤ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}` is an equivalence: it is full and faithful by
`AlgebraicGeometry.Stack.ThickeningPushout.fiberSquareComparison_full_and_faithful`, and
essentially surjective by the local-to-global step. -/
theorem fiberSquareComparison_isEquivalence_of_localPreimage
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) [𝒳.val.p.IsFibered]
    (hst : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (h𝒳 : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) (w : i ≫ a = f ≫ b)
    (hi : IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (hloc : ∀ e : CategoricalPullback (𝒳.val.p.chosenPullbacks.pullbackFunctor f)
      (𝒳.val.p.chosenPullbacks.pullbackFunctor i),
      ∃ (Y'₁ : BigFppfOver B S hS) (q : Y'₁ ⟶ Y'),
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
        Flat ((BigFppfOver.toScheme B S hS).map q) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
        Nonempty (LocalPreimage (p := 𝒳.val.p) (f := f) (i := i) (b := b) (a := a) w.symm e q)) :
    (fiberSquareComparison 𝒳.val.p 𝒳.val.p.chosenPullbacks f i b a w.symm).IsEquivalence := by
  obtain ⟨hfull, hfaith⟩ := fiberSquareComparison_full_and_faithful B S hS 𝒳 h𝒳 i f a b w hi hsq
  refine { faithful := hfaith, full := hfull, essSurj := ⟨fun e => ?_⟩ }
  obtain ⟨Y'₁, q, hqs, hqf, hqp, ⟨L⟩⟩ := hloc e
  exact mem_essImage_fiberSquareComparison_of_localPreimage 𝒳 hst h𝒳 w hi hsq q hqs hqf hqp e L

/-- **The comparison functor of an algebraic stack is an equivalence once preimages exist
locally.** The statement of Stacks 07WN for an algebraic stack `𝒵`, reduced to the existence of
local preimages: if every object of `𝒵_Y ×_{𝒵_X} 𝒵_{X'}` has a local preimage along some flat,
locally finitely presented and surjective morphism to `Y'`, the comparison functor
`𝒵_{Y'} ⥤ 𝒵_Y ×_{𝒵_X} 𝒵_{X'}` is an equivalence. -/
theorem fiberSquareComparison_isEquivalence_of_isAlgebraicStack_of_localPreimage.{w'}
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsAlgebraicStack.{u, w'} B S hS 𝒵) (w : i ≫ a = f ≫ b)
    (hi : IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b))
    (hloc : letI : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
      ∀ e : CategoricalPullback (𝒵.p.chosenPullbacks.pullbackFunctor f)
        (𝒵.p.chosenPullbacks.pullbackFunctor i),
      ∃ (Y'₁ : BigFppfOver B S hS) (q : Y'₁ ⟶ Y'),
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
        Flat ((BigFppfOver.toScheme B S hS).map q) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
        Nonempty (LocalPreimage (p := 𝒵.p) (f := f) (i := i) (b := b) (a := a) w.symm e q)) :
    letI : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
    (fiberSquareComparison 𝒵.p 𝒵.p.chosenPullbacks f i b a w.symm).IsEquivalence := by
  let : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
  let 𝒳 := CatFiberedInGroupoids.mk 𝒵 (Classical.choose h𝒵)
  exact fiberSquareComparison_isEquivalence_of_localPreimage 𝒳 (Classical.choose_spec h𝒵).1.1
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp
      (Classical.choose_spec h𝒵).2.1) w hi hsq hloc

end AlgebraicGeometry.Stack.ThickeningPushout
