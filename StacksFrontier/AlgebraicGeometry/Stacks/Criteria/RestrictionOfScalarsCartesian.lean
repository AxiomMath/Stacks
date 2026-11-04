module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalars

/-!
# Restriction of scalars as a fibre product of relative morphism functors

Let `S` be a scheme contained in a big fppf site and let `x : X ⟶ Z` and `z : Z ⟶ Q` be morphisms
of algebraic spaces over `S`. The restriction of scalars `Res_{Z/Q}(X)` of Stacks 05YA sits in a
square

```text
Mor_Q(Z, X) ⟶ Mor_Q(Z, Z)
     ↑              ↑ id_Z
Res_{Z/Q}(X) ⟶     Q
```

of presheaves on the big fppf site of `S`, and that square is cartesian. Its top arrow
postcomposes the second component of a pair of Stacks 05Y1 with `x`; its left arrow forgets that
the second component of a pair of Stacks 05Y9 lies over `Z` and remembers only that it lies over
`Q`; its bottom arrow is the projection of Stacks 05YA, reading off the first component; and its
right arrow sends `a : T ⟶ Q` to the identity endomorphism of `T ×_{a, Q} Z`, which in the
description of a pair used here is the projection `T ×_{a, Q} Z ⟶ Z`.

## Main definitions

* `AlgebraicGeometry.Space.relativeHomPostcompose`: the morphism `Mor_Q(Z, X) ⟶ Mor_Q(Z, X')`
  induced by a morphism `g : X ⟶ X'` over `Q`, by postcomposition on second components.
* `AlgebraicGeometry.Space.relativeHomIdentity`: the morphism `Q ⟶ Mor_Q(Z, Z)` sending
  `a : T ⟶ Q` to the identity endomorphism of `T ×_{a, Q} Z`.
* `AlgebraicGeometry.Space.restrictionOfScalarsToRelativeHom`: the morphism
  `Res_{Z/Q}(X) ⟶ Mor_Q(Z, X)` forgetting that the second component of a pair lies over `Z`.
* `AlgebraicGeometry.Space.restrictionOfScalarsOfPairs`: the morphism into `Res_{Z/Q}(X)` defined
  by a family of pairs of Stacks 05Y9 compatible with base change.
* `AlgebraicGeometry.Space.RelativeMorphism.postcomp` and
  `AlgebraicGeometry.Space.RelativeMorphism.identity`: postcomposition of a pair of Stacks 05Y1 in
  its second component, and the pair whose second component is the projection to `Z`.

## Main results

* `AlgebraicGeometry.Space.isPullback_restrictionOfScalars` and
  `AlgebraicGeometry.Space.isPullback_restrictionOfScalars_relativeHomData`: **Stacks 05YE**, the
  square above is cartesian in presheaves on the big fppf site of `S` — for an arbitrary
  construction of the two functors, and for the constructions of Stacks 05YA and 05Y2.
* `AlgebraicGeometry.Space.sections_relativeHomPostcompose`,
  `AlgebraicGeometry.Space.sections_relativeHomIdentity` and
  `AlgebraicGeometry.Space.sections_restrictionOfScalarsToRelativeHom`: the three arrows read on
  sections.
* `AlgebraicGeometry.Space.RestrictionPair.postcomp_toRelativeMorphism` and
  `AlgebraicGeometry.Space.RelativeMorphism.liesOverZ_of_postcomp_eq_identity`: a pair of
  Stacks 05Y1 for `x ≫ z` lies over `Z` exactly when postcomposing its second component with `x`
  produces the identity endomorphism of the base change of `Z`.

## References

* [Stacks Project, Tag 05YE](https://stacks.math.columbia.edu/tag/05YE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ u₁

namespace CategoryTheory

/-- Naturality of the Yoneda bijection, read on the inverse bijection: the morphism
`yoneda.obj Y ⟶ F` attached to a restricted section is the restriction of the morphism attached to
the section. -/
theorem yonedaEquiv_symm_naturality {C : Type u₁} [Category.{v₁} C] {F : Cᵒᵖ ⥤ Type v₁} {X Y : C}
    (a : F.obj (op X)) (g : Y ⟶ X) :
    yonedaEquiv.symm (F.map g.op a) = yoneda.map g ≫ yonedaEquiv.symm a := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]

namespace Limits

variable {C : Type u₁} [Category.{v₁} C]

/-- The first projection of the comparison isomorphism of two fibre products that differ only in
their first factor. -/
@[reassoc (attr := simp)]
theorem pullback.congrHom_hom_fst {W X Y : C} {f₁ f₂ : W ⟶ Y} (g : X ⟶ Y) (h : f₁ = f₂)
    [HasPullback f₁ g] [HasPullback f₂ g] :
    (pullback.congrHom h (rfl : g = g)).hom ≫ pullback.fst f₂ g = pullback.fst f₁ g := by
  simp [pullback.congrHom]

/-- The second projection of the comparison isomorphism of two fibre products that differ only in
their first factor. -/
@[reassoc (attr := simp)]
theorem pullback.congrHom_hom_snd {W X Y : C} {f₁ f₂ : W ⟶ Y} (g : X ⟶ Y) (h : f₁ = f₂)
    [HasPullback f₁ g] [HasPullback f₂ g] :
    (pullback.congrHom h (rfl : g = g)).hom ≫ pullback.snd f₂ g = pullback.snd f₁ g := by
  simp [pullback.congrHom]

/-- Base change of a fibre product in its first factor does not move the projection to the second
factor. -/
theorem pullback.map_id_snd {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (g : X ⟶ Y)
    [HasPullback a g] [HasPullback (t ≫ a) g] (e₁ : (t ≫ a) ≫ 𝟙 Y = t ≫ a)
    (e₂ : g ≫ 𝟙 Y = 𝟙 X ≫ g) :
    pullback.map (t ≫ a) g a g t (𝟙 X) (𝟙 Y) e₁ e₂ ≫ pullback.snd a g =
      pullback.snd (t ≫ a) g := by
  rw [pullback.map_snd, Category.comp_id]

end Limits

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Operations on pairs -/

/-- Two pairs of Stacks 05Y1 with the same first component are equal as soon as their second
components are. -/
theorem RelativeMorphism.mk_eq_mk {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} {b : T ⟶ Q} {m m' : pullback b z ⟶ X} (hm : m = m')
    {hc : m ≫ x = pullback.snd b z ≫ z} {hc' : m' ≫ x = pullback.snd b z ≫ z} :
    (RelativeMorphism.mk b m hc : RelativeMorphism B S hS Z X Q z x T) =
      RelativeMorphism.mk b m' hc' := by
  subst hm
  rfl

/-- Postcomposition of a pair `(a, b)` of Stacks 05Y1 in its second component with a morphism
`g : X ⟶ X'` over the base `Q`. -/
noncomputable def RelativeMorphism.postcomp {Z X X' Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {x' : X' ⟶ Q} (g : X ⟶ X') (hg : g ≫ x' = x)
    (p : RelativeMorphism B S hS Z X Q z x T) : RelativeMorphism B S hS Z X' Q z x' T where
  base := p.base
  morphism := p.morphism ≫ g
  commutes := by
    rw [Category.assoc, hg]
    exact p.commutes

/-- The first component of a pair is unchanged by postcomposition. -/
@[simp] theorem RelativeMorphism.postcomp_base {Z X X' Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {x' : X' ⟶ Q} (g : X ⟶ X') (hg : g ≫ x' = x)
    (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.postcomp g hg p).base = p.base := rfl

/-- The second component of a postcomposed pair. -/
@[simp] theorem RelativeMorphism.postcomp_morphism {Z X X' Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {x' : X' ⟶ Q} (g : X ⟶ X') (hg : g ≫ x' = x)
    (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.postcomp g hg p).morphism = p.morphism ≫ g := rfl

/-- The pair of Stacks 05Y1 recording the identity endomorphism of `T ×_{a, Q} Z`: its first
component is `a` and its second component is the projection to `Z`. -/
noncomputable def RelativeMorphism.identity {Z Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q)
    (a : T ⟶ Q) : RelativeMorphism B S hS Z Z Q z z T where
  base := a
  morphism := pullback.snd a z
  commutes := rfl

/-- The first component of the identity pair. -/
@[simp] theorem RelativeMorphism.identity_base {Z Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ Q) (a : T ⟶ Q) : (RelativeMorphism.identity z a).base = a := rfl

/-- The second component of the identity pair. -/
@[simp] theorem RelativeMorphism.identity_morphism {Z Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ Q) (a : T ⟶ Q) :
    (RelativeMorphism.identity z a).morphism = pullback.snd a z := rfl

/-- The second components of two equal pairs agree after the canonical identification of their two
base changes. This is the converse of
`AlgebraicGeometry.Space.RelativeMorphism.ext_of_base_eq`. -/
theorem RelativeMorphism.morphism_eq_of_eq {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} {p q : RelativeMorphism B S hS Z X Q z x T} (h : p = q)
    (hbase : p.base = q.base) :
    p.morphism = (pullback.congrHom hbase rfl).hom ≫ q.morphism := by
  subst h
  have hid : (pullback.congrHom hbase (rfl : z = z)).hom = 𝟙 (pullback p.base z) :=
    pullback.hom_ext (by rw [pullback.congrHom_hom_fst, Category.id_comp])
      (by rw [pullback.congrHom_hom_snd, Category.id_comp])
  rw [hid, Category.id_comp]

/-- Postcomposition commutes with base change of pairs. -/
theorem RelativeMorphism.restrict_postcomp {Z X X' Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {x' : X' ⟶ Q} (g : X ⟶ X') (hg : g ≫ x' = x) (t : T' ⟶ T)
    (p : RelativeMorphism B S hS Z X Q z x T) :
    RelativeMorphism.restrict t (RelativeMorphism.postcomp g hg p) =
      RelativeMorphism.postcomp g hg (RelativeMorphism.restrict t p) :=
  RelativeMorphism.mk_eq_mk (Category.assoc _ _ _).symm

/-- The identity pair base changes to the identity pair. -/
theorem RelativeMorphism.restrict_identity {Z Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (z : Z ⟶ Q) (a : T ⟶ Q) (t : T' ⟶ T) :
    RelativeMorphism.restrict t (RelativeMorphism.identity z a) =
      RelativeMorphism.identity z (t ≫ a) :=
  RelativeMorphism.mk_eq_mk (pullback.map_id_snd t a z _ _)

/-- The base change of a pair along a morphism is unique: a pair `p'` presented as a base change
of `p` along `f`, by a comparison of the two fibre products, equals
`AlgebraicGeometry.Space.RelativeMorphism.restrict f p`. -/
theorem RelativeMorphism.eq_restrict_of_comparison
    {Z X Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q} {f : T' ⟶ T}
    {p : RelativeMorphism B S hS Z X Q z x T} {p' : RelativeMorphism B S hS Z X Q z x T'}
    (hbase : p'.base = f ≫ p.base)
    (h : ∃ c : pullback p'.base z ⟶ pullback p.base z,
      (c ≫ pullback.fst p.base z = pullback.fst p'.base z ≫ f) ∧
      (c ≫ pullback.snd p.base z = pullback.snd p'.base z) ∧
      (p'.morphism = c ≫ p.morphism)) :
    p' = RelativeMorphism.restrict f p := by
  obtain ⟨c, hfst, hsnd, hmor⟩ := h
  refine RelativeMorphism.ext_of_base_eq hbase ?_
  have hc : c = (pullback.congrHom hbase (rfl : z = z)).hom ≫
      pullback.map (f ≫ p.base) z p.base z f (𝟙 Z) (𝟙 Q) (by simp) (by simp) := by
    refine pullback.hom_ext ?_ ?_
    · simpa using hfst
    · simpa using hsnd
  rw [hmor, hc, RelativeMorphism.restrict_morphism, Category.assoc]
  rfl

/-- Forgetting that the second component of a pair of Stacks 05Y9 lies over `Z` commutes with base
change of pairs. -/
theorem RestrictionPair.toRelativeMorphism_restrict {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T)
    (p : RestrictionPair B S hS x z T) :
    (RestrictionPair.restrict f p).toRelativeMorphism =
      RelativeMorphism.restrict f p.toRelativeMorphism := rfl

/-- A pair of Stacks 05Y9 is determined by the pair of Stacks 05Y1 underlying it. -/
theorem RestrictionPair.toRelativeMorphism_injective {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p q : RestrictionPair B S hS x z T}
    (h : p.toRelativeMorphism = q.toRelativeMorphism) : p = q :=
  RestrictionPair.ext_of_base_eq (congrArg RelativeMorphism.base h)
    (RelativeMorphism.morphism_eq_of_eq h (congrArg RelativeMorphism.base h))

/-- The pair of Stacks 05Y1 underlying the pair of Stacks 05Y9 built from a pair lying over `Z`
is that pair again. -/
@[simp] theorem toRelativeMorphism_restrictionPairEquivSubtype
    {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : {p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) T //
      RelativeMorphism.LiesOverZ x z p}) :
    (restrictionPairEquivSubtype x z T p).toRelativeMorphism = p.1 := rfl

/-! ### Lying over `Z` as an equality of pairs

The second component of a pair of Stacks 05Y1 for `x ≫ z` lies over `Z` exactly when
postcomposing it with `x` produces the identity endomorphism of the base change of `Z`. -/

/-- Postcomposing the pair of Stacks 05Y1 underlying a pair of Stacks 05Y9 with `x` gives the
identity pair. -/
theorem RestrictionPair.postcomp_toRelativeMorphism {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : RestrictionPair B S hS x z T) :
    RelativeMorphism.postcomp x.hom rfl p.toRelativeMorphism =
      RelativeMorphism.identity z.hom p.base :=
  RelativeMorphism.mk_eq_mk p.over

/-- A pair of Stacks 05Y1 that postcomposes to an identity pair lies over `Z`. -/
theorem RelativeMorphism.liesOverZ_of_postcomp_eq_identity {X Z Q : AlgebraicSpaces B S hS}
    {x : X ⟶ Z} {z : Z ⟶ Q} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : RelativeMorphism B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) T} {a : T ⟶ Q.obj}
    (h : RelativeMorphism.postcomp x.hom rfl p = RelativeMorphism.identity z.hom a) :
    RelativeMorphism.LiesOverZ x z p :=
  (RelativeMorphism.morphism_eq_of_eq h (congrArg RelativeMorphism.base h)).trans
    (pullback.congrHom_hom_snd z.hom (congrArg RelativeMorphism.base h))

/-! ### The arrows of the diagram -/

/-- The restriction maps of a relative morphism functor are base change of pairs, as an equality
of pairs rather than up to a comparison of fibre products. -/
theorem RelativeHomConstruction.sections_map_eq {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (H : RelativeHomConstruction B S hS Z X Q z x)
    {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U) (p : H.functor.obj T) :
    H.sections U.unop (H.functor.map f p) =
      RelativeMorphism.restrict (yoneda.map f.unop) (H.sections T.unop p) := by
  obtain ⟨hbase, c, hfst, hsnd, hmor⟩ := H.sections_map f.unop p
  exact RelativeMorphism.eq_restrict_of_comparison hbase ⟨c, hfst, hsnd, hmor⟩

/-- The morphism `Mor_Q(Z, X) ⟶ Mor_Q(Z, X')` of relative morphism functors induced by a morphism
`g : X ⟶ X'` over `Q`: postcompose the second component of a pair with `g`. -/
noncomputable def relativeHomPostcompose {Z X X' Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} {x' : X' ⟶ Q} (HX : RelativeHomConstruction B S hS Z X Q z x)
    (HX' : RelativeHomConstruction B S hS Z X' Q z x') (g : X ⟶ X') (hg : g ≫ x' = x) :
    HX.functor ⟶ HX'.functor where
  app T := ↾fun p =>
    (HX'.sections T.unop).symm (RelativeMorphism.postcomp g hg (HX.sections T.unop p))
  naturality T U f := by
    ext p
    refine (HX'.sections U.unop).injective ?_
    change HX'.sections U.unop ((HX'.sections U.unop).symm
          (RelativeMorphism.postcomp g hg (HX.sections U.unop (HX.functor.map f p)))) =
        HX'.sections U.unop (HX'.functor.map f ((HX'.sections T.unop).symm
          (RelativeMorphism.postcomp g hg (HX.sections T.unop p))))
    rw [Equiv.apply_symm_apply, HX'.sections_map_eq, Equiv.apply_symm_apply,
      HX.sections_map_eq, RelativeMorphism.restrict_postcomp]

/-- On sections, `AlgebraicGeometry.Space.relativeHomPostcompose` postcomposes the second
component of a pair with `g`. -/
theorem sections_relativeHomPostcompose {Z X X' Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} {x' : X' ⟶ Q} (HX : RelativeHomConstruction B S hS Z X Q z x)
    (HX' : RelativeHomConstruction B S hS Z X' Q z x') (g : X ⟶ X') (hg : g ≫ x' = x)
    (T : (BigFppfOver B S hS)ᵒᵖ) (p : HX.functor.obj T) :
    HX'.sections T.unop ((relativeHomPostcompose HX HX' g hg).app T p) =
      RelativeMorphism.postcomp g hg (HX.sections T.unop p) :=
  Equiv.apply_symm_apply _ _

/-- The morphism `Q ⟶ Mor_Q(Z, Z)` sending `a : T ⟶ Q` to the identity endomorphism of
`T ×_{a, Q} Z`, which in the description of a pair used here is the projection
`T ×_{a, Q} Z ⟶ Z`. -/
noncomputable def relativeHomIdentity {Z Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    (H : RelativeHomConstruction B S hS Z Z Q z z) : Q ⟶ H.functor where
  app T := ↾fun a => (H.sections T.unop).symm (RelativeMorphism.identity z (yonedaEquiv.symm a))
  naturality T U f := by
    ext a
    refine (H.sections U.unop).injective ?_
    have hy : (yonedaEquiv.symm (Q.map f a) : yoneda.obj U.unop ⟶ Q) =
        yoneda.map f.unop ≫ yonedaEquiv.symm a :=
      yonedaEquiv_symm_naturality a f.unop
    change H.sections U.unop ((H.sections U.unop).symm
          (RelativeMorphism.identity z (yonedaEquiv.symm (Q.map f a)))) =
        H.sections U.unop (H.functor.map f ((H.sections T.unop).symm
          (RelativeMorphism.identity z (yonedaEquiv.symm a))))
    rw [Equiv.apply_symm_apply, H.sections_map_eq, Equiv.apply_symm_apply,
      RelativeMorphism.restrict_identity, hy]

/-- On sections, `AlgebraicGeometry.Space.relativeHomIdentity` produces the pair whose second
component is the projection to `Z`. -/
theorem sections_relativeHomIdentity {Z Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    (H : RelativeHomConstruction B S hS Z Z Q z z) (T : (BigFppfOver B S hS)ᵒᵖ) (a : Q.obj T) :
    H.sections T.unop ((relativeHomIdentity H).app T a) =
      RelativeMorphism.identity z (yonedaEquiv.symm a) :=
  Equiv.apply_symm_apply _ _

/-- The morphism `Res_{Z/Q}(X) ⟶ Mor_Q(Z, X)` forgetting that the second component of a pair of
Stacks 05Y9 lies over `Z` and remembering only that it lies over `Q`. -/
noncomputable def restrictionOfScalarsToRelativeHom {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} (R : RestrictionOfScalarsConstruction B S hS x z)
    (H : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom)) :
    R.presheaf ⟶ H.functor where
  app T := ↾fun v => (H.sections T.unop).symm (R.pairEquiv T.unop v).toRelativeMorphism
  naturality T U f := by
    ext v
    refine (H.sections U.unop).injective ?_
    have hR : R.pairEquiv U.unop (R.presheaf.map f v) =
        RestrictionPair.restrict (yoneda.map f.unop) (R.pairEquiv T.unop v) :=
      RestrictionPair.eq_restrict_of_isPullbackAlong (R.natural f.unop v)
    change H.sections U.unop ((H.sections U.unop).symm
          (R.pairEquiv U.unop (R.presheaf.map f v)).toRelativeMorphism) =
        H.sections U.unop (H.functor.map f ((H.sections T.unop).symm
          (R.pairEquiv T.unop v).toRelativeMorphism))
    rw [Equiv.apply_symm_apply, H.sections_map_eq, Equiv.apply_symm_apply, hR,
      RestrictionPair.toRelativeMorphism_restrict]

/-- On sections, `AlgebraicGeometry.Space.restrictionOfScalarsToRelativeHom` sends a pair of
Stacks 05Y9 to its underlying pair of Stacks 05Y1. -/
theorem sections_restrictionOfScalarsToRelativeHom {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} (R : RestrictionOfScalarsConstruction B S hS x z)
    (H : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom))
    (T : (BigFppfOver B S hS)ᵒᵖ) (v : R.presheaf.obj T) :
    H.sections T.unop ((restrictionOfScalarsToRelativeHom R H).app T v) =
      (R.pairEquiv T.unop v).toRelativeMorphism :=
  Equiv.apply_symm_apply _ _

/-- A family of pairs of Stacks 05Y9, one for every point of a presheaf `W` and compatible with
base change, defines a morphism `W ⟶ Res_{Z/Q}(X)`. -/
noncomputable def restrictionOfScalarsOfPairs {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} (R : RestrictionOfScalarsConstruction B S hS x z)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (P : ∀ T : (BigFppfOver B S hS)ᵒᵖ, W.obj T → RestrictionPair B S hS x z (yoneda.obj T.unop))
    (hP : ∀ {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U) (w : W.obj T),
      P U (W.map f w) = RestrictionPair.restrict (yoneda.map f.unop) (P T w)) :
    W ⟶ R.presheaf where
  app T := ↾fun w => (R.pairEquiv T.unop).symm (P T w)
  naturality T U f := by
    ext w
    refine (R.pairEquiv U.unop).injective ?_
    have hR : R.pairEquiv U.unop (R.presheaf.map f ((R.pairEquiv T.unop).symm (P T w))) =
        RestrictionPair.restrict (yoneda.map f.unop)
          (R.pairEquiv T.unop ((R.pairEquiv T.unop).symm (P T w))) :=
      RestrictionPair.eq_restrict_of_isPullbackAlong
        (R.natural f.unop ((R.pairEquiv T.unop).symm (P T w)))
    change R.pairEquiv U.unop ((R.pairEquiv U.unop).symm (P U (W.map f w))) =
      R.pairEquiv U.unop (R.presheaf.map f ((R.pairEquiv T.unop).symm (P T w)))
    rw [Equiv.apply_symm_apply, hR, Equiv.apply_symm_apply, hP]

/-- The pair attached to a section of a morphism built from a family of pairs is that family's
value. -/
theorem pairEquiv_restrictionOfScalarsOfPairs {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} (R : RestrictionOfScalarsConstruction B S hS x z)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (P : ∀ T : (BigFppfOver B S hS)ᵒᵖ, W.obj T → RestrictionPair B S hS x z (yoneda.obj T.unop))
    (hP : ∀ {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U) (w : W.obj T),
      P U (W.map f w) = RestrictionPair.restrict (yoneda.map f.unop) (P T w))
    (T : (BigFppfOver B S hS)ᵒᵖ) (w : W.obj T) :
    R.pairEquiv T.unop ((restrictionOfScalarsOfPairs R P hP).app T w) = P T w :=
  Equiv.apply_symm_apply _ _

/-! ### The cartesian square -/

/-- The square

```text
Mor_Q(Z, X) ⟶ Mor_Q(Z, Z)
     ↑              ↑ id_Z
Res_{Z/Q}(X) ⟶     Q
```

of presheaves on the big fppf site of `S` is cartesian: the restriction of scalars of `x : X ⟶ Z`
along `z : Z ⟶ Q` is the fibre product of `Mor_Q(Z, X)` and `Q` over `Mor_Q(Z, Z)`, where the
morphism from `Q` picks out the identity endomorphism of `Z`. -/
@[stacks 05YE "the cartesian square of presheaves on the big fppf site"]
theorem isPullback_restrictionOfScalars {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z} {z : Z ⟶ Q}
    (R : RestrictionOfScalarsConstruction B S hS x z)
    (HX : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom))
    (HZ : RelativeHomConstruction B S hS Z.obj Z.obj Q.obj z.hom z.hom) :
    IsPullback (restrictionOfScalarsToRelativeHom R HX) R.projection
      (relativeHomPostcompose HX HZ x.hom rfl) (relativeHomIdentity HZ) := by
  have hproj : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (v : R.presheaf.obj T),
      (R.pairEquiv T.unop v).base = yonedaEquiv.symm (R.projection.app T v) := fun T v =>
    yonedaEquiv.eq_symm_apply.2 (R.projection_pairEquiv T.unop v).symm
  have hw : restrictionOfScalarsToRelativeHom R HX ≫ relativeHomPostcompose HX HZ x.hom rfl =
      R.projection ≫ relativeHomIdentity HZ := by
    ext T v
    refine (HZ.sections T.unop).injective ?_
    exact (sections_relativeHomPostcompose HX HZ x.hom rfl T
        ((restrictionOfScalarsToRelativeHom R HX).app T v)).trans
      ((congrArg (RelativeMorphism.postcomp x.hom rfl)
          (sections_restrictionOfScalarsToRelativeHom R HX T v)).trans
        ((RestrictionPair.postcomp_toRelativeMorphism (R.pairEquiv T.unop v)).trans
          ((congrArg (RelativeMorphism.identity z.hom) (hproj T v)).trans
            (sections_relativeHomIdentity HZ T (R.projection.app T v)).symm)))
  have hkey : ∀ (s : PullbackCone (relativeHomPostcompose HX HZ x.hom rfl)
      (relativeHomIdentity HZ)) (T : (BigFppfOver B S hS)ᵒᵖ) (w : s.pt.obj T),
      RelativeMorphism.postcomp x.hom rfl (HX.sections T.unop (s.fst.app T w)) =
        RelativeMorphism.identity z.hom (yonedaEquiv.symm (s.snd.app T w)) := by
    intro s T w
    have hc : (relativeHomPostcompose HX HZ x.hom rfl).app T (s.fst.app T w) =
        (relativeHomIdentity HZ).app T (s.snd.app T w) :=
      types_congr_hom (NatTrans.congr_app s.condition T) w
    refine Eq.trans (sections_relativeHomPostcompose HX HZ x.hom rfl T (s.fst.app T w)).symm ?_
    exact (congrArg (HZ.sections T.unop) hc).trans
      (sections_relativeHomIdentity HZ T (s.snd.app T w))
  have hover : ∀ (s : PullbackCone (relativeHomPostcompose HX HZ x.hom rfl)
      (relativeHomIdentity HZ)) (T : (BigFppfOver B S hS)ᵒᵖ) (w : s.pt.obj T),
      RelativeMorphism.LiesOverZ x z (HX.sections T.unop (s.fst.app T w)) :=
    fun s T w => RelativeMorphism.liesOverZ_of_postcomp_eq_identity (hkey s T w)
  have hbase : ∀ (s : PullbackCone (relativeHomPostcompose HX HZ x.hom rfl)
      (relativeHomIdentity HZ)) (T : (BigFppfOver B S hS)ᵒᵖ) (w : s.pt.obj T),
      (HX.sections T.unop (s.fst.app T w)).base = yonedaEquiv.symm (s.snd.app T w) :=
    fun s T w => congrArg RelativeMorphism.base (hkey s T w)
  have hmono : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m₁ m₂ : W ⟶ R.presheaf),
      m₁ ≫ restrictionOfScalarsToRelativeHom R HX =
        m₂ ≫ restrictionOfScalarsToRelativeHom R HX → m₁ = m₂ := by
    intro W m₁ m₂ h
    ext T w
    refine (R.pairEquiv T.unop).injective (RestrictionPair.toRelativeMorphism_injective ?_)
    refine (sections_restrictionOfScalarsToRelativeHom R HX T (m₁.app T w)).symm.trans ?_
    exact (congrArg (HX.sections T.unop) (types_congr_hom (NatTrans.congr_app h T) w)).trans
      (sections_restrictionOfScalarsToRelativeHom R HX T (m₂.app T w))
  have hlift : ∀ s : PullbackCone (relativeHomPostcompose HX HZ x.hom rfl)
      (relativeHomIdentity HZ), ∃ l : s.pt ⟶ R.presheaf,
      l ≫ restrictionOfScalarsToRelativeHom R HX = s.fst ∧ l ≫ R.projection = s.snd := by
    intro s
    have hP : ∀ {T U : (BigFppfOver B S hS)ᵒᵖ} (f : T ⟶ U) (w : s.pt.obj T),
        restrictionPairEquivSubtype x z (yoneda.obj U.unop)
            ⟨HX.sections U.unop (s.fst.app U (s.pt.map f w)), hover s U (s.pt.map f w)⟩ =
          RestrictionPair.restrict (yoneda.map f.unop)
            (restrictionPairEquivSubtype x z (yoneda.obj T.unop)
              ⟨HX.sections T.unop (s.fst.app T w), hover s T w⟩) := by
      intro T U f w
      refine RestrictionPair.toRelativeMorphism_injective ?_
      exact (congrArg (HX.sections U.unop) (types_congr_hom (s.fst.naturality f) w)).trans
        (HX.sections_map_eq f (s.fst.app T w))
    refine ⟨restrictionOfScalarsOfPairs R
      (fun T w => restrictionPairEquivSubtype x z (yoneda.obj T.unop)
        ⟨HX.sections T.unop (s.fst.app T w), hover s T w⟩) hP, ?_, ?_⟩
    · ext T w
      refine (HX.sections T.unop).injective ?_
      refine (sections_restrictionOfScalarsToRelativeHom R HX T _).trans ?_
      exact congrArg RestrictionPair.toRelativeMorphism
        (pairEquiv_restrictionOfScalarsOfPairs R _ hP T w)
    · ext T w
      refine yonedaEquiv.symm.injective ((hproj T _).symm.trans ?_)
      exact (congrArg RestrictionPair.base (pairEquiv_restrictionOfScalarsOfPairs R _ hP T w)).trans
        (hbase s T w)
  exact { w := hw
          isLimit' := ⟨PullbackCone.IsLimit.mk hw (fun s => (hlift s).choose)
            (fun s => (hlift s).choose_spec.1) (fun s => (hlift s).choose_spec.2)
            fun s m hm _ => hmono m _ (hm.trans (hlift s).choose_spec.1.symm)⟩ }

/-- The square of `AlgebraicGeometry.Space.isPullback_restrictionOfScalars` is cartesian for the
relative morphism functor of Stacks 05Y2 and the restriction of scalars of Stacks 05YA. -/
@[stacks 05YE "the cartesian square, for the functors of Stacks 05Y2 and 05YA"]
theorem isPullback_restrictionOfScalars_relativeHomData {X Z Q : AlgebraicSpaces B S hS}
    (x : X ⟶ Z) (z : Z ⟶ Q) :
    IsPullback
      (restrictionOfScalarsToRelativeHom (restrictionOfScalars B S hS x z)
        (relativeHomData B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) Z.property X.property
          Q.property))
      (restrictionOfScalars B S hS x z).projection
      (relativeHomPostcompose
        (relativeHomData B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) Z.property X.property
          Q.property)
        (relativeHomData B S hS Z.obj Z.obj Q.obj z.hom z.hom Z.property Z.property Q.property)
        x.hom rfl)
      (relativeHomIdentity
        (relativeHomData B S hS Z.obj Z.obj Q.obj z.hom z.hom Z.property Z.property Q.property)) :=
  isPullback_restrictionOfScalars _ _ _

end AlgebraicGeometry.Space

end
