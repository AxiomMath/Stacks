module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidCompose

/-!
# The translation laws for the finite part of a groupoid

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over `B` whose source morphism is
separated and locally of finite type, and let `(U', Z_univ)` be the object space and the arrow
space of its finite part, Stacks 04RT. The target morphism of the finite part is the rule
`t' : (u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z))`, so the three groupoid laws which mention `t'` — that the
target of a unit is its own object, that the target of an inverse is the source, and the cocycle
identity for the target of a composite — are *identities between pairs of Stacks 04PC*:

* `c(Z, i ∘ (e ∘ u)) = Z`,
* `c(c(Z, i ∘ z), i ∘ (i ∘ z)) = Z`,
* `c(Z₂, i ∘ (z₁ ∘ z₂)) = c(c(Z₂, i ∘ z₂), i ∘ z₁)`.

This file proves them, together with the compatibility of the translation with base change which
is what lets them be read at a scheme-valued point of `Z_univ`.

## Main definitions

* `AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChangeAlong`: the relation saying that one
  pair of Stacks 04PC is a base change of another along a morphism of algebraic spaces. This is
  the shape in which Stacks 04PE, part (2), presents the pair named at a point.
* `AlgebraicGeometry.Space.baseChangePair`: the base change of a pair of Stacks 04PC along a
  morphism of algebraic spaces, as an operation rather than a relation.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.composeArrow`: the composite of two families of
  arrows over an algebraic space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePairOf`: the translation
  `c(Z, i ∘ z)` of a pair, with the base morphism of the result carried as a parameter.

## Main results

* `AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChangeAlong.unique`: a base change of a pair
  of Stacks 04PC is unique, so the pair named at a scheme-valued point is determined.
* `AlgebraicGeometry.Space.sections_eq_baseChangePair`: the pair which a morphism into the finite
  part names at a scheme-valued point is the base change of the pair it names.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translateBwd_identityHom` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translateBwd_comp`: the two identities between the
  translating isomorphisms out of which all three laws are read — translating by a unit is the
  identity, and translating twice is translating by the composite.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePairOf_identityHom`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePairOf_inverseHom` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePairOf_composeArrow`: the three laws.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.baseChangePair_translatePairOf`: the translation
  commutes with base change.

## Implementation notes

The base morphism of the translated pair is carried as a parameter `b` together with the equation
`z ≫ t = b`, rather than being fixed to `z ≫ t`. This is what makes the three laws equalities
rather than equalities-up-to-transport: the open subspace of a pair is a subfunctor of
`T ×_{b, U, s} R`, so two pairs whose base morphisms are merely *equal* have open subspaces of
different types, and the laws would need a dependent transport. With `b` a parameter the two
sides of each law can be presented over the same `b`, their open subspaces are subfunctors of the
same ambient fibre product, and the law becomes an equality of subfunctors. The intended instance
is `b = z ≫ t`, for which
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.translatePair_eq_translatePairOf` identifies the two
translations.

With that in place each law reduces to an identity between the inverse translating morphisms
`c(-, z)` of Stacks 04RT, because the open subspace of a translation is by construction the
preimage of the original one along `c(-, z)` and the preimage of a preimage is the preimage of the
composite. Those identities are in turn the pointwise groupoid laws of the original groupoid:
`w ∘ e(s(w)) = w` for the unit, and associativity for the composite.

Base change of a pair is recorded here as an operation, `baseChangePair`, rather than only as the
relation that Stacks 04PE, part (2), supplies, so that the pair named at a scheme-valued point has
a name. Uniqueness of base change, which is what makes that legitimate, is
`FiniteOpenSubspace.IsBaseChangeAlong.unique`; it is the same argument as
`AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange.unique`, for a morphism of algebraic
spaces instead of a morphism of the site.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RS](https://stacks.math.columbia.edu/tag/04RS)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace Deformation.PointwiseGroupoid

variable {U R : Type w} {source target : R → U}
  {comp : { p : R × R // source p.1 = target p.2 } → R}

/-- The unit of a septuple does not depend on which groupoid structure witnesses it: a two-sided
unit at a point is unique. -/
theorem identityArrow_eq (P P' : PointwiseGroupoid source target comp) (x : U) :
    P.identityArrow x = P'.identityArrow x := by
  have h : source (P.identityArrow x) = target (P'.identityArrow x) :=
    (P.source_identityArrow x).trans (P'.target_identityArrow x).symm
  exact (P'.comp_identityArrow_snd (P.identityArrow x) x (P.source_identityArrow x) h).symm.trans
    (P.comp_identityArrow_fst (P'.identityArrow x) x (P'.target_identityArrow x) h)

end Deformation.PointwiseGroupoid

namespace AlgebraicGeometry.Space

namespace FiniteOpenSubspace

/-- Two pairs of Stacks 04PC over the same algebraic space with the same base morphism and the
same open subspace are equal. -/
theorem eq_of_subspace_eq (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {p q : FiniteOpenSubspace B S hS f T} (hb : p.toBase = q.toBase)
    (hz : HEq p.subspace q.subspace) : p = q := by
  obtain ⟨a, Z, ho, hf⟩ := p
  obtain ⟨a', Z', ho', hf'⟩ := q
  dsimp only at hb hz
  subst hb
  have hZ : Z = Z' := eq_of_heq hz
  subst hZ
  rfl

/-- The pair `q` over `T'` is a base change of the pair `p` over `T` along `g`: the base
morphisms agree after composing with `g`, and the open subspace of `q` is cartesian over that of
`p` along `g`, compatibly with the two morphisms to `X`.

This is the shape in which Stacks 04PE, part (2), presents the pair named at a point, with `g` a
morphism of algebraic spaces rather than of the site. -/
def IsBaseChangeAlong (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T T' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : T'.obj ⟶ T.obj)
    (p : FiniteOpenSubspace B S hS f T) (q : FiniteOpenSubspace B S hS f T') : Prop :=
  q.toBase.hom = g ≫ p.toBase.hom ∧
    ∃ j : q.subspace.toFunctor ⟶ p.subspace.toFunctor,
      IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g
          (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) ∧
        j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
          q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom

/-- A base change of a pair of Stacks 04PC along a morphism of algebraic spaces is unique. -/
theorem IsBaseChangeAlong.unique (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T T' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : T'.obj ⟶ T.obj}
    {p : FiniteOpenSubspace B S hS f T} {q r : FiniteOpenSubspace B S hS f T'}
    (hq : IsBaseChangeAlong B S hS f g p q) (hr : IsBaseChangeAlong B S hS f g p r) : q = r := by
  obtain ⟨ha, j, hj, hjx⟩ := hq
  obtain ⟨hb, l, hl, hlx⟩ := hr
  refine ext_of_iso B S hS (ha.trans hb.symm) (hj.isoIsPullback _ _ hl) ?_ ?_
  · exact hj.isoIsPullback_hom_fst _ _ hl
  · rw [← hlx, ← Category.assoc, ← Category.assoc, hj.isoIsPullback_hom_snd _ _ hl]
    exact hjx

end FiniteOpenSubspace

/-- The base-change morphism of ambient fibre products is the identity on the `X` component. -/
theorem baseChangeAmbientMap_comp_snd (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y T T' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (a : T ⟶ Y) (h : T' ⟶ T) :
    baseChangeAmbientMap B S hS f a h ≫ pullback.snd a.hom f.hom =
      pullback.snd (h ≫ a).hom f.hom := by
  dsimp [baseChangeAmbientMap]
  rw [pullback.lift_snd]
  exact Category.comp_id _

/-- The base-change morphism of ambient fibre products is `h` on the base component. -/
theorem baseChangeAmbientMap_comp_fst (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y T T' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (a : T ⟶ Y) (h : T' ⟶ T) :
    baseChangeAmbientMap B S hS f a h ≫ pullback.fst a.hom f.hom =
      pullback.fst (h ≫ a).hom f.hom ≫ h.hom := by
  dsimp [baseChangeAmbientMap]
  rw [pullback.lift_fst]

/-- The base change of a pair of Stacks 04PC along a morphism of algebraic spaces: its base
morphism is the composite, and its open subspace is the preimage of the given one under the
base-change morphism of ambient fibre products. -/
noncomputable def baseChangePair (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T T' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (p : FiniteOpenSubspace B S hS f T) (h : T' ⟶ T) :
    FiniteOpenSubspace B S hS f T' where
  toBase := h ≫ p.toBase
  subspace := p.subspace.preimage (baseChangeAmbientMap B S hS f p.toBase h)
  isOpen :=
    isOpenSubspace_preimage B S hS (baseChangeAmbientMap B S hS f p.toBase h) p.subspace
      (isAlgebraicSpace_pullback B S hS p.toBase.hom f.hom T.property X.property Y.property)
      (isAlgebraicSpace_pullback B S hS (h ≫ p.toBase).hom f.hom T'.property X.property
        Y.property)
      p.isOpen
  finite_projection :=
    isFinite_of_isPullback B S hS
      ((Subfunctor.isPullback_preimage (baseChangeAmbientMap B S hS f p.toBase h)
          p.subspace).paste_vert
        (isPullback_baseChangeAmbientMap B S hS f p.toBase h))
      p.finite_projection

/-- The base morphism of the base change of a pair along `h` is `h ≫ p.toBase`. -/
@[simp]
theorem baseChangePair_toBase (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T T' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (p : FiniteOpenSubspace B S hS f T) (h : T' ⟶ T) :
    (baseChangePair B S hS f p h).toBase = h ≫ p.toBase := rfl

/-- The open subspace of the base change of a pair along `h` is the preimage of the given one under
the base-change morphism of ambient fibre products. -/
theorem baseChangePair_subspace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T T' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (p : FiniteOpenSubspace B S hS f T) (h : T' ⟶ T) :
    (baseChangePair B S hS f p h).subspace =
      p.subspace.preimage (baseChangeAmbientMap B S hS f p.toBase h) := rfl

/-- The base change of a pair really is a base change of it. -/
theorem isBaseChangeAlong_baseChangePair (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y T T' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (p : FiniteOpenSubspace B S hS f T) (h : T' ⟶ T) :
    FiniteOpenSubspace.IsBaseChangeAlong B S hS f h.hom p (baseChangePair B S hS f p h) := by
  refine ⟨rfl, p.subspace.fromPreimage (baseChangeAmbientMap B S hS f p.toBase h), ?_, ?_⟩
  · exact ((Subfunctor.isPullback_preimage (baseChangeAmbientMap B S hS f p.toBase h)
      p.subspace).paste_vert (isPullback_baseChangeAmbientMap B S hS f p.toBase h)).flip
  · calc p.subspace.fromPreimage (baseChangeAmbientMap B S hS f p.toBase h) ≫
          p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom
        = (p.subspace.fromPreimage (baseChangeAmbientMap B S hS f p.toBase h) ≫
            p.subspace.ι) ≫ pullback.snd p.toBase.hom f.hom := (Category.assoc _ _ _).symm
      _ = ((p.subspace.preimage (baseChangeAmbientMap B S hS f p.toBase h)).ι ≫
            baseChangeAmbientMap B S hS f p.toBase h) ≫ pullback.snd p.toBase.hom f.hom :=
          congrArg (fun m => m ≫ pullback.snd p.toBase.hom f.hom)
            (Subfunctor.fromPreimage_ι p.subspace (baseChangeAmbientMap B S hS f p.toBase h))
      _ = (p.subspace.preimage (baseChangeAmbientMap B S hS f p.toBase h)).ι ≫
            baseChangeAmbientMap B S hS f p.toBase h ≫ pullback.snd p.toBase.hom f.hom :=
          Category.assoc _ _ _
      _ = (p.subspace.preimage (baseChangeAmbientMap B S hS f p.toBase h)).ι ≫
            pullback.snd (h ≫ p.toBase).hom f.hom :=
          congrArg
            (fun m => (p.subspace.preimage (baseChangeAmbientMap B S hS f p.toBase h)).ι ≫ m)
            (baseChangeAmbientMap_comp_snd B S hS f p.toBase h)

/-- Every base change of a pair of Stacks 04PC is the one `baseChangePair` produces. -/
theorem eq_baseChangePair (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y T T' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {p : FiniteOpenSubspace B S hS f T} {q : FiniteOpenSubspace B S hS f T'} {h : T' ⟶ T}
    (hq : FiniteOpenSubspace.IsBaseChangeAlong B S hS f h.hom p q) :
    q = baseChangePair B S hS f p h :=
  FiniteOpenSubspace.IsBaseChangeAlong.unique B S hS hq
    (isBaseChangeAlong_baseChangePair B S hS f p h)

/-- A morphism from a representable presheaf into an algebraic space, read as a morphism of
algebraic spaces out of the corresponding scheme of the site. -/
def schemePointHom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS) (m : yoneda.obj V ⟶ T.obj) :
    schemeSpace V ⟶ T := ObjectProperty.homMk m

/-- The underlying morphism of presheaves of `schemePointHom B S hS V m` is `m`. -/
@[simp]
theorem schemePointHom_hom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS) (m : yoneda.obj V ⟶ T.obj) :
    (schemePointHom B S hS V m).hom = m := rfl

/-- **Stacks 04PE, part (2), as a computation.** The pair which a morphism into the finite part
of `f` names at a scheme-valued point of its source is the base change, along that point, of the
pair which the morphism names. -/
theorem sections_eq_baseChangePair (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : AlgebraicSpaces B S hS)
    (v : T.obj ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ T.obj) :
    (finiteOpenSubspacePresheaf B S hS f).sections V (v.app (op V) (yonedaEquiv g)) =
      baseChangePair B S hS f ((finiteOpenSubspaceEquiv B S hS f T).1 v)
        (schemePointHom B S hS V g) :=
  eq_baseChangePair B S hS f ((finiteOpenSubspaceEquiv B S hS f T).2 v V g)

/-- Two morphisms into the finite part of `f` agree as soon as the pairs they name at every
point agree. -/
theorem natTrans_ext_of_sections (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (v w : F ⟶ (finiteOpenSubspacePresheaf B S hS f).toFunctor)
    (h : ∀ (V : BigFppfOver B S hS) (x : F.obj (op V)),
      (finiteOpenSubspacePresheaf B S hS f).sections V (v.app (op V) x) =
        (finiteOpenSubspacePresheaf B S hS f).sections V (w.app (op V) x)) :
    v = w := by
  ext V x
  exact ((finiteOpenSubspacePresheaf B S hS f).sections V.unop).injective (h V.unop x)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}
  {T : AlgebraicSpaces C S hS}

/-! ### Two more pointwise laws for families of arrows -/

/-- Composing a family of arrows with the unit at its own source returns the family. -/
theorem composeHom_identity_snd {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (β : F ⟶ G.arrows.obj)
    (h : β ≫ G.source.hom = (β ≫ G.source.hom ≫ (identityHom G).hom) ≫ G.target.hom) :
    composeHom β (β ≫ G.source.hom ≫ (identityHom G).hom) h = β := by
  ext V x
  exact (G.toGroupoidInFunctors.pointwiseData V).comp_identityArrow_snd (β.app V x)
    (G.source.hom.app V (β.app V x)) rfl _

/-- Composition of families of arrows is associative. -/
theorem composeHom_assoc {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (α β γ : F ⟶ G.arrows.obj)
    (hab : α ≫ G.source.hom = β ≫ G.target.hom)
    (hbg : β ≫ G.source.hom = γ ≫ G.target.hom)
    (h₁ : composeHom α β hab ≫ G.source.hom = γ ≫ G.target.hom)
    (h₂ : α ≫ G.source.hom = composeHom β γ hbg ≫ G.target.hom) :
    composeHom (composeHom α β hab) γ h₁ = composeHom α (composeHom β γ hbg) h₂ := by
  ext V x
  exact (G.toGroupoidInFunctors.pointwiseData V).comp_assoc (α.app V x) (β.app V x)
    (γ.app V x) _ _ _ _

/-- The composite of two families of arrows over an algebraic space, as a morphism of algebraic
spaces. -/
noncomputable def composeArrow (z₁ z₂ : T ⟶ G.arrows)
    (hc : z₁.hom ≫ G.source.hom = z₂.hom ≫ G.target.hom) : T ⟶ G.arrows :=
  ObjectProperty.homMk (composeHom z₁.hom z₂.hom hc)

/-- The underlying morphism of presheaves of `composeArrow z₁ z₂ hc` is the composite
`composeHom z₁.hom z₂.hom hc` of families of arrows. -/
@[simp]
theorem composeArrow_hom (z₁ z₂ : T ⟶ G.arrows)
    (hc : z₁.hom ≫ G.source.hom = z₂.hom ≫ G.target.hom) :
    (composeArrow z₁ z₂ hc).hom = composeHom z₁.hom z₂.hom hc := rfl

/-! ### The translation with its base morphism named -/

/-- **The translation `c(Z, i ∘ z)` of Stacks 04RT**, with the base morphism of the translated
pair carried as a parameter `b` together with the equation `z ≫ t = b`.

Carrying `b` rather than using `z ≫ t` is what makes the groupoid laws for the target morphism
equalities of pairs rather than equalities up to a dependent transport: two instances with the
same `b` have open subspaces inside the same ambient fibre product. -/
noncomputable def translatePairOf (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = p.toBase.hom)
    (b : T ⟶ G.objects) (hzt : z.hom ≫ G.target.hom = b.hom) :
    Space.FiniteOpenSubspace C S hS G.source T where
  toBase := b
  subspace := p.subspace.preimage (translateBwd z hzs hzt)
  isOpen := (Space.FiniteOpenSubspace.ofAmbientIso C S hS p b
    (translateAmbientIso z hzs hzt) (translateFwd_fst z hzs hzt)).isOpen
  finite_projection := (Space.FiniteOpenSubspace.ofAmbientIso C S hS p b
    (translateAmbientIso z hzs hzt) (translateFwd_fst z hzs hzt)).finite_projection

/-- The base morphism of the named translation `translatePairOf p z hzs b hzt` is `b`. -/
@[simp]
theorem translatePairOf_toBase (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = p.toBase.hom)
    (b : T ⟶ G.objects) (hzt : z.hom ≫ G.target.hom = b.hom) :
    (translatePairOf p z hzs b hzt).toBase = b := rfl

/-- The open subspace of the named translation is the preimage of the open subspace of `p` under
`translateBwd z hzs hzt`. -/
theorem translatePairOf_subspace (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = p.toBase.hom)
    (b : T ⟶ G.objects) (hzt : z.hom ≫ G.target.hom = b.hom) :
    (translatePairOf p z hzs b hzt).subspace =
      p.subspace.preimage (translateBwd z hzs hzt) := rfl

/-- The translation of Stacks 04RT is the named translation with `b = z ≫ t`. -/
theorem translatePair_eq_translatePairOf (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hz : z.hom ≫ G.source.hom = p.toBase.hom) :
    translatePair p z hz = translatePairOf p z hz (z ≫ G.target) rfl := rfl

/-- The named translation depends only on the pair, the arrow and the base morphism. -/
theorem translatePairOf_congr {p p' : Space.FiniteOpenSubspace C S hS G.source T}
    {z z' : T ⟶ G.arrows} {b b' : T ⟶ G.objects} (hp : p = p') (hz : z = z') (hb : b = b')
    (hzs : z.hom ≫ G.source.hom = p.toBase.hom) (hzt : z.hom ≫ G.target.hom = b.hom)
    (hzs' : z'.hom ≫ G.source.hom = p'.toBase.hom) (hzt' : z'.hom ≫ G.target.hom = b'.hom) :
    translatePairOf p z hzs b hzt = translatePairOf p' z' hzs' b' hzt' := by
  subst hp
  subst hz
  subst hb
  rfl

/-- The inverse translating morphism depends only on the arrow. -/
theorem translateBwd_congr {a b : T ⟶ G.objects} {z z' : T ⟶ G.arrows} (hz : z = z')
    (hzs : z.hom ≫ G.source.hom = a.hom) (hzt : z.hom ≫ G.target.hom = b.hom)
    (hzs' : z'.hom ≫ G.source.hom = a.hom) (hzt' : z'.hom ≫ G.target.hom = b.hom) :
    translateBwd z hzs hzt = translateBwd z' hzs' hzt' := by
  subst hz
  rfl

/-! ### The two identities between translating morphisms -/

/-- **Translating by a unit is the identity.** The inverse translating morphism of the family of
units at the base morphism is the identity of the ambient fibre product; pointwise this is the
groupoid law `w ∘ e(s(w)) = w`. -/
theorem translateBwd_identityHom {a : T ⟶ G.objects}
    (hzs : (a ≫ identityHom G).hom ≫ G.source.hom = a.hom)
    (hzt : (a ≫ identityHom G).hom ≫ G.target.hom = a.hom) :
    translateBwd (a ≫ identityHom G) hzs hzt = 𝟙 (pullback a.hom G.source.hom) := by
  have hunit : pullback.snd a.hom G.source.hom ≫ G.source.hom =
      (pullback.snd a.hom G.source.hom ≫ G.source.hom ≫ (identityHom G).hom) ≫
        G.target.hom := by
    simp only [Category.assoc, identityHom_comp_target, Category.comp_id]
  have hcond : pullback.fst a.hom G.source.hom ≫ (a ≫ identityHom G).hom =
      pullback.snd a.hom G.source.hom ≫ G.source.hom ≫ (identityHom G).hom := by
    show pullback.fst a.hom G.source.hom ≫ a.hom ≫ (identityHom G).hom = _
    rw [← Category.assoc, pullback.condition, Category.assoc]
  apply pullback.hom_ext
  · rw [translateBwd_fst, Category.id_comp]
  · rw [translateBwd_snd, Category.id_comp]
    refine (composeHom_congr rfl hcond (translateBwd_condition _ hzt) hunit).trans
      (composeHom_identity_snd (pullback.snd a.hom G.source.hom) hunit)

/-- **Translating twice is translating by the composite.** The composite of the inverse
translating morphisms of `z₁` and `z₂` is the inverse translating morphism of `z₁ ∘ z₂`;
pointwise this is associativity. -/
theorem translateBwd_comp {a b₂ b₁ : T ⟶ G.objects} (z₁ z₂ : T ⟶ G.arrows)
    (hzs₂ : z₂.hom ≫ G.source.hom = a.hom) (hzt₂ : z₂.hom ≫ G.target.hom = b₂.hom)
    (hzs₁ : z₁.hom ≫ G.source.hom = b₂.hom) (hzt₁ : z₁.hom ≫ G.target.hom = b₁.hom)
    (hc : z₁.hom ≫ G.source.hom = z₂.hom ≫ G.target.hom)
    (hzs : (composeArrow z₁ z₂ hc).hom ≫ G.source.hom = a.hom)
    (hzt : (composeArrow z₁ z₂ hc).hom ≫ G.target.hom = b₁.hom) :
    translateBwd z₁ hzs₁ hzt₁ ≫ translateBwd z₂ hzs₂ hzt₂ =
      translateBwd (composeArrow z₁ z₂ hc) hzs hzt := by
  have hcpt : (pullback.fst b₁.hom G.source.hom ≫ z₁.hom) ≫ G.source.hom =
      (pullback.fst b₁.hom G.source.hom ≫ z₂.hom) ≫ G.target.hom := by
    simp only [Category.assoc]
    rw [hc]
  have hinner : composeHom (pullback.snd b₁.hom G.source.hom)
      (pullback.fst b₁.hom G.source.hom ≫ z₁.hom) (translateBwd_condition z₁ hzt₁) ≫
      G.source.hom = (pullback.fst b₁.hom G.source.hom ≫ z₂.hom) ≫ G.target.hom := by
    rw [composeHom_comp_source]
    exact hcpt
  have houter : pullback.snd b₁.hom G.source.hom ≫ G.source.hom =
      composeHom (pullback.fst b₁.hom G.source.hom ≫ z₁.hom)
        (pullback.fst b₁.hom G.source.hom ≫ z₂.hom) hcpt ≫ G.target.hom := by
    rw [composeHom_comp_target]
    simp only [Category.assoc]
    rw [hzt₁, ← pullback.condition]
  apply pullback.hom_ext
  · rw [Category.assoc, translateBwd_fst, translateBwd_fst, translateBwd_fst]
  · rw [Category.assoc, translateBwd_snd, translateBwd_snd]
    refine (composeHom_comp_left (translateBwd z₁ hzs₁ hzt₁) (translateBwd_condition z₂ hzt₂)
        (translateBwd_snd z₁ hzs₁ hzt₁)
        (by rw [← Category.assoc, translateBwd_fst]) hinner).trans ?_
    refine (composeHom_assoc (pullback.snd b₁.hom G.source.hom)
      (pullback.fst b₁.hom G.source.hom ≫ z₁.hom)
      (pullback.fst b₁.hom G.source.hom ≫ z₂.hom)
      (translateBwd_condition z₁ hzt₁) hcpt hinner houter).trans ?_
    refine composeHom_congr rfl ?_ houter (translateBwd_condition _ hzt)
    exact (comp_composeHom (pullback.fst b₁.hom G.source.hom) z₁.hom z₂.hom hc hcpt).symm

/-! ### The three laws -/

/-- **The target of a unit is its own object.** Translating a pair by the family of units at its
base morphism returns the pair: `c(Z, i ∘ (e ∘ u)) = Z`. -/
theorem translatePairOf_identityHom (p : Space.FiniteOpenSubspace C S hS G.source T)
    (hzs : (p.toBase ≫ identityHom G).hom ≫ G.source.hom = p.toBase.hom)
    (hzt : (p.toBase ≫ identityHom G).hom ≫ G.target.hom = p.toBase.hom) :
    translatePairOf p (p.toBase ≫ identityHom G) hzs p.toBase hzt = p := by
  refine Space.FiniteOpenSubspace.eq_of_subspace_eq C S hS rfl (heq_of_eq ?_)
  show p.subspace.preimage (translateBwd (p.toBase ≫ identityHom G) hzs hzt) = p.subspace
  rw [translateBwd_identityHom hzs hzt, Subfunctor.preimage_id]

/-- **The cocycle identity for the target.** Translating by a composite is translating twice:
`c(Z₂, i ∘ (z₁ ∘ z₂)) = c(c(Z₂, i ∘ z₂), i ∘ z₁)`. -/
theorem translatePairOf_composeArrow (p : Space.FiniteOpenSubspace C S hS G.source T)
    {b₂ b₁ : T ⟶ G.objects} (z₁ z₂ : T ⟶ G.arrows)
    (hzs₂ : z₂.hom ≫ G.source.hom = p.toBase.hom) (hzt₂ : z₂.hom ≫ G.target.hom = b₂.hom)
    (hzs₁ : z₁.hom ≫ G.source.hom = b₂.hom) (hzt₁ : z₁.hom ≫ G.target.hom = b₁.hom)
    (hc : z₁.hom ≫ G.source.hom = z₂.hom ≫ G.target.hom)
    (hzs : (composeArrow z₁ z₂ hc).hom ≫ G.source.hom = p.toBase.hom)
    (hzt : (composeArrow z₁ z₂ hc).hom ≫ G.target.hom = b₁.hom) :
    translatePairOf p (composeArrow z₁ z₂ hc) hzs b₁ hzt =
      translatePairOf (translatePairOf p z₂ hzs₂ b₂ hzt₂) z₁ hzs₁ b₁ hzt₁ := by
  refine Space.FiniteOpenSubspace.eq_of_subspace_eq C S hS rfl (heq_of_eq ?_)
  show p.subspace.preimage (translateBwd (composeArrow z₁ z₂ hc) hzs hzt) =
    (p.subspace.preimage (translateBwd z₂ hzs₂ hzt₂)).preimage (translateBwd z₁ hzs₁ hzt₁)
  rw [← Subfunctor.preimage_comp,
    translateBwd_comp z₁ z₂ hzs₂ hzt₂ hzs₁ hzt₁ hc hzs hzt]

/-- **The target of an inverse is the source.** Translating a translated pair by the inverse of
the arrow returns the original pair: `c(c(Z, i ∘ z), i ∘ (i ∘ z)) = Z`. -/
theorem translatePairOf_inverseHom (p : Space.FiniteOpenSubspace C S hS G.source T)
    {b₂ : T ⟶ G.objects} (z : T ⟶ G.arrows)
    (hzs : z.hom ≫ G.source.hom = p.toBase.hom) (hzt : z.hom ≫ G.target.hom = b₂.hom)
    (hzs' : (z ≫ inverseHom G).hom ≫ G.source.hom = b₂.hom)
    (hzt' : (z ≫ inverseHom G).hom ≫ G.target.hom = p.toBase.hom) :
    translatePairOf (translatePairOf p z hzs b₂ hzt) (z ≫ inverseHom G) hzs' p.toBase hzt' = p
    := by
  have hc : (z ≫ inverseHom G).hom ≫ G.source.hom = z.hom ≫ G.target.hom := by
    simp [inverseHom_comp_source]
  have hid₁ : (p.toBase ≫ identityHom G).hom ≫ G.source.hom = p.toBase.hom := by
    simp [identityHom_comp_source]
  have hid₂ : (p.toBase ≫ identityHom G).hom ≫ G.target.hom = p.toBase.hom := by
    simp [identityHom_comp_target]
  have hzsc : (composeArrow (z ≫ inverseHom G) z hc).hom ≫ G.source.hom = p.toBase.hom := by
    simp [composeHom_comp_source, hzs]
  have hztc : (composeArrow (z ≫ inverseHom G) z hc).hom ≫ G.target.hom = p.toBase.hom := by
    simp [composeHom_comp_target, inverseHom_comp_target, hzs]
  have hzid : composeArrow (z ≫ inverseHom G) z hc = p.toBase ≫ identityHom G := by
    apply ObjectProperty.hom_ext
    simp [composeHom_self_inverse z.hom hc, ← hzs]
  calc translatePairOf (translatePairOf p z hzs b₂ hzt) (z ≫ inverseHom G) hzs' p.toBase hzt'
      = translatePairOf p (composeArrow (z ≫ inverseHom G) z hc) hzsc p.toBase hztc :=
        (translatePairOf_composeArrow p (z ≫ inverseHom G) z hzs hzt hzs' hzt' hc hzsc hztc).symm
    _ = translatePairOf p (p.toBase ≫ identityHom G) hid₁ p.toBase hid₂ :=
        translatePairOf_congr rfl hzid rfl _ _ _ _
    _ = p := translatePairOf_identityHom p hid₁ hid₂

/-! ### The translation commutes with base change -/

/-- The translation of Stacks 04RT commutes with base change: the base change of `c(Z, i ∘ z)`
along `k` is the translation of the base change of `Z` by the restriction of `z`. -/
theorem baseChangePair_translatePairOf (p : Space.FiniteOpenSubspace C S hS G.source T)
    (z : T ⟶ G.arrows) (hzs : z.hom ≫ G.source.hom = p.toBase.hom)
    (b : T ⟶ G.objects) (hzt : z.hom ≫ G.target.hom = b.hom)
    {T' : AlgebraicSpaces C S hS} (k : T' ⟶ T)
    (hzs' : (k ≫ z).hom ≫ G.source.hom = (k ≫ p.toBase).hom)
    (hzt' : (k ≫ z).hom ≫ G.target.hom = (k ≫ b).hom) :
    Space.baseChangePair C S hS G.source (translatePairOf p z hzs b hzt) k =
      translatePairOf (Space.baseChangePair C S hS G.source p k) (k ≫ z) hzs' (k ≫ b) hzt' := by
  have hmor : Space.baseChangeAmbientMap C S hS G.source b k ≫ translateBwd z hzs hzt =
      translateBwd (k ≫ z) hzs' hzt' ≫
        Space.baseChangeAmbientMap C S hS G.source p.toBase k := by
    apply pullback.hom_ext
    · rw [Category.assoc, translateBwd_fst, Space.baseChangeAmbientMap_comp_fst,
        Category.assoc, Space.baseChangeAmbientMap_comp_fst, ← Category.assoc,
        translateBwd_fst]
    · rw [Category.assoc, translateBwd_snd, Category.assoc,
        Space.baseChangeAmbientMap_comp_snd, translateBwd_snd]
      refine composeHom_comp_left (Space.baseChangeAmbientMap C S hS G.source b k)
        (translateBwd_condition z hzt) (Space.baseChangeAmbientMap_comp_snd C S hS G.source b k)
        ?_ (translateBwd_condition (k ≫ z) hzt')
      rw [← Category.assoc, Space.baseChangeAmbientMap_comp_fst, Category.assoc]
      rfl
  refine Space.FiniteOpenSubspace.eq_of_subspace_eq C S hS rfl (heq_of_eq ?_)
  show (p.subspace.preimage (translateBwd z hzs hzt)).preimage
      (Space.baseChangeAmbientMap C S hS G.source b k) =
    (p.subspace.preimage (Space.baseChangeAmbientMap C S hS G.source p.toBase k)).preimage
      (translateBwd (k ≫ z) hzs' hzt')
  rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, hmor]

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
