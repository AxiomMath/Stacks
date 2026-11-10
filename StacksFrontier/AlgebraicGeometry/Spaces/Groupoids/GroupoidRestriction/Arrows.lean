module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Restriction of a groupoid in algebraic spaces: the space of arrows

Part of the restriction of a groupoid in algebraic spaces along a morphism `g : U' ⟶ G.objects`
(Stacks 044B). This file contains the evaluation lemmas for pullbacks of presheaves of types, the
projections `fiberProductFst` and `fiberProductSnd` of the chosen fibre product of algebraic
spaces, the space of arrows `restrictionArrows` of the restriction with its three projections
`restrictionArrowsToArrows`, `restrictionSource` and `restrictionTarget` and their compatibilities,
and the source and target of composites in an evaluated groupoid in functors.

`fiberProductFst`, `fiberProductSnd` and `fiberProduct_condition` are the two projections of
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` and their defining compatibility, and are
spelled after it.

`eq_id_of_idempotent_isIso` is stated for an arbitrary endomorphism that is an isomorphism, which
is strictly more general than the groupoid form it is used at; the groupoid form is recovered by
bare application.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace GroupoidInAlgebraicSpaces
/-- A section over `T` of a pullback of presheaves of types is a pair of sections of the two
factors with the same image in the base. -/
public noncomputable def pullbackAppEquiv
    {D : Type v} [Category.{w} D] {F G H : Dᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (T : Dᵒᵖ) :
    (pullback f g).obj T ≃
      {p : F.obj T × G.obj T // f.app T p.1 = g.app T p.2} :=
  (pullbackObjIso f g T).toEquiv.trans
    (Types.pullbackIsoPullback (f.app T) (g.app T)).toEquiv

/-- `pullbackAppEquiv` reads off its first component along the first projection. -/
public theorem pullbackAppEquiv_fst
    {D : Type v} [Category.{w} D] {F G H : Dᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (T : Dᵒᵖ) (x : (pullback f g).obj T) :
    (pullbackAppEquiv f g T x).1.1 = (pullback.fst f g).app T x := by
  change ((Types.pullbackIsoPullback (f.app T) (g.app T)).hom
    ((pullbackObjIso f g T).hom x)).1.1 = _
  rw [Types.pullbackIsoPullback_hom_fst]
  exact congrArg (fun k => k x) (pullbackObjIso_hom_comp_fst f g T)

/-- `pullbackAppEquiv` reads off its second component along the second projection. -/
public theorem pullbackAppEquiv_snd
    {D : Type v} [Category.{w} D] {F G H : Dᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (T : Dᵒᵖ) (x : (pullback f g).obj T) :
    (pullbackAppEquiv f g T x).1.2 = (pullback.snd f g).app T x := by
  change ((Types.pullbackIsoPullback (f.app T) (g.app T)).hom
    ((pullbackObjIso f g T).hom x)).1.2 = _
  rw [Types.pullbackIsoPullback_hom_snd]
  exact congrArg (fun k => k x) (pullbackObjIso_hom_comp_snd f g T)

/-- The defining compatibility of a pullback of presheaves of types, evaluated on a section. -/
public theorem pullback_condition_app
    {D : Type v} [Category.{w} D] {F G H : Dᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (T : Dᵒᵖ) (x : (pullback f g).obj T) :
    f.app T ((pullback.fst f g).app T x) =
      g.app T ((pullback.snd f g).app T x) := by
  have hh := congrArg (fun k => k.app T x) (pullback.condition (f := f) (g := g))
  simpa using hh

/-- First projection from the chosen fibre product of algebraic spaces. -/
public noncomputable abbrev fiberProductFst
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {F G H : AlgebraicSpaces C S hS} (f : F ⟶ H) (g : G ⟶ H) :
    AlgebraicSpaces.fiberProduct C S hS f g ⟶ F :=
  ObjectProperty.homMk (pullback.fst f.hom g.hom)

/-- Second projection from the chosen fibre product of algebraic spaces. -/
public noncomputable abbrev fiberProductSnd
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {F G H : AlgebraicSpaces C S hS} (f : F ⟶ H) (g : G ⟶ H) :
    AlgebraicSpaces.fiberProduct C S hS f g ⟶ G :=
  ObjectProperty.homMk (pullback.snd f.hom g.hom)

/-- The arrows of the restriction: an original arrow with a chosen lift of each endpoint. -/
public noncomputable def restrictionArrows
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    AlgebraicSpaces C S hS :=
  AlgebraicSpaces.fiberProduct C S hS
    (fiberProductSnd g G.target) (fiberProductFst G.source g)

/-- The canonical projection of restricted arrows to the original arrows. -/
public noncomputable def restrictionArrowsToArrows
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrows G g ⟶ G.arrows :=
  fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g) ≫
    fiberProductSnd g G.target

/-- Source of a restricted arrow, the chosen lift of its source. -/
public noncomputable def restrictionSource
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrows G g ⟶ U' :=
  fiberProductSnd (fiberProductSnd g G.target) (fiberProductFst G.source g) ≫
    fiberProductSnd G.source g

/-- Target of a restricted arrow, the chosen lift of its target. -/
public noncomputable def restrictionTarget
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrows G g ⟶ U' :=
  fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g) ≫
    fiberProductFst g G.target

/-- The defining compatibility of the two projections of
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`. -/
public lemma fiberProduct_condition
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {F G H : AlgebraicSpaces C S hS} (f : F ⟶ H) (g : G ⟶ H) :
    fiberProductFst f g ≫ f = fiberProductSnd f g ≫ g :=
  ObjectProperty.hom_ext _ pullback.condition

/-- The lift of the source of an arrow of a restriction maps to the source of that arrow. -/
public lemma restriction_condition
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionSource G g ≫ g =
      restrictionArrowsToArrows G g ≫ G.source := by
  apply ObjectProperty.hom_ext
  ext T x
  have h₁ := pullback_condition_app G.source.hom g.hom T
    ((pullback.snd (pullback.snd g.hom G.target.hom)
      (pullback.fst G.source.hom g.hom)).app T x)
  have h₂ := pullback_condition_app (pullback.snd g.hom G.target.hom)
    (pullback.fst G.source.hom g.hom) T x
  calc
    _ = G.source.hom.app T ((pullback.fst G.source.hom g.hom).app T
        ((pullback.snd (pullback.snd g.hom G.target.hom)
          (pullback.fst G.source.hom g.hom)).app T x)) := h₁.symm
    _ = _ := congrArg (G.source.hom.app T) h₂.symm

/-- The lift of the target of an arrow of a restriction maps to the target of that arrow. -/
public lemma restriction_condition'
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrowsToArrows G g ≫ G.target = restrictionTarget G g ≫ g := by
  apply ObjectProperty.hom_ext
  ext T x
  exact (pullback_condition_app g.hom G.target.hom T
    ((pullback.fst (pullback.snd g.hom G.target.hom)
      (pullback.fst G.source.hom g.hom)).app T x)).symm

/-- An idempotent endomorphism which is an isomorphism is the identity.

Stated for an arbitrary isomorphism rather than in a groupoid, which is the generality it is
used at here; the groupoid form follows by bare application. -/
public theorem eq_id_of_idempotent_isIso
    {D : Type v} [Groupoid.{w} D] {X : D}
    (f : X ⟶ X) (h : f ≫ f = f) : f = 𝟙 X := by
  calc
    f = f ≫ 𝟙 X := by simp
    _ = f ≫ (f ≫ Groupoid.inv f) := congrArg (f ≫ ·) (Groupoid.comp_inv f).symm
    _ = (f ≫ f) ≫ Groupoid.inv f := by rw [Category.assoc]
    _ = f ≫ Groupoid.inv f := by rw [h]
    _ = 𝟙 X := Groupoid.comp_inv f

/-- The source and target of a composite in an evaluated groupoid in functors. -/
private theorem functorGroupoid_comp_source_target
    {D : Type v} [Category.{w} D]
    (K : Deformation.GroupoidInFunctors.{v, w, u} D)
    (T : D) (a b : K.arrows.obj T)
    (h : K.source.app T a = K.target.app T b) :
    K.source.app T (K.compose T a b h) = K.source.app T b ∧
      K.target.app T (K.compose T a b h) = K.target.app T a := by
  let pd := K.pointwiseData T
  let : Category.{u} (K.objects.obj T) := pd.groupoid.toCategory
  let eₐ := K.evaluationArrowEquiv T (K.target.app T b) (K.target.app T a)
  let eᵦ := K.evaluationArrowEquiv T (K.source.app T b) (K.target.app T b)
  let fa := eₐ.symm ⟨a, h, rfl⟩
  let fb := eᵦ.symm ⟨b, rfl, rfl⟩
  have hc := pd.comp_eq fb fa
  have hs := (pd.arrowEquiv (K.source.app T b) (K.target.app T a) (fb ≫ fa)).2
  have hfa : (pd.arrowEquiv (K.target.app T b) (K.target.app T a) fa).1 = a := by
    change (eₐ (eₐ.symm ⟨a, h, rfl⟩)).1 = a
    simp
  have hfb : (pd.arrowEquiv (K.source.app T b) (K.target.app T b) fb).1 = b := by
    change (eᵦ (eᵦ.symm ⟨b, rfl, rfl⟩)).1 = b
    simp
  have hc' :
      (pd.arrowEquiv (K.source.app T b) (K.target.app T a) (fb ≫ fa)).1 =
        K.compose T a b h := by
    calc
      _ = K.comp.app T ⟨((pd.arrowEquiv (K.target.app T b) (K.target.app T a) fa).1,
          (pd.arrowEquiv (K.source.app T b) (K.target.app T b) fb).1), _⟩ := hc
      _ = K.compose T a b h := by
        unfold Deformation.GroupoidInFunctors.compose
        congr 1
        apply Subtype.ext
        exact Prod.ext hfa hfb
  rw [← hc']
  simpa [fa, fb, eₐ, eᵦ] using hs

/-- The source of a composite in an evaluated groupoid in functors is the source of the arrow
composed first, which by the convention of `Deformation.GroupoidInFunctors.compose` is the
second argument. -/
public theorem functorGroupoid_comp_source
    {D : Type v} [Category.{w} D]
    (K : Deformation.GroupoidInFunctors.{v, w, u} D)
    (T : D) (a b : K.arrows.obj T)
    (h : K.source.app T a = K.target.app T b) :
    K.source.app T (K.compose T a b h) = K.source.app T b :=
  (functorGroupoid_comp_source_target K T a b h).1

/-- The target of a composite in an evaluated groupoid in functors is the target of the arrow
composed last, which by the convention of `Deformation.GroupoidInFunctors.compose` is the
first argument. -/
public theorem functorGroupoid_comp_target
    {D : Type v} [Category.{w} D]
    (K : Deformation.GroupoidInFunctors.{v, w, u} D)
    (T : D) (a b : K.arrows.obj T)
    (h : K.source.app T a = K.target.app T b) :
    K.target.app T (K.compose T a b h) = K.target.app T a :=
  (functorGroupoid_comp_source_target K T a b h).2

end GroupoidInAlgebraicSpaces

end AlgebraicGeometry

end
