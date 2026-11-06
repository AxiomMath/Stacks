module

public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupoidObjectComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidTarget

/-!
# A groupoid in algebraic spaces as an internal groupoid object

A groupoid in algebraic spaces over `B` (Stacks 043W) carries its source, target and
composition as data, and asks only that the *evaluation* at every test scheme be a groupoid.
That condition says nothing about the identity and the inverse as morphisms, and so does not
by itself exhibit the quintuple as a groupoid object of a category.  The identity and the
inverse are nevertheless determined (Stacks 06K5), and are available as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityHom` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseHom`.

This file assembles those seven morphisms into a `Deformation.GroupoidObject` of the category of
presheaves of types on the big fppf site over `S`, whose laws hold for generalized elements
indexed by an arbitrary presheaf.  That is the form in which the groupoid transports along a
functor, and in which it can be compared with a groupoid scheme.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.toGroupoidObject`: **the groupoid in presheaves
  of a groupoid in algebraic spaces, as a groupoid object.**  Its object of composable pairs is
  the presheaf fibre product of the source and the target, which is the underlying presheaf of
  the algebraic space on which the composition of the quintuple is given, and its object of
  composable triples is the presheaf fibre product of the second with the first projection.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.comp_app_pair`: the composition of a groupoid in
  algebraic spaces, evaluated at a point of the presheaf fibre product whose two projections are
  known, is the composite of those two arrows in the evaluated groupoid.  This is the dictionary
  between the composition carried by the quintuple and the composition of the pointwise
  groupoids, and every law below is read through it.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.toGroupoidObject_objects` and its companions
  identify the four objects and the seven structure morphisms of
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.toGroupoidObject`.

## Implementation notes

The laws of a groupoid object are quantified over generalized elements indexed by an arbitrary
object of the ambient category.  Here the ambient category is a category of presheaves of types,
where an equality of morphisms is an equality of functions at every test object, so each law is
checked at a point and follows from the corresponding law of the pointwise groupoid at that test
object: `Deformation.PointwiseGroupoid.comp_identityArrow_fst`,
`…comp_identityArrow_snd`, `…comp_inverseArrow_fst`, `…comp_inverseArrow_snd` and
`…comp_assoc`.  No reduction to a universal composable pair is needed, and
`Deformation.GroupoidObject.ofUniversal` is therefore not used.

The composition of the quintuple is a morphism out of the *chosen* fibre product of algebraic
spaces, whereas the pointwise groupoid condition is stated about the composition read on the
presheaf of composable pairs through `AlgebraicGeometry.composableToPullback`.  The two are
related by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.comp_app_pair`, whose proof is that a
point of a presheaf fibre product is determined by its two projections,
`AlgebraicGeometry.Space.pullback_app_ext`.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_groupoidObjectOfSpaces
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_groupoidObjectOfSpaces
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_groupoidObjectOfSpaces.has_limit _

/-- **The composition of a groupoid in algebraic spaces, with the presheaf fibre product of its
source and target named as the domain.**

The algebraic space `AlgebraicGeometry.AlgebraicSpaces.fiberProduct` on which the quintuple
gives its composition has that presheaf fibre product as its underlying presheaf, so this is the
composition of the quintuple and nothing else.  Naming the domain is what lets the composition
be rewritten inside a composite of presheaf morphisms: `CategoryTheory.Category.assoc` is
applied by unification at `implicit` transparency, which does not unfold
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct`, so a composite whose first factor is
`G.comp.hom` with its original domain cannot be re-associated. -/
noncomputable def compOnPairs {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B) :
    pullback G.source.hom G.target.hom ⟶ G.arrows.obj :=
  G.comp.hom

/-- The composition with its domain named is the composition of the quintuple. -/
theorem compOnPairs_eq {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B) :
    compOnPairs G = G.comp.hom := rfl

/-- **The composition of a groupoid in algebraic spaces, read at a point whose two projections
are known.**  A family of points of the presheaf fibre product of the source and the target,
indexed by a presheaf, is sent by the composition of the quintuple to the composite of its two
projections in the groupoid of points over the test object. -/
theorem comp_app_pair {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (k : F ⟶ pullback G.source.hom G.target.hom) (T : (BigFppfOver C S hS)ᵒᵖ) (x : F.obj T)
    (a b : G.arrows.obj.obj T)
    (ha : (pullback.fst G.source.hom G.target.hom).app T (k.app T x) = a)
    (hb : (pullback.snd G.source.hom G.target.hom).app T (k.app T x) = b)
    (hab : G.source.hom.app T a = G.target.hom.app T b) :
    (k ≫ compOnPairs G).app T x = G.toGroupoidInFunctors.comp.app T ⟨(a, b), hab⟩ := by
  have hq : (composableToPullback G.source.hom G.target.hom).app T ⟨(a, b), hab⟩ =
      k.app T x := by
    refine Space.pullback_app_ext C hS G.source.hom G.target.hom T _ _ ?_ ?_
    · rw [Space.composableToPullback_fst_app, ha]
    · rw [Space.composableToPullback_snd_app, hb]
  show G.comp.hom.app T (k.app T x) = G.comp.hom.app T
    ((composableToPullback G.source.hom G.target.hom).app T ⟨(a, b), hab⟩)
  rw [hq]

/-- The identity arrow of a groupoid in algebraic spaces, at a point of a test object, is the
identity arrow of the groupoid of points there. -/
theorem identityHom_app_eq_identityArrow {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.objects.obj.obj T) :
    (identityHom G).hom.app T x = (G.toGroupoidInFunctors.pointwiseData T).identityArrow x :=
  rfl

/-- The composition of a groupoid in algebraic spaces at a point of the presheaf fibre product is
the composite of its two projections in the groupoid of points. -/
private theorem comp_app_eq_comp_app_fst_snd {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ) (q : (pullback G.source.hom G.target.hom).obj T) :
    G.comp.hom.app T q = G.toGroupoidInFunctors.comp.app T
      ⟨((pullback.fst G.source.hom G.target.hom).app T q,
        (pullback.snd G.source.hom G.target.hom).app T q),
        pullback_condition_app G.source.hom G.target.hom T q⟩ :=
  comp_app_pair G (𝟙 _) T q _ _ rfl rfl (pullback_condition_app G.source.hom G.target.hom T q)

/-- The composite of a composable pair of arrows of a groupoid in algebraic spaces has the
source of the arrow composed first. -/
theorem comp_hom_comp_source_hom {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B) :
    compOnPairs G ≫ G.source.hom =
      pullback.snd G.source.hom G.target.hom ≫ G.source.hom := by
  ext T q
  show G.source.hom.app T (G.comp.hom.app T q) =
    G.source.hom.app T ((pullback.snd G.source.hom G.target.hom).app T q)
  rw [comp_app_eq_comp_app_fst_snd]
  exact (G.toGroupoidInFunctors.pointwiseData T).source_comp _ _
    (pullback_condition_app G.source.hom G.target.hom T q)

/-- The composite of a composable pair of arrows of a groupoid in algebraic spaces has the
target of the arrow composed last. -/
theorem comp_hom_comp_target_hom {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B) :
    compOnPairs G ≫ G.target.hom =
      pullback.fst G.source.hom G.target.hom ≫ G.target.hom := by
  ext T q
  show G.target.hom.app T (G.comp.hom.app T q) =
    G.target.hom.app T ((pullback.fst G.source.hom G.target.hom).app T q)
  rw [comp_app_eq_comp_app_fst_snd]
  exact (G.toGroupoidInFunctors.pointwiseData T).target_comp _ _
    (pullback_condition_app G.source.hom G.target.hom T q)

/-- Associativity of the composition of a pointwise groupoid, for arrows named only up to the
equations the laws of a groupoid object supply: the four arrows composed are given as the two
projections of two composable pairs, and the three overlaps are equations rather than syntactic
identities. -/
private theorem comp_assoc_of_eq {U R : Type u} {source target : R → U}
    {comp : {p : R × R // source p.1 = target p.2} → R}
    (P : Deformation.PointwiseGroupoid source target comp)
    {af bf bg d mf ms nf ns : R}
    (hab : source af = target bf) (hbd : source bg = target d) (hkl : bf = bg)
    (hm₁ : mf = comp ⟨(af, bf), hab⟩) (hm₂ : ms = d)
    (hn₁ : nf = af) (hn₂ : ns = comp ⟨(bg, d), hbd⟩)
    (hm : source mf = target ms) (hn : source nf = target ns) :
    comp ⟨(mf, ms), hm⟩ = comp ⟨(nf, ns), hn⟩ := by
  have hbd' : source bf = target d := by rw [hkl]; exact hbd
  have hn₂' : ns = comp ⟨(bf, d), hbd'⟩ := hn₂.trans (P.comp_congr hkl.symm rfl hbd hbd')
  refine (P.comp_congr hm₁ hm₂ hm ((P.source_comp af bf hab).trans hbd')).trans ?_
  refine Eq.trans ?_
    (P.comp_congr hn₁ hn₂' hn (hab.trans (P.target_comp bf d hbd').symm)).symm
  exact P.comp_assoc af bf d hab hbd' ((P.source_comp af bf hab).trans hbd')
    (hab.trans (P.target_comp bf d hbd').symm)

/-- **The groupoid in presheaves of a groupoid in algebraic spaces, as a groupoid object.**

The object and arrow presheaves, the source, the target and the composition are those of the
quintuple; the identity and the inverse are the ones the quintuple determines, Stacks 06K5.  The
object of composable pairs is the presheaf fibre product of the source and the target, on which
the composition of the quintuple is given, and the object of composable triples is the presheaf
fibre product of the second with the first projection. -/
noncomputable def toGroupoidObject {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B) :
    Deformation.GroupoidObject ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) where
  objects := G.objects.obj
  arrows := G.arrows.obj
  pairs := pullback G.source.hom G.target.hom
  triples := pullback (pullback.snd G.source.hom G.target.hom)
    (pullback.fst G.source.hom G.target.hom)
  source := G.source.hom
  target := G.target.hom
  identity := (identityHom G).hom
  inverse := (inverseHom G).hom
  fst := pullback.fst G.source.hom G.target.hom
  snd := pullback.snd G.source.hom G.target.hom
  isPullback_pairs := IsPullback.of_hasPullback G.source.hom G.target.hom
  comp := compOnPairs G
  fst₃ := pullback.fst (pullback.snd G.source.hom G.target.hom)
    (pullback.fst G.source.hom G.target.hom)
  snd₃ := pullback.snd (pullback.snd G.source.hom G.target.hom)
    (pullback.fst G.source.hom G.target.hom)
  isPullback_triples := IsPullback.of_hasPullback _ _
  identity_source := identityHom_comp_source G
  identity_target := identityHom_comp_target G
  inverse_source := inverseHom_comp_source G
  inverse_target := inverseHom_comp_target G
  comp_source := comp_hom_comp_source_hom G
  comp_target := comp_hom_comp_target_hom G
  comp_identity_left := by
    intro F a k h₁ h₂
    ext T x
    have hfst : (pullback.fst G.source.hom G.target.hom).app T (k.app T x) =
        (G.toGroupoidInFunctors.pointwiseData T).identityArrow
          (G.target.hom.app T (a.app T x)) :=
      congrArg (fun m : F ⟶ G.arrows.obj => m.app T x) h₁
    have hsnd : (pullback.snd G.source.hom G.target.hom).app T (k.app T x) = a.app T x :=
      congrArg (fun m : F ⟶ G.arrows.obj => m.app T x) h₂
    refine (comp_app_pair G k T x _ _ hfst hsnd
      ((G.toGroupoidInFunctors.pointwiseData T).source_identityArrow _)).trans ?_
    exact (G.toGroupoidInFunctors.pointwiseData T).comp_identityArrow_fst (a.app T x)
      (G.target.hom.app T (a.app T x)) rfl _
  comp_identity_right := by
    intro F a k h₁ h₂
    ext T x
    have hfst : (pullback.fst G.source.hom G.target.hom).app T (k.app T x) = a.app T x :=
      congrArg (fun m : F ⟶ G.arrows.obj => m.app T x) h₁
    have hsnd : (pullback.snd G.source.hom G.target.hom).app T (k.app T x) =
        (G.toGroupoidInFunctors.pointwiseData T).identityArrow
          (G.source.hom.app T (a.app T x)) :=
      congrArg (fun m : F ⟶ G.arrows.obj => m.app T x) h₂
    refine (comp_app_pair G k T x _ _ hfst hsnd
      ((G.toGroupoidInFunctors.pointwiseData T).target_identityArrow _).symm).trans ?_
    exact (G.toGroupoidInFunctors.pointwiseData T).comp_identityArrow_snd (a.app T x)
      (G.source.hom.app T (a.app T x)) rfl _
  comp_inverse_left := by
    intro F a k h₁ h₂
    ext T x
    have hfst : (pullback.fst G.source.hom G.target.hom).app T (k.app T x) =
        (G.toGroupoidInFunctors.pointwiseData T).inverseArrow (a.app T x) :=
      congrArg (fun m : F ⟶ G.arrows.obj => m.app T x) h₁
    have hsnd : (pullback.snd G.source.hom G.target.hom).app T (k.app T x) = a.app T x :=
      congrArg (fun m : F ⟶ G.arrows.obj => m.app T x) h₂
    refine (comp_app_pair G k T x _ _ hfst hsnd
      ((G.toGroupoidInFunctors.pointwiseData T).source_inverseArrow _)).trans ?_
    exact (G.toGroupoidInFunctors.pointwiseData T).comp_inverseArrow_fst (a.app T x) _
  comp_inverse_right := by
    intro F a k h₁ h₂
    ext T x
    have hfst : (pullback.fst G.source.hom G.target.hom).app T (k.app T x) = a.app T x :=
      congrArg (fun m : F ⟶ G.arrows.obj => m.app T x) h₁
    have hsnd : (pullback.snd G.source.hom G.target.hom).app T (k.app T x) =
        (G.toGroupoidInFunctors.pointwiseData T).inverseArrow (a.app T x) :=
      congrArg (fun m : F ⟶ G.arrows.obj => m.app T x) h₂
    refine (comp_app_pair G k T x _ _ hfst hsnd
      ((G.toGroupoidInFunctors.pointwiseData T).target_inverseArrow _).symm).trans ?_
    exact (G.toGroupoidInFunctors.pointwiseData T).comp_inverseArrow_snd (a.app T x) _
  comp_assoc := by
    intro F k l m n hkl hm₁ hm₂ hn₁ hn₂
    ext T x
    refine (comp_app_pair G m T x _ _ rfl rfl
      (pullback_condition_app G.source.hom G.target.hom T (m.app T x))).trans ?_
    refine Eq.trans ?_ (comp_app_pair G n T x _ _ rfl rfl
      (pullback_condition_app G.source.hom G.target.hom T (n.app T x))).symm
    exact comp_assoc_of_eq (G.toGroupoidInFunctors.pointwiseData T)
      (pullback_condition_app G.source.hom G.target.hom T (k.app T x))
      (pullback_condition_app G.source.hom G.target.hom T (l.app T x))
      (congrArg (fun z : F ⟶ G.arrows.obj => z.app T x) hkl)
      ((congrArg (fun z : F ⟶ G.arrows.obj => z.app T x) hm₁).trans
        (comp_app_pair G k T x _ _ rfl rfl
          (pullback_condition_app G.source.hom G.target.hom T (k.app T x))))
      (congrArg (fun z : F ⟶ G.arrows.obj => z.app T x) hm₂)
      (congrArg (fun z : F ⟶ G.arrows.obj => z.app T x) hn₁)
      ((congrArg (fun z : F ⟶ G.arrows.obj => z.app T x) hn₂).trans
        (comp_app_pair G l T x _ _ rfl rfl
          (pullback_condition_app G.source.hom G.target.hom T (l.app T x))))
      _ _

/-- The object presheaf of the groupoid object of a groupoid in algebraic spaces is the
underlying presheaf of its object space. -/
@[simp] theorem toGroupoidObject_objects {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).objects = G.objects.obj := rfl

/-- The arrow presheaf of the groupoid object of a groupoid in algebraic spaces is the
underlying presheaf of its arrow space. -/
@[simp] theorem toGroupoidObject_arrows {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).arrows = G.arrows.obj := rfl

/-- The object of composable pairs of the groupoid object of a groupoid in algebraic spaces is
the presheaf fibre product of its source and target. -/
@[simp] theorem toGroupoidObject_pairs {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).pairs = pullback G.source.hom G.target.hom := rfl

/-- The source of the groupoid object of a groupoid in algebraic spaces is its source. -/
@[simp] theorem toGroupoidObject_source {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).source = G.source.hom := rfl

/-- The target of the groupoid object of a groupoid in algebraic spaces is its target. -/
@[simp] theorem toGroupoidObject_target {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).target = G.target.hom := rfl

/-- The composition of the groupoid object of a groupoid in algebraic spaces is its
composition. -/
@[simp] theorem toGroupoidObject_comp {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).comp = compOnPairs G := rfl

/-- The identity of the groupoid object of a groupoid in algebraic spaces is the unit the
quintuple determines. -/
@[simp] theorem toGroupoidObject_identity {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).identity = (identityHom G).hom := rfl

/-- The inverse of the groupoid object of a groupoid in algebraic spaces is the inverse the
quintuple determines. -/
@[simp] theorem toGroupoidObject_inverse {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).inverse = (inverseHom G).hom := rfl

/-- The first projection of the object of composable pairs of the groupoid object of a groupoid
in algebraic spaces is the first projection of the presheaf fibre product. -/
@[simp] theorem toGroupoidObject_fst {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).fst = pullback.fst G.source.hom G.target.hom := rfl

/-- The second projection of the object of composable pairs of the groupoid object of a groupoid
in algebraic spaces is the second projection of the presheaf fibre product. -/
@[simp] theorem toGroupoidObject_snd {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (toGroupoidObject G).snd = pullback.snd G.source.hom G.target.hom := rfl

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
