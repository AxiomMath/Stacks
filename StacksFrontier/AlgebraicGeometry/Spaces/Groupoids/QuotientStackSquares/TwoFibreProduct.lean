module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyExistence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.Sites.Stack.Groupoid
public import StacksFrontier.CategoryTheory.Sites.Stack.FiberedInSets
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidTwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.StackTransport
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidTransport
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# The 2-cartesian square of a quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `π : 𝒮_U ⟶ [U/R]` be the canonical projection of
Stacks 044R. The square

    𝒮_R ---s---> 𝒮_U
     |            |
     t            π
     v            v
    𝒮_U ---π---> [U/R]

2-commutes by Stacks 044S. Stacks 04M9 says it is 2-cartesian: the arrow space `R` presents the
2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U`.

## Main definitions

* `AlgebraicGeometry.Stack.liftedAssociatedMap`,
  `AlgebraicGeometry.Stack.liftedQuotientStackProjection` and
  `AlgebraicGeometry.Stack.liftedQuotientStackTwoArrow`: the three structure maps of the square,
  transported along that equivalence.
* `AlgebraicGeometry.Stack.quotientStackSquare`: the 2-commutative square itself.
* `AlgebraicGeometry.Stack.arrowToRelativeProduct`: the comparison 1-morphism from `𝒮_R` to the
  canonical 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U`, sending an arrow to its source, its target and
  the 2-arrow of Stacks 044S at it.

## Main results

* `AlgebraicGeometry.Stack.quotientStack_twoFibreProduct`: **Stacks 04M9** — the square is a
  2-fibre product.
* `AlgebraicGeometry.Stack.isFinalTwoCommSq_relativeProductSquare` and
  `AlgebraicGeometry.Stack.isFinalTwoCommSq_of_isTwoFibreProduct_of_isStackInGroupoids`: the
  relative product of a
  cospan of stacks in groupoids, and every terminal object of the quotient category of squares
  over such a cospan, is a 2-fibre product in the sense of Stacks 003Q, with the uniqueness of
  the 2-isomorphism of Stacks 003P (2).
* `AlgebraicGeometry.Stack.quotientStack_twoCartesian_source_target`: **Stacks 04P6**, the
  displayed 2-cartesian diagram of More on Groupoids in Spaces, Section 1, with its apex `R`, legs
  `s` and `t`, projections `π` and canonical 2-arrow written out in the statement.
* `AlgebraicGeometry.Stack.isEquivalence_arrowToRelativeProduct`: that comparison is an
  equivalence of the underlying categories, with
  `AlgebraicGeometry.Stack.arrowToRelativeProduct_comp_relativeProjection` saying that it is
  strictly over the site and `AlgebraicGeometry.Stack.comparison_source` and
  `...obj_y` naming its two components. This is the explicit form of Stacks 04M9: unlike
  `quotientStack_twoFibreProduct`, which is terminality and is produced by a choice, it names the
  1-morphism doing the work, which is what a consumer identifying the arrow space with a
  self-intersection must compute with.

## Implementation notes

The square is stated between the stacks in groupoids associated with the object and arrow
algebraic spaces. Their morphism universes have to be enlarged, through the canonical equivalence,
so that they inhabit the same bicategory as the quotient stack; the projection and the 2-arrow are
the canonical ones of Stacks 044R and Stacks 044S, transported along that equivalence.

The universal property is proved as *terminality* in the bicategory of 2-commutative squares,
rather than by exhibiting a comparison 1-morphism and checking it is an equivalence. The
comparison functor is still what does the work — it sends an object of `𝒮_R` to the triple
consisting of its source, its target and the isomorphism between their images in the quotient — but
once it is known to be an equivalence over the site, terminality transports along it, and the
two-sided inverse needed for an equivalence of squares comes from
`CategoryTheory.Bicategory.Equivalence.mkOfAdjointify`.

That the comparison is an equivalence is checked fibrewise: full faithfulness reduces to
Stacks 044V, the identification of the isomorphism sheaf of two presented objects with the fibre
of the arrow space, and essential surjectivity to the fact that a point of the relative product is
exactly an arrow of the evaluated groupoid.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04P6](https://stacks.math.columbia.edu/tag/04P6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : C.Contains S} {B : AlgebraicSpaces C S hS}

universe u₀ v₀ w₀ v₁ w₁

/-- A map of algebraic spaces acting on their enlarged fibred categories. -/
def liftedAssociatedMap
    {X Y : AlgebraicSpaces C S hS} (a : X ⟶ Y) :
    liftedFibredCategory X ⥤ᵇ liftedFibredCategory Y :=
  BasedFunctor.comp
    (BasedFunctor.comp (liftedFibredCategoryDown X)
      (associatedMap C S hS a.hom).1.hom)
    ⟨ULiftHom.up, rfl⟩

/-- The projection of the enlarged object space to the quotient stack. -/
noncomputable def liftedQuotientStackProjection
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    liftedFibredCategory G.objects ⥤ᵇ quotientStack G :=
  BasedFunctor.comp (liftedFibredCategoryDown G.objects)
    (quotientStackProjection G)

/-- The canonical two-arrow, precomposed with the equivalence from the
enlarged arrow category to the original one. -/
noncomputable def liftedQuotientStackTwoArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedFunctor.comp (liftedAssociatedMap G.source)
      (liftedQuotientStackProjection G) ⟶
    BasedFunctor.comp (liftedAssociatedMap G.target)
      (liftedQuotientStackProjection G) := by
  convert BasedCategory.whiskerLeft
    (liftedFibredCategoryDown G.arrows)
    (quotientStackTwoArrow G) using 1 <;> rfl

/-- The canonical source-target square over the quotient stack. -/
@[stacks 04P6 "the displayed square of a groupoid over its quotient stack"]
noncomputable def quotientStackSquare
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    let J := BigFppfOver.topology C S hS
    let U : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨liftedFibredCategory G.objects,
        isStackInGroupoids_liftedFibredCategory G.objects⟩
    let Q : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨quotientStack G,
        isStackInGroupoids_quotientStack G⟩
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom
        (liftedQuotientStackProjection G) : U ⟶ Q)
      (Bicategory.InducedBicategory.mkHom
        (liftedQuotientStackProjection G) : U ⟶ Q) := by
  let J := BigFppfOver.topology C S hS
  let R : StackInGroupoids (BigFppfOver C S hS) J :=
    ⟨liftedFibredCategory G.arrows,
      isStackInGroupoids_liftedFibredCategory G.arrows⟩
  let α := liftedQuotientStackTwoArrow G
  haveI (x : (liftedFibredCategory G.arrows).obj) : IsIso (α.app x) := by
    have hα := α.isHomLift' x
    have hcart := (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift
      (𝟙 ((liftedFibredCategory G.arrows).p.obj x)) (α.app x)
    let := hcart
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := (quotientStack G).p)
      (f := 𝟙 ((liftedFibredCategory G.arrows).p.obj x)) (α.app x)
  let β :
      (BasedFunctor.comp (liftedAssociatedMap G.source)
        (liftedQuotientStackProjection G)).toFunctor ≅
      (BasedFunctor.comp (liftedAssociatedMap G.target)
        (liftedQuotientStackProjection G)).toFunctor :=
    NatIso.ofComponents (fun x => asIso (α.app x))
      (by intro x y f; exact α.naturality f)
  let γ := BasedNatIso.mkNatIso β (fun x => α.isHomLift' x)
  exact {
    pt := R
    fst := Bicategory.InducedBicategory.mkHom
      (liftedAssociatedMap G.source)
    snd := Bicategory.InducedBicategory.mkHom
      (liftedAssociatedMap G.target)
    iso := Bicategory.InducedBicategory.isoMk γ }

private theorem morSection_eq_pullbackFiberHom
    {D : Type u₀} [Category.{v₀} D] {E : Type w₀} [Category.{v₁} E]
    (p : E ⥤ D) [p.IsFibered] {U : D} {x y : p.Fiber U} (f : x ⟶ y) :
    p.morSection x y f = Functor.pullbackFiberHom f (𝟙 U) := by
  unfold Functor.morSection
  rw [← Category.assoc, ← Functor.pullbackFiberHom_id_base f]
  simp

private theorem fullyFaithful_of_iso_morPresheafMap
    {D : Type u₀} [Category.{v₀} D] {E : Type w₀} [Category.{v₁} E]
    {E' : Type w₁} [Category.{v₁} E']
    (p : E ⥤ D) (q : E' ⥤ D) [p.IsFibered] [q.IsFibered]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : E ⥤ E') (hF : p.IsFibredOneMorphism q F)
    (h : ∀ U (x y : p.Fiber U), IsIso (hF.morPresheafMap x y)) :
    F.Full ∧ F.Faithful := by
  let := hp.isFibered
  let := hq.isFibered
  apply (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
    p q hp hq F hF.comp_eq).mpr
  intro U
  let K := Functor.fiberFunctorOfCompEq hF.comp_eq U
  have hm {x y : p.Fiber U} (f : x ⟶ y) :
      (hF.morPresheafMap x y).app (Opposite.op (Over.mk (𝟙 U)))
        (p.morSection x y f) = q.morSection (K.obj x) (K.obj y) (K.map f) := by
    rw [morSection_eq_pullbackFiberHom, morSection_eq_pullbackFiberHom]
    exact hF.morMapAt_pullbackFiberHom f (𝟙 U)
  have hi (x y : p.Fiber U) :
      Function.Bijective ((hF.morPresheafMap x y).app (Opposite.op (Over.mk (𝟙 U)))) := by
    let := h U x y
    exact (ConcreteCategory.bijective_of_isIso _)
  have hf : K.Full := by
    constructor
    intro x y f
    obtain ⟨a, ha⟩ := (hi x y).2 (q.morSection (K.obj x) (K.obj y) f)
    refine ⟨p.morOfSection x y a, ?_⟩
    apply q.morSection_injective
    rw [← hm, Functor.morSection_morOfSection, ha]
  have hfaith : K.Faithful := by
    constructor
    intro x y a b hab
    apply p.morSection_injective
    apply (hi x y).1
    rw [hm, hm, hab]
  exact ⟨hf, hfaith⟩

private theorem pointwiseToQuotientStack_fullyFaithful
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (pointwiseToQuotientStack G).Full ∧
      (pointwiseToQuotientStack G).Faithful := by
  obtain ⟨hf, hi⟩ := fullyFaithful_of_iso_morPresheafMap
    (quotientPrestack G).p (quotientStack G).p
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G)
    (toQuotientStack G) (isFibredOneMorphism_toQuotientStack G)
    (isomPresheaf_equiv_arrowFiber C S hS G)
  let := hf
  let := hi
  change ((quotientPrestackEquivalence G).functor ⋙
    toQuotientStack G).Full ∧
    ((quotientPrestackEquivalence G).functor ⋙
    toQuotientStack G).Faithful
  constructor <;> infer_instance

private abbrev pointwiseCategory
    (G : GroupoidInAlgebraicSpaces C S hS B) :=
  (presheafOfGroupoids
    (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj

private theorem pointwise_hom_ext
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {x y : pointwiseCategory G} (f g : x ⟶ y)
    (hb : f.base = g.base)
    (hr : (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op x.base) _ _ f.fiber).1 =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op x.base) _ _ g.fiber).1) :
    f = g := by
  cases f with | mk fb ff =>
    cases g with | mk gb gf =>
      dsimp at hb
      subst gb
      have he : ff = gf :=
        (G.toGroupoidInFunctors.evaluationArrowEquiv _ _ _).injective (Subtype.ext hr)
      cases he
      rfl

private noncomputable def pointwiseArrow
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (Opposite.op T)) :
    (⟨T, G.source.hom.app (Opposite.op T) r⟩ : pointwiseCategory G) ⟶
      ⟨T, G.target.hom.app (Opposite.op T) r⟩ :=
  (quotientStackTwoArrow_app G ⟨T, Discrete.mk r⟩).choose

private theorem pointwiseArrow_base
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (Opposite.op T)) :
    (pointwiseArrow G T r).base = 𝟙 T :=
  (quotientStackTwoArrow_app G ⟨T, Discrete.mk r⟩).choose_spec.1

private theorem pointwiseArrow_value
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (Opposite.op T)) :
    (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _
      (pointwiseArrow G T r).fiber).1 = r :=
  (quotientStackTwoArrow_app G ⟨T, Discrete.mk r⟩).choose_spec.2.1

private theorem pointwiseArrow_image
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (Opposite.op T)) :
    HEq ((quotientStackTwoArrow G).app ⟨T, Discrete.mk r⟩)
      ((pointwiseToQuotientStack G).map (pointwiseArrow G T r)) :=
  (quotientStackTwoArrow_app G ⟨T, Discrete.mk r⟩).choose_spec.2.2

private theorem pointwise_arrow_endpoints
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (x y : G.objects.obj.obj (Opposite.op T))
    (f : (⟨T, x⟩ : pointwiseCategory G) ⟶ ⟨T, y⟩) (hf : f.base = 𝟙 T) :
    let r := (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1
    G.source.hom.app (Opposite.op T) r = x ∧
      G.target.hom.app (Opposite.op T) r = y := by
  have h := (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).2
  refine ⟨h.1, ?_⟩
  exact h.2.trans (by change G.objects.obj.map f.base.op y = y; simp [hf])

attribute [local implicit_reducible] BasedFunctor.comp in
/-- **The comparison 1-morphism of Stacks 04M9.** The arrow space of a groupoid in algebraic
spaces maps to the canonical 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U` of the projection of
Stacks 044R with itself: an arrow `r` over a test object goes to the triple consisting of its
source, its target and the canonical 2-arrow of Stacks 044S at `r`, which is invertible because
it lies over an identity of the site. -/
noncomputable def arrowToRelativeProduct
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (liftedFibredCategory G.arrows).obj ⥤
      TwoFibreProductOver
        (liftedFibredCategory G.objects).p
        (liftedFibredCategory G.objects).p
        (quotientStack G).p
        (liftedQuotientStackProjection G).toFunctor
        (liftedQuotientStackProjection G).toFunctor := by
  let A := liftedFibredCategory G.arrows
  let X := liftedFibredCategory G.objects
  let Q := quotientStack G
  let H := (liftedAssociatedMap G.source).toFunctor
  let K := (liftedAssociatedMap G.target).toFunctor
  let F := (liftedQuotientStackProjection G).toFunctor
  let α := liftedQuotientStackTwoArrow G
  have hαiso (x : A.obj) : IsIso (α.app x) := by
    have hα := α.isHomLift' x
    have hcart := (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift
      (𝟙 (A.p.obj x)) (α.app x)
    let := hcart
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := Q.p) (f := 𝟙 (A.p.obj x)) (α.app x)
  letI (x : A.obj) : IsIso (α.app x) := hαiso x
  let t : H ⋙ F ≅ K ⋙ F :=
    NatIso.ofComponents (fun x => asIso (α.app x))
      (by intro x y f; exact α.naturality f)
  exact TwoFibreProductOver.lift X.p X.p Q.p F F A.p H K
    (liftedAssociatedMap G.source).w (liftedAssociatedMap G.target).w t
    (fun x => α.isHomLift' x)

private theorem hom_heq_transport {D : Type u₀} [Category.{v₀} D]
    {a a' b b' : D} (ha : a = a') (hb : b = b') (f : a' ⟶ b) :
    HEq (eqToHom ha ≫ f ≫ eqToHom hb) f := by
  subst a' b'
  simp

private theorem pointwise_map_heq_of_value
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    {x x' y y' : G.objects.obj.obj (Opposite.op T)}
    (hx : x = x') (hy : y = y')
    (f : (⟨T, x⟩ : pointwiseCategory G) ⟶ ⟨T, y⟩)
    (g : (⟨T, x'⟩ : pointwiseCategory G) ⟶ ⟨T, y'⟩)
    (hb : f.base = g.base)
    (hr : (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1 =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).1) :
    HEq ((pointwiseToQuotientStack G).map f)
      ((pointwiseToQuotientStack G).map g) := by
  subst x' y'
  rw [pointwise_hom_ext G f g hb hr]

private theorem pointwise_value_eq_of_map_heq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS)
    {x x' y y' : G.objects.obj.obj (Opposite.op T)}
    (hx : x = x') (hy : y = y')
    (f : (⟨T, x⟩ : pointwiseCategory G) ⟶ ⟨T, y⟩)
    (g : (⟨T, x'⟩ : pointwiseCategory G) ⟶ ⟨T, y'⟩)
    (h : HEq ((pointwiseToQuotientStack G).map f)
      ((pointwiseToQuotientStack G).map g)) :
    (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ f.fiber).1 =
      (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).1 := by
  subst x' y'
  let := (pointwiseToQuotientStack_fullyFaithful G).2
  have he := (pointwiseToQuotientStack G).map_injective (eq_of_heq h)
  cases he
  rfl

private abbrev relativeProduct
    (G : GroupoidInAlgebraicSpaces C S hS B) :=
  TwoFibreProductOver (liftedFibredCategory G.objects).p
    (liftedFibredCategory G.objects).p (quotientStack G).p
    (liftedQuotientStackProjection G).toFunctor
    (liftedQuotientStackProjection G).toFunctor

private theorem relativeProduct_ext
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (P Q : relativeProduct G) (hb : P.base = Q.base) (hx : P.x = Q.x)
    (hy : P.y = Q.y) (hi : HEq P.iso.hom Q.iso.hom) : P = Q := by
  cases P; cases Q
  dsimp at *
  subst_vars
  have hi' := Iso.ext (eq_of_heq hi)
  cases hi'
  rfl

private theorem relativeProduct_iso_heq
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {P Q : relativeProduct G} (h : P = Q) : HEq P.iso.hom Q.iso.hom := by
  cases h
  rfl

/-- The first component of the comparison of Stacks 04M9 at an arrow `r` of the groupoid is the
source of `r`. -/
private theorem comparison_source
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (Opposite.op T)) :
    ((arrowToRelativeProduct G).obj ⟨T, Discrete.mk r⟩).x =
      ⟨T, Discrete.mk (G.source.hom.app (Opposite.op T) r)⟩ :=
  associatedMap_obj C S hS G.source.hom _

/-- The second component of the comparison of Stacks 04M9 at an arrow `r` of the groupoid is the
target of `r`. -/
private theorem comparison_target
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (r : G.arrows.obj.obj (Opposite.op T)) :
    ((arrowToRelativeProduct G).obj ⟨T, Discrete.mk r⟩).y =
      ⟨T, Discrete.mk (G.target.hom.app (Opposite.op T) r)⟩ :=
  associatedMap_obj C S hS G.target.hom _

/-- The first component of the comparison of Stacks 04M9 at an arrow `r` of the groupoid is the
source of `r`.

The public form of the file-local `comparison_source`, which the base keeps `private`; it is
named separately rather than de-privatized so that the base declaration stays byte-identical. -/
alias arrowToRelativeProduct_obj_x := comparison_source

/-- The second component of the comparison of Stacks 04M9 at an arrow `r` of the groupoid is the
target of `r`.

The public form of the file-local `comparison_target`, which the base keeps `private`; it is
named separately rather than de-privatized so that the base declaration stays byte-identical. -/
alias arrowToRelativeProduct_obj_y := comparison_target

private theorem comparison_obj_injective
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Function.Injective (arrowToRelativeProduct G).obj := by
  rintro ⟨T, ⟨r⟩⟩ ⟨T', ⟨r'⟩⟩ h
  have hb := congrArg (fun P : relativeProduct G => P.base) h
  change T = T' at hb
  subst T'
  have hx := congrArg (fun P : relativeProduct G => P.x) h
  have hy := congrArg (fun P : relativeProduct G => P.y) h
  rw [comparison_source, comparison_source] at hx
  rw [comparison_target, comparison_target] at hy
  have inj (u v : G.objects.obj.obj (Opposite.op T))
      (h : (⟨T, Discrete.mk u⟩ : (fibredCategory C S hS G.objects.obj).val.obj) =
        ⟨T, Discrete.mk v⟩) : u = v := by
    injection h with _ h
    exact Discrete.mk.inj h
  have hs := inj _ _ hx
  have ht := inj _ _ hy
  have hi := relativeProduct_iso_heq G h
  have himg := (pointwiseArrow_image G T r).symm.trans
    (hi.trans (pointwiseArrow_image G T r'))
  have hr := pointwise_value_eq_of_map_heq G T hs ht
    (pointwiseArrow G T r) (pointwiseArrow G T r') himg
  rw [pointwiseArrow_value, pointwiseArrow_value] at hr
  cases hr
  rfl

private theorem comparison_obj_surjective
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Function.Surjective (arrowToRelativeProduct G).obj := by
  rintro ⟨T, ⟨Tx, ⟨x⟩⟩, ⟨Ty, ⟨y⟩⟩, hx, hy, e, he⟩
  change Tx = T at hx
  change Ty = T at hy
  subst Tx Ty
  let F := pointwiseToQuotientStack G
  let := (pointwiseToQuotientStack_fullyFaithful G).1
  let := (pointwiseToQuotientStack_fullyFaithful G).2
  let px : (liftedQuotientStackProjection G).obj ⟨T, Discrete.mk x⟩ = F.obj ⟨T, x⟩ :=
    quotientStackProjection_obj G ⟨T, Discrete.mk x⟩
  let py : (liftedQuotientStackProjection G).obj ⟨T, Discrete.mk y⟩ = F.obj ⟨T, y⟩ :=
    quotientStackProjection_obj G ⟨T, Discrete.mk y⟩
  let f : F.obj (⟨T, x⟩ : pointwiseCategory G) ⟶ F.obj ⟨T, y⟩ :=
    eqToHom px.symm ≫ e.hom ≫ eqToHom py
  let g := F.preimage f
  have hg : F.map g = f := F.map_preimage f
  let : (quotientStack G).p.IsHomLift (𝟙 T) e.hom := he
  have hf : (quotientStack G).p.IsHomLift (𝟙 T) f := by
    dsimp only [f]; infer_instance
  have hgm : (quotientStack G).p.IsHomLift (𝟙 T) (F.map g) := hg.symm ▸ hf
  let := hgm
  have hgl := Functor.isHomLift_of_isHomLift_map
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq (𝟙 T) g
  have hgb : g.base = 𝟙 T := by
    let := hgl
    have hh := IsHomLift.fac' (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p (𝟙 T) g
    change g.base = eqToHom (rfl : T = T) ≫ 𝟙 T ≫ eqToHom (rfl : T = T) at hh
    simpa using hh
  let r := (G.toGroupoidInFunctors.evaluationArrowEquiv (Opposite.op T) _ _ g.fiber).1
  obtain ⟨hs, ht⟩ := pointwise_arrow_endpoints G T x y g hgb
  refine ⟨⟨T, Discrete.mk r⟩, relativeProduct_ext G _ _ rfl ?_ ?_ ?_⟩
  · exact (comparison_source G T r).trans (by rw [hs])
  · exact (comparison_target G T r).trans (by rw [ht])
  · have hgg := pointwise_map_heq_of_value G T hs ht (pointwiseArrow G T r) g
      ((pointwiseArrow_base G T r).trans hgb.symm) (pointwiseArrow_value G T r)
    exact (pointwiseArrow_image G T r).trans
      (hgg.trans ((heq_of_eq hg).trans (hom_heq_transport px.symm py e.hom)))

/-- **The universe-enlarged fibred category of an algebraic space is faithful over the site.**
Its fibres are discrete, so a morphism of it is determined by the morphism of the site it lies
over. -/
theorem liftedFibredCategory_faithful
    (X : AlgebraicSpaces C S hS) :
    (liftedFibredCategory X).p.Faithful := by
  let := faithful_fibredCategory_projection X.obj
  constructor
  intro x y f g h
  apply ULift.ext
  exact (fibredCategory C S hS X.obj).val.p.map_injective h

private theorem hom_eq_of_lift {D : Type u₀} [Category.{v₀} D]
    {E : Type w₀} [Category.{v₁} E] (p : E ⥤ D) [p.Faithful]
    {U V : D} (f : U ⟶ V) {x y : E} (a b : x ⟶ y)
    [p.IsHomLift f a] [p.IsHomLift f b] : a = b := by
  apply p.map_injective
  rw [IsHomLift.fac' p f a, IsHomLift.fac' p f b]

private theorem liftedPoints_eq_of_vertical
    (X : AlgebraicSpaces C S hS)
    (T : BigFppfOver C S hS)
    {x y : (liftedFibredCategory X).obj} (f : x ⟶ y)
    (hf : (liftedFibredCategory X).p.IsHomLift (𝟙 T) f) : x = y := by
  let := hf
  have hx := IsHomLift.domain_eq (liftedFibredCategory X).p (𝟙 T) f
  have hy := IsHomLift.codomain_eq (liftedFibredCategory X).p (𝟙 T) f
  rcases x with ⟨Tx, ⟨x⟩⟩
  rcases y with ⟨Ty, ⟨y⟩⟩
  change Tx = T at hx
  change Ty = T at hy
  subst Tx Ty
  have hb := IsHomLift.fac' (liftedFibredCategory X).p (𝟙 T) f
  change f.down.base = eqToHom (rfl : T = T) ≫ 𝟙 T ≫ eqToHom (rfl : T = T) at hb
  simp only [eqToHom_refl, Category.comp_id] at hb
  have he := Discrete.eq_of_hom f.down.fiber
  change x = X.obj.map f.down.base.op y at he
  rw [hb] at he
  change x = X.obj.map (𝟙 (Opposite.op T)) y at he
  have hxy : x = y := by simpa using he
  cases hxy
  rfl

/-- The structure functor of the canonical 2-fibre product of the quotient-stack projection
`π : 𝒮_U ⟶ [U/R]` with itself: the explicit 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U` of Stacks 0040,
read as a category over the site. -/
noncomputable abbrev relativeProjection
    (G : GroupoidInAlgebraicSpaces C S hS B) :=
  TwoFibreProductOver.structureFunctor (liftedFibredCategory G.objects).p
    (liftedFibredCategory G.objects).p (quotientStack G).p
    (liftedQuotientStackProjection G).toFunctor
    (liftedQuotientStackProjection G).toFunctor

private theorem relativeProjection_faithful
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (relativeProjection G).Faithful := by
  let := liftedFibredCategory_faithful G.objects
  constructor
  intro P Q a b h
  change a.hbase = b.hbase at h
  apply TwoFibreProductOver.Hom.ext'
  · have := a.ha
    have : (liftedFibredCategory G.objects).p.IsHomLift a.hbase b.a := h.symm ▸ b.ha
    exact hom_eq_of_lift (liftedFibredCategory G.objects).p a.hbase a.a b.a
  · have := a.hb
    have : (liftedFibredCategory G.objects).p.IsHomLift a.hbase b.b := h.symm ▸ b.hb
    exact hom_eq_of_lift (liftedFibredCategory G.objects).p a.hbase a.b b.b

private theorem hom_heq_of_comm {D : Type u₀} [Category.{v₀} D]
    {a a' b b' : D} (ha : a = a') (hb : b = b')
    (f : a ⟶ b) (g : a' ⟶ b')
    (h : eqToHom ha ≫ g = f ≫ eqToHom hb) : HEq f g := by
  subst a' b'
  simpa using h.symm

private theorem relativeProduct_eq_of_vertical
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) {P Q : relativeProduct G} (f : P ⟶ Q)
    (hf : (relativeProjection G).IsHomLift (𝟙 T) f) : P = Q := by
  let := hf
  let := liftedFibredCategory_faithful G.objects
  have hfa : (liftedFibredCategory G.objects).p.IsHomLift (𝟙 T) f.a :=
    Functor.isHomLift_map_of_comp_eq
    (TwoFibreProductOver.fst_comp_eq (p𝒳 := (liftedFibredCategory G.objects).p)
      (p𝒴 := (liftedFibredCategory G.objects).p) (p𝒮 := (quotientStack G).p)
      (F := (liftedQuotientStackProjection G).toFunctor)
      (G := (liftedQuotientStackProjection G).toFunctor)) (𝟙 T) f
  have hfb : (liftedFibredCategory G.objects).p.IsHomLift (𝟙 T) f.b :=
    Functor.isHomLift_map_of_comp_eq
    (TwoFibreProductOver.snd_comp_eq (p𝒳 := (liftedFibredCategory G.objects).p)
      (p𝒴 := (liftedFibredCategory G.objects).p) (p𝒮 := (quotientStack G).p)
      (F := (liftedQuotientStackProjection G).toFunctor)
      (G := (liftedQuotientStackProjection G).toFunctor)) (𝟙 T) f
  have hx := liftedPoints_eq_of_vertical G.objects T f.a hfa
  have hy := liftedPoints_eq_of_vertical G.objects T f.b hfb
  have := hfa
  have := hfb
  have := IsHomLift.eqToHom_domain_lift_id hx
    (IsHomLift.domain_eq (liftedFibredCategory G.objects).p (𝟙 T) f.a)
  have := IsHomLift.eqToHom_domain_lift_id hy
    (IsHomLift.domain_eq (liftedFibredCategory G.objects).p (𝟙 T) f.b)
  have ha := hom_eq_of_lift (liftedFibredCategory G.objects).p (𝟙 T) f.a (eqToHom hx)
  have hb := hom_eq_of_lift (liftedFibredCategory G.objects).p (𝟙 T) f.b (eqToHom hy)
  refine relativeProduct_ext G P Q
    ((IsHomLift.domain_eq (relativeProjection G) (𝟙 T) f).trans
      (IsHomLift.codomain_eq (relativeProjection G) (𝟙 T) f).symm)
    hx hy ?_
  have hw := f.w
  rw [ha, hb, eqToHom_map, eqToHom_map] at hw
  exact hom_heq_of_comm _ _ _ _ hw

private theorem full_of_injective_on_objects
    {D : Type u₀} [Category.{v₀} D] {E : Type w₀} [Category.{v₁} E]
    {E' : Type w₁} [Category.{v₁} E']
    (p : E ⥤ D) (q : E' ⥤ D) [q.Faithful]
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : E ⥤ E') (hF : F ⋙ q = p) (hi : Function.Injective F.obj)
    (hs : ∀ (U : D) {x y : E'} (f : x ⟶ y), q.IsHomLift (𝟙 U) f → x = y) :
    F.Full := by
  subst hF
  constructor
  intro x y f
  obtain ⟨z, a, ha⟩ := hp.exists_lift (q.map f) y rfl
  have hz : (F ⋙ q).obj z = (F ⋙ q).obj x :=
    IsHomLift.domain_eq (F ⋙ q) (q.map f) a
  have hfac : eqToHom hz.symm ≫ q.map (F.map a) = q.map f := by
    have hh := IsHomLift.fac (F ⋙ q) (q.map f) a
    simpa using hh.symm
  obtain ⟨t, ⟨ht, htcomp⟩, _⟩ := hq.unique_lift (F.map a) f (eqToHom hz.symm) hfac
  have htl : q.IsHomLift (𝟙 (q.obj (F.obj x))) t :=
    IsHomLift.of_fac' q _ t rfl hz (by rw [ht]; simp)
  have hxz := hi (hs _ t htl)
  subst z
  have htid : t = 𝟙 (F.obj x) := by
    apply q.map_injective
    simpa using ht
  refine ⟨a, ?_⟩
  simpa [htid] using htcomp

private theorem comparison_comp_projection
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    arrowToRelativeProduct G ⋙ relativeProjection G = (liftedFibredCategory G.arrows).p :=
  TwoFibreProductOver.lift_comp_structureFunctor _ _ _ _ _ _ _ _
    (liftedAssociatedMap G.source).w (liftedAssociatedMap G.target).w _ _

/-- The comparison of Stacks 04M9 is strictly over the big fppf site of `S`.

The public form of the file-local `comparison_comp_projection`, which the base keeps `private`;
it is named separately rather than de-privatized so that the base declaration stays
byte-identical. -/
alias arrowToRelativeProduct_comp_relativeProjection := comparison_comp_projection

/-- The canonical 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U` is fibred in groupoids over the big fppf
site of `S`. -/
private theorem relativeProjection_isFiberedInGroupoids
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (relativeProjection G).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (isFiberedInGroupoids_uliftHom _
      (fibredCategory C S hS G.objects.obj).property)
    (isFiberedInGroupoids_uliftHom _
      (fibredCategory C S hS G.objects.obj).property)
    (isFiberedInGroupoids_quotientStack G)
    (liftedQuotientStackProjection G).w (liftedQuotientStackProjection G).w

/-- **Stacks 04M9, as an equivalence of the underlying categories.** The comparison 1-morphism
from the arrow space to the canonical 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U` is an equivalence: it
is faithful because the 2-fibre product is faithful over the site, full because it is injective
on objects and the 2-fibre product has no non-identity vertical arrows, and essentially
surjective because `𝒮_{pointwise} ⟶ [U/R]` is fully faithful. -/
theorem isEquivalence_arrowToRelativeProduct
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowToRelativeProduct G).IsEquivalence := by
  let := relativeProjection_faithful G
  let := liftedFibredCategory_faithful G.arrows
  let : (arrowToRelativeProduct G).Faithful :=
    Functor.Faithful.of_comp_eq (arrowToRelativeProduct_comp_relativeProjection G)
  let : (arrowToRelativeProduct G).Full := full_of_injective_on_objects
    (liftedFibredCategory G.arrows).p (relativeProjection G)
    (isFiberedInGroupoids_uliftHom _
      (fibredCategory C S hS G.arrows.obj).property)
    (relativeProjection_isFiberedInGroupoids G)
    (arrowToRelativeProduct G) (arrowToRelativeProduct_comp_relativeProjection G)
    (comparison_obj_injective G) (relativeProduct_eq_of_vertical G)
  let : (arrowToRelativeProduct G).EssSurj := ⟨fun P => by
    obtain ⟨r, hr⟩ := comparison_obj_surjective G P
    exact ⟨r, ⟨eqToIso hr⟩⟩⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private noncomputable def comparisonEquivalence
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    BasedCategory.Equivalence (liftedFibredCategory G.arrows)
      (BasedCategory.ofFunctor (relativeProjection G)) := by
  let h := Functor.IsFiberedInGroupoids.isEquivalence_over
    (liftedFibredCategory G.arrows).p (relativeProjection G)
    (isFiberedInGroupoids_uliftHom _
      (fibredCategory C S hS G.arrows.obj).property)
    (relativeProjection_isFiberedInGroupoids G)
    (arrowToRelativeProduct G) (arrowToRelativeProduct_comp_relativeProjection G)
    (isEquivalence_arrowToRelativeProduct G)
  let F := h.choose
  have hF := h.choose_spec.choose
  let η := h.choose_spec.choose_spec.choose
  let ε := h.choose_spec.choose_spec.choose_spec.choose
  have hη := h.choose_spec.choose_spec.choose_spec.choose_spec.1
  have hε := h.choose_spec.choose_spec.choose_spec.choose_spec.2
  exact ⟨⟨arrowToRelativeProduct G, arrowToRelativeProduct_comp_relativeProjection G⟩,
    ⟨F, hF⟩, BasedNatIso.mkNatIso η hη, BasedNatIso.mkNatIso ε hε⟩

/-- The canonical 2-fibre product `𝒮_U ×_{[U/R]} 𝒮_U` is a stack in groupoids: it is equivalent,
over the site, to the stack in groupoids `𝒮_R` of the arrow space. -/
theorem relativeProjection_isStackInGroupoids
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (relativeProjection G).IsStackInGroupoids (BigFppfOver.topology C S hS) :=
  ((comparisonEquivalence G).isStack _ (liftedFibredCategory_isStack G.arrows)).isStackInGroupoids
    (relativeProjection_isFiberedInGroupoids G)

attribute [local implicit_reducible] StackInGroupoids.bicategory
  Bicategory.InducedBicategory Bicategory.InducedBicategory.forget
  BasedNatTrans.forgetful

section Terminality

open TwoFibreProductOver

universe w₂

variable {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
  {X₀ V₀ Y₀ : StackInGroupoids.{w₂, u, u + 1, u + 1, u + 1} D J}
  (h₀ : X₀ ⟶ Y₀) (s₀ : V₀ ⟶ Y₀)
  (hprod : (structureFunctor X₀.toBasedCategory.p V₀.toBasedCategory.p Y₀.toBasedCategory.p
    h₀.hom.toFunctor s₀.hom.toFunctor).IsStackInGroupoids J)

/-- The relative product, packaged as a square in categories fibred in groupoids. -/
noncomputable def relativeProductSquare : Bicategory.TwoCommSq h₀ s₀ := by
  let Q : StackInGroupoids.{w₂, u, u + 1, u + 1, u + 1} D J :=
    ⟨BasedCategory.ofFunctor
      (structureFunctor X₀.toBasedCategory.p V₀.toBasedCategory.p Y₀.toBasedCategory.p
        h₀.hom.toFunctor s₀.hom.toFunctor), hprod⟩
  let p1 : Q ⟶ X₀ := Bicategory.InducedBicategory.mkHom
    { toFunctor := fst X₀.toBasedCategory.p V₀.toBasedCategory.p Y₀.toBasedCategory.p
        h₀.hom.toFunctor s₀.hom.toFunctor
      w := fst_comp_eq }
  let p2 : Q ⟶ V₀ := Bicategory.InducedBicategory.mkHom
    { toFunctor := snd X₀.toBasedCategory.p V₀.toBasedCategory.p Y₀.toBasedCategory.p
        h₀.hom.toFunctor s₀.hom.toFunctor
      w := snd_comp_eq }
  refine { pt := Q, fst := p1, snd := p2, iso := ?_ }
  exact Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso
      (psiIso X₀.toBasedCategory.p V₀.toBasedCategory.p Y₀.toBasedCategory.p
        h₀.hom.toFunctor s₀.hom.toFunctor)
      (fun q => psiIso_hom_vertical q))


/-- The relative product receives a compatible morphism from every cone. -/
noncomputable def relativeProductPreHom (T : Bicategory.TwoCommSq h₀ s₀) :
    Bicategory.TwoCommSq.PreHom T (relativeProductSquare h₀ s₀ hprod) := by
  let t : T.fst.hom.toFunctor ⋙ h₀.hom.toFunctor ≅
      T.snd.hom.toFunctor ⋙ s₀.hom.toFunctor :=
    (BasedNatTrans.forgetful T.pt.toBasedCategory Y₀.toBasedCategory).mapIso
      ((Bicategory.InducedBicategory.forget.mapFunctor T.pt Y₀).mapIso T.iso)
  let F : T.pt.toBasedCategory.obj ⥤
      TwoFibreProductOver X₀.toBasedCategory.p V₀.toBasedCategory.p Y₀.toBasedCategory.p
      h₀.hom.toFunctor s₀.hom.toFunctor :=
    lift X₀.toBasedCategory.p V₀.toBasedCategory.p Y₀.toBasedCategory.p
        h₀.hom.toFunctor s₀.hom.toFunctor
      T.pt.toBasedCategory.p T.fst.hom.toFunctor T.snd.hom.toFunctor
      T.fst.hom.w T.snd.hom.w t T.iso.hom.hom.isHomLift'
  let k : T.pt ⟶ (relativeProductSquare h₀ s₀ hprod).pt :=
    Bicategory.InducedBicategory.mkHom
      { toFunctor := F, w := lift_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ _ }
  refine { hom := k, isoFst := Iso.refl _, isoSnd := Iso.refl _, compat := ?_ }
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  ext w
  change T.iso.hom.hom.app w ≫ s₀.hom.map (𝟙 _) ≫ 𝟙 _ =
    h₀.hom.map (𝟙 _) ≫ 𝟙 _ ≫ T.iso.hom.hom.app w
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  change T.iso.hom.hom.app w ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ T.iso.hom.hom.app w
  simp


/-- A morphism of a 2-fibre product whose `𝒳`-component lies over `u` lies over `u`: the base
morphism is determined by that component. Stated for abstract categories, because in the
bicategory of stacks the base object of the 2-fibre product and the base object of its first
projection are only definitionally equal and `rw` cannot see through that. -/
lemma isHomLift_of_isHomLift_a {E 𝒜 ℬ 𝒮 : Type*} [Category E] [Category 𝒜] [Category ℬ]
    [Category 𝒮] {p𝒜 : 𝒜 ⥤ E} {pℬ : ℬ ⥤ E} {p𝒮 : 𝒮 ⥤ E} {Fx : 𝒜 ⥤ 𝒮} {Gy : ℬ ⥤ 𝒮}
    {P Q : TwoFibreProductOver p𝒜 pℬ p𝒮 Fx Gy} (Φ : P ⟶ Q) {R S : E} (u : R ⟶ S)
    (hΦ : p𝒜.IsHomLift u Φ.a) : (structureFunctor p𝒜 pℬ p𝒮 Fx Gy).IsHomLift u Φ := by
  have := hΦ
  have hdom : p𝒜.obj P.x = R := IsHomLift.domain_eq p𝒜 u Φ.a
  have hcod : p𝒜.obj Q.x = S := IsHomLift.codomain_eq p𝒜 u Φ.a
  refine IsHomLift.of_fac' _ u Φ (P.hx.symm.trans hdom) (Q.hx.symm.trans hcod) ?_
  rw [structureFunctor_map, Hom.hbase_eq Φ, IsHomLift.fac' p𝒜 u Φ.a]
  simp
  rfl

/-- Transposing a commuting square whose vertical sides are isomorphisms. Stated for four
morphisms of an abstract category: in the bicategory of stacks the two spellings of the objects
involved are only definitionally equal, and `rw` cannot see that, whereas here the variables are
opaque and every step is syntactic. -/
lemma comp_iso_transpose {E : Type*} [Category E] {x y z v : E}
    (α : x ≅ y) (β : z ≅ v) (f : y ⟶ v) (g : x ⟶ z)
    (h : f ≫ β.inv = α.inv ≫ g) : α.hom ≫ f = g ≫ β.hom := by
  have hf : f = α.inv ≫ g ≫ β.hom := by
    rw [← Category.assoc, ← h, Category.assoc, β.inv_hom_id, Category.comp_id]
  rw [hf, α.hom_inv_id_assoc]

attribute [local implicit_reducible] BasedFunctor.comp relativeProductSquare
  TwoFibreProductOver.fst TwoFibreProductOver.snd BasedCategory.ofFunctor

/-- Every pre-morphism of squares from `T` to the relative product `relativeProductSquare` is
equivalent, in the sense of `Bicategory.TwoCommSq.PreHom.Rel`, to `relativeProductPreHom`. -/
theorem relativeProductPreHom_rel (T : Bicategory.TwoCommSq h₀ s₀)
    (F : Bicategory.TwoCommSq.PreHom T (relativeProductSquare h₀ s₀ hprod)) :
    Bicategory.TwoCommSq.PreHom.Rel F
      (relativeProductPreHom h₀ s₀ hprod T) := by
  let γ := F.hom.hom.toFunctor
  let a := (BasedNatTrans.forgetful T.pt.toBasedCategory X₀.toBasedCategory).mapIso
    ((Bicategory.InducedBicategory.forget.mapFunctor T.pt X₀).mapIso F.isoFst.symm)
  let b := (BasedNatTrans.forgetful T.pt.toBasedCategory V₀.toBasedCategory).mapIso
    ((Bicategory.InducedBicategory.forget.mapFunctor T.pt V₀).mapIso F.isoSnd.symm)
  let t := (BasedNatTrans.forgetful T.pt.toBasedCategory Y₀.toBasedCategory).mapIso
    ((Bicategory.InducedBicategory.forget.mapFunctor T.pt Y₀).mapIso T.iso)
  have ha (w) : X₀.toBasedCategory.p.IsHomLift
      (𝟙 (T.pt.toBasedCategory.p.obj w)) (a.hom.app w) := F.isoFst.inv.hom.isHomLift' w
  have hb (w) : V₀.toBasedCategory.p.IsHomLift
      (𝟙 (T.pt.toBasedCategory.p.obj w)) (b.hom.app w) := F.isoSnd.inv.hom.isHomLift' w
  have hab : Functor.whiskerRight a.hom h₀.hom.toFunctor ≫ t.hom =
      Functor.whiskerLeft γ (psiIso X₀.toBasedCategory.p V₀.toBasedCategory.p Y₀.toBasedCategory.p
        h₀.hom.toFunctor s₀.hom.toFunctor).hom ≫
        Functor.whiskerRight b.hom s₀.hom.toFunctor := by
    ext w
    change h₀.hom.toFunctor.map (a.hom.app w) ≫ t.hom.app w =
      (γ.obj w).iso.hom ≫ s₀.hom.toFunctor.map (b.hom.app w)
    have hfwd : T.iso.hom.hom.toNatTrans.app w ≫
        s₀.hom.toFunctor.map (F.isoSnd.hom.hom.toNatTrans.app w) =
      h₀.hom.toFunctor.map (F.isoFst.hom.hom.toNatTrans.app w) ≫
        (γ.obj w).iso.hom := by
      have hh := congrArg (fun η => η.hom.toNatTrans.app w) F.compat
      rw [← Category.comp_id (s₀.hom.toFunctor.map (F.isoSnd.hom.hom.toNatTrans.app w)),
        ← Category.id_comp (γ.obj w).iso.hom]
      exact hh
    change t.hom.app w ≫ s₀.hom.toFunctor.map (b.inv.app w) =
      h₀.hom.toFunctor.map (a.inv.app w) ≫ (γ.obj w).iso.hom at hfwd
    exact comp_iso_transpose (h₀.hom.toFunctor.mapIso (a.app w))
      (s₀.hom.toFunctor.mapIso (b.app w)) (t.hom.app w) ((γ.obj w).iso.hom) hfwd
  let e := liftIso γ a b ha hb hab T.fst.hom.w T.snd.hom.w
    T.iso.hom.hom.isHomLift'
  let G := relativeProductPreHom h₀ s₀ hprod T
  let θ : F.hom ≅ G.hom := Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso e (fun w =>
      isHomLift_of_isHomLift_a (e.hom.app w) (𝟙 (T.pt.toBasedCategory.p.obj w)) (ha w)))
  refine ⟨θ, ?_, ?_⟩ <;>
    (apply Bicategory.InducedBicategory.hom₂_ext; apply BasedNatTrans.ext; ext w)
  · exact NatTrans.congr_app
      (congrArg (fun η => η.hom.toNatTrans) F.isoFst.hom_inv_id) w
  · exact NatTrans.congr_app
      (congrArg (fun η => η.hom.toNatTrans) F.isoSnd.hom_inv_id) w

/-- **The relative product is a 2-fibre product**: it receives a compatible 1-morphism from
every 2-commutative square, uniquely up to the 2-cell equivalence, so it is terminal in the
category of 2-commutative squares over the cospan. -/
noncomputable def relativeProductIsTerminal :
    Bicategory.IsTwoFibreProduct (relativeProductSquare h₀ s₀ hprod) :=
  Limits.IsTerminal.ofUniqueHom (fun T => Quotient.mk _ (relativeProductPreHom h₀ s₀ hprod T))
    fun T q => Quotient.inductionOn q fun F =>
      Quotient.sound (relativeProductPreHom_rel h₀ s₀ hprod T F)

/-- **The projections of the relative product jointly detect 2-cells.** A morphism of the explicit
2-fibre product over the site is determined by its two components. -/
theorem legsDetectTwoCells_relativeProductSquare :
    (relativeProductSquare h₀ s₀ hprod).LegsDetectTwoCells := by
  intro t a b η θ hfst hsnd
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  ext w
  exact Hom.ext' (congrArg (fun ε => ε.hom.toNatTrans.app w) hfst)
    (congrArg (fun ε => ε.hom.toNatTrans.app w) hsnd)

/-- **The relative product is a 2-fibre product in the sense of Stacks 003Q** in the 2-category
of stacks in groupoids: a final object of the 2-category of 2-commutative diagrams over the
cospan, any two 1-morphisms into it being isomorphic by a unique 2-morphism. -/
noncomputable def isFinalTwoCommSq_relativeProductSquare :
    Bicategory.IsFinalTwoCommSq (relativeProductSquare h₀ s₀ hprod) :=
  Bicategory.isFinalTwoCommSq_of_legsDetect (relativeProductIsTerminal h₀ s₀ hprod)
    (legsDetectTwoCells_relativeProductSquare h₀ s₀ hprod)

variable {h₀ s₀} in
/-- **For a cospan of stacks in groupoids whose explicit 2-fibre product is a stack in groupoids,
the two notions of 2-fibre product agree**: every terminal object of the quotient category of
2-commutative squares over the cospan is a final object of the 2-category of 2-commutative
diagrams (Stacks 003Q). -/
noncomputable def isFinalTwoCommSq_of_isTwoFibreProduct_of_isStackInGroupoids
    {P : Bicategory.TwoCommSq h₀ s₀}
    (hP : Bicategory.IsTwoFibreProduct P) : Bicategory.IsFinalTwoCommSq P :=
  Bicategory.isFinalTwoCommSq_of_isTwoFibreProduct_of_legsDetect hP
    (relativeProductIsTerminal h₀ s₀ hprod) (legsDetectTwoCells_relativeProductSquare h₀ s₀ hprod)

end Terminality

open Bicategory

private def reversePreHomOfRetraction {B : Type*} [Bicategory B]
    {x y z : B} {f : x ⟶ z} {g : y ⟶ z}
    {P Q : TwoCommSq f g} (a : TwoCommSq.PreHom P Q)
    (b : Q.pt ⟶ P.pt) (ε : b ≫ a.hom ≅ 𝟙 Q.pt) : TwoCommSq.PreHom Q P := by
  refine { hom := b, isoFst := ?_, isoSnd := ?_, compat := ?_ }
  · exact (λ_ Q.fst).symm ≪≫ whiskerRightIso ε.symm Q.fst ≪≫
      (α_ b a.hom Q.fst) ≪≫ whiskerLeftIso b a.isoFst.symm
  · exact (λ_ Q.snd).symm ≪≫ whiskerRightIso ε.symm Q.snd ≪≫
      (α_ b a.hom Q.snd) ≪≫ whiskerLeftIso b a.isoSnd.symm
  · have hInv :
        (a.hom ◁ Q.iso.hom) ≫ (α_ a.hom Q.snd g).inv ≫ (a.isoSnd.inv ▷ g) =
          (α_ a.hom Q.fst f).inv ≫ (a.isoFst.inv ▷ f) ≫ P.iso.hom := by
        have H := congrArg (fun t =>
          (α_ a.hom Q.fst f).inv ≫ (a.isoFst.inv ▷ f) ≫ t ≫
            (α_ a.hom Q.snd g).inv ≫ (a.isoSnd.inv ▷ g)) a.compat
        simpa [Category.assoc, ← comp_whiskerRight] using H.symm
    have hInv' : (α_ a.hom Q.fst f).hom ≫ (a.hom ◁ Q.iso.hom) ≫
        (α_ a.hom Q.snd g).inv ≫ (a.isoSnd.inv ▷ g) =
      (a.isoFst.inv ▷ f) ≫ P.iso.hom := by
      have H := congrArg (fun t => (α_ a.hom Q.fst f).hom ≫ t) hInv
      simpa [Category.assoc] using H
    have hε : Q.iso.hom ≫ (λ_ (Q.snd ≫ g)).inv ≫
        ε.inv ▷ (Q.snd ≫ g) =
      (λ_ (Q.fst ≫ f)).inv ≫ ε.inv ▷ (Q.fst ≫ f) ≫
        (b ≫ a.hom) ◁ Q.iso.hom := by
      simp only [← Category.assoc]
      rw [leftUnitor_inv_naturality Q.iso.hom]
      simp only [Category.assoc]
      rw [whisker_exchange]
    let pfx : Q.fst ≫ f ⟶ b ≫ ((a.hom ≫ Q.fst) ≫ f) :=
      (λ_ Q.fst).inv ▷ f ≫ ε.inv ▷ Q.fst ▷ f ≫
        (α_ b a.hom Q.fst).hom ▷ f ≫ (α_ b (a.hom ≫ Q.fst) f).hom
    let sfx : (b ≫ a.hom) ≫ (Q.snd ≫ g) ⟶ b ≫ (P.snd ≫ g) :=
      (α_ b a.hom (Q.snd ≫ g)).hom ≫
        b ◁ ((α_ a.hom Q.snd g).inv ≫ (a.isoSnd.inv ▷ g))
    calc
      _ = (Q.iso.hom ≫ (λ_ (Q.snd ≫ g)).inv ≫ ε.inv ▷ (Q.snd ≫ g)) ≫ sfx := by
            dsimp [sfx]
            simp only [Iso.symm_hom, whiskerRightIso_hom,
              whiskerLeftIso_hom, comp_whiskerRight, whisker_assoc, Category.assoc]
            bicategory
      _ = ((λ_ (Q.fst ≫ f)).inv ≫ ε.inv ▷ (Q.fst ≫ f) ≫
            (b ≫ a.hom) ◁ Q.iso.hom) ≫ sfx := by rw [hε]
      _ = pfx ≫ b ◁ ((α_ a.hom Q.fst f).hom ≫ (a.hom ◁ Q.iso.hom) ≫
          (α_ a.hom Q.snd g).inv ≫ (a.isoSnd.inv ▷ g)) := by
            dsimp [pfx, sfx]
            simp only [Category.assoc]
            bicategory
      _ = pfx ≫ b ◁ ((a.isoFst.inv ▷ f) ≫ P.iso.hom) := by rw [hInv']
      _ = _ := by
        dsimp [pfx]
        simp only [Iso.symm_hom, whiskerRightIso_hom,
          whiskerLeftIso_hom, comp_whiskerRight, whisker_assoc, Category.assoc]
        bicategory

attribute [local implicit_reducible] Bicategory.Equivalence.mkOfAdjointifyCounit

private def terminalOfEquivalencePreHom {B : Type*} [Bicategory B]
    {x y z : B} {f : x ⟶ z} {g : y ⟶ z}
    {P Q : TwoCommSq f g} (a : TwoCommSq.PreHom P Q)
    (b : Q.pt ⟶ P.pt) (η : 𝟙 P.pt ≅ a.hom ≫ b)
    (ε : b ≫ a.hom ≅ 𝟙 Q.pt) (hQ : IsTwoFibreProduct Q) :
    IsTwoFibreProduct P := by
  let e := Bicategory.Equivalence.mkOfAdjointifyCounit η ε
  let c := reversePreHomOfRetraction a b e.counit
  have htri := congrArg Iso.inv e.left_triangle
  have htri' : (a.hom ◁ e.counit.inv) ≫ (α_ a.hom b a.hom).inv ≫
      (η.inv ▷ a.hom) = (ρ_ a.hom).hom ≫ (λ_ a.hom).inv := by
    simpa [e, Bicategory.Equivalence.mkOfAdjointifyCounit,
      leftZigzagIso_inv, rightZigzag, bicategoricalComp] using htri
  have htriQ {w : B} (q : Q.pt ⟶ w) :
      a.hom ◁ (λ_ q).inv ≫ a.hom ◁ e.counit.inv ▷ q ≫
        a.hom ◁ (α_ b a.hom q).hom ≫
          (α_ a.hom b (a.hom ≫ q)).inv ≫ η.inv ▷ (a.hom ≫ q) =
        (λ_ (a.hom ≫ q)).inv := by
    have H := congrArg (fun t => t ▷ q) htri'
    simp only [comp_whiskerRight] at H
    calc
      _ = a.hom ◁ (λ_ q).inv ≫ (α_ a.hom (𝟙 Q.pt) q).inv ≫
          ((a.hom ◁ e.counit.inv) ▷ q ≫
            (α_ a.hom b a.hom).inv ▷ q ≫
            (η.inv ▷ a.hom) ▷ q) ≫
          (α_ (𝟙 P.pt) a.hom q).hom := by bicategory
      _ = a.hom ◁ (λ_ q).inv ≫ (α_ a.hom (𝟙 Q.pt) q).inv ≫
          ((ρ_ a.hom).hom ▷ q ≫ (λ_ a.hom).inv ▷ q) ≫
          (α_ (𝟙 P.pt) a.hom q).hom := by rw [H]
      _ = _ := by bicategory
  have hconj {w : B} {t : P.pt ⟶ w} {q : Q.pt ⟶ w}
      (d : t ≅ a.hom ≫ q) :
      d.hom ≫ a.hom ◁ (λ_ q).inv ≫ a.hom ◁ e.counit.inv ▷ q ≫
        a.hom ◁ (α_ b a.hom q).hom ≫ a.hom ◁ b ◁ d.inv ≫
          (α_ a.hom b t).inv ≫ η.inv ▷ t = (λ_ t).inv := by
    have hnat : a.hom ◁ b ◁ d.inv ≫ (α_ a.hom b t).inv ≫ η.inv ▷ t =
        (α_ a.hom b (a.hom ≫ q)).inv ≫ η.inv ▷ (a.hom ≫ q) ≫
          (𝟙 P.pt) ◁ d.inv := by
      simp only [← Category.assoc]
      rw [associator_inv_naturality_right]
      simp only [Category.assoc]
      rw [whisker_exchange]
    calc
      _ = d.hom ≫
          (a.hom ◁ (λ_ q).inv ≫ a.hom ◁ e.counit.inv ▷ q ≫
            a.hom ◁ (α_ b a.hom q).hom ≫
            (α_ a.hom b (a.hom ≫ q)).inv ≫ η.inv ▷ (a.hom ≫ q)) ≫
          (𝟙 P.pt) ◁ d.inv := by rw [hnat]; simp only [Category.assoc]
      _ = d.hom ≫ (λ_ (a.hom ≫ q)).inv ≫ (𝟙 P.pt) ◁ d.inv := by rw [htriQ]
      _ = (λ_ t).inv := by
        simp only [← Category.assoc]
        rw [leftUnitor_inv_naturality d.hom]
        simp
  have h₁ : TwoCommSq.PreHom.Rel (a.comp c) (TwoCommSq.PreHom.id P) := by
    refine ⟨e.unit.symm, ?_, ?_⟩
    all_goals dsimp [TwoCommSq.PreHom.comp, TwoCommSq.PreHom.id, c,
      reversePreHomOfRetraction]
    all_goals simp only [whiskerLeftIso_hom, Iso.trans_hom, Iso.symm_hom,
      whiskerRightIso_hom, whiskerLeft_comp, Category.assoc]
    · exact hconj a.isoFst
    · exact hconj a.isoSnd
  have h₂ : TwoCommSq.PreHom.Rel (c.comp a) (TwoCommSq.PreHom.id Q) := by
    refine ⟨e.counit, ?_, ?_⟩
    all_goals dsimp [TwoCommSq.PreHom.comp, TwoCommSq.PreHom.id, c,
      reversePreHomOfRetraction]
    all_goals simp
  let i : P ≅ Q :=
    { hom := Quotient.mk _ a
      inv := Quotient.mk _ c
      hom_inv_id := Quotient.sound h₁
      inv_hom_id := Quotient.sound h₂ }
  exact hQ.ofIso i.symm


private theorem quotientStackSquare_isTerminal
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Nonempty (Bicategory.IsTwoFibreProduct (quotientStackSquare G)) := by
  let J := BigFppfOver.topology C S hS
  let U : StackInGroupoids (BigFppfOver C S hS) J :=
    ⟨liftedFibredCategory G.objects, isStackInGroupoids_liftedFibredCategory G.objects⟩
  let Q : StackInGroupoids (BigFppfOver C S hS) J :=
    ⟨quotientStack G, isStackInGroupoids_quotientStack G⟩
  let π : U ⟶ Q := Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G)
  let P := quotientStackSquare G
  have hprod : (relativeProjection G).IsStackInGroupoids J :=
    relativeProjection_isStackInGroupoids G
  let R := relativeProductSquare π π hprod
  let k := relativeProductPreHom π π hprod P
  let e := comparisonEquivalence G
  let b : R.pt ⟶ P.pt := Bicategory.InducedBicategory.mkHom e.inverse
  let η : 𝟙 P.pt ≅ k.hom ≫ b :=
    (Bicategory.InducedBicategory.isoMk e.unitIso).symm
  let ε : b ≫ k.hom ≅ 𝟙 R.pt := Bicategory.InducedBicategory.isoMk e.counitIso
  exact ⟨terminalOfEquivalencePreHom k b η ε (relativeProductIsTerminal π π hprod)⟩

/-- The canonical square of the quotient stack is a two-fibre product of
stacks in groupoids over the big fppf site. -/
@[stacks 04M9]
noncomputable def quotientStack_twoFibreProduct
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.IsTwoFibreProduct (quotientStackSquare G) := by
  exact Classical.choice (by exact quotientStackSquare_isTerminal G)

/-- **The 2-cartesian square `R ⇉ U → [U/R]`.** Take the square whose apex is the arrow space
`R`, whose two legs `R ⟶ U` are the source `s` and the target `t`, whose two maps `U ⟶ [U/R]` are
both the projection `π`, and whose filler is the canonical 2-arrow `π ∘ s ⟶ π ∘ t` of
Stacks 044S. That 2-arrow is invertible, so the square 2-commutes through it, and the square is
2-cartesian. Here `R` and `U` stand for the stacks in groupoids attached to the two spaces. -/
@[stacks 04P6 "the 2-cartesian square R ⇉ U → [U/R]: legs s, t, π twice, 2-arrow of 044S"]
theorem quotientStack_twoCartesian_source_target
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    let J := BigFppfOver.topology C S hS
    let R : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨liftedFibredCategory G.arrows, isStackInGroupoids_liftedFibredCategory G.arrows⟩
    let U : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨liftedFibredCategory G.objects, isStackInGroupoids_liftedFibredCategory G.objects⟩
    let Q : StackInGroupoids (BigFppfOver C S hS) J :=
      ⟨quotientStack G, isStackInGroupoids_quotientStack G⟩
    let s : R ⟶ U := Bicategory.InducedBicategory.mkHom (liftedAssociatedMap G.source)
    let t : R ⟶ U := Bicategory.InducedBicategory.mkHom (liftedAssociatedMap G.target)
    let π : U ⟶ Q := Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G)
    ∃ γ : s ≫ π ≅ t ≫ π,
      γ.hom = Bicategory.InducedBicategory.mkHom₂ (liftedQuotientStackTwoArrow G) ∧
      Nonempty (Bicategory.IsTwoFibreProduct
        ({ pt := R, fst := s, snd := t, iso := γ } : Bicategory.TwoCommSq π π)) :=
  ⟨(quotientStackSquare G).iso, rfl, ⟨quotientStack_twoFibreProduct G⟩⟩

end AlgebraicGeometry.Stack

end
