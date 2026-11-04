module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionGroupoidComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInFunctorsIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ConjugationConvention
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecFiniteCover
public import StacksFrontier.Deformation.GroupoidQuotient.EvaluationEquivalence

/-!
# `FA_d` is the pointwise groupoid of the conjugation action groupoid

Stacks 05YQ compares the presheaf `FA_d` of free rank-`d` algebra structures with the quotient
stack of the conjugation action of the unit-fixing subgroup `G ⊆ GL_d` on the scheme `X` of
structure constants. The comparison of the two *stacks* is
`AlgebraicGeometry.FiniteFreeAlgebra.nonempty_isEquivalenceOver_finiteCover_quotientStack`, which
holds for any groupoid in algebraic spaces whose pointwise groupoid presheaf is isomorphic to
`FA_d`; this file produces that isomorphism for the action groupoid of the conjugation action,
which is the remaining content of the tag.

The isomorphism is assembled from three identifications.

* **Stacks 05YP**, `AlgebraicGeometry.FiniteFreeAlgebra.presheaf_actionGroupoid`: `FA_d` is
  isomorphic, as a presheaf in groupoids on all schemes of the site, to the action-groupoid
  presheaf `T ↦ (X(T), G(T) × X(T))` of the concrete conjugation action. Restricting along the
  functor that forgets the structure morphism to `S` gives
  `AlgebraicGeometry.FiniteFreeAlgebra.siteActionFunctor`, and the isomorphism is
  `AlgebraicGeometry.FiniteFreeAlgebra.actionPresheafIso` whiskered by that functor.
* **Stacks 06K4**, `CategoryTheory.Deformation.GroupoidInFunctors.evaluationIso`: that presheaf in
  groupoids is the evaluation of the groupoid in presheaves
  `CategoryTheory.Deformation.GroupoidInFunctors.ofGrpdFunctor` built from it, whose objects at
  `T` are the points of `X` there and whose arrows are triples of two objects and a morphism
  between them.
* The comparison of *that* groupoid in presheaves with the action groupoid of Stacks 0444 of the
  transported action, over the base itself. This is the content of the file:
  `AlgebraicGeometry.FiniteFreeAlgebra.siteActionGroupoidIso`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.actionPresheaf` and
  `AlgebraicGeometry.FiniteFreeAlgebra.actionPresheafIso`: the action-groupoid presheaf of
  Stacks 05YP and its comparison with `FA_d`, chosen from the existential statement.
* `AlgebraicGeometry.FiniteFreeAlgebra.siteActionGroupoid`: the groupoid in presheaves on the
  site over `S` whose evaluation is that presheaf in groupoids.
* `AlgebraicGeometry.FiniteFreeAlgebra.siteActionMatrix`: the unit-fixing matrix of one of its
  arrows.
* `AlgebraicGeometry.FiniteFreeAlgebra.siteActionObjectsIso` and
  `AlgebraicGeometry.FiniteFreeAlgebra.siteActionArrowsIso`: its object and arrow presheaves are
  the functor of points of `X` and the product of the functors of points of `G` and of `X`.
* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationGroupoidInSpaces`: the action groupoid in
  algebraic spaces of the conjugation action, over the base itself.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.siteActionGroupoidIso`: the two groupoids in presheaves
  are isomorphic.
* `AlgebraicGeometry.FiniteFreeAlgebra.conjugationFfaIso`: **`FA_d` on the site over `S` is
  isomorphic to the pointwise groupoid presheaf of the action groupoid of the conjugation
  action.**

## Implementation notes

The comparison is made at the level of
`CategoryTheory.Deformation.GroupoidInFunctors`, not of presheaves in groupoids. An isomorphism
of presheaves in groupoids asks, at each test object, for an isomorphism in `Grpd`, whose inverse
laws are literal equalities of functors; an isomorphism of groupoids in presheaves asks only for
isomorphisms of the object and the arrow presheaf respecting source, target and composition, by
`CategoryTheory.Deformation.GroupoidInFunctors.isoOfMaps`, and those are isomorphisms of
presheaves of *types*, so their inverse laws are checked on elements.

The two conventions for the matrix of an arrow both invert it, and the two inversions cancel:
`AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints_inv` is the change of convention and
`AlgebraicGeometry.FiniteFreeAlgebra.siteActionArrowsIso_hom_app` records that the arrow
identification is matrix-preserving. Nothing in the type checker notices a stray inverse, since
both conventions have the same type.

The arrow bijection is built from `Equiv.sigmaFiberEquiv`: an arrow out of `x` is a matrix `g`
together with the equation `a(g, x) = y` identifying its target, so the pairs `(y, (g, h))` with
`h : a(g, x) = y` are the matrices. Composing the bijections rather than writing the inverse by
hand is what makes the dependent round trip free.

Everything that could be `rw` is written in term mode with `congrArg` and `Eq.trans`: the
underlying presheaf of a tensor product in a slice is a pullback by definition and not
syntactically, so a goal mentioning both spellings is type-correct only at default transparency
and `rw` refuses it.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 06K4](https://stacks.math.columbia.edu/tag/06K4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-! ### The action-groupoid presheaf of Stacks 05YP -/

/-- The action-groupoid presheaf `T ↦ (X(T), G(T) × X(T))` of the concrete conjugation action,
chosen from `AlgebraicGeometry.FiniteFreeAlgebra.presheaf_actionGroupoid`. The relations it
records are a proposition, so the chosen witness is interchangeable with
`AlgebraicGeometry.FiniteFreeAlgebra.conjugationPreservesAlgebraLaws`. -/
noncomputable def actionPresheaf :
    ActionGroupoidPresheaf 𝒞 d (conjugationPreservesAlgebraLaws.{u} (d := d)) :=
  (presheaf_actionGroupoid 𝒞 d (FiniteFreeAlgebra.presheaf 𝒞 d)).choose_spec.choose

/-- **Stacks 05YP, the comparison.** `FA_d` is isomorphic to the action-groupoid presheaf of the
conjugation action. -/
noncomputable def actionPresheafIso :
    (FiniteFreeAlgebra.presheaf 𝒞 d).functor ≅ (actionPresheaf 𝒞 d).toFunctor :=
  (presheaf_actionGroupoid 𝒞 d
    (FiniteFreeAlgebra.presheaf 𝒞 d)).choose_spec.choose_spec.choose

/-- The action-groupoid presheaf, restricted to the big fppf site over `S`. -/
noncomputable abbrev siteActionFunctor : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Grpd.{u, u} :=
  (BigFppfOver.forget 𝒞 S hS).op ⋙ (actionPresheaf 𝒞 d).toFunctor

/-- The groupoid in presheaves on the site over `S` whose evaluation is the action-groupoid
presheaf: its objects at `T` are the points of `X` there, and its arrows are triples of two
points and a morphism between them. -/
noncomputable abbrev siteActionGroupoid :
    Deformation.GroupoidInFunctors ((BigFppfOver 𝒞 S hS)ᵒᵖ) :=
  Deformation.GroupoidInFunctors.ofGrpdFunctor (siteActionFunctor 𝒞 S hS d)

/-! ### The two pointwise bijections -/

/-- **An arrow of the action-groupoid presheaf is a unit-fixing matrix and a point of `X`.** The
target of an arrow out of `x` with matrix `g` is `a(g, x)`, so it carries no information beyond
`g` and `x`: that is `Equiv.sigmaFiberEquiv` for the map `g ↦ a(g, x)`. -/
noncomputable def actionArrowsEquiv (T : 𝒞.Schemesᵒᵖ) :
    (Σ x : ↥((actionPresheaf 𝒞 d).toFunctor.obj T),
        Σ y : ↥((actionPresheaf 𝒞 d).toFunctor.obj T), (x ⟶ y)) ≃
      (UnitFixingMatrix Γ(T.unop.1, ⊤) d × (T.unop.1 ⟶ FiniteFreeAlgebra.scheme.{u} d)) :=
  (Equiv.sigmaCongrRight fun x =>
      (Equiv.sigmaCongrRight fun y => (actionPresheaf 𝒞 d).arrowEquiv T x y).trans
        (Equiv.sigmaFiberEquiv fun g : UnitFixingMatrix Γ(T.unop.1, ⊤) d =>
          conjugationOnPoints conjugationPreservesAlgebraLaws T.unop.1 g x)).trans
    ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))

/-- The unit-fixing matrix of an arrow of
`AlgebraicGeometry.FiniteFreeAlgebra.siteActionGroupoid`, in the convention of Stacks 05YP: an
arrow with matrix `g` out of `x` has target `a(g, x)`. -/
noncomputable def siteActionMatrix (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    UnitFixingMatrix Γ(Space.siteScheme 𝒞 S hS T.unop, ⊤) d :=
  ((actionPresheaf 𝒞 d).arrowEquiv
    ((BigFppfOver.forget 𝒞 S hS).op.obj T) a.1 a.2.1 a.2.2).1

/-- The objects of `AlgebraicGeometry.FiniteFreeAlgebra.siteActionGroupoid` at `T` are the
`T`-points of the scheme `X_S` of structure constants. -/
noncomputable def siteActionObjectEquiv (T : (BigFppfOver 𝒞 S hS)ᵒᵖ) :
    (siteActionGroupoid 𝒞 S hS d).objects.obj T ≃
      (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)).obj T :=
  (Space.structureConstantsPointEquiv 𝒞 S hS d T.unop).symm

/-- The arrows of `AlgebraicGeometry.FiniteFreeAlgebra.siteActionGroupoid` at `T` are a `T`-point
of the unit-fixing group scheme `G_S` and a `T`-point of `X_S`. The group component is the
*inverse* of the matrix of Stacks 05YP, because the action recorded by
`AlgebraicGeometry.Space.conjugationModObj` is the left action `g • x = a(g⁻¹, x)`. -/
noncomputable def siteActionArrowEquiv (T : (BigFppfOver 𝒞 S hS)ᵒᵖ) :
    (siteActionGroupoid 𝒞 S hS d).arrows.obj T ≃
      ((Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⊗
        yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)).obj T :=
  (actionArrowsEquiv 𝒞 d ((BigFppfOver.forget 𝒞 S hS).op.obj T)).trans
    (Equiv.prodCongr
      ((Equiv.inv _).trans (Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).toEquiv.symm)
      (Space.structureConstantsPointEquiv 𝒞 S hS d T.unop).symm)

/-- `AlgebraicGeometry.FiniteFreeAlgebra.siteActionArrowEquiv`, written out. -/
theorem siteActionArrowEquiv_apply (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    siteActionArrowEquiv 𝒞 S hS d T a =
      ((Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).symm (siteActionMatrix 𝒞 S hS d T a)⁻¹,
        siteActionObjectEquiv 𝒞 S hS d T a.1) := rfl

/-! ### Naturality -/

/-- Base change in a tensor product of presheaves of types is componentwise, first component. -/
theorem tensorObj_map_fst (M N : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U) (v : (M ⊗ N).obj T) :
    ((M ⊗ N).map f v).1 = M.map f v.1 := rfl

/-- Base change in a tensor product of presheaves of types is componentwise, second component. -/
theorem tensorObj_map_snd (M N : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U) (v : (M ⊗ N).obj T) :
    ((M ⊗ N).map f v).2 = N.map f v.2 := rfl

/-- The map on global sections induced by a morphism of the big fppf site over `S`. -/
noncomputable abbrev siteGamma {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U) :
    Γ(Space.siteScheme 𝒞 S hS T.unop, ⊤) →+* Γ(Space.siteScheme 𝒞 S hS U.unop, ⊤) :=
  ((Space.toSchemeOver 𝒞 S hS).map f.unop).left.appTop.hom

/-- The object identification commutes with base change: pullback of points of `X` in the
action-groupoid presheaf is precomposition. -/
theorem siteActionObjectEquiv_naturality {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U)
    (x : (siteActionGroupoid 𝒞 S hS d).objects.obj T) :
    siteActionObjectEquiv 𝒞 S hS d U (((siteActionFunctor 𝒞 S hS d).map f).obj x) =
      (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)).map f
        (siteActionObjectEquiv 𝒞 S hS d T x) :=
  (Space.structureConstantsPointEquiv 𝒞 S hS d U.unop).symm_apply_eq.2
    (((actionPresheaf 𝒞 d).pullback_obj ((BigFppfOver.forget 𝒞 S hS).op.map f) x).trans
      ((congrArg
            (fun q : Space.siteScheme 𝒞 S hS T.unop ⟶ FiniteFreeAlgebra.scheme.{u} d =>
              ((Space.toSchemeOver 𝒞 S hS).map f.unop).left ≫ q)
            (Equiv.apply_symm_apply
              (Space.structureConstantsPointEquiv 𝒞 S hS d T.unop) x).symm).trans
        (Space.structureConstantsPointEquiv_naturality 𝒞 S hS d f.unop
          ((Space.structureConstantsPointEquiv 𝒞 S hS d T.unop).symm x)).symm))

/-- Base change extends the entries of the matrix of an arrow. -/
theorem siteActionMatrix_map {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    siteActionMatrix 𝒞 S hS d U ((siteActionGroupoid 𝒞 S hS d).arrows.map f a) =
      UnitFixingMatrix.map (siteGamma 𝒞 S hS f) (siteActionMatrix 𝒞 S hS d T a) :=
  (actionPresheaf 𝒞 d).pullback_arrow ((BigFppfOver.forget 𝒞 S hS).op.map f) a.2.2

/-- `AlgebraicGeometry.Space.unitFixingMatrixEquiv` is natural in the other direction too. -/
theorem unitFixingMatrixEquiv_symm_naturality {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U)
    (g : UnitFixingMatrix Γ(Space.siteScheme 𝒞 S hS T.unop, ⊤) d) :
    (Space.unitFixingMatrixEquiv 𝒞 S hS d U.unop).symm
        (UnitFixingMatrix.map (siteGamma 𝒞 S hS f) g) =
      (Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat).map f
        ((Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).symm g) :=
  (Space.unitFixingMatrixEquiv 𝒞 S hS d U.unop).symm_apply_eq.2
    (((Space.unitFixingMatrixEquiv_naturality 𝒞 S hS d f
          ((Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).symm g)).trans
        (congrArg (UnitFixingMatrix.map (siteGamma 𝒞 S hS f))
          (MulEquiv.apply_symm_apply _ g))).symm)

/-- The arrow identification commutes with base change. -/
theorem siteActionArrowEquiv_naturality {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    siteActionArrowEquiv 𝒞 S hS d U ((siteActionGroupoid 𝒞 S hS d).arrows.map f a) =
      ((Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⊗
          yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)).map f
        (siteActionArrowEquiv 𝒞 S hS d T a) :=
  have h : (Space.unitFixingMatrixEquiv 𝒞 S hS d U.unop).symm
        (siteActionMatrix 𝒞 S hS d U ((siteActionGroupoid 𝒞 S hS d).arrows.map f a))⁻¹ =
      (Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat).map f
        ((Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).symm
          (siteActionMatrix 𝒞 S hS d T a)⁻¹) :=
    (congrArg
        (fun m : UnitFixingMatrix Γ(Space.siteScheme 𝒞 S hS U.unop, ⊤) d =>
          (Space.unitFixingMatrixEquiv 𝒞 S hS d U.unop).symm m⁻¹)
        (siteActionMatrix_map 𝒞 S hS d f a)).trans
      ((congrArg (Space.unitFixingMatrixEquiv 𝒞 S hS d U.unop).symm
          (map_inv (UnitFixingMatrix.mapMonoidHom (siteGamma 𝒞 S hS f))
            (siteActionMatrix 𝒞 S hS d T a)).symm).trans
        (unitFixingMatrixEquiv_symm_naturality 𝒞 S hS d f (siteActionMatrix 𝒞 S hS d T a)⁻¹))
  (siteActionArrowEquiv_apply 𝒞 S hS d U _).trans
    (Prod.ext
      (h.trans (tensorObj_map_fst 𝒞 S hS
        (Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat)
        (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)) f
        (siteActionArrowEquiv 𝒞 S hS d T a)).symm)
      ((siteActionObjectEquiv_naturality 𝒞 S hS d f a.1).trans
        (tensorObj_map_snd 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat)
          (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)) f
          (siteActionArrowEquiv 𝒞 S hS d T a)).symm))

/-! ### The two isomorphisms of presheaves -/

/-- **The object presheaf of `AlgebraicGeometry.FiniteFreeAlgebra.siteActionGroupoid` is the
functor of points of `X_S`.** -/
noncomputable def siteActionObjectsIso :
    (siteActionGroupoid 𝒞 S hS d).objects ≅
      yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d) :=
  NatIso.ofComponents (fun T => (siteActionObjectEquiv 𝒞 S hS d T).toIso)
    fun f => ConcreteCategory.hom_ext _ _ fun x => siteActionObjectEquiv_naturality 𝒞 S hS d f x

/-- **The arrow presheaf of `AlgebraicGeometry.FiniteFreeAlgebra.siteActionGroupoid` is the
product of the functors of points of `G_S` and of `X_S`.** -/
noncomputable def siteActionArrowsIso :
    (siteActionGroupoid 𝒞 S hS d).arrows ≅
      (Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⊗
        yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d) :=
  NatIso.ofComponents (fun T => (siteActionArrowEquiv 𝒞 S hS d T).toIso)
    fun f => ConcreteCategory.hom_ext _ _ fun a => siteActionArrowEquiv_naturality 𝒞 S hS d f a

/-- The object identification, read on points. -/
theorem siteActionObjectsIso_hom_app (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (x : (siteActionGroupoid 𝒞 S hS d).objects.obj T) :
    (siteActionObjectsIso 𝒞 S hS d).hom.app T x = siteActionObjectEquiv 𝒞 S hS d T x := rfl

/-- The arrow identification, read on points: an arrow with matrix `g` in the convention of
Stacks 05YP goes to the group element `g⁻¹`, so composing with the inversion that
`AlgebraicGeometry.FiniteFreeAlgebra.presheaf_actionGroupoid` already performs the comparison
with `FA_d` is matrix-preserving. -/
theorem siteActionArrowsIso_hom_app (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    (siteActionArrowsIso 𝒞 S hS d).hom.app T a =
      ((Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).symm (siteActionMatrix 𝒞 S hS d T a)⁻¹,
        siteActionObjectEquiv 𝒞 S hS d T a.1) := rfl

/-! ### The target of an arrow and the matrix of a composite -/

/-- The target of an arrow is the action of its matrix on its source. -/
theorem conjugationOnPoints_siteActionMatrix (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    conjugationOnPoints conjugationPreservesAlgebraLaws
        (Space.siteScheme 𝒞 S hS T.unop) (siteActionMatrix 𝒞 S hS d T a) a.1 = a.2.1 :=
  ((actionPresheaf 𝒞 d).arrowEquiv
    ((BigFppfOver.forget 𝒞 S hS).op.obj T) a.1 a.2.1 a.2.2).2

/-- **The matrix of a composite is the product of the matrices**, the second factor first: in the
right-action convention of Stacks 05YP the matrix of the arrow that is traversed first comes
first. -/
theorem siteActionMatrix_compose (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a b : (siteActionGroupoid 𝒞 S hS d).arrows.obj T)
    (h : (siteActionGroupoid 𝒞 S hS d).source.app T a =
      (siteActionGroupoid 𝒞 S hS d).target.app T b) :
    siteActionMatrix 𝒞 S hS d T ((siteActionGroupoid 𝒞 S hS d).compose T a b h) =
      siteActionMatrix 𝒞 S hS d T b * siteActionMatrix 𝒞 S hS d T a := by
  obtain ⟨xa, ya, ea⟩ := a
  obtain ⟨xb, yb, eb⟩ := b
  have hp : xa = yb := h
  subst hp
  rw [show (siteActionGroupoid 𝒞 S hS d).compose T ⟨xa, ya, ea⟩ ⟨xb, xa, eb⟩ h =
        ⟨xb, ya, eb ≫ ea⟩ from
      Deformation.GroupoidInFunctors.grpdComp_app
        (siteActionFunctor 𝒞 S hS d) T xb xa ya eb ea]
  exact (actionPresheaf 𝒞 d).arrowEquiv_comp
    ((BigFppfOver.forget 𝒞 S hS).op.obj T) eb ea

/-! ### The action groupoid of the conjugation action over the base itself -/

variable (hG : IsAlgebraicSpace 𝒞 S hS
    (Space.groupOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
      (Space.unitFixingPointsOnSite 𝒞 S hS d)).left)
  (hX : IsAlgebraicSpace 𝒞 S hS
    (Space.objectOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
      (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).left)

/-- The action groupoid of Stacks 0444 of the conjugation action, over the base itself: the
groupoid in algebraic spaces whose quotient stack is the `[X/G]` of Stacks 05YQ. -/
noncomputable abbrev conjugationGroupoidInSpaces :
    GroupoidInAlgebraicSpaces 𝒞 S hS (Space.terminalSpace 𝒞 S hS) :=
  (Space.groupoidOfAction (Space.terminalSpace 𝒞 S hS)
    (Space.groupOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
      (Space.unitFixingPointsOnSite 𝒞 S hS d))
    (Space.objectOverStar 𝒞 S hS (Space.terminalSpace 𝒞 S hS).obj
      (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))) hG hX).groupoid

/-- **The action of the group component of an arrow on its object component is the target of the
arrow.** This is where the two inversions cancel: the group element is `g⁻¹` and the left action
is `h • x = a(h⁻¹, x)`, so the result is `a(g, x)`. -/
theorem smul_siteActionArrows (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    γ[Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat,
          yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)].app T
        ((siteActionArrowsIso 𝒞 S hS d).hom.app T a) =
      (siteActionObjectsIso 𝒞 S hS d).hom.app T a.2.1 :=
  congrArg (Space.structureConstantsPointEquiv 𝒞 S hS d T.unop).symm
    (((congrArg₂
            (fun (g : UnitFixingMatrix Γ(Space.siteScheme 𝒞 S hS T.unop, ⊤) d)
                (x : Space.siteScheme 𝒞 S hS T.unop ⟶ FiniteFreeAlgebra.scheme.{u} d) =>
              leftConjugationOnPoints conjugationPreservesAlgebraLaws
                (Space.siteScheme 𝒞 S hS T.unop) g x)
            (MulEquiv.apply_symm_apply (Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop)
              (siteActionMatrix 𝒞 S hS d T a)⁻¹)
            (Equiv.apply_symm_apply
              (Space.structureConstantsPointEquiv 𝒞 S hS d T.unop) a.1)).trans
        (leftConjugationOnPoints_inv conjugationPreservesAlgebraLaws
          (Space.siteScheme 𝒞 S hS T.unop) (siteActionMatrix 𝒞 S hS d T a) a.1)).trans
      (conjugationOnPoints_siteActionMatrix 𝒞 S hS d T a))

/-- **The arrow identification turns composition into the law `(g, x) ∘ (h, y) = (g * h, y)`** of
Stacks 05YP: the two inversions of the matrix convention reverse the order of the product. -/
theorem siteActionArrowsIso_compose (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a b : (siteActionGroupoid 𝒞 S hS d).arrows.obj T)
    (h : (siteActionGroupoid 𝒞 S hS d).source.app T a =
      (siteActionGroupoid 𝒞 S hS d).target.app T b) :
    (siteActionArrowsIso 𝒞 S hS d).hom.app T
        ((siteActionGroupoid 𝒞 S hS d).compose T a b h) =
      (((siteActionArrowsIso 𝒞 S hS d).hom.app T a).1 *
          ((siteActionArrowsIso 𝒞 S hS d).hom.app T b).1,
        ((siteActionArrowsIso 𝒞 S hS d).hom.app T b).2) :=
  Prod.ext
    ((congrArg
          (fun m : UnitFixingMatrix Γ(Space.siteScheme 𝒞 S hS T.unop, ⊤) d =>
            (Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).symm m⁻¹)
          (siteActionMatrix_compose 𝒞 S hS d T a b h)).trans
      ((congrArg (Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).symm
          (mul_inv_rev (siteActionMatrix 𝒞 S hS d T b)
            (siteActionMatrix 𝒞 S hS d T a))).trans
        (map_mul (Space.unitFixingMatrixEquiv 𝒞 S hS d T.unop).symm
          (siteActionMatrix 𝒞 S hS d T a)⁻¹ (siteActionMatrix 𝒞 S hS d T b)⁻¹)))
    rfl

/-! ### The three compatibilities -/

/-- An element is the inverse of its image under an isomorphism of presheaves of types, once the
image is identified. -/
private theorem eq_inv_app_of_hom_app_eq {C : Type*} [Category C] {F G : C ⥤ Type u}
    (e : F ≅ G) (T : C) {x : F.obj T} {y : G.obj T} (h : e.hom.app T x = y) :
    x = e.inv.app T y :=
  (Deformation.GroupoidInFunctors.app_apply_eq e.hom_inv_id T x).symm.trans (congrArg _ h)

/-- The arrow identification respects the source. -/
theorem source_siteActionArrows (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    (conjugationGroupoidInSpaces 𝒞 S hS d hG hX).toGroupoidInFunctors.source.app T
        ((Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
          ((siteActionArrowsIso 𝒞 S hS d).hom.app T a)) =
      (Space.objectsTerminalIso 𝒞 S hS
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
        ((siteActionObjectsIso 𝒞 S hS d).hom.app T a.1) :=
  eq_inv_app_of_hom_app_eq _ T
    ((Deformation.GroupoidInFunctors.app_apply_eq
          (Space.groupoidOfAction_terminal_source 𝒞 S hS
            (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)) hG hX) T _).trans
      (congrArg Prod.snd
        (Deformation.GroupoidInFunctors.app_apply_eq
          (Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv_hom_id T _)))

/-- The arrow identification respects the target: the target of an arrow of the action groupoid
is the action morphism, and that is the action of the group component. -/
theorem target_siteActionArrows (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a : (siteActionGroupoid 𝒞 S hS d).arrows.obj T) :
    (conjugationGroupoidInSpaces 𝒞 S hS d hG hX).toGroupoidInFunctors.target.app T
        ((Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
          ((siteActionArrowsIso 𝒞 S hS d).hom.app T a)) =
      (Space.objectsTerminalIso 𝒞 S hS
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
        ((siteActionObjectsIso 𝒞 S hS d).hom.app T a.2.1) :=
  eq_inv_app_of_hom_app_eq _ T
    ((Deformation.GroupoidInFunctors.app_apply_eq
          (Space.groupoidOfAction_terminal_target 𝒞 S hS
            (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)) hG hX) T _).trans
      ((congrArg
          (γ[Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat,
            yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)].app T)
          (Deformation.GroupoidInFunctors.app_apply_eq
            (Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
              (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv_hom_id T _)).trans
        (smul_siteActionArrows 𝒞 S hS d T a)))

/-- The arrow identification respects composition. -/
theorem compose_siteActionArrows (T : (BigFppfOver 𝒞 S hS)ᵒᵖ)
    (a b : (siteActionGroupoid 𝒞 S hS d).arrows.obj T)
    (h : (siteActionGroupoid 𝒞 S hS d).source.app T a =
      (siteActionGroupoid 𝒞 S hS d).target.app T b)
    (h' : (conjugationGroupoidInSpaces 𝒞 S hS d hG hX).toGroupoidInFunctors.source.app T
        ((Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
          ((siteActionArrowsIso 𝒞 S hS d).hom.app T a)) =
      (conjugationGroupoidInSpaces 𝒞 S hS d hG hX).toGroupoidInFunctors.target.app T
        ((Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
          ((siteActionArrowsIso 𝒞 S hS d).hom.app T b))) :
    (conjugationGroupoidInSpaces 𝒞 S hS d hG hX).toGroupoidInFunctors.compose T
        ((Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
          ((siteActionArrowsIso 𝒞 S hS d).hom.app T a))
        ((Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
            (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
          ((siteActionArrowsIso 𝒞 S hS d).hom.app T b)) h' =
      (Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
          (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv.app T
        ((siteActionArrowsIso 𝒞 S hS d).hom.app T
          ((siteActionGroupoid 𝒞 S hS d).compose T a b h)) :=
  eq_inv_app_of_hom_app_eq _ T
    ((Space.groupoidOfAction_terminal_compose 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
          (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)) hG hX T _ _ h').trans
      ((congrArg₂
          (fun u v : ((Space.unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⊗
              yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)).obj T =>
            (u.1 * v.1, v.2))
          (Deformation.GroupoidInFunctors.app_apply_eq
            (Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
              (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv_hom_id T _)
          (Deformation.GroupoidInFunctors.app_apply_eq
            (Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
              (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).inv_hom_id T _)).trans
        (siteActionArrowsIso_compose 𝒞 S hS d T a b h).symm))

/-! ### The comparison -/

/-- **The groupoid in presheaves of the action-groupoid presheaf is the action groupoid of the
conjugation action**, over the base itself: the two identifications of the object and the arrow
presheaf respect source, target and composition, and the clause for identities is free. -/
noncomputable def siteActionGroupoidIso :
    siteActionGroupoid 𝒞 S hS d ≅
      (conjugationGroupoidInSpaces 𝒞 S hS d hG hX).toGroupoidInFunctors :=
  Deformation.GroupoidInFunctors.isoOfMaps
    (siteActionObjectsIso 𝒞 S hS d ≪≫
      (Space.objectsTerminalIso 𝒞 S hS
        (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).symm)
    (siteActionArrowsIso 𝒞 S hS d ≪≫
      (Space.arrowsTerminalIso 𝒞 S hS (Space.unitFixingPointsOnSite 𝒞 S hS d)
        (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d))).symm)
    (source_siteActionArrows 𝒞 S hS d hG hX) (target_siteActionArrows 𝒞 S hS d hG hX)
    fun T a b h => compose_siteActionArrows 𝒞 S hS d hG hX T a b h _

/-- **Part of Stacks Project, Tag 05YQ.** The presheaf `FA_d` of free rank-`d` algebra structures
on the big fppf site over `S` is isomorphic to the pointwise groupoid presheaf of the action
groupoid of the conjugation action of the unit-fixing subgroup `G ⊆ GL_d` on the scheme `X` of
structure constants, over the base itself. This is the hypothesis of
`AlgebraicGeometry.FiniteFreeAlgebra.nonempty_isEquivalenceOver_finiteCover_quotientStack`. -/
noncomputable def conjugationFfaIso :
    ffaSitePresheaf 𝒞 S hS d ≅
      AlgebraicGeometry.Stack.evaluationGroupoidFunctor
        (conjugationGroupoidInSpaces 𝒞 S hS d hG hX).toGroupoidInFunctors :=
  Functor.isoWhiskerLeft (BigFppfOver.forget 𝒞 S hS).op (actionPresheafIso 𝒞 d) ≪≫
    (Deformation.GroupoidInFunctors.evaluationIso (siteActionFunctor 𝒞 S hS d)).symm ≪≫
      Deformation.GroupoidInFunctors.evaluationGrpdFunctor.mapIso
        (siteActionGroupoidIso 𝒞 S hS d hG hX)

end AlgebraicGeometry.FiniteFreeAlgebra

end
