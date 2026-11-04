module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliaryPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackComparison
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonFullness
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.PresentedFibreArrows

/-!
# Local essential surjectivity of the comparison 1-morphism of Section 78.21

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site, and let
`(U'', R'', s'', t'', c'')` be the auxiliary groupoid of Section 78.21, with
`U'' = U ×_{f, U', t'} R'` and `R'' = R ×_{f ∘ s, U', t'} R'`. This file proves that the
comparison 1-morphism

```
[U''/R''] ⟶ [U/R] ×_{[φ], [U'/R'], π'} 𝒮_{U'}
```

of `AlgebraicGeometry.Stack.auxQuotientComparison` is **locally essentially surjective on
fibres**. Together with full faithfulness this is what
`AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare_of` asks for.

## Main results

* `AlgebraicGeometry.Stack.locallyEssSurjOnFibers_auxQuotientComparison`: **the comparison
  1-morphism of Section 78.21 is locally essentially surjective on fibres.**

## Implementation notes

*The argument.* Let `P = (T, y, u', α)` be an object of the 2-fibre product over a test object
`T`, with `y` an object of `[U/R]_T`, `u'` a `T`-point of `U'` and `α : [φ](y) ≅ π'(u')` vertical.
By Stacks 044X (1), `AlgebraicGeometry.Stack.essImage_toQuotientStack`, there is a covering sieve
of `T` along each member `f : V ⟶ T` of which `y` receives a morphism `ξ : π(u) ⟶ y` of `[U/R]`
over `f` from the image of a `V`-point `u` of `U`; the sieve this file produces is that one, and
the whole of the work is then over a single `f`.

Over such an `f`, a cartesian lift `β : v' ⟶ u'` of `f` in the object-space fibration gives one
morphism `π'(v') ⟶ π'(u')` over `f`, and pushing `ξ` through `[φ]`, composing with `α` and
cancelling the 2-isomorphism of Stacks 046Q gives a second one out of `π'(f(u))`. Both are
cartesian, because `[U'/R']` is fibred in groupoids, so
`CategoryTheory.Functor.fiberIsoOfCartesian` compares them by a vertical isomorphism
`π'(f(u)) ≅ π'(v')`, and Stacks 044X (2) in the form
`AlgebraicGeometry.Stack.exists_evaluationArrow` writes that isomorphism as an arrow of the
evaluated groupoid `G'(V)`, i.e. as a `V`-point of `R'`.

Its *inverse* `r'` runs from `v'` to `f(u)`, so `(u, r')` is a `V`-point of `U''`, and the object
of the fibre of `[U''/R'']` that the argument returns is the one that point presents. The two
components of the morphism of the 2-fibre product out of its image are `ξ` and `β`, each
corrected by the bridge identifying the corresponding component of the image of a presented point
with the presented point itself: the 2-isomorphism of Stacks 046Q for the `[U/R]`-component, and
the unit of the universal property of the stackification for the `𝒮_{U'}`-component. The
commuting square is then formal, once the filler is known on a presented object, which is
`AlgebraicGeometry.Stack.auxSquareCell_hom_app_toQuotientStack`: there it is the arrow `r'`
itself.

*Why the generic helpers.* Every step above is a lemma stated over **plain variables** and then
instantiated. There are two reasons. First, `rw [CategoryTheory.Category.assoc]` is unusable
on a composite in `[U'/R']`: the two `≫`s of a nested composite reach their `Category` instance by
different paths, so `rw` does not match a pattern that is visibly present. Second, typeclass
resolution does not see through the semireducible definitions in play — `IsPreFibered`,
`IsCartesian` and `IsIso` for the quotient stacks all fail to resolve at the spellings this file
needs them at, whereas in a generic context, where the instance is a variable, they resolve
syntactically.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### Generic helpers -/

/- A morphism of a category fibred in groupoids lying over an identity is an isomorphism, and its
inverse is again vertical. -/
private theorem exists_inv_of_vertical {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {U : 𝒞} {a b : 𝒳} (α : a ⟶ b)
    (hα : p.IsHomLift (𝟙 U) α) :
    ∃ αinv : b ⟶ a, p.IsHomLift (𝟙 U) αinv ∧ αinv ≫ α = 𝟙 b := by
  have := hα
  have := hp.isStronglyCartesian_homLift (𝟙 U) α
  have : IsIso α := Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 U) α
  exact ⟨CategoryTheory.inv α, inferInstance, IsIso.inv_hom_id α⟩

/- The domain of a morphism lying over `f : V ⟶ U` lies over `V`, with the morphism an explicit
argument so that the instance argument is never a metavariable. -/
private theorem domain_eq_of_isHomLift {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {U V : 𝒞} (f : V ⟶ U) {a b : 𝒳} (α : a ⟶ b) (hα : p.IsHomLift f α) :
    p.obj a = V := by
  have := hα
  exact IsHomLift.domain_eq p f α

/- Every morphism of a category fibred in groupoids lying over `f` is cartesian over `f`. -/
private theorem isCartesian_of_isHomLift {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {U V : 𝒞} (f : V ⟶ U) {a b : 𝒳} (α : a ⟶ b)
    (hα : p.IsHomLift f α) : p.IsCartesian f α := by
  have := hα
  have := hp.isStronglyCartesian_homLift f α
  infer_instance

/- The chosen pullback morphism lies over the morphism it is chosen for. -/
private theorem isHomLift_pullbackMap {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) [p.IsPreFibered] {U V : 𝒞} {a : 𝒳} (ha : p.obj a = U) (f : V ⟶ U) :
    p.IsHomLift f (Functor.IsPreFibered.pullbackMap ha f) := inferInstance

/- The chosen pullback morphism is cartesian. -/
private theorem isCartesian_pullbackMap {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) [p.IsPreFibered] {U V : 𝒞} {a : 𝒳} (ha : p.obj a = U) (f : V ⟶ U) :
    p.IsCartesian f (Functor.IsPreFibered.pullbackMap ha f) := inferInstance

/- A vertical morphism followed by one over `f` lies over `f`. -/
private theorem isHomLift_id_comp {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {U V : 𝒞} (f : V ⟶ U) {a b c : 𝒳} (g : a ⟶ b) (h : b ⟶ c)
    (hg : p.IsHomLift (𝟙 V) g) (hh : p.IsHomLift f h) : p.IsHomLift f (g ≫ h) := by
  have := hg
  have := hh
  have h₂ : p.IsHomLift (𝟙 V ≫ f) (g ≫ h) := inferInstance
  rwa [Category.id_comp] at h₂

/- A morphism over `f` followed by a vertical one lies over `f`. -/
private theorem isHomLift_comp_id {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {U V : 𝒞} (f : V ⟶ U) {a b c : 𝒳} (g : a ⟶ b) (h : b ⟶ c)
    (hg : p.IsHomLift f g) (hh : p.IsHomLift (𝟙 U) h) : p.IsHomLift f (g ≫ h) := by
  have := hg
  have := hh
  have h₂ : p.IsHomLift (f ≫ 𝟙 U) (g ≫ h) := inferInstance
  rwa [Category.comp_id] at h₂

/- A morphism coming from an equality of objects is vertical. -/
private theorem isHomLift_eqToHom {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {a b : 𝒳} (h : a = b) {V : 𝒞} (ha : p.obj a = V) :
    p.IsHomLift (𝟙 V) (eqToHom h) := by
  subst h
  exact IsHomLift.id ha

/- Reassociating the image of a triple composite followed by a morphism, over plain variables. -/
private theorem map_three_comp {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : D ⥤ E) {a b c d : D} (g : a ⟶ b) (h : b ⟶ c) (k : c ⟶ d) {z : E} (m : F.obj d ⟶ z)
    {w : F.obj a ⟶ z} (hw : F.map g ≫ F.map h ≫ F.map k ≫ m = w) :
    F.map (g ≫ h ≫ k) ≫ m = w := by
  rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc]
  exact hw

/- Reassociating a morphism followed by the image of a triple composite, over plain variables. -/
private theorem comp_map_three {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : D ⥤ E) {a b c d : D} (g : a ⟶ b) (h : b ⟶ c) (k : c ⟶ d) {z : E} (m : z ⟶ F.obj a)
    {w : z ⟶ F.obj d} (hw : m ≫ F.map g ≫ F.map h ≫ F.map k = w) :
    m ≫ F.map (g ≫ h ≫ k) = w := by
  rw [F.map_comp, F.map_comp]
  exact hw

/- Congruence of a functor in its morphism argument, over plain variables: the shape in which the
identities between arrows of the evaluated groupoids below are transported. -/
private theorem map_congr {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : D ⥤ E) {a b : D} {g g' : a ⟶ b} (h : g = g') : F.map g = F.map g' := by rw [h]

/- Cancelling a two-sided conjugation against an inverse, over plain variables: the shape in
which the comparison arrow at `(u, r')` and the arrow `arr'` it inverts cancel in the evaluated
groupoid `G'(V)`. -/
private theorem conj_inv_aux {D : Type*} [Category* D] {A₀ V₀ F₀ B₀ : D}
    (eA : A₀ ⟶ V₀) (i : V₀ ⟶ F₀) (eB' : F₀ ⟶ B₀) (eB : B₀ ⟶ F₀) (arr : F₀ ⟶ V₀)
    (h1 : eB' ≫ eB = 𝟙 F₀) (h2 : i ≫ arr = 𝟙 V₀) :
    (eA ≫ i ≫ eB') ≫ eB ≫ arr = eA := by
  rw [Category.assoc, Category.assoc, ← Category.assoc eB' eB arr, h1, Category.id_comp, h2,
    Category.comp_id]

/- The comparison of a presented object with the chosen pullback, over plain variables: a
cartesian morphism over `f` out of the image of an object of the fibre of `p` over `V` exhibits
the chosen pullback along `f` as lying in the essential image of the induced functor on fibres. -/
private theorem nonempty_iso_pullbackFiber {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    {𝒴 : Type*} [Category* 𝒴] (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) [q.IsPreFibered] (F : 𝒳 ⥤ 𝒴)
    (hF : F ⋙ q = p) {U V : 𝒞} (x : q.Fiber U) (f : V ⟶ U) (z : p.Fiber V)
    (Φ : F.obj z.1 ⟶ x.1) (hΦ : q.IsCartesian f Φ) :
    Nonempty ((Functor.Fiber.mapOfComp p q F hF V).obj z ≅ Functor.pullbackFiber q x f) :=
  ⟨Functor.fiberIsoOfCartesian (p := q) (z := (Functor.Fiber.mapOfComp p q F hF V).obj z)
    (z' := Functor.pullbackFiber q x f) f Φ (Functor.IsPreFibered.pullbackMap x.2 f) hΦ
    (isCartesian_pullbackMap q x.2 f)⟩

/- The commuting square of the morphism of the 2-fibre product that local essential surjectivity
produces, as an identity between plain morphisms of a category. Stated over variables because the
composites it manipulates live in `[U'/R']`, where the two `≫`s of a nested composite reach their
`Category` instance by different paths, so neither `rw [Category.assoc]` nor `simp` fires. -/
private theorem square_aux {D : Type*} [Category* D] {A B₁ B₂ B₃ B₄ B₅ Z₁ Z₂ Z₃ : D}
    (Cell : A ⟶ B₁) (Ub : B₁ ⟶ B₂) (Cmp : B₂ ⟶ B₃) (Ab : A ⟶ Z₁) (Cm : Z₁ ⟶ B₃)
    (Cmh : B₃ ⟶ Z₁) (Eq1 : Z₁ ⟶ Z₂) (Eq2 : B₃ ⟶ B₄) (Cmu : B₄ ⟶ Z₂) (Arr : B₄ ⟶ B₅)
    (Eq3 : B₂ ⟶ B₅) (XiP : Z₂ ⟶ Z₃) (Bet : B₅ ⟶ Z₃)
    (hcell : Cell ≫ Ub ≫ Cmp = Ab ≫ Cm) (hcmi : Cm ≫ Cmh = 𝟙 Z₁)
    (hnat : Cmh ≫ Eq1 = Eq2 ≫ Cmu) (hstar : Arr ≫ Bet = Cmu ≫ XiP)
    (hcmp : Cmp ≫ Eq2 ≫ Arr = Eq3) :
    Ab ≫ Eq1 ≫ XiP = Cell ≫ Ub ≫ Eq3 ≫ Bet := by
  have hcell' : Cell ≫ Ub ≫ Cmp ≫ Eq2 ≫ Arr ≫ Bet = Ab ≫ Cm ≫ Eq2 ≫ Arr ≫ Bet := by
    rw [← Category.assoc Ub Cmp (Eq2 ≫ Arr ≫ Bet),
      ← Category.assoc Cell (Ub ≫ Cmp) (Eq2 ≫ Arr ≫ Bet), hcell, Category.assoc]
  have h₂ : Cm ≫ Eq2 ≫ Arr ≫ Bet = Eq1 ≫ XiP := by
    rw [hstar, ← Category.assoc Eq2 Cmu XiP, ← hnat, Category.assoc Cmh Eq1 XiP,
      ← Category.assoc Cm Cmh (Eq1 ≫ XiP), hcmi, Category.id_comp]
  rw [← hcmp, Category.assoc Cmp (Eq2 ≫ Arr) Bet, Category.assoc Eq2 Arr Bet, hcell', h₂]

/-! ### The filler at an object coming from the presentation -/

section Iota

attribute [local implicit_reducible] CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  CategoryTheory.BasedCategory.ofFunctor Grpd.forgetToCat Grpd.of
  CategoryTheory.Pseudofunctor.CoGrothendieck.categoryStruct
  CategoryTheory.Pseudofunctor.CoGrothendieck.category

/- The fibre inclusion of the evaluated groupoid does not change the underlying element of the
arrow space. -/
private theorem evaluationArrow_iota (H : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) {a b : H.toGroupoidInFunctors.Evaluation (op T)} (m : a ⟶ b) :
    (H.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _
        ((CoGrothendieck.ι (evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' T).map m).fiber).1 =
      (H.toGroupoidInFunctors.evaluationArrowEquiv (op T) a b m).1 := by
  show (H.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _
      (m ≫ ((evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor'.mapId ⟨op T⟩).inv.toNatTrans.app b)).1 = _
  rw [Functor.toPseudofunctor'_mapId_inv_app]
  exact evaluationArrow_comp_eqToHom H.toGroupoidInFunctors (op T) m _

/- The image of an arrow of an evaluated groupoid under the fibre inclusion lies in a single
fibre. -/
private theorem iota_base (H : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) {a b : H.toGroupoidInFunctors.Evaluation (op T)} (m : a ⟶ b) :
    ((CoGrothendieck.ι (evaluationGroupoidFunctor H.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor' T).map m).base = 𝟙 T := rfl

/- **The comparison arrow at a point `(u, r')` of `U''` is the arrow of the evaluated groupoid
`G'(T)` whose underlying point of the arrow space is `r'`**, read through the fibre inclusion. -/
private theorem auxComparisonArrow_eq_iota (φ : Hom G G')
    (Z : (presheafOfGroupoids
      (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj)
    (ρ : (show G'.toGroupoidInFunctors.Evaluation (op Z.base) from
        ((auxPointwiseToObjects φ).obj Z).fiber) ⟶ ((auxPointwiseMap φ).obj Z).fiber)
    (hρ : (G'.toGroupoidInFunctors.evaluationArrowEquiv (op Z.base) _ _ ρ).1 =
      (auxObjectsSnd φ).hom.app (op Z.base) Z.fiber) :
    auxComparisonArrow φ Z =
      (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' Z.base).map ρ :=
  pointwiseHom_ext G'.toGroupoidInFunctors
    ((auxComparisonArrow_base φ Z).trans (iota_base G' Z.base ρ).symm)
    ((auxComparisonArrow_arrow φ Z).trans
      (hρ.symm.trans (evaluationArrow_iota G' Z.base ρ).symm))

end Iota

section Presented

/- The two legs of the square are spelled one way in the filler and another in the square, and
the two spellings agree only after the 1-morphisms below are unfolded; naming them is what makes
the rewrites of this section type-correct when instance arguments are compared. -/
attribute [local implicit_reducible] CategoryTheory.BasedFunctor.comp auxQuotientStackUpper
  auxQuotientStackLower auxQuotientToTargetObjects auxLiftedQuotientStackToObjects
  quotientStackOfInvariant liftedQuotientStackProjection toQuotientStackBased
  auxQuotientToSource quotientStackMap GroupoidInAlgebraicSpaces.auxGroupoid
  CategoryTheory.Bicategory.InducedBicategory fibredCategory auxPointwiseToObjects
  prestackOfInvariant liftedFibredCategoryDown liftedFibredCategoryUp quotientPrestackDown

/- The upper leg, restricted to the presentation, is the unit of the universal property of the
stackification for the invariant morphism `U'' ⟶ U'`. -/
private theorem auxRestrictedUpperIso_hom_app (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxRestrictedUpperIso φ).hom.toNatTrans.app X =
      (liftedQuotientStackProjection G').map
        ((quotientStackOfInvariantUnit (auxGroupoid φ) (auxToTargetObjects φ)
          (auxToTargetObjects_invariant φ)).hom.app X) := rfl

/- The lower leg, restricted to the presentation, is the unit of the universal property of the
stackification for the quotient stack map of `g`, followed by the 2-isomorphism of
Stacks 046Q. -/
private theorem auxRestrictedLowerIso_hom_app (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxRestrictedLowerIso φ).hom.toNatTrans.app X =
      (quotientStackMap φ).map ((quotientMapExtensionUnit (auxHom φ)).hom.app X) ≫
        (quotientStackMap_commutes φ).inv.toNatTrans.app
          ((quotientPointwiseMap (auxHom φ)).obj
            ((quotientPrestackDown (auxGroupoid φ)).obj X)) := rfl

/- The square restricted to the presentation, factored through the middle comparison. -/
private theorem auxRestrictedSquare_hom_comp (φ : Hom G G') :
    (auxRestrictedSquare φ).hom ≫ (auxRestrictedLowerIso φ).hom =
      (auxRestrictedUpperIso φ).hom ≫ (auxRestrictedMiddleIso φ).hom := by
  rw [show auxRestrictedSquare φ =
      ((auxRestrictedUpperIso φ).trans (auxRestrictedMiddleIso φ)).trans
        (auxRestrictedLowerIso φ).symm from rfl,
    Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/- The square restricted to the presentation, read at an object. -/
private theorem auxRestrictedSquare_hom_comp_app (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxRestrictedSquare φ).hom.toNatTrans.app X ≫
        (auxRestrictedLowerIso φ).hom.toNatTrans.app X =
      (auxRestrictedUpperIso φ).hom.toNatTrans.app X ≫
        (auxRestrictedMiddleIso φ).hom.toNatTrans.app X :=
  congrArg (fun k : BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ))
      (auxQuotientStackUpper φ) ⟶ auxPresentationComposite φ (auxPointwiseMap φ) =>
    k.toNatTrans.app X) (auxRestrictedSquare_hom_comp φ)

/- The components of the restricted square and of its inverse compose to the identity. -/
private theorem auxRestrictedSquare_inv_hom_app (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxRestrictedSquare φ).inv.toNatTrans.app X ≫
        (auxRestrictedSquare φ).hom.toNatTrans.app X = 𝟙 _ :=
  congrArg (fun k : BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ))
      (auxQuotientStackLower φ) ⟶ BasedFunctor.comp (toQuotientStackBased (auxGroupoid φ))
      (auxQuotientStackLower φ) =>
    k.toNatTrans.app X) (auxRestrictedSquare φ).inv_hom_id

/- **The filler of the square of Section 78.21, at an object coming from the presentation of
`[U''/R'']`**, cleared of inverses: composing it with the two bridges identifying the components
of the image of a presented point with that point gives the comparison arrow. -/
private theorem auxSquareCell_presented (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxSquareCell φ).hom.app ((toQuotientStack (auxGroupoid φ)).obj X) ≫
        (auxRestrictedUpperIso φ).hom.toNatTrans.app X ≫
          (auxRestrictedMiddleIso φ).hom.toNatTrans.app X =
      (auxRestrictedLowerIso φ).hom.toNatTrans.app X := by
  rw [auxSquareCell_hom_app_toQuotientStack, ← auxRestrictedSquare_hom_comp_app,
    ← Category.assoc, auxRestrictedSquare_inv_hom_app]
  exact Category.id_comp _

end Presented

/-! ### The morphism of the 2-fibre product attached to a point of `U''` -/

/- The components of the 2-isomorphism of Stacks 046Q and of its inverse compose to the
identity. -/
private theorem commutes_inv_hom_app (φ : Hom G G')
    (z : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) :
    (quotientStackMap_commutes φ).inv.toNatTrans.app z ≫
        (quotientStackMap_commutes φ).hom.toNatTrans.app z = 𝟙 _ :=
  NatTrans.congr_app
    (congrArg (fun α => BasedNatTrans.toNatTrans α) (quotientStackMap_commutes φ).inv_hom_id) z

section Assembly

/- The 1-morphisms below cross between the pointwise presentation of `[U'/R']` and the enlarged
object space of `U'` by three nested composites; naming them is what lets the elaborator compare
the endpoints of the composites of this section without unfolding the stackification. -/
attribute [local implicit_reducible] liftedQuotientStackProjection quotientStackProjection
  pointwiseObjectInclusion liftedFibredCategoryDown CategoryTheory.BasedFunctor.comp
  pointwiseToQuotientStack quotientStackMap

/- **The morphism of the 2-fibre product attached to a `V`-point `(u, r')` of `U''`.** Given a
morphism `ξ` of `[U/R]` over `f` out of `π(u)`, a morphism `β` of `𝒮_{U'}` over `f` out of the
point `v' = s'(r')`, and an arrow `arr'` of the evaluated groupoid `G'(V)` from `f(u)` to `v'`
whose inverse is represented by `r'` and which compares the two legs over `f`, the image of the
object of `[U''/R'']` presented by `(u, r')` receives a morphism to the given object of the
2-fibre product, lying over `f`. -/
private theorem exists_hom_of_point (φ : Hom G G')
    (P : functorialityTwoFibreProductObj φ) {V : BigFppfOver C S hS} (f : V ⟶ P.base)
    (u : G.objects.obj.obj (op V)) (v' : G'.objects.obj.obj (op V))
    (r' : G'.arrows.obj.obj (op V)) (hrs : G'.source.hom.app (op V) r' = v')
    (hrt : G'.target.hom.app (op V) r' = φ.toGroupoidHom.mapObjects.app (op V) u)
    (ξ : (pointwiseToQuotientStack G).obj ⟨V, u⟩ ⟶ P.x)
    (hξ : (quotientStack G).p.IsHomLift f ξ)
    (β : enlargedPoint G' V v' ⟶ P.y)
    (hβ : (liftedFibredCategory G'.objects).p.IsHomLift f β)
    (arr' : (show G'.toGroupoidInFunctors.Evaluation (op V) from
      φ.toGroupoidHom.mapObjects.app (op V) u) ⟶ v')
    (hinv : (G'.toGroupoidInFunctors.evaluationArrowEquiv (op V) v' _
      (Groupoid.inv arr')).1 = r')
    (hstar : (pointwiseToQuotientStack G').map ((CoGrothendieck.ι
          (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' V).map arr') ≫
        (liftedQuotientStackProjection G').map β =
      (quotientStackMap_commutes φ).hom.toNatTrans.app ⟨V, u⟩ ≫
        (quotientStackMap φ).map ξ ≫ P.iso.hom) :
    ∃ Φ : (auxQuotientComparison φ).obj
        ((pointwiseToQuotientStack (auxGroupoid φ)).obj
          ⟨V, auxPoint φ (op V) u r' hrt⟩) ⟶ P,
      (functorialityTwoFibreProduct φ).IsHomLift f Φ := by
  -- the two endpoints of the comparison arrow at the point `(u, r')`
  have hA : (show G'.toGroupoidInFunctors.Evaluation (op V) from
      G'.source.hom.app (op V)
        ((auxObjectsSnd φ).hom.app (op V) (auxPoint φ (op V) u r' hrt))) = v' :=
    (congrArg (fun w => G'.source.hom.app (op V) w) (auxPoint_snd φ (op V) u r' hrt)).trans hrs
  have hBf : (show G'.toGroupoidInFunctors.Evaluation (op V) from
      φ.toGroupoidHom.mapObjects.app (op V)
        ((auxObjectsFst φ).hom.app (op V) (auxPoint φ (op V) u r' hrt))) =
      φ.toGroupoidHom.mapObjects.app (op V) u :=
    congrArg (fun w => φ.toGroupoidHom.mapObjects.app (op V) w)
      (auxPoint_fst φ (op V) u r' hrt)
  -- the arrow of `G'(V)` that the comparison arrow at `(u, r')` is
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : @Quiver.Hom (G'.toGroupoidInFunctors.Evaluation (op V)) _
      (G'.source.hom.app (op V)
        ((auxObjectsSnd φ).hom.app (op V) (auxPoint φ (op V) u r' hrt)))
      (φ.toGroupoidHom.mapObjects.app (op V)
        ((auxObjectsFst φ).hom.app (op V) (auxPoint φ (op V) u r' hrt))),
      eqToHom hA ≫ Groupoid.inv arr' ≫ eqToHom hBf.symm = ρ := ⟨_, rfl⟩
  have hρ : (G'.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _ ρ).1 =
      (auxObjectsSnd φ).hom.app (op V) (auxPoint φ (op V) u r' hrt) := by
    rw [← hρdef]
    exact (evaluationArrow_eqToHom_comp G'.toGroupoidInFunctors (op V) hA
        (Groupoid.inv arr' ≫ eqToHom hBf.symm)).trans
      ((evaluationArrow_comp_eqToHom G'.toGroupoidInFunctors (op V) (Groupoid.inv arr')
          hBf.symm).trans
        (hinv.trans (auxPoint_snd φ (op V) u r' hrt).symm))
  have hρarr : ρ ≫ eqToHom hBf ≫ arr' = eqToHom hA := by
    rw [← hρdef]
    exact conj_inv_aux _ _ _ _ _ ((eqToHom_trans hBf.symm hBf).trans (eqToHom_refl _ _))
      (Groupoid.inv_comp arr')
  -- the bridge identifying the `[U/R]`-component of the image of the presented point
  have hfstO : (quotientPointwiseMap (auxHom φ)).obj
      (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
        (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) =
      (⟨V, u⟩ : (presheafOfGroupoids
        (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) :=
    congrArg (fun w => (⟨V, w⟩ : (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj))
      (auxPoint_fst φ (op V) u r' hrt)
  -- the bridge identifying the `𝒮_{U'}`-component of the image of the presented point
  have hsndO : (prestackOfInvariant (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ)).obj
      ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
        ⟨V, auxPoint φ (op V) u r' hrt⟩) = enlargedPoint G' V v' :=
    (congrArg (fun w => enlargedPoint G' V (G'.source.hom.app (op V) w))
      (auxPoint_snd φ (op V) u r' hrt)).trans (congrArg (enlargedPoint G' V) hrs)
  -- the two components lie over `f`
  have hvp : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      (𝟙 V) (eqToHom hfstO) :=
    isHomLift_eqToHom (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p hfstO rfl
  have hvm : (quotientStack G).p.IsHomLift (𝟙 V)
      ((pointwiseToQuotientStack G).map (eqToHom hfstO)) :=
    Functor.isHomLift_map_of_comp_eq_general
      (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq (𝟙 V) (eqToHom hfstO) hvp
  have ha : (quotientStack G).p.IsHomLift f
      ((quotientMapExtensionUnit (auxHom φ)).hom.app
          ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
            ⟨V, auxPoint φ (op V) u r' hrt⟩) ≫
        (pointwiseToQuotientStack G).map (eqToHom hfstO) ≫ ξ) :=
    isHomLift_id_comp (quotientStack G).p f _ _
      (quotientMapExtensionUnit_hom_isHomLift (auxHom φ)
        ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
          ⟨V, auxPoint φ (op V) u r' hrt⟩))
      (isHomLift_id_comp (quotientStack G).p f _ _ hvm hξ)
  have hVy : (liftedFibredCategory G'.objects).p.obj
      ((prestackOfInvariant (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ)).obj
          ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
            ⟨V, auxPoint φ (op V) u r' hrt⟩)) = V := rfl
  have hbv : (liftedFibredCategory G'.objects).p.IsHomLift f
      ((quotientStackOfInvariantUnit (auxGroupoid φ) (auxToTargetObjects φ)
          (auxToTargetObjects_invariant φ)).hom.app
          ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
            ⟨V, auxPoint φ (op V) u r' hrt⟩) ≫ eqToHom hsndO ≫ β) :=
    isHomLift_id_comp (liftedFibredCategory G'.objects).p f _ _
      (isHomLift_quotientStackOfInvariantUnit_app (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ)
        ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
          ⟨V, auxPoint φ (op V) u r' hrt⟩))
      (isHomLift_id_comp (liftedFibredCategory G'.objects).p f _ _
        (isHomLift_eqToHom (liftedFibredCategory G'.objects).p hsndO hVy) hβ)
  -- the comparison arrow at the presented point cancels the arrow it inverts
  have hPt : (auxPointwiseToObjects φ).obj
      (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
        (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) =
      (⟨V, v'⟩ : (presheafOfGroupoids
        (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).obj) :=
    (congrArg (fun w => (⟨V, G'.source.hom.app (op V) w⟩ : (presheafOfGroupoids
        (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).obj))
      (auxPoint_snd φ (op V) u r' hrt)).trans
      (congrArg (fun w => (⟨V, w⟩ : (presheafOfGroupoids
        (evaluationGroupoidFunctor G'.toGroupoidInFunctors)).obj)) hrs)
  have heq2 : (quotientPointwiseMap φ).map (eqToHom hfstO) =
      (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' V).map (eqToHom hBf) :=
    (eqToHom_map (quotientPointwiseMap φ).toFunctor hfstO).trans
      (eqToHom_map (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor' V) hBf).symm
  have hiota : (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map ρ ≫
      (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map (eqToHom hBf) ≫
        (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map arr' = eqToHom hPt :=
    (congrArg (fun k => (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map ρ ≫ k)
        (Functor.map_comp (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V) (eqToHom hBf) arr')).symm.trans
      ((Functor.map_comp (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' V) ρ (eqToHom hBf ≫ arr')).symm.trans
        ((map_congr (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' V) hρarr).trans
          (eqToHom_map (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' V) hA)))
  have h5pt : auxComparisonArrow φ
        (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) ≫
      (quotientPointwiseMap φ).map (eqToHom hfstO) ≫
        (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map arr' = eqToHom hPt := by
    rw [auxComparisonArrow_eq_iota φ
        (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj) ρ hρ, heq2]
    exact hiota
  -- the two legs on the presentation, compared through the arrow that `(u, r')` carries
  have hcmp : (pointwiseToQuotientStack G').map (auxComparisonArrow φ
        (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj)) ≫
      (pointwiseToQuotientStack G').map ((quotientPointwiseMap φ).map (eqToHom hfstO)) ≫
        (pointwiseToQuotientStack G').map ((CoGrothendieck.ι
          (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' V).map arr') =
      (liftedQuotientStackProjection G').map (eqToHom hsndO) :=
    ((congrArg (fun k => (pointwiseToQuotientStack G').map (auxComparisonArrow φ
          (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
            (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj)) ≫ k)
          (Functor.map_comp (pointwiseToQuotientStack G')
            ((quotientPointwiseMap φ).map (eqToHom hfstO))
            ((CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor' V).map arr'))).symm.trans
        ((Functor.map_comp (pointwiseToQuotientStack G') (auxComparisonArrow φ
            (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
              (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj))
            ((quotientPointwiseMap φ).map (eqToHom hfstO) ≫
              (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
                Grpd.forgetToCat).toPseudofunctor' V).map arr')).symm.trans
          ((map_congr (pointwiseToQuotientStack G') h5pt).trans
            (eqToHom_map (pointwiseToQuotientStack G') hPt)))).trans
      (eqToHom_map (liftedQuotientStackProjection G').toFunctor hsndO).symm
  -- the filler at the presented point, in the shape the commuting square consumes it
  have hcell : (auxSquareCell φ).hom.app
        ((pointwiseToQuotientStack (auxGroupoid φ)).obj
          ⟨V, auxPoint φ (op V) u r' hrt⟩) ≫
      (liftedQuotientStackProjection G').map
          ((quotientStackOfInvariantUnit (auxGroupoid φ) (auxToTargetObjects φ)
            (auxToTargetObjects_invariant φ)).hom.app
            ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
              ⟨V, auxPoint φ (op V) u r' hrt⟩)) ≫
        (pointwiseToQuotientStack G').map (auxComparisonArrow φ
          (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
            (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj)) =
      (quotientStackMap φ).map ((quotientMapExtensionUnit (auxHom φ)).hom.app
          ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
            ⟨V, auxPoint φ (op V) u r' hrt⟩)) ≫
        (quotientStackMap_commutes φ).inv.toNatTrans.app
          ((quotientPointwiseMap (auxHom φ)).obj (⟨V, auxPoint φ (op V) u r' hrt⟩ :
            (presheafOfGroupoids
              (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj)) :=
    auxSquareCell_presented φ ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
          ⟨V, auxPoint φ (op V) u r' hrt⟩)
  -- the commuting square of the morphism of the 2-fibre product
  have hw : (quotientStackMap φ).toFunctor.map
        ((quotientMapExtensionUnit (auxHom φ)).hom.app
            ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
              ⟨V, auxPoint φ (op V) u r' hrt⟩) ≫
          (pointwiseToQuotientStack G).map (eqToHom hfstO) ≫ ξ) ≫ P.iso.hom =
      (auxSquareCell φ).hom.app
          ((pointwiseToQuotientStack (auxGroupoid φ)).obj
            ⟨V, auxPoint φ (op V) u r' hrt⟩) ≫
        (liftedQuotientStackProjection G').toFunctor.map
          ((quotientStackOfInvariantUnit (auxGroupoid φ) (auxToTargetObjects φ)
              (auxToTargetObjects_invariant φ)).hom.app
              ((quotientPrestackEquivalence (auxGroupoid φ)).functor.obj
                ⟨V, auxPoint φ (op V) u r' hrt⟩) ≫ eqToHom hsndO ≫ β) := by
    refine map_three_comp (quotientStackMap φ).toFunctor _ _ _ P.iso.hom ?_
    refine Eq.trans ?_
      (comp_map_three (liftedQuotientStackProjection G').toFunctor _ _ _ _ rfl).symm
    exact square_aux _ _ _ _ _ _ _ _ _ _ _ _ _ hcell
      (commutes_inv_hom_app φ ((quotientPointwiseMap (auxHom φ)).obj
        (⟨V, auxPoint φ (op V) u r' hrt⟩ : (presheafOfGroupoids
          (evaluationGroupoidFunctor (auxGroupoid φ).toGroupoidInFunctors)).obj)))
      (quotientStackMap_commutes_naturality φ (eqToHom hfstO)).symm hstar hcmp
  obtain ⟨Φ, hΦb⟩ : ∃ Φ : (auxQuotientComparison φ).obj
      ((pointwiseToQuotientStack (auxGroupoid φ)).obj
        ⟨V, auxPoint φ (op V) u r' hrt⟩) ⟶ P,
      (functorialityTwoFibreProduct φ).map Φ = f :=
    ⟨⟨f, _, _, ha, hbv, hw⟩, rfl⟩
  refine ⟨Φ, ?_⟩
  have hlift := IsHomLift.map (functorialityTwoFibreProduct φ) Φ
  rwa [hΦb] at hlift


/- **The step of Stacks 04Y4 that produces the object of the fibre of `[U''/R''].`** Given a
point `u` of the object space over a test object `V` and a morphism `ξ` of `[U/R]` over
`f : V ⟶ P.base` from `π(u)` to the `[U/R]`-component of an object `P` of the 2-fibre product,
there is a `V`-point `r'` of `R'` with `t'(r') = f(u)` and a morphism of the 2-fibre product over
`f` from the image of the object presented by `(u, r')` to `P`. -/
private theorem exists_hom_of_presented (φ : Hom G G')
    (P : functorialityTwoFibreProductObj φ) {V : BigFppfOver C S hS} (f : V ⟶ P.base)
    (u : G.objects.obj.obj (op V))
    (ξ : (pointwiseToQuotientStack G).obj ⟨V, u⟩ ⟶ P.x)
    (hξ : (quotientStack G).p.IsHomLift f ξ) :
    ∃ (r' : G'.arrows.obj.obj (op V))
      (hrt : G'.target.hom.app (op V) r' = φ.toGroupoidHom.mapObjects.app (op V) u)
      (Φ : (auxQuotientComparison φ).obj
        ((pointwiseToQuotientStack (auxGroupoid φ)).obj
          ⟨V, auxPoint φ (op V) u r' hrt⟩) ⟶ P),
      (functorialityTwoFibreProduct φ).IsHomLift f Φ := by
  -- the cartesian lift of `f` at the `𝒮_{U'}`-component of `P`
  have hgpdY : (liftedFibredCategory G'.objects).p.IsFiberedInGroupoids :=
    isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS G'.objects.obj).property
  obtain ⟨y₀, β, hβ⟩ := hgpdY.exists_lift f P.y P.hy
  obtain ⟨Vc, dpt⟩ := y₀
  obtain ⟨v'⟩ := dpt
  have hVc : V = Vc :=
    (domain_eq_of_isHomLift (liftedFibredCategory G'.objects).p f β hβ).symm
  subst hVc
  -- the two legs over `f` into `π'(P.y)` in the quotient stack `[U'/R']`
  have hmapξ : (quotientStack G').p.IsHomLift f ((quotientStackMap φ).map ξ) :=
    Functor.isHomLift_map_of_comp_eq_general (quotientStackMap φ).w f ξ hξ
  have hD : (quotientStack G').p.IsHomLift f
      ((quotientStackMap_commutes φ).hom.toNatTrans.app ⟨V, u⟩ ≫
        (quotientStackMap φ).map ξ ≫ P.iso.hom) :=
    isHomLift_id_comp (quotientStack G').p f _ _
      ((quotientStackMap_commutes φ).hom.isHomLift' ⟨V, u⟩)
      (isHomLift_comp_id (quotientStack G').p f ((quotientStackMap φ).map ξ) P.iso.hom
        hmapξ P.vertical)
  have hβ' : (quotientStack G').p.IsHomLift f ((liftedQuotientStackProjection G').map β) :=
    Functor.isHomLift_map_of_comp_eq_general (liftedQuotientStackProjection G').w f β hβ
  have hd := domain_eq_of_isHomLift (quotientStack G').p f _ hD
  have hd' := domain_eq_of_isHomLift (quotientStack G').p f _ hβ'
  have hcart := isCartesian_of_isHomLift (quotientStack G').p
    (isFiberedInGroupoids_quotientStack G') f _ hD
  have hcart' := isCartesian_of_isHomLift (quotientStack G').p
    (isFiberedInGroupoids_quotientStack G') f _ hβ'
  -- Stacks 044X (2): the comparison of the two cartesian lifts is induced by an arrow of `R'`
  obtain ⟨arr', hstar⟩ : ∃ arr' : (show G'.toGroupoidInFunctors.Evaluation (op V) from
        φ.toGroupoidHom.mapObjects.app (op V) u) ⟶ v',
      (pointwiseToQuotientStack G').map ((CoGrothendieck.ι
            (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor' V).map arr') ≫
          (liftedQuotientStackProjection G').map β =
        (quotientStackMap_commutes φ).hom.toNatTrans.app ⟨V, u⟩ ≫
          (quotientStackMap φ).map ξ ≫ P.iso.hom := by
    let ψ := Functor.fiberIsoOfCartesian (p := (quotientStack G').p) (z := ⟨_, hd⟩)
      (z' := ⟨_, hd'⟩) f ((quotientStackMap_commutes φ).hom.toNatTrans.app ⟨V, u⟩ ≫
        (quotientStackMap φ).map ξ ≫ P.iso.hom) ((liftedQuotientStackProjection G').map β)
      hcart hcart'
    obtain ⟨arr', harr'⟩ := exists_evaluationArrow G' V _ v'
      (Functor.Fiber.fiberInclusion.map ψ.hom) ψ.hom.2
    refine ⟨arr', (eq_whisker harr' ((liftedQuotientStackProjection G').map β)).trans ?_⟩
    exact Functor.fiberIsoOfCartesian_hom_fac (p := (quotientStack G').p)
      (z := ⟨_, hd⟩) (z' := ⟨_, hd'⟩) f _ _ hcart hcart'
  -- the inverse arrow, and the `V`-point of `R'` it names
  obtain ⟨r', hr'⟩ : ∃ r', (G'.toGroupoidInFunctors.evaluationArrowEquiv (op V) v' _
      (Groupoid.inv arr')).1 = r' := ⟨_, rfl⟩
  obtain ⟨hrs, hrt⟩ := hr' ▸ (G'.toGroupoidInFunctors.evaluationArrowEquiv (op V) v' _
    (Groupoid.inv arr')).2
  obtain ⟨Φ, hΦ⟩ := exists_hom_of_point φ P f u v' r' hrs hrt ξ hξ β hβ arr' hr' hstar
  exact ⟨r', hrt, Φ, hΦ⟩

end Assembly

/-! ### Local essential surjectivity on fibres -/

/-- **The comparison 1-morphism of Section 78.21 is locally essentially surjective on fibres.**

For every object `P` of the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}` over a test object `T`
there is a covering sieve of `T` such that along each member `f : V ⟶ T` the base change of `P`
is isomorphic, in the fibre over `V`, to the image under the comparison 1-morphism of an object
of `[U''/R'']`. The sieve is the one Stacks 044X (1) supplies for the `[U/R]`-component of `P`,
and the object is the one presented by the `V`-point `(u, r')` of
`U'' = U ×_{f, U', t'} R'` built from the local presentation `π(u)` of that component and from
the arrow of the evaluated groupoid `G'(V)` comparing the two cartesian lifts of `f`.

Together with full faithfulness this is everything
`AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare_of` asks for. -/
theorem locallyEssSurjOnFibers_auxQuotientComparison (φ : Hom G G') :
    Functor.LocallyEssSurjOnFibers (isFibered_functorialityTwoFibreProduct φ)
      (isFibredOneMorphism_auxQuotientComparison φ).comp_eq
      (BigFppfOver.topology C S hS) := by
  intro T x
  obtain ⟨P, hPT⟩ := x
  subst hPT
  obtain ⟨R₀, hR₀, hess⟩ := essImage_toQuotientStack G _ ⟨P.x, P.hx⟩
  refine ⟨R₀, hR₀, ?_⟩
  intro V f hf
  obtain ⟨w, ⟨e⟩⟩ := hess hf
  obtain ⟨w₀, hw₀⟩ := w
  obtain ⟨Vb, upt⟩ := w₀
  have hVb : V = Vb := hw₀.symm
  subst hVb
  obtain ⟨r', hrt, Φ, hΦ⟩ := exists_hom_of_presented φ P f upt
    (Functor.Fiber.fiberInclusion.map e.hom ≫ Functor.IsPreFibered.pullbackMap P.hx f)
    (isHomLift_id_comp (quotientStack G).p f _ _ e.hom.2
      (isHomLift_pullbackMap (quotientStack G).p P.hx f))
  have hfib : (functorialityTwoFibreProduct φ).IsFibered :=
    isFibered_functorialityTwoFibreProduct φ
  have hV : (quotientStack (auxGroupoid φ)).p.obj
      ((pointwiseToQuotientStack (auxGroupoid φ)).obj
        ⟨V, auxPoint φ (op V) upt r' hrt⟩) = V := rfl
  exact ⟨⟨(pointwiseToQuotientStack (auxGroupoid φ)).obj
      ⟨V, auxPoint φ (op V) upt r' hrt⟩, hV⟩,
    nonempty_iso_pullbackFiber (quotientStack (auxGroupoid φ)).p
      (functorialityTwoFibreProduct φ) (auxQuotientComparison φ)
      (isFibredOneMorphism_auxQuotientComparison φ).comp_eq ⟨P, rfl⟩ f
      ⟨(pointwiseToQuotientStack (auxGroupoid φ)).obj
        ⟨V, auxPoint φ (op V) upt r' hrt⟩, hV⟩ Φ
      (isCartesian_of_isHomLift (functorialityTwoFibreProduct φ)
        (isFiberedInGroupoids_functorialityTwoFibreProduct φ) f Φ hΦ)⟩

end AlgebraicGeometry.Stack

end
