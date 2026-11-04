module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackAdjunction
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# Change of base of an algebraic stack

Let `S ⟶ S'` be a morphism of a big fppf site and let `𝒳'` be an algebraic stack over `S'`. The
*change of base* of `𝒳'` is the algebraic stack over `S` whose total category is the strict
pullback of the structure functor of `𝒳'` along the relocalization functor `Over.map g` of the
big fppf site of `S` along `g`, with the first projection as structure functor. Its objects are a
pair of an object `U` over `S` and an object of `𝒳'` lying over the image of `U` in the site of
`S'`, on the nose.

## Main definitions

* `AlgebraicGeometry.Stack.changeOfBaseCategory`: the category over `S` underlying the change of
  base, the strict pullback of the structure functor of `𝒳'` along `Over.map g`.
* `AlgebraicGeometry.Stack.changeOfBase`: the change of base of `𝒳'` as an object of the
  2-category of algebraic stacks over `S`.
* `AlgebraicGeometry.Stack.ChangeOfBaseTwoFibreProductWitness`: the data of the canonical
  two-fibre-product presentation of the change of base.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_changeOfBaseCategory`: the strict pullback of an
  algebraic stack along a morphism of base schemes is an algebraic stack.
* `AlgebraicGeometry.Stack.changeOfBase_twoFibreProductWitness`: the canonical two-fibre-product
  characterization. Under the correspondence of Stacks 04X5 the change of base is the two-fibre
  product of `𝒳'` and the stack represented by `S/S'` over the stack represented by the final
  object `S'/S'`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

section Pullback

variable {C : Type (u + 1)} [Category.{u} C] {s s' : C}

/-- The strict pullback of `X` along `Over.map g`, read as a category over `s'` rather than over
`s`: this is Construction A of Stacks 04X5 applied to the change of base. -/
private abbrev changeOfBaseOver (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s')) :
    BasedCategory.{u, u + 1} (Over s') where
  obj := StrictPullback (Over.map g) X.p
  p := StrictPullback.structureFunctor (Over.map g) X.p ⋙ Over.map g

/-- The 2-fibre product of `X` and the category represented by `s/s'` over the category
represented by the final object `s'/s'`, as a category over `s'`. -/
private abbrev changeOfBaseProduct (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s')) :
    BasedCategory.{u, u + 1} (Over s') where
  obj := TwoFibreProductOver X.p (Over.forget (Over.mk g))
    (Over.forget (Over.mk (𝟙 s')))
    (X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))
    (Over.forget (Over.mk g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))
  p := TwoFibreProductOver.structureFunctor X.p (Over.forget (Over.mk g))
    (Over.forget (Over.mk (𝟙 s')))
    (X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))
    (Over.forget (Over.mk g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))

/-- The projection of the strict pullback to `X`, as a 1-morphism over `s'`. -/
private abbrev changeOfBaseProjection (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s')) :
    changeOfBaseOver g X ⥤ᵇ X :=
  ⟨StrictPullback.pr (Over.map g) X.p, StrictPullback.pr_comp_eq _ _⟩

/-- The second projection of the strict pullback, as a 1-morphism over `s'` to the category
represented by `s/s'`: the structure functor of the strict pullback read through the inverse of
the iterated-slice equivalence at `s/s'`. -/
private abbrev changeOfBaseSliceProjection (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s')) :
    changeOfBaseOver g X ⥤ᵇ BasedCategory.ofFunctor (Over.forget (Over.mk g)) :=
  ⟨StrictPullback.structureFunctor (Over.map g) X.p ⋙ Over.iteratedSliceBackward (Over.mk g),
    rfl⟩

/-- The 1-morphism to the category represented by the final object `s'/s'`: the structure functor
read through the inverse of the iterated-slice equivalence. -/
private abbrev toTerminalSliceOver (X : BasedCategory.{u, u + 1} (Over s')) :
    X ⥤ᵇ BasedCategory.ofFunctor (Over.forget (Over.mk (𝟙 s'))) :=
  ⟨X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')), by
    change X.p ⋙ Over.map (𝟙 s') = X.p
    rw [Over.mapId_eq, Functor.comp_id]⟩

/-- The components of the `eqToIso` of an equality of 1-morphisms over `E` are vertical: the
equality identifies two functors with the same composite to `E`, so each component lies over an
identity. -/
private lemma isHomLift_eqToIso_app {D E W : Type*} [Category D] [Category E] [Category W]
    (q : D ⥤ E) {F G : W ⥤ D} (e : F = G) {pW : W ⥤ E} (hF : F ⋙ q = pW) (x : W) :
    q.IsHomLift (𝟙 (pW.obj x)) ((eqToIso e).hom.app x) := by
  subst e
  subst hF
  show q.IsHomLift (𝟙 (q.obj (F.obj x))) (𝟙 (F.obj x))
  infer_instance

/-- The two legs of the strict-pullback cone agree after mapping to the final slice object: the
strict pullback is a pullback on the nose, so the comparison is an equality of functors rather
than merely an isomorphism. -/
private lemma changeOfBaseCone_eq (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s')) :
    StrictPullback.pr (Over.map g) X.p ⋙
        (X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s'))) =
      (StrictPullback.structureFunctor (Over.map g) X.p ⋙
          Over.iteratedSliceBackward (Over.mk g)) ⋙
        (Over.forget (Over.mk g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s'))) := by
  rw [← Functor.assoc, StrictPullback.pr_comp_eq]
  rfl

/-- The first leg of the strict-pullback cone is a 1-morphism over `s'`. -/
private lemma changeOfBaseCone_w (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s')) :
    (StrictPullback.pr (Over.map g) X.p ⋙
          (X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))) ⋙
        Over.forget (Over.mk (𝟙 s')) =
      StrictPullback.structureFunctor (Over.map g) X.p ⋙ Over.map g :=
  ((changeOfBaseProjection g X).comp (toTerminalSliceOver X)).w

/-- The components of the comparison isomorphism of the strict-pullback cone are vertical. -/
private lemma changeOfBaseCone_isHomLift (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s'))
    (x : (changeOfBaseOver g X).obj) :
    (Over.forget (Over.mk (𝟙 s'))).IsHomLift
      (𝟙 ((StrictPullback.structureFunctor (Over.map g) X.p ⋙ Over.map g).obj x))
      ((eqToIso (changeOfBaseCone_eq g X)).hom.app x) :=
  isHomLift_eqToIso_app _ (changeOfBaseCone_eq g X) (changeOfBaseCone_w g X) x

/-- The mediating 1-morphism from the strict pullback to the 2-fibre product, induced by the
strict-pullback cone. -/
private abbrev changeOfBaseOverToProduct (g : s ⟶ s')
    (X : BasedCategory.{u, u + 1} (Over s')) :
    changeOfBaseOver g X ⥤ᵇ changeOfBaseProduct g X :=
  ⟨TwoFibreProductOver.lift X.p (Over.forget (Over.mk g)) (Over.forget (Over.mk (𝟙 s')))
      (X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))
      (Over.forget (Over.mk g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))
      (StrictPullback.structureFunctor (Over.map g) X.p ⋙ Over.map g)
      (StrictPullback.pr (Over.map g) X.p)
      (StrictPullback.structureFunctor (Over.map g) X.p ⋙
        Over.iteratedSliceBackward (Over.mk g))
      (StrictPullback.pr_comp_eq _ _) rfl (eqToIso (changeOfBaseCone_eq g X))
      (changeOfBaseCone_isHomLift g X),
    TwoFibreProductOver.lift_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ _⟩

/-- The first projection of the 2-fibre product factors through the strict pullback: its
composite with the structure functor of `X` is the second projection followed by the
relocalization functor of `g`. -/
private lemma changeOfBaseProduct_leg_eq (g : s ⟶ s')
    (X : BasedCategory.{u, u + 1} (Over s')) :
    TwoFibreProductOver.fst X.p (Over.forget (Over.mk g)) (Over.forget (Over.mk (𝟙 s')))
          (X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))
          (Over.forget (Over.mk g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s'))) ⋙ X.p =
      (TwoFibreProductOver.snd X.p (Over.forget (Over.mk g)) (Over.forget (Over.mk (𝟙 s')))
            (X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))
            (Over.forget (Over.mk g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s'))) ⋙
          Over.iteratedSliceForward (Over.mk g)) ⋙ Over.map g := by
  rw [Over.comp_iteratedSliceForward_comp_map, TwoFibreProductOver.fst_comp_eq,
    TwoFibreProductOver.snd_comp_eq]

/-- The lift of the 2-fibre product to the strict pullback is a 1-morphism over `s'`. -/
private lemma productToChangeOfBaseOver_w (g : s ⟶ s')
    (X : BasedCategory.{u, u + 1} (Over s')) :
    (StrictPullback.liftFib _ _ (changeOfBaseProduct_leg_eq g X) ⋙
          StrictPullback.structureFunctor (Over.map g) X.p) ⋙ Over.map g =
      TwoFibreProductOver.structureFunctor X.p (Over.forget (Over.mk g))
        (Over.forget (Over.mk (𝟙 s')))
        (X.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s')))
        (Over.forget (Over.mk g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 s'))) := by
  rw [StrictPullback.liftFib_comp_structureFunctor,
    Over.comp_iteratedSliceForward_comp_map]
  exact TwoFibreProductOver.snd_comp_eq

/-- The mediating 1-morphism from the 2-fibre product to the strict pullback: the two projections
of the 2-fibre product are a cone for the strict pullback. -/
private abbrev productToChangeOfBaseOver (g : s ⟶ s')
    (X : BasedCategory.{u, u + 1} (Over s')) :
    changeOfBaseProduct g X ⥤ᵇ changeOfBaseOver g X :=
  ⟨StrictPullback.liftFib _ _ (changeOfBaseProduct_leg_eq g X),
    productToChangeOfBaseOver_w g X⟩

/-- The strict pullback is a retract of the 2-fibre product on the nose: an object of the strict
pullback is recovered from the two components and the comparison isomorphism it induces. -/
private lemma changeOfBaseOverToProduct_comp (g : s ⟶ s')
    (X : BasedCategory.{u, u + 1} (Over s')) :
    (changeOfBaseOverToProduct g X).comp (productToChangeOfBaseOver g X) =
      BasedFunctor.id _ :=
  BasedCategory.BasedFunctor.ext' rfl

/-- Two objects of this 2-fibre product with the same two components are equal: the comparison
isomorphism is vertical and `CategoryTheory.Over.forget` is faithful, so it is determined by the
two components it compares. -/
private lemma changeOfBaseProduct_obj_ext {g : s ⟶ s'}
    {X : BasedCategory.{u, u + 1} (Over s')}
    {P Q : (changeOfBaseProduct g X).obj} (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  rcases P with ⟨b, x, y, hx₁, hy₁, i, hi⟩
  rcases Q with ⟨b', x', y', hx₂, hy₂, i', hi'⟩
  dsimp at hx hy
  subst x' y'
  have hb : b = b' := hx₁.symm.trans hx₂
  cases hb
  have he : i = i' := by
    apply Iso.ext
    apply (Over.forget (Over.mk (𝟙 s'))).map_injective
    have := hi
    have := hi'
    rw [IsHomLift.fac' _ (𝟙 b) i.hom, IsHomLift.fac' _ (𝟙 b) i'.hom]
  cases he
  rfl

/-- The `X`-component of the round trip through the strict pullback is the identity, on the nose.
-/
private lemma roundTrip_obj_x (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s'))
    (q : (changeOfBaseProduct g X).obj) :
    (((productToChangeOfBaseOver g X).comp (changeOfBaseOverToProduct g X)).obj q).x =
      ((BasedFunctor.id (changeOfBaseProduct g X)).obj q).x :=
  rfl

/-- The slice component of the round trip through the strict pullback is the identity, by the
strictness of the iterated-slice equivalence. -/
private lemma roundTrip_obj_y (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s'))
    (q : (changeOfBaseProduct g X).obj) :
    (((productToChangeOfBaseOver g X).comp (changeOfBaseOverToProduct g X)).obj q).y =
      ((BasedFunctor.id (changeOfBaseProduct g X)).obj q).y :=
  Functor.congr_obj
    (Over.iteratedSliceForward_comp_iteratedSliceBackward (Over.mk g)) q.y

/-- The round trip through the strict pullback is the identity on objects. -/
private lemma roundTrip_obj (g : s ⟶ s') (X : BasedCategory.{u, u + 1} (Over s'))
    (q : (changeOfBaseProduct g X).obj) :
    ((productToChangeOfBaseOver g X).comp (changeOfBaseOverToProduct g X)).obj q =
      (BasedFunctor.id (changeOfBaseProduct g X)).obj q :=
  changeOfBaseProduct_obj_ext (roundTrip_obj_x g X q) (roundTrip_obj_y g X q)

/-- The round trip through the strict pullback is the identity. -/
private lemma productToChangeOfBaseOver_comp (g : s ⟶ s')
    (X : BasedCategory.{u, u + 1} (Over s')) :
    (productToChangeOfBaseOver g X).comp (changeOfBaseOverToProduct g X) =
      BasedFunctor.id _ := by
  apply BasedCategory.BasedFunctor.ext'
  refine CategoryTheory.Functor.ext (roundTrip_obj g X) (fun a b f => ?_)
  refine TwoFibreProductOver.Hom.ext' ?_ ?_
  · rw [TwoFibreProductOver.comp_a, TwoFibreProductOver.comp_a,
      TwoFibreProductOver.eqToHom_a, TwoFibreProductOver.eqToHom_a]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  · rw [TwoFibreProductOver.comp_b, TwoFibreProductOver.comp_b,
      TwoFibreProductOver.eqToHom_b, TwoFibreProductOver.eqToHom_b]
    exact Functor.congr_hom
      (Over.iteratedSliceForward_comp_iteratedSliceBackward (Over.mk g)) f.b

/-- The strict pullback and the 2-fibre product are equivalent as categories over `s'`, and
strictly so: both unit and counit are `eqToIso` of an equality of 1-morphisms. -/
private def changeOfBaseOverProductEquivalence (g : s ⟶ s')
    (X : BasedCategory.{u, u + 1} (Over s')) :
    BasedCategory.Equivalence (changeOfBaseOver g X) (changeOfBaseProduct g X) where
  functor := changeOfBaseOverToProduct g X
  inverse := productToChangeOfBaseOver g X
  unitIso := eqToIso (changeOfBaseOverToProduct_comp g X)
  counitIso := eqToIso (productToChangeOfBaseOver_comp g X)

/-- The comparison from the strict pullback to the 2-fibre product is an equivalence of the
underlying categories. -/
private lemma isEquivalence_changeOfBaseOverToProduct (g : s ⟶ s')
    (X : BasedCategory.{u, u + 1} (Over s')) :
    (changeOfBaseOverToProduct g X).toFunctor.IsEquivalence :=
  (changeOfBaseOverProductEquivalence g X).equiv.isEquivalence_functor

end Pullback

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- The category over `S` underlying the change of base of an algebraic stack over `S'`: the
strict pullback of the structure functor of `𝒳'` along the relocalization functor of `g`. Its
objects are a pair of an object over `S` and an object of `𝒳'` lying over its image in the site
of `S'`. -/
def changeOfBaseCategory (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    BasedCategory.{u, u + 1} (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    (StrictPullback.structureFunctor (Over.map g) 𝒳'.val.val.p)

/-- Construction A of the change of base is the strict pullback read over `S'`. -/
private lemma changeBase_changeOfBaseCategory (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    changeBase B S S' hS hS' g (changeOfBaseCategory B S S' hS hS' g 𝒳') =
      changeOfBaseOver g 𝒳'.val.val :=
  rfl

/-- The 2-fibre product of `𝒳'` and the category represented by `S/S'`, formed from their two
1-morphisms to the category represented by the final object of the site of `S'`, is
`changeOfBaseProduct`. -/
private lemma changeOfBaseProduct_eq (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor 𝒳'.val.val.p
          (schemeFibredCategory B S' hS' (Over.mk g)).val.p
          (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p
          (toTerminalSliceOver 𝒳'.val.val).toFunctor
          (toTerminalSliceOver (schemeFibredCategory B S' hS' (Over.mk g)).val).toFunctor) =
      changeOfBaseProduct g 𝒳'.val.val :=
  rfl

/-- The strict pullback of an algebraic stack along a morphism of base schemes is an algebraic
stack. -/
theorem isAlgebraicStack_changeOfBaseCategory (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    IsAlgebraicStack.{u, w} B S hS (changeOfBaseCategory B S S' hS hS' g 𝒳') := by
  refine (isAlgebraicStack_changeBase_iff B S S' hS hS' g _).mp ?_
  rw [changeBase_changeOfBaseCategory]
  refine (isAlgebraicStack_iff_of_equivalence B S' hS'
    (changeOfBaseOverProductEquivalence g 𝒳'.val.val)).mpr ?_
  rw [← changeOfBaseProduct_eq]
  exact isAlgebraicStack_twoFibreProduct B S' hS' 𝒳'.val.val
    (schemeFibredCategory B S' hS' (Over.mk g)).val
    (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val
    (toTerminalSliceOver 𝒳'.val.val)
    (toTerminalSliceOver (schemeFibredCategory B S' hS' (Over.mk g)).val)
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S' hS'
      (Over.mk (𝟙 (B.obj hS')))).choose_spec.1
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S' hS'
      (Over.mk (𝟙 (B.obj hS')))).choose_spec.2.1
    𝒳'.property
    (isAlgebraicStack_schemeFibredCategory B S' hS' (Over.mk g))

/-- The change of base of an algebraic stack `𝒳'` over `S'` along a morphism `S ⟶ S'` of the big
fppf site: the algebraic stack over `S` whose total category is the strict pullback of the
structure functor of `𝒳'` along the relocalization functor of `g`. -/
@[stacks 04X7]
def changeOfBase (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    AlgebraicStacks.{u, w} B S hS :=
  let P := changeOfBaseCategory B S S' hS hS' g 𝒳'
  let hP := isAlgebraicStack_changeOfBaseCategory B S S' hS hS' g 𝒳'
  ⟨⟨P, hP.choose⟩, hP⟩

/-- The category over `S` underlying the change of base is the strict pullback. -/
@[simp]
lemma changeOfBase_val_val (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    (changeOfBase B S S' hS hS' g 𝒳').val.val =
      changeOfBaseCategory B S S' hS hS' g 𝒳' :=
  rfl

/-! ### The canonical 2-fibre-product presentation -/

/-- The 1-morphism from an algebraic stack over `S'` to the stack represented by the final object
`S'/S'` of the big fppf site of `S'`: its structure functor, read through the inverse of the
iterated-slice equivalence at the final object. -/
private def toTerminalSchemeStack (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    𝒳' ⟶ schemeStack B S' hS' (Over.mk (𝟙 (B.obj hS'))) :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (toTerminalSliceOver 𝒳'.val.val))

/-- The canonical 2-commutative square exhibiting Construction A of the change of base as a
2-fibre product: its apex is Construction A of the change of base, its first leg the projection
of the strict pullback to `𝒳'` and its second leg the structure functor read in the localization
of the site of `S'` at `S/S'`. -/
private def changeOfBaseStackSquare (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    Bicategory.TwoCommSq (toTerminalSchemeStack B S' hS' 𝒳')
      (toTerminalSchemeStack B S' hS' (schemeStack B S' hS' (Over.mk g))) where
  pt := changeBaseAlgebraicStack B S S' hS hS' g (changeOfBase B S S' hS hS' g 𝒳')
  fst := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (changeOfBaseProjection g 𝒳'.val.val))
  snd := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (changeOfBaseSliceProjection g 𝒳'.val.val))
  iso := Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (eqToIso (changeOfBaseCone_eq g 𝒳'.val.val))
      (changeOfBaseCone_isHomLift g 𝒳'.val.val)))

/-- The canonical square of the change of base is a 2-fibre product. -/
private noncomputable def isTwoFibreProduct_changeOfBaseStackSquare
    (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    Bicategory.IsTwoFibreProduct (changeOfBaseStackSquare B S S' hS hS' g 𝒳') :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        _ _)
      (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} _ _
        (changeOfBaseStackSquare B S S' hS hS' g 𝒳').underlying)
      (isEquivalence_changeOfBaseOverToProduct g 𝒳'.val.val))

/-- The data of the canonical two-fibre-product presentation of the change of base. The two
1-morphisms to the stack represented by the final object `S'/S'` of the big fppf site of `S'` are
the structure functor of `𝒳'` and the forgetful functor of `S/S'`, read through the inverse of
the iterated-slice equivalence; the apex of the square is the image of the change of base under
the correspondence of Stacks 04X5, its second leg is that correspondence's structural 1-morphism
and its first leg is the projection of the strict pullback to `𝒳'`. -/
structure ChangeOfBaseTwoFibreProductWitness (𝒳' : AlgebraicStacks.{u, w} B S' hS') where
  /-- the 1-morphism from `𝒳'` to the stack represented by the final object `S'/S'` -/
  f : 𝒳' ⟶ schemeStack B S' hS' (Over.mk (𝟙 (B.obj hS')))
  /-- the 1-morphism from the stack represented by `S/S'` to the one represented by `S'/S'` -/
  k : schemeStack.{u, w} B S' hS' (Over.mk g) ⟶
    schemeStack B S' hS' (Over.mk (𝟙 (B.obj hS')))
  /-- `f` is the structure functor of `𝒳'`, read through the iterated-slice equivalence -/
  f_underlying : f.hom.hom.toFunctor =
    𝒳'.val.val.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))
  /-- `k` is the forgetful functor of `S/S'`, read through the iterated-slice equivalence -/
  k_underlying : k.hom.hom.toFunctor =
    Over.forget (Over.mk g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))
  /-- the 2-commutative square over the cospan `(f, k)` -/
  square : Bicategory.TwoCommSq f k
  /-- its apex is the image of the change of base under the correspondence of Stacks 04X5 -/
  pt_eq : square.pt = (algebraicStackConstructionObjEquiv B S S' hS hS' g
    (changeOfBase B S S' hS hS' g 𝒳')).1
  /-- its second leg is that correspondence's structural 1-morphism -/
  snd_eq : HEq square.snd.hom (algebraicStackConstructionObjEquiv B S S' hS hS' g
    (changeOfBase B S S' hS hS' g 𝒳')).2
  /-- its first leg is the projection of the strict pullback to `𝒳'` -/
  fst_underlying : HEq square.fst.hom.hom.toFunctor
    (StrictPullback.pr (Over.map g) 𝒳'.val.val.p)
  /-- the square is a 2-fibre product -/
  isTwoFibreProduct : Bicategory.IsTwoFibreProduct square

/-- Under the canonical 2-categorical correspondence of Stacks 04X5 between algebraic stacks over
`S` and algebraic stacks over `S'` equipped with a 1-morphism to the stack represented by `S/S'`,
the change of base of `𝒳'` is the 2-fibre product of `𝒳'` and the stack represented by `S/S'`
over the stack represented by the final object `S'/S'`.

The two 1-morphisms to the base are the structure functor of `𝒳'` and the forgetful functor of
`S/S'` read through the iterated-slice equivalence, the apex is the correspondence's image of the
change of base, the second projection is the correspondence's structural 1-morphism and the first
is the projection of the strict pullback. -/
@[stacks 04X7 "canonical two-fibre-product characterization"]
theorem changeOfBase_twoFibreProductWitness (𝒳' : AlgebraicStacks.{u, w} B S' hS') :
    Nonempty (ChangeOfBaseTwoFibreProductWitness B S S' hS hS' g 𝒳') :=
  ⟨{ f := toTerminalSchemeStack B S' hS' 𝒳'
     k := toTerminalSchemeStack B S' hS' (schemeStack B S' hS' (Over.mk g))
     f_underlying := rfl
     k_underlying := rfl
     square := changeOfBaseStackSquare B S S' hS hS' g 𝒳'
     pt_eq := rfl
     snd_eq := HEq.rfl
     fst_underlying := HEq.rfl
     isTwoFibreProduct := isTwoFibreProduct_changeOfBaseStackSquare B S S' hS hS' g 𝒳' }⟩

end AlgebraicGeometry.Stack

end
