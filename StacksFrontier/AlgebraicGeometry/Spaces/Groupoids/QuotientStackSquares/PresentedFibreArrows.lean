module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FibreFullFaithfulness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparison
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# Arrows of the presentation inside a fibre of a quotient stack

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `[U/R]` be its quotient stack and let
`π : 𝒮_U ⟶ [U/R]` be the projection of Stacks 044R. Stacks 044X (2) says that the functor induced
on the fibre over a test object `T` by the stackification map out of the *presentation*
`AlgebraicGeometry.Stack.quotientPrestack` is fully faithful. This file transports that statement
to the **pointwise groupoid fibration** `𝒮_{G}` of Stacks 044Q — the un-universe-raised
presentation, whose objects over `T` are the `T`-points of `U` and whose vertical arrows over `T`
are the `T`-points of `R` — which is the form in which the two halves of Stacks 04ZN consume it.

The file also records the two pieces of bookkeeping that a morphism of the 2-fibre product
`[U/R] ×_{[U'/R']} 𝒮_{U'}` has to be pushed through before Stacks 044X applies to it: the filler
of the square of Stacks 04ZN *is* a component of the 2-isomorphism of Stacks 046Q, with no
transport, and the commuting square of a morphism of the 2-fibre product is therefore equivalent
to an equation between two morphisms of the pointwise presentation of `[U'/R']`.

## Main results

* `AlgebraicGeometry.Stack.full_and_faithful_fiberFunctor_pointwiseToQuotientStack`:
  **Stacks 044X** (2) for the pointwise groupoid fibration — the functor it induces on the fibre
  over a test object is full and faithful.
* `AlgebraicGeometry.Stack.pointwiseToQuotientStack_map_inj`: the faithful half, spelled out: a
  vertical morphism of the pointwise fibration is determined by its image in the quotient stack.
* `AlgebraicGeometry.Stack.exists_evaluationArrow`: the full half, spelled out: a vertical
  morphism of `[U/R]` between two presented objects over `T` is the image of an arrow of the
  evaluated groupoid `G(T)`, i.e. of a `T`-point of the arrow space.
* `AlgebraicGeometry.Stack.functorialityComparison_obj_iso_hom`: the filler of the square of
  Stacks 04ZN, read at a point of the object space, is the component of the 2-isomorphism of
  Stacks 046Q at the corresponding point of the pointwise presentation. The `eqToHom` that
  `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted` carries is an identity.
* `AlgebraicGeometry.Stack.squarePointwise`: **the commuting square of a morphism of the 2-fibre
  product, transported to the presentation.** If the `[U/R]`-component of a morphism
  `c(w₁) ⟶ c(w₂)` of the 2-fibre product is the image of a morphism `ψ` of the pointwise
  presentation of `[U/R]`, then the images in `[U'/R']` of `[φ](ψ)` and of the
  `𝒮_{U'}`-component agree. This is what turns the square into a statement about `T`-points of
  `R'`, which is where the cartesian source square of Stacks 04ZN enters.

## Implementation notes

The transport of Stacks 044X (2) is by factoring: the stackification map out of the pointwise
fibration is the universe-raising equivalence
`AlgebraicGeometry.Stack.quotientPrestackEquivalence` followed by
`AlgebraicGeometry.Stack.toQuotientStack`, both strictly over the site, so the induced functor on
each fibre factors as the corresponding two, the first full and faithful because an equivalence is
(Stacks 003Z (1)) and the second by Stacks 044X (2). Both factorisations hold by `rfl`:
`CategoryTheory.Functor.fiberFunctorOfCompEq` and
`CategoryTheory.Functor.Fiber.mapOfComp` are the same functor, and both are functorial in the
1-morphism on the nose.

The passage from a vertical morphism of the pointwise fibration to an arrow of the evaluated
groupoid is Mathlib's: `CategoryTheory.Functor.Fiber.inducedFunctor` of
`CategoryTheory.Pseudofunctor.CoGrothendieck.comp_const` is an equivalence, so it is in particular
full, which is exactly the passage wanted.

For `AlgebraicGeometry.Stack.squarePointwise` the 2-isomorphism of Stacks 046Q is cancelled on
both sides. The composition is written out in term mode: `rw` does not fire on these goals,
because the two `≫`s of a nested composite in the quotient stack reach their `Category` instance
by different paths, and `rw` matches syntactically.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### Stacks 044X (2) for the pointwise groupoid fibration -/

/-- **Stacks 044X** (2) for the pointwise groupoid fibration of Stacks 044Q: the functor it
induces on the fibre of `[U/R]` over a test object is full and faithful.

The stackification map out of the pointwise fibration is the universe-raising equivalence followed
by the stackification map out of the presentation, so the induced functor on the fibre factors
likewise; the first factor is full and faithful by Stacks 003Z (1) because an equivalence is, and
the second by `AlgebraicGeometry.Stack.fullyFaithful_fiberFunctor_toQuotientStack`. -/
theorem full_and_faithful_fiberFunctor_pointwiseToQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS) :
    (Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq T).Full ∧
      (Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq T).Faithful := by
  obtain ⟨hff⟩ := fullyFaithful_fiberFunctor_toQuotientStack G T
  have h2f : (Functor.fiberFunctorOfCompEq
    (isFibredOneMorphism_toQuotientStack G).comp_eq T).Full := hff.full
  have h2ff : (Functor.fiberFunctorOfCompEq
    (isFibredOneMorphism_toQuotientStack G).comp_eq T).Faithful := hff.faithful
  have hff1 := (quotientPrestackEquivalence G).fullyFaithfulFunctor
  have := hff1.full
  have := hff1.faithful
  obtain ⟨h1f₀, h1ff₀⟩ := (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p
    (quotientPrestack G).p
    (isFiberedInGroupoids_presheafOfGroupoids _)
    (isFiberedInGroupoids_quotientPrestack G)
    (quotientPrestackEquivalence G).functor (quotientPrestackEquivalence_comp G)).mp
    ⟨inferInstance, inferInstance⟩ T
  have h1f : (Functor.fiberFunctorOfCompEq (quotientPrestackEquivalence_comp G) T).Full := h1f₀
  have h1ff : (Functor.fiberFunctorOfCompEq (quotientPrestackEquivalence_comp G) T).Faithful :=
    h1ff₀
  have heq : Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq T =
      Functor.fiberFunctorOfCompEq (quotientPrestackEquivalence_comp G) T ⋙
        Functor.fiberFunctorOfCompEq (isFibredOneMorphism_toQuotientStack G).comp_eq T := rfl
  rw [heq]
  exact ⟨Functor.Full.comp _ _, Functor.Faithful.comp _ _⟩

/-- **A vertical morphism of the pointwise groupoid fibration is determined by its image in the
quotient stack**: the faithful half of Stacks 044X (2), in the shape the proof of Stacks 04ZN uses
it — a morphism of `R'`-points is pinned down by the transition isomorphism it induces. -/
theorem pointwiseToQuotientStack_map_inj
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS)
    {z₁ z₂ : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj}
    (ψ₁ ψ₂ : z₁ ⟶ z₂)
    (h₁ : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      (𝟙 T) ψ₁)
    (h₂ : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
      (𝟙 T) ψ₂)
    (h : (pointwiseToQuotientStack G).map ψ₁ = (pointwiseToQuotientStack G).map ψ₂) :
    ψ₁ = ψ₂ := by
  have hfaith := (full_and_faithful_fiberFunctor_pointwiseToQuotientStack G T).2
  have := h₁
  have := h₂
  let P := presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)
  let FF := Functor.fiberFunctorOfCompEq
    (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq T
  let M₁ : Functor.Fiber.mk (IsHomLift.domain_eq P.p (𝟙 T) ψ₁) ⟶
      Functor.Fiber.mk (IsHomLift.codomain_eq P.p (𝟙 T) ψ₁) :=
    Functor.Fiber.homMk P.p T ψ₁
  let M₂ : Functor.Fiber.mk (IsHomLift.domain_eq P.p (𝟙 T) ψ₁) ⟶
      Functor.Fiber.mk (IsHomLift.codomain_eq P.p (𝟙 T) ψ₁) :=
    Functor.Fiber.homMk P.p T ψ₂
  have hM : M₁ = M₂ :=
    Functor.Faithful.map_injective (F := FF) (Functor.Fiber.hom_ext h)
  exact congrArg Functor.Fiber.fiberInclusion.map hM

/-- **A vertical morphism of `[U/R]` between two presented objects comes from an arrow of the
evaluated groupoid**: the full half of Stacks 044X (2), in the shape the proof of Stacks 04ZN uses
it — a transition isomorphism between two `T`-points of `U` is induced by a `T`-point of `R`.

The arrow is produced through the inclusion of the fibre of the pointwise groupoid fibration,
which is an equivalence onto the fibre over the test object by Mathlib's
`CategoryTheory.Pseudofunctor.CoGrothendieck.comp_const`. -/
theorem exists_evaluationArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS)
    (u₁ u₂ : G.objects.obj.obj (op T))
    (m : (pointwiseToQuotientStack G).obj ⟨T, u₁⟩ ⟶ (pointwiseToQuotientStack G).obj ⟨T, u₂⟩)
    (hm : (quotientStack G).p.IsHomLift (𝟙 T) m) :
    ∃ arr : (show G.toGroupoidInFunctors.Evaluation (op T) from u₁) ⟶ u₂,
      (pointwiseToQuotientStack G).map
        ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' T).map arr) = m := by
  have hc := CoGrothendieck.comp_const
    (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor' T
  have hK : (Functor.Fiber.inducedFunctor hc).Full := inferInstance
  have hKP : (Functor.Fiber.inducedFunctor
      (p := (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) hc).Full :=
    hK
  have hFF := (full_and_faithful_fiberFunctor_pointwiseToQuotientStack G T).1
  have hcomp : (Functor.Fiber.inducedFunctor
      (p := (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) hc ⋙
      Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq T).Full :=
    Functor.Full.comp _ _
  have := hm
  obtain ⟨arr, harr⟩ := hcomp.map_surjective
    (Functor.Fiber.homMk (quotientStack G).p T m)
  exact ⟨arr, congrArg Functor.Fiber.fiberInclusion.map harr⟩

/-! ### The filler of the square of Stacks 04ZN on the presentation -/

/-- The 2-isomorphism of Stacks 046Q restricted along the inclusion of the object points has the
components of the 2-isomorphism of Stacks 046Q itself. -/
theorem quotientStackProjectionCell_hom_app_eq (φ : Hom G G')
    (x : (fibredCategory C S hS G.objects.obj).val.obj) :
    (quotientStackProjectionCell φ).hom.app x =
      (quotientStackMap_commutes φ).inv.toNatTrans.app
        ((pointwiseObjectInclusion G).obj x) := rfl

/-- **The `eqToHom` that `AlgebraicGeometry.Stack.functorialityProjectionCellUnlifted` carries is
an identity**: the two spellings of the target of the 2-isomorphism of Stacks 046Q restricted
along the inclusion of the object points agree on objects by definition. Hence the filler of the
square of Stacks 04ZN has the components of the 2-isomorphism of Stacks 046Q. -/
theorem functorialityProjectionCellUnlifted_hom_app_eq (φ : Hom G G')
    (x : (fibredCategory C S hS G.objects.obj).val.obj) :
    (functorialityProjectionCellUnlifted φ).hom.app x =
      (quotientStackMap_commutes φ).inv.toNatTrans.app
        ((pointwiseObjectInclusion G).obj x) :=
  (functorialityProjectionCellUnlifted_hom_app φ x).trans
    (((congrArg (fun k => (quotientStackProjectionCell φ).hom.app x ≫ k)
      (eqToHom_refl _ (Functor.congr_obj
        (pointwiseObjectInclusion_comp_quotientPointwiseMap_comp φ) x))).trans
      (Category.comp_id _)).trans (quotientStackProjectionCell_hom_app_eq φ x))

/-- **The comparison isomorphism of the object of the 2-fibre product attached to a point of the
object space is a component of the 2-isomorphism of Stacks 046Q.** -/
theorem functorialityComparison_obj_iso_hom (φ : Hom G G')
    (w : (liftedFibredCategory G.objects).obj) :
    ((functorialityComparison φ).obj w).iso.hom =
      (quotientStackMap_commutes φ).inv.toNatTrans.app
        ((pointwiseObjectInclusion G).obj ((liftedFibredCategoryDown G.objects).obj w)) :=
  (functorialityProjectionCellLifted_hom_app φ w).trans
    (functorialityProjectionCellUnlifted_hom_app_eq φ
      ((liftedFibredCategoryDown G.objects).obj w))

/-- The components of the 2-isomorphism of Stacks 046Q and of its inverse compose to the
identity. -/
theorem quotientStackMap_commutes_hom_inv_app (φ : Hom G G')
    (z : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) :
    (quotientStackMap_commutes φ).hom.toNatTrans.app z ≫
        (quotientStackMap_commutes φ).inv.toNatTrans.app z = 𝟙 _ :=
  NatTrans.congr_app
    (congrArg BasedNatTrans.toNatTrans (quotientStackMap_commutes φ).hom_inv_id) z

/-- **Stacks 046Q read on the pointwise presentations**: the naturality of the 2-isomorphism of
Stacks 046Q, in the shape where both composites are spelled out. -/
theorem quotientStackMap_commutes_naturality (φ : Hom G G')
    {z₁ z₂ : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj}
    (ψ : z₁ ⟶ z₂) :
    (pointwiseToQuotientStack G').map ((quotientPointwiseMap φ).map ψ) ≫
        (quotientStackMap_commutes φ).hom.toNatTrans.app z₂ =
      (quotientStackMap_commutes φ).hom.toNatTrans.app z₁ ≫
        (quotientStackMap φ).map ((pointwiseToQuotientStack G).map ψ) :=
  (quotientStackMap_commutes φ).hom.toNatTrans.naturality ψ

/-! ### The commuting square of a morphism of the 2-fibre product, on the presentation -/

/-- The cancellation of a 2-isomorphism on both sides of a commuting square, over variables: the
shape in which `AlgebraicGeometry.Stack.squarePointwise` consumes the naturality of Stacks 046Q
and the commuting square of the morphism of the 2-fibre product. -/
private theorem cancel_square_aux {D : Type*} [Category* D] {P1 P2 Q1 Q2 : D}
    (A L : P1 ⟶ P2) (H1 : P1 ⟶ Q1) (H2 : P2 ⟶ Q2) (I1 : Q1 ⟶ P1) (I2 : Q2 ⟶ P2) (M : Q1 ⟶ Q2)
    (hnat : A ≫ H2 = H1 ≫ M) (hw : M ≫ I2 = I1 ≫ L)
    (h1 : H1 ≫ I1 = 𝟙 P1) (h2 : H2 ≫ I2 = 𝟙 P2) : A = L := by
  rw [← Category.comp_id A, ← h2, ← Category.assoc, hnat, Category.assoc, hw,
    ← Category.assoc, h1, Category.id_comp]

/-- **The commuting square of a morphism of the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}`,
transported to the pointwise presentation of `[U'/R']`.**

Let `Φ : c(w₁) ⟶ c(w₂)` be a morphism of the 2-fibre product between the images under the
comparison 1-morphism of two points `w₁, w₂` of the enlarged object space, and suppose the
`[U/R]`-component of `Φ` is the image of a morphism `ψ` of the pointwise presentation of `[U/R]`
between the corresponding presented points — which Stacks 044X (2) always provides when `Φ` is
vertical. Then the images in `[U'/R']` of `[φ](ψ)` and of the `𝒮_{U'}`-component of `Φ` agree.

Both sides are images under the stackification map of the pointwise presentation of
`(U', R', s', t', c')`, so with `AlgebraicGeometry.Stack.pointwiseToQuotientStack_map_inj` this
turns the square of the 2-fibre product into an equation between `T`-points of `R'` — which is
the form in which the cartesian source square that Stacks 04ZN assumes can be applied. -/
theorem squarePointwise (φ : Hom G G')
    {w₁ w₂ : (liftedFibredCategory G.objects).obj}
    (Φ : (functorialityComparison φ).obj w₁ ⟶ (functorialityComparison φ).obj w₂)
    (ψ : (pointwiseObjectInclusion G).obj ((liftedFibredCategoryDown G.objects).obj w₁) ⟶
      (pointwiseObjectInclusion G).obj ((liftedFibredCategoryDown G.objects).obj w₂))
    (hψ : (pointwiseToQuotientStack G).map ψ = Φ.a) :
    (pointwiseToQuotientStack G').map ((quotientPointwiseMap φ).map ψ) =
      (liftedQuotientStackProjection G').map Φ.b := by
  have hw : (quotientStackMap φ).map ((pointwiseToQuotientStack G).map ψ) ≫
      (quotientStackMap_commutes φ).inv.toNatTrans.app
        ((pointwiseObjectInclusion G).obj ((liftedFibredCategoryDown G.objects).obj w₂)) =
      (quotientStackMap_commutes φ).inv.toNatTrans.app
        ((pointwiseObjectInclusion G).obj ((liftedFibredCategoryDown G.objects).obj w₁)) ≫
        (liftedQuotientStackProjection G').map Φ.b := by
    rw [hψ]
    have h := Φ.w
    rw [functorialityComparison_obj_iso_hom φ w₁,
      functorialityComparison_obj_iso_hom φ w₂] at h
    exact h
  exact cancel_square_aux _ _ _ _ _ _ _
    (quotientStackMap_commutes_naturality φ ψ) hw
    (quotientStackMap_commutes_hom_inv_app φ _) (quotientStackMap_commutes_hom_inv_app φ _)

end AlgebraicGeometry.Stack

end
