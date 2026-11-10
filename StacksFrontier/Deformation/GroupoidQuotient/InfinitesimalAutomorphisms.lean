module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Applications.TangentModuleEquivalence
public import StacksFrontier.Deformation.Applications.TwoFibreProductSelfExact
public import StacksFrontier.Deformation.ArtinCriteria.TangentSpace
public import StacksFrontier.Deformation.CofiberedPresentation.Prorepresentable
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.GroupoidQuotient.DeformationCategory
public import StacksFrontier.Deformation.GroupoidQuotient.TangentSpace

/-!
# Infinitesimal automorphisms of the quotient of a groupoid in functors

For a smooth groupoid in deformation functors `(U, R, s, t, c)` on `𝒞_Λ`, the space of
infinitesimal automorphisms of the quotient is the kernel of the differential of the
source-and-target map: the sequence of `k`-vector spaces

`0 ⟶ Inf([U/R]) ⟶ TR ⟶ TU ⊕ TU`

is exact, the first map being the boundary map of the six-term sequence and the second the pair
of the differentials of `s` and of `t`.

The identification rests on the arrow functor being the self `2`-fibre product of the quotient
morphism, `R = U ×_{q, [U/R], q} U`: an arrow of the groupoid over `A` with source `x` and
target `y` is the same thing as an isomorphism over `A` between the images of `x` and of `y` in
the quotient. The exact sequence is then the one of Tag 06L6 part (2) for the quotient
morphism, transported along that identification.

## Main definitions

* `Deformation.quotientHomArrow`: the arrow of the groupoid representing the fibre component of
  a morphism of the quotient category.
* `Deformation.QuotientSelfProduct`, `Deformation.productArrow`: the self `2`-fibre product of
  the quotient morphism, and the arrow attached to one of its objects.
* `Deformation.quotientArrowsBasedFunctor`: the comparison `U ×_{[U/R]} U ⟶ R` over `𝒞_Λ`.
* `Deformation.quotientSelfProductTangentEquiv`: the resulting identification of tangent
  modules.
* `Deformation.quotientInfinitesimalBoundary`: the boundary map `Inf([U/R]) ⟶ TR`.

## Main results

* `Deformation.isThin_fiber_quotientSelfProduct`, `Deformation.full_fiberFunctor_quotientArrows`,
  `Deformation.essSurj_fiberFunctor_quotientArrows`: the comparison is an equivalence on every
  strict fibre.
* `Deformation.quotientInfinitesimalBoundary_exact`: **Tag 06KU, part (3)**.

## Implementation notes

The comparison is taken from the `2`-fibre product to the category of elements of the arrow
functor, not the other way round: a functor into a category of elements is given by an object of
the base together with a point, and its functoriality is then automatic, whereas a functor out of
one has to produce the comparison isomorphisms of the `2`-fibre product. Only an equivalence on
each strict fibre is needed for the tangent modules to agree
(`Deformation.tangentLinearEquivOfFiberEquivalence`), and that is proved fibrewise rather than by
exhibiting an equivalence of categories.

The two differentials are the maps on tangent modules induced by `s` and `t`, at an arbitrary
coordinate module. At the rank-one module these are the differentials of Tag 06IJ used in
part (2) of the tag.

## References

* [Stacks Project, Tag 06KU](https://stacks.math.columbia.edu/tag/06KU)
* [Stacks Project, Tag 06L6](https://stacks.math.columbia.edu/tag/06L6)
-/

@[expose] public section

namespace Deformation

/-! ### Arrows of the groupoid from morphisms of the quotient -/

section
open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The arrow of the groupoid representing the fibre component of a morphism of the quotient
category. Its source is the image of the fibre component of the domain and its target is the
fibre component of the codomain. -/
public noncomputable def quotientHomArrow (G : GroupoidInFunctors.{u, v, w} C)
    {X Y : Grothendieck (evaluationFunctor G)} (φ : X ⟶ Y) : G.arrows.obj Y.base :=
  (G.evaluationArrowEquiv Y.base (G.objects.map φ.base X.fiber) Y.fiber φ.fiber).1

/-- The source of the arrow of a morphism of the quotient category. -/
public theorem quotientHomArrow_source (G : GroupoidInFunctors.{u, v, w} C)
    {X Y : Grothendieck (evaluationFunctor G)} (φ : X ⟶ Y) :
    G.source.app Y.base (quotientHomArrow G φ) = G.objects.map φ.base X.fiber :=
  (G.evaluationArrowEquiv Y.base (G.objects.map φ.base X.fiber) Y.fiber φ.fiber).2.1

/-- The target of the arrow of a morphism of the quotient category. -/
public theorem quotientHomArrow_target (G : GroupoidInFunctors.{u, v, w} C)
    {X Y : Grothendieck (evaluationFunctor G)} (φ : X ⟶ Y) :
    G.target.app Y.base (quotientHomArrow G φ) = Y.fiber :=
  (G.evaluationArrowEquiv Y.base (G.objects.map φ.base X.fiber) Y.fiber φ.fiber).2.2

/-- Transports of both endpoints do not change the arrow represented by a morphism of an
evaluated groupoid. -/
public theorem evaluationArrowEquiv_eqToHom_comp_eqToHom
    (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    {x x' y y' : G.Evaluation T} (hx : x' = x) (hy : y = y') (a : x ⟶ y) :
    (G.evaluationArrowEquiv T x' y' (eqToHom hx ≫ a ≫ eqToHom hy)).1 =
      (G.evaluationArrowEquiv T x y a).1 := by
  cases hx
  cases hy
  simp

/-- The fibre component of the image of a morphism of the category of elements under the
quotient morphism. -/
public theorem quotientMorphism_map_fiber (G : GroupoidInFunctors.{u, v, w} C)
    {X Y : G.objects.Elements} (f : X ⟶ Y) :
    ((quotientMorphism G).map f).fiber =
      eqToHom (show ((evaluationFunctor G).map f.1).toFunctor.obj X.2 = Y.2 from f.2) := rfl

/-- Postcomposing a morphism of the quotient with the image of a morphism of the category of
elements pushes its arrow forward along the underlying morphism of the base. -/
public theorem quotientHomArrow_comp_quotientMorphism_map
    (G : GroupoidInFunctors.{u, v, w} C) {X : Grothendieck (evaluationFunctor G)}
    {P Q : G.objects.Elements} (χ : X ⟶ (quotientMorphism G).obj P) (f : P ⟶ Q) :
    quotientHomArrow G (χ ≫ (quotientMorphism G).map f) =
      G.arrows.map f.1 (quotientHomArrow G χ) := by
  have h : quotientHomArrow G (χ ≫ (quotientMorphism G).map f) =
      (G.evaluationArrowEquiv Q.1 _ _
        ((evaluationMap G f.1).map χ.fiber)).1 := by
    change (G.evaluationArrowEquiv Q.1 _ _ ((χ ≫ (quotientMorphism G).map f).fiber)).1 = _
    rw [Grothendieck.comp_fiber, quotientMorphism_map_fiber]
    exact evaluationArrowEquiv_eqToHom_comp_eqToHom G Q.1 _ f.2 _
  rw [h, evaluationMap_map_arrow]
  rfl

/-- Precomposing a morphism of the quotient with the image of a morphism of the category of
elements does not change its arrow. -/
public theorem quotientHomArrow_quotientMorphism_map_comp
    (G : GroupoidInFunctors.{u, v, w} C) {P Q : G.objects.Elements}
    {Z : Grothendieck (evaluationFunctor G)} (f : P ⟶ Q)
    (χ : (quotientMorphism G).obj Q ⟶ Z) :
    quotientHomArrow G ((quotientMorphism G).map f ≫ χ) = quotientHomArrow G χ := by
  have h : quotientHomArrow G ((quotientMorphism G).map f ≫ χ) =
      (G.evaluationArrowEquiv Z.base _ _
        (((evaluationFunctor G).map χ.base).toFunctor.map
          (eqToHom (show ((evaluationFunctor G).map f.1).toFunctor.obj P.2 = Q.2 from f.2)) ≫
            χ.fiber)).1 := by
    change (G.evaluationArrowEquiv Z.base _ _
      (((quotientMorphism G).map f ≫ χ).fiber)).1 = _
    rw [Grothendieck.comp_fiber, quotientMorphism_map_fiber]
    exact evaluationArrowEquiv_eqToHom_comp G Z.base _ _
  rw [h, eqToHom_map]
  exact evaluationArrowEquiv_eqToHom_comp G Z.base _ χ.fiber

end


/-! ### The arrows functor as the self two-fibre product of the quotient morphism -/

section
open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The self `2`-fibre product `U ×_{q, [U/R], q} U` of the quotient morphism. -/
public abbrev QuotientSelfProduct (G : GroupoidInFunctors.{u, v, w} C) : Type _ :=
  TwoFibreProductOver (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
    (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
    (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G) (quotientMorphism G)

/-- The leg of the quotient presentation projects a point of the object functor to its base. -/
@[simp]
public theorem quotientLeg_obj (G : GroupoidInFunctors.{u, v, w} C) (P : G.objects.Elements) :
    (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G)).obj P = P.1 := rfl

/-- The base equality of the first component of an object of the `2`-fibre product, read on the
image of that component in the quotient. -/
public theorem productFstBase (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) : ((quotientMorphism G).obj W.x).base = W.base := W.hx

/-- The base equality of the second component of an object of the `2`-fibre product, read on the
image of that component in the quotient. -/
public theorem productSndBase (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) : ((quotientMorphism G).obj W.y).base = W.base := W.hy

/-- The base component of the inverse comparison isomorphism of an object of the `2`-fibre
product is the transport between the two base equalities. -/
public theorem productIso_inv_base (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) :
    W.iso.inv.base ≫ eqToHom (productFstBase G W) = eqToHom (productSndBase G W) := by
  let _ : (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 W.base) W.iso.inv :=
    TwoFibreProductOver.psiIso_inv_vertical W
  have h := IsHomLift.fac' (Grothendieck.forget (evaluationFunctor G)) (𝟙 W.base) W.iso.inv
  change W.iso.inv.base = _ at h
  rw [h, Category.id_comp, eqToHom_trans]
  exact eqToHom_trans _ _

/-- The base component of the inverse comparison isomorphism, as a composite of transports. -/
public theorem productIso_inv_base_eq (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) :
    W.iso.inv.base =
      eqToHom (productSndBase G W) ≫ eqToHom (productFstBase G W).symm := by
  rw [← productIso_inv_base G W, Category.assoc,
    show eqToHom (productFstBase G W) ≫ eqToHom (productFstBase G W).symm = 𝟙 _ from
      eqToHom_trans _ _, Category.comp_id]

/-- The arrow of the groupoid attached to an object of `U ×_{[U/R]} U`: the fibre component of
the inverse comparison isomorphism, transported to the base object. -/
public noncomputable def productArrow (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) : G.arrows.obj W.base :=
  G.arrows.map (eqToHom (productFstBase G W)) (quotientHomArrow G W.iso.inv)

/-- The arrow of an object of the `2`-fibre product, unfolded. -/
public theorem productArrow_eq (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) :
    productArrow G W =
      G.arrows.map (eqToHom (productFstBase G W)) (quotientHomArrow G W.iso.inv) := rfl

/-- The target of the arrow of an object of the `2`-fibre product is its first component. -/
public theorem productArrow_target (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) :
    G.target.app W.base (productArrow G W) =
      G.objects.map (eqToHom (productFstBase G W))
        ((quotientMorphism G).obj W.x).fiber :=
  (NatTrans.naturality_apply G.target (eqToHom (productFstBase G W))
      (quotientHomArrow G W.iso.inv)).trans
    (congrArg (fun z => G.objects.map (eqToHom (productFstBase G W)) z)
      (quotientHomArrow_target G W.iso.inv))

/-- The target of the arrow of an object of the `2`-fibre product, as the value of its first
component in the fibre over the base. -/
public theorem productArrow_target_value (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) :
    G.target.app W.base (productArrow G W) =
      elementsFiberValue G.objects W.base ⟨W.x, W.hx⟩ :=
  productArrow_target G W

/-- The source of the arrow of an object of the `2`-fibre product is its second component. -/
public theorem productArrow_source (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) :
    G.source.app W.base (productArrow G W) =
      G.objects.map (eqToHom (productSndBase G W))
        ((quotientMorphism G).obj W.y).fiber := by
  have h1 : G.source.app W.base (productArrow G W) =
      G.objects.map (eqToHom (productFstBase G W))
        (G.objects.map W.iso.inv.base ((quotientMorphism G).obj W.y).fiber) :=
    (NatTrans.naturality_apply G.source (eqToHom (productFstBase G W))
        (quotientHomArrow G W.iso.inv)).trans
      (congrArg (fun z => G.objects.map (eqToHom (productFstBase G W)) z)
        (quotientHomArrow_source G W.iso.inv))
  rw [h1, ← G.objects.map_comp_apply, productIso_inv_base]

/-- The source of the arrow of an object of the `2`-fibre product, as the value of its second
component in the fibre over the base. -/
public theorem productArrow_source_value (G : GroupoidInFunctors.{u, v, w} C)
    (W : QuotientSelfProduct G) :
    G.source.app W.base (productArrow G W) =
      elementsFiberValue G.objects W.base ⟨W.y, W.hy⟩ :=
  productArrow_source G W

/-- The first component of a morphism of the `2`-fibre product, compatible with the transports
to the two base objects. -/
public theorem productHom_a_comp (G : GroupoidInFunctors.{u, v, w} C)
    {W W' : QuotientSelfProduct G} (g : W ⟶ W') :
    eqToHom (productFstBase G W) ≫ g.hbase =
      g.a.1 ≫ eqToHom (productFstBase G W') := by
  rw [TwoFibreProductOver.Hom.hbase_eq g]
  simp only [eqToHom_trans_assoc]
  exact Category.id_comp _

/-- The second component of a morphism of the `2`-fibre product, compatible with the transports
to the two base objects. -/
public theorem productHom_b_comp (G : GroupoidInFunctors.{u, v, w} C)
    {W W' : QuotientSelfProduct G} (g : W ⟶ W') :
    eqToHom (productSndBase G W) ≫ g.hbase =
      g.b.1 ≫ eqToHom (productSndBase G W') := by
  have h : g.hbase = eqToHom W.hy.symm ≫ g.b.1 ≫ eqToHom W'.hy := by
    let _ := g.hb
    exact IsHomLift.fac
      (p := quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
      (f := g.hbase) (φ := g.b)
  rw [h]
  simp only [eqToHom_trans_assoc]
  exact Category.id_comp _

/-- A morphism of the `2`-fibre product identifies the arrows of the two comparison
isomorphisms. -/
public theorem productArrow_quotientHomArrow (G : GroupoidInFunctors.{u, v, w} C)
    {W W' : QuotientSelfProduct G} (g : W ⟶ W') :
    G.arrows.map g.a.1 (quotientHomArrow G W.iso.inv) = quotientHomArrow G W'.iso.inv := by
  have hsq : W.iso.inv ≫ (quotientMorphism G).map g.a =
      (quotientMorphism G).map g.b ≫ W'.iso.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← g.w, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h := congrArg (quotientHomArrow G) hsq
  rwa [quotientHomArrow_comp_quotientMorphism_map,
    quotientHomArrow_quotientMorphism_map_comp] at h

/-- The arrow attached to an object of the `2`-fibre product is natural. -/
public theorem productArrow_map (G : GroupoidInFunctors.{u, v, w} C)
    {W W' : QuotientSelfProduct G} (g : W ⟶ W') :
    G.arrows.map g.hbase (productArrow G W) = productArrow G W' :=
  ((G.arrows.map_comp_apply (eqToHom (productFstBase G W)) g.hbase
        (quotientHomArrow G W.iso.inv)).symm.trans
      (congrArg (fun f => G.arrows.map f (quotientHomArrow G W.iso.inv))
        (productHom_a_comp G g))).trans
    ((G.arrows.map_comp_apply g.a.1 (eqToHom (productFstBase G W'))
        (quotientHomArrow G W.iso.inv)).trans
      (congrArg (fun z => G.arrows.map (eqToHom (productFstBase G W')) z)
        (productArrow_quotientHomArrow G g)))

/-- The comparison of the self `2`-fibre product of the quotient morphism with the category of
elements of the arrow functor. -/
public noncomputable def quotientArrowsFunctor (G : GroupoidInFunctors.{u, v, w} C) :
    QuotientSelfProduct G ⥤ G.arrows.Elements where
  obj W := G.arrows.elementsMk W.base (productArrow G W)
  map g := Functor.Elements.homMk g.hbase (productArrow_map G g)
  map_id W := by apply Functor.Elements.hom_ext; rfl
  map_comp f g := by apply Functor.Elements.hom_ext; rfl

/-- The comparison lies over the base category. -/
public theorem quotientArrowsFunctor_over (G : GroupoidInFunctors.{u, v, w} C) :
    quotientArrowsFunctor G ⋙ Functor.Elements.π G.arrows =
      TwoFibreProductOver.structureFunctor
        (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
        (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
        (quotientMorphism G) := rfl

/-- The comparison of the self `2`-fibre product of the quotient morphism with the category of
elements of the arrow functor, as a `1`-morphism over the base. -/
public noncomputable def quotientArrowsBasedFunctor (G : GroupoidInFunctors.{u, v, w} C) :
    BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor
          (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
          (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
          (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
          (quotientMorphism G)) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.Elements.π G.arrows) where
  toFunctor := quotientArrowsFunctor G
  w := quotientArrowsFunctor_over G

/-! ### The comparison is an equivalence on each strict fibre -/

/-- The strict fibres of the self `2`-fibre product of the quotient morphism are thin: a
vertical morphism has both of its components vertical in a category of elements, and those are
determined by the morphism of the base they lie over. -/
public theorem isThin_fiber_quotientSelfProduct (G : GroupoidInFunctors.{u, v, w} C) (A : C) :
    Quiver.IsThin (Functor.Fiber
      (TwoFibreProductOver.structureFunctor
        (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
        (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
        (quotientMorphism G)) A) := by
  intro Z Z'
  refine ⟨fun f g => ?_⟩
  apply Functor.Fiber.hom_ext
  have hbase : ∀ h : Z ⟶ Z', (h.1).hbase = eqToHom Z.2 ≫ eqToHom Z'.2.symm := by
    intro h
    let _ := h.2
    have h2 : (h.1).hbase = eqToHom Z.2 ≫ 𝟙 A ≫ eqToHom Z'.2.symm :=
      IsHomLift.fac'
        (TwoFibreProductOver.structureFunctor
          (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
          (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
          (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
          (quotientMorphism G)) (𝟙 A) h.1
    rw [h2, Category.id_comp]
  have hfg : (f.1).hbase = (g.1).hbase := by rw [hbase f, hbase g]
  change f.1 = g.1
  refine TwoFibreProductOver.Hom.ext' ?_ ?_
  · apply Functor.Elements.hom_ext
    have h : (f.1).a.1 ≫ eqToHom (productFstBase G Z'.1) =
        (g.1).a.1 ≫ eqToHom (productFstBase G Z'.1) := by
      rw [← productHom_a_comp G f.1, ← productHom_a_comp G g.1, hfg]
    exact (cancel_mono _).1 h
  · apply Functor.Elements.hom_ext
    have h : (f.1).b.1 ≫ eqToHom (productSndBase G Z'.1) =
        (g.1).b.1 ≫ eqToHom (productSndBase G Z'.1) := by
      rw [← productHom_b_comp G f.1, ← productHom_b_comp G g.1, hfg]
    exact (cancel_mono _).1 h

/-- The comparison is faithful on each strict fibre, the fibres of the `2`-fibre product being
thin. -/
public theorem faithful_fiberFunctor_quotientArrows (G : GroupoidInFunctors.{u, v, w} C)
    (A : C) : (fiberFunctor (quotientArrowsBasedFunctor G) A).Faithful :=
  ⟨fun {X Y} {a b} _ => @Subsingleton.elim _ (isThin_fiber_quotientSelfProduct G A X Y) a b⟩

/-- A functor sends `f₁ ≫ f₂ ≫ eqToHom e.symm` to the identity transport of a point when it sends
`f₁ ≫ f₂` to the transport along `e`. -/
private theorem map_comp_comp_eqToHom_symm_apply {F : C ⥤ Type w} {X Y Z B : C} {u : F.obj X}
    {v : F.obj Z} {f₁ : X ⟶ Y} {f₂ : Y ⟶ B} (e : Z = B)
    (h : F.map (f₁ ≫ f₂) u = F.map (eqToHom e) v) :
    F.map (f₁ ≫ f₂ ≫ eqToHom e.symm) u = v := by
  subst e
  simpa using h

/-- **A vertical morphism between the images of two objects of the `2`-fibre product comes from
a vertical morphism there.** The transport between the two base objects identifies the arrows of
the two objects, hence their first and second components; the transports between those
components are the two halves of the sought morphism, and their compatibility with the
comparison isomorphisms is the identification of the arrows. -/
public theorem exists_productHom_of_arrow_eq (G : GroupoidInFunctors.{u, v, w} C)
    (W W' : QuotientSelfProduct G) (hb : W.base = W'.base)
    (hm : G.arrows.map (eqToHom hb) (productArrow G W) = productArrow G W') :
    ∃ g : W ⟶ W', g.hbase = eqToHom hb := by
  have harr : G.arrows.map (eqToHom (productFstBase G W) ≫ eqToHom hb ≫
      eqToHom (productFstBase G W').symm) (quotientHomArrow G W.iso.inv) =
      quotientHomArrow G W'.iso.inv := by
    refine map_comp_comp_eqToHom_symm_apply (productFstBase G W') ?_
    rw [G.arrows.map_comp_apply, ← productArrow_eq, hm, productArrow_eq]
  have hx : G.objects.map (eqToHom (productFstBase G W) ≫ eqToHom hb ≫
      eqToHom (productFstBase G W').symm) ((quotientMorphism G).obj W.x).fiber =
      ((quotientMorphism G).obj W'.x).fiber := by
    refine map_comp_comp_eqToHom_symm_apply (productFstBase G W') ?_
    rw [G.objects.map_comp_apply, ← productArrow_target, ← NatTrans.naturality_apply, hm,
      productArrow_target]
  have hy : G.objects.map (eqToHom (productSndBase G W) ≫ eqToHom hb ≫
      eqToHom (productSndBase G W').symm) ((quotientMorphism G).obj W.y).fiber =
      ((quotientMorphism G).obj W'.y).fiber := by
    refine map_comp_comp_eqToHom_symm_apply (productSndBase G W') ?_
    rw [G.objects.map_comp_apply, ← productArrow_source, ← NatTrans.naturality_apply, hm,
      productArrow_source]
  let a : W.x ⟶ W'.x :=
    ⟨eqToHom (productFstBase G W) ≫ eqToHom hb ≫ eqToHom (productFstBase G W').symm, hx⟩
  let b : W.y ⟶ W'.y :=
    ⟨eqToHom (productSndBase G W) ≫ eqToHom hb ≫ eqToHom (productSndBase G W').symm, hy⟩
  have hsq' : W.iso.inv ≫ (quotientMorphism G).map a =
      (quotientMorphism G).map b ≫ W'.iso.inv := by
    refine Grothendieck.ext _ _ ?_ ?_
    · change W.iso.inv.base ≫ (eqToHom (productFstBase G W) ≫ eqToHom hb ≫
          eqToHom (productFstBase G W').symm) =
        (eqToHom (productSndBase G W) ≫ eqToHom hb ≫
          eqToHom (productSndBase G W').symm) ≫ W'.iso.inv.base
      rw [productIso_inv_base_eq G W, productIso_inv_base_eq G W']
      simp
    · apply (G.evaluationArrowEquiv ((quotientMorphism G).obj W'.x).base _ _).injective
      apply Subtype.ext
      rw [evaluationArrowEquiv_eqToHom_comp]
      change quotientHomArrow G (W.iso.inv ≫ (quotientMorphism G).map a) =
        quotientHomArrow G ((quotientMorphism G).map b ≫ W'.iso.inv)
      rw [quotientHomArrow_comp_quotientMorphism_map,
        quotientHomArrow_quotientMorphism_map_comp]
      exact harr
  have hsq : (quotientMorphism G).map a ≫ W'.iso.hom =
      W.iso.hom ≫ (quotientMorphism G).map b :=
    calc (quotientMorphism G).map a ≫ W'.iso.hom
        = W.iso.hom ≫ (W.iso.inv ≫ (quotientMorphism G).map a) ≫ W'.iso.hom := by simp
      _ = W.iso.hom ≫ ((quotientMorphism G).map b ≫ W'.iso.inv) ≫ W'.iso.hom := by rw [hsq']
      _ = W.iso.hom ≫ (quotientMorphism G).map b := by simp
  have hbase : eqToHom W.hy.symm ≫
      (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G)).map b ≫
        eqToHom W'.hy =
      eqToHom W.hx.symm ≫
        (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G)).map a ≫
          eqToHom W'.hx := by
    change eqToHom (productSndBase G W).symm ≫
        (eqToHom (productSndBase G W) ≫ eqToHom hb ≫
          eqToHom (productSndBase G W').symm) ≫ eqToHom (productSndBase G W') =
      eqToHom (productFstBase G W).symm ≫
        (eqToHom (productFstBase G W) ≫ eqToHom hb ≫
          eqToHom (productFstBase G W').symm) ≫ eqToHom (productFstBase G W')
    simp
  refine ⟨TwoFibreProductOver.Hom.mk' a b hbase hsq, ?_⟩
  change eqToHom (productFstBase G W).symm ≫
    (eqToHom (productFstBase G W) ≫ eqToHom hb ≫
      eqToHom (productFstBase G W').symm) ≫ eqToHom (productFstBase G W') = eqToHom hb
  simp

/-- The comparison is full on each strict fibre. -/
public theorem full_fiberFunctor_quotientArrows (G : GroupoidInFunctors.{u, v, w} C)
    (A : C) : (fiberFunctor (quotientArrowsBasedFunctor G) A).Full := by
  refine ⟨fun {Z Z'} m => ?_⟩
  have hm : G.arrows.map (eqToHom (Z.2.trans Z'.2.symm)) (productArrow G Z.1) =
      productArrow G Z'.1 := by
    let _ : (Functor.Elements.π G.arrows).IsHomLift (𝟙 A) m.1 := m.2
    have h2 : (m.1).1 = eqToHom Z.2 ≫ 𝟙 A ≫ eqToHom Z'.2.symm :=
      IsHomLift.fac' (Functor.Elements.π G.arrows) (𝟙 A) m.1
    have h3 : G.arrows.map (m.1).1 (productArrow G Z.1) = productArrow G Z'.1 := (m.1).2
    rwa [h2, Category.id_comp, eqToHom_trans] at h3
  obtain ⟨g, hg⟩ := exists_productHom_of_arrow_eq G Z.1 Z'.1 (Z.2.trans Z'.2.symm) hm
  have hlift : (TwoFibreProductOver.structureFunctor
      (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
      (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
      (quotientMorphism G)).IsHomLift (𝟙 A) g := by
    refine IsHomLift.of_fac' _ (𝟙 A) g Z.2 Z'.2 ?_
    change g.hbase = eqToHom Z.2 ≫ 𝟙 A ≫ eqToHom Z'.2.symm
    rw [hg, Category.id_comp, eqToHom_trans]
    rfl
  exact ⟨⟨g, hlift⟩, @Subsingleton.elim _ (elementsFiber_isThin G.arrows A _ _) _ _⟩

/-- The value of the target of the arrow of an object of the `2`-fibre product is the value of
its first component. -/
public theorem elementsFiberValue_target_productArrow (G : GroupoidInFunctors.{u, v, w} C)
    {A : C} (W : QuotientSelfProduct G) (hW : W.base = A) :
    elementsFiberValue G.objects A
        ⟨(NatTrans.mapElements G.target).obj (G.arrows.elementsMk W.base (productArrow G W)), hW⟩ =
      elementsFiberValue G.objects A ⟨W.x, W.hx.trans hW⟩ := by
  change G.objects.map (eqToHom hW) (G.target.app W.base (productArrow G W)) =
    G.objects.map (eqToHom (W.hx.trans hW)) W.x.2
  rw [productArrow_target, ← G.objects.map_comp_apply]
  exact congrArg (fun f => G.objects.map f ((quotientMorphism G).obj W.x).fiber)
    (eqToHom_trans _ _)

/-- The value of the source of the arrow of an object of the `2`-fibre product is the value of
its second component. -/
public theorem elementsFiberValue_source_productArrow (G : GroupoidInFunctors.{u, v, w} C)
    {A : C} (W : QuotientSelfProduct G) (hW : W.base = A) :
    elementsFiberValue G.objects A
        ⟨(NatTrans.mapElements G.source).obj (G.arrows.elementsMk W.base (productArrow G W)), hW⟩ =
      elementsFiberValue G.objects A ⟨W.y, W.hy.trans hW⟩ := by
  change G.objects.map (eqToHom hW) (G.source.app W.base (productArrow G W)) =
    G.objects.map (eqToHom (W.hy.trans hW)) W.y.2
  rw [productArrow_source, ← G.objects.map_comp_apply]
  exact congrArg (fun f => G.objects.map f ((quotientMorphism G).obj W.y).fiber)
    (eqToHom_trans _ _)

/-- An arrow of the groupoid over `A` with source `x` and target `y` makes the images of `x`
and of `y` in the quotient isomorphic over `A`, through an isomorphism whose inverse has that
arrow as its fibre component. -/
public noncomputable def quotientIsoOfArrow (G : GroupoidInFunctors.{u, v, w} C) (A : C)
    {x y : G.objects.obj A} (r : G.arrows.obj A) (hs : G.source.app A r = x)
    (ht : G.target.app A r = y) :
    (quotientMorphism G).obj (G.objects.elementsMk A x) ≅
      (quotientMorphism G).obj (G.objects.elementsMk A y) := by
  let _ : Groupoid (G.objects.obj A) := G.evaluationGroupoid A
  let a : x ⟶ y := (G.evaluationArrowEquiv A x y).symm ⟨r, hs, ht⟩
  exact Grothendieck.isoMk (Iso.refl A)
    ((eqToIso (G.objects.map_id_apply A x)).trans (asIso a))

/-- The arrow of the isomorphism attached to an arrow is that arrow. -/
public theorem quotientHomArrow_quotientIsoOfArrow (G : GroupoidInFunctors.{u, v, w} C) (A : C)
    {x y : G.objects.obj A} (r : G.arrows.obj A) (hs : G.source.app A r = x)
    (ht : G.target.app A r = y) :
    quotientHomArrow G (quotientIsoOfArrow G A r hs ht).hom = r := by
  let _ : Groupoid (G.objects.obj A) := G.evaluationGroupoid A
  have h : quotientHomArrow G (quotientIsoOfArrow G A r hs ht).hom =
      (G.evaluationArrowEquiv A x y
        ((G.evaluationArrowEquiv A x y).symm ⟨r, hs, ht⟩)).1 := by
    rw [← evaluationArrowEquiv_eqToHom_comp G A (G.objects.map_id_apply A x)
      ((G.evaluationArrowEquiv A x y).symm ⟨r, hs, ht⟩)]
    rfl
  rw [h, Equiv.apply_symm_apply]

/-- The base component of the inverse of the isomorphism attached to an arrow is the
identity. -/
public theorem quotientIsoOfArrow_inv_base (G : GroupoidInFunctors.{u, v, w} C) (A : C)
    {x y : G.objects.obj A} (r : G.arrows.obj A) (hs : G.source.app A r = x)
    (ht : G.target.app A r = y) :
    (Grothendieck.forget (evaluationFunctor G)).map (quotientIsoOfArrow G A r hs ht).inv =
      𝟙 A := rfl

/-- The comparison is essentially surjective on each strict fibre: an arrow of the groupoid
over `A` is the arrow of the object of the `2`-fibre product given by its target, its source,
and the isomorphism it induces in the quotient. -/
public theorem essSurj_fiberFunctor_quotientArrows (G : GroupoidInFunctors.{u, v, w} C)
    (A : C) : (fiberFunctor (quotientArrowsBasedFunctor G) A).EssSurj := by
  refine ⟨fun Z => ?_⟩
  let r : G.arrows.obj A := elementsFiberValue G.arrows A Z
  let ι := quotientIsoOfArrow G A r rfl rfl
  have hvert : (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 A) ι.inv :=
    (quotientIsoOfArrow_inv_base G A r rfl rfl).symm ▸
      IsHomLift.map (Grothendieck.forget (evaluationFunctor G)) ι.inv
  let W : QuotientSelfProduct G :=
    { base := A
      x := G.objects.elementsMk A (G.target.app A r)
      y := G.objects.elementsMk A (G.source.app A r)
      hx := rfl
      hy := rfl
      iso := ι.symm
      vertical := hvert }
  have harr : productArrow G W = r := by
    change G.arrows.map (eqToHom (rfl : A = A)) (quotientHomArrow G ι.hom) = r
    rw [quotientHomArrow_quotientIsoOfArrow, eqToHom_refl, G.arrows.map_id_apply]
  refine ⟨Functor.Fiber.mk (p := TwoFibreProductOver.structureFunctor
      (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
      (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
      (quotientMorphism G)) (a := W) rfl, ?_⟩
  refine elementsFiberIsoOfValueEq G.arrows A _ Z ?_
  change G.arrows.map (eqToHom (rfl : A = A)) (productArrow G W) = r
  rw [harr, eqToHom_refl, G.arrows.map_id_apply]

end

/-! ### Part (3) of Tag 06KU -/

section
open CategoryTheory CategoryTheory.Functor

universe u v w t

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Two objects of the strict fibre of a category of elements over `k[M]` with the same value
have the same class in the tangent module. -/
public theorem tangentClassAt_elements_eq_of_value_eq
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (hF : IsDeformationCategory.{u, v, w} (Functor.Elements.π F))
    (M : FGModuleCat.{max v w} k)
    (z z' : Functor.Fiber (Functor.Elements.π F)
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
    (h : elementsFiberValue F _ z = elementsFiberValue F _ z') :
    tangentClassAt.{u, v, w} (BasedCategory.ofFunctor (Functor.Elements.π F)) hF M z =
      tangentClassAt.{u, v, w} (BasedCategory.ofFunctor (Functor.Elements.π F)) hF M z' := by
  obtain ⟨e⟩ := elementsFiberIsoOfValueEq F _ z z' h
  exact (tangentClassAt_eq_iff.{u, v, w}
    (BasedCategory.ofFunctor (Functor.Elements.π F)) hF M z z').2 ⟨e⟩

variable (G : GroupoidInFunctors.{_, max v w, t} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))

/-- The leg `U → [U/R]` of the quotient presentation is a deformation category. -/
public abbrev quotientLeg_isDeformationCategory
    (hU : IsDeformationFunctor.{u, v, w} G.objects) :
    IsDeformationCategory.{u, v, w}
      (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G)) :=
  isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} G.objects
    (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
    (quotientMorphism_over G) hU

/-- The category of elements of the object functor is a deformation category. -/
public abbrev objectsBasedDeformationCategory
    (hU : IsDeformationFunctor.{u, v, w} G.objects) :
    IsDeformationCategory.{u, v, w}
      (BasedCategory.ofFunctor (Functor.Elements.π G.objects)).p :=
  (isDeformationCategory_iff G.objects).2 hU

/-- The category of elements of the arrow functor is a deformation category. -/
public abbrev arrowsBasedDeformationCategory
    (hR : IsDeformationFunctor.{u, v, w} G.arrows) :
    IsDeformationCategory.{u, v, w}
      (BasedCategory.ofFunctor (Functor.Elements.π G.arrows)).p :=
  (isDeformationCategory_iff G.arrows).2 hR

/-- The self `2`-fibre product of the quotient morphism is a deformation category. -/
public abbrev quotientSelfProduct_isDeformationCategory
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor.{u, v, w} G.objects)
    (hR : IsDeformationFunctor.{u, v, w} G.arrows) :
    IsDeformationCategory.{u, v, w}
      (productBased.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G) (quotientMorphism G)).p :=
  isDeformationCategory_productBased.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
    (quotientMorphism G) (quotientMorphism G) (quotientLeg_isDeformationCategory G hU)
    (quotientLeg_isDeformationCategory G hU)
    (quotient_isDeformationCategory.{u, v, w, t} G hG hU hR)

/-- **The tangent module of `U ×_{[U/R]} U` is the tangent space of the arrow functor.** The
comparison is an equivalence on the strict fibre over `k[M]`. -/
public noncomputable def quotientSelfProductTangentEquiv
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor.{u, v, w} G.objects)
    (hR : IsDeformationFunctor.{u, v, w} G.arrows) (M : FGModuleCat.{max v w} k) :
    ↥(tangentModuleAt.{u, v, w}
        (productBased.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
          (quotientMorphism G) (quotientMorphism G))
        (quotientSelfProduct_isDeformationCategory G hG hU hR) M) ≃ₗ[k]
      ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor (Functor.Elements.π G.arrows))
        (arrowsBasedDeformationCategory G hR) M) :=
  tangentLinearEquivOfFiberEquivalence.{u, v, w}
    (quotientSelfProduct_isDeformationCategory G hG hU hR)
    (arrowsBasedDeformationCategory G hR) (quotientArrowsBasedFunctor G) M
    (full_fiberFunctor_quotientArrows G _) (faithful_fiberFunctor_quotientArrows G _)
    (essSurj_fiberFunctor_quotientArrows G _)

/-- The boundary map `Inf([U/R]) → TR` of part (3) of Tag 06KU: the boundary map of the six-term
sequence of the self `2`-fibre product of the quotient morphism, read on the tangent space of the
arrow functor. -/
public noncomputable def quotientInfinitesimalBoundary
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor.{u, v, w} G.objects)
    (hR : IsDeformationFunctor.{u, v, w} G.arrows) {y₀ : G.objects.Elements}
    (PF : ChosenPushforwardsAt (Grothendieck.forget (evaluationFunctor G))
      ((quotientMorphism G).obj y₀))
    (M : FGModuleCat.{max v w} k) :
    ↥((infinitesimalAutomorphismLinearLift.{u, v, w} PF
        (quotient_isDeformationCategory.{u, v, w, t} G hG hU hR).satisfiesRS).functor.obj M) →ₗ[k]
      ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor (Functor.Elements.π G.arrows))
        (arrowsBasedDeformationCategory G hR) M) :=
  (quotientSelfProductTangentEquiv G hG hU hR M).toLinearMap.comp
    (selfBoundaryLinearMap.{u, v, w} (Grothendieck.forget (evaluationFunctor G)) G.objects
      (quotientMorphism G) (quotientLeg_isDeformationCategory G hU)
      (quotient_isDeformationCategory.{u, v, w, t} G hG hU hR)
      (chosenPushforwardsAtOfCofibered
        (quotientLeg_isDeformationCategory G hU).predeformation.cofibered y₀) PF M)

/-- The differential of a morphism `σ` of the arrow functor to the object functor, read through the
comparison with the `2`-fibre product, is the differential of a projection `P` as soon as `σ` and
`P` have the same value on every object of the fibre. -/
private theorem tangentMapAt_quotientSelfProductTangentEquiv_of_value_eq
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor.{u, v, w} G.objects)
    (hR : IsDeformationFunctor.{u, v, w} G.arrows) (M : FGModuleCat.{max v w} k)
    (σ : G.arrows ⟶ G.objects)
    (P : productBased.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
      (quotientMorphism G) (quotientMorphism G) ⥤ᵇ
        BasedCategory.ofFunctor (quotientMorphism G ⋙ Grothendieck.forget (evaluationFunctor G)))
    (hval : ∀ X : Functor.Fiber (productBased.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G) (quotientMorphism G)).p
        ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M),
      elementsFiberValue G.objects _
        ((fiberFunctor (elementsBasedFunctor σ) _).obj
          ((fiberFunctor (quotientArrowsBasedFunctor G) _).obj X)) =
        elementsFiberValue G.objects _ ((fiberFunctor P _).obj X))
    (wv : ↥(tangentModuleAt.{u, v, w}
      (productBased.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G) (quotientMorphism G))
      (quotientSelfProduct_isDeformationCategory G hG hU hR) M)) :
    tangentMapAt.{u, v, w} (arrowsBasedDeformationCategory G hR)
        (objectsBasedDeformationCategory G hU) (elementsBasedFunctor σ) M
        (quotientSelfProductTangentEquiv G hG hU hR M wv) =
      tangentMapAt.{u, v, w} (quotientSelfProduct_isDeformationCategory G hG hU hR)
        (quotientLeg_isDeformationCategory G hU) P M wv := by
  obtain ⟨X, rfl⟩ := tangentClassAt_surjective.{u, v, w} _
    (quotientSelfProduct_isDeformationCategory G hG hU hR) M wv
  have hL : tangentMapAt.{u, v, w} (arrowsBasedDeformationCategory G hR)
      (objectsBasedDeformationCategory G hU) (elementsBasedFunctor σ) M
      (quotientSelfProductTangentEquiv G hG hU hR M
        (tangentClassAt.{u, v, w} _ (quotientSelfProduct_isDeformationCategory G hG hU hR)
          M X)) =
      tangentClassAt.{u, v, w} (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
        (objectsBasedDeformationCategory G hU) M
        ((fiberFunctor (elementsBasedFunctor σ)
          ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj
          ((fiberFunctor (quotientArrowsBasedFunctor G)
            ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)).obj X)) := by
    change tangentMapAt.{u, v, w} _ _ (elementsBasedFunctor σ) M
        (tangentMapAt.{u, v, w} _ _ (quotientArrowsBasedFunctor G) M
          (tangentClassAt.{u, v, w} _ _ M X)) = _
    rw [tangentMapAt_tangentClassAt.{u, v, w}, tangentMapAt_tangentClassAt.{u, v, w}]
  rw [hL, tangentMapAt_tangentClassAt.{u, v, w}
    (quotientSelfProduct_isDeformationCategory G hG hU hR)
    (quotientLeg_isDeformationCategory G hU) P M X]
  exact tangentClassAt_elements_eq_of_value_eq.{u, v, w} G.objects
    (objectsBasedDeformationCategory G hU) M _ _ (hval X)

/-- The differential of the source map, read through the comparison with the `2`-fibre
product. -/
public theorem tangentMapAt_source_quotientSelfProductTangentEquiv
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor.{u, v, w} G.objects)
    (hR : IsDeformationFunctor.{u, v, w} G.arrows) (M : FGModuleCat.{max v w} k)
    (wv : ↥(tangentModuleAt.{u, v, w}
      (productBased.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G) (quotientMorphism G))
      (quotientSelfProduct_isDeformationCategory G hG hU hR) M)) :
    tangentMapAt.{u, v, w} (arrowsBasedDeformationCategory G hR)
        (objectsBasedDeformationCategory G hU) (elementsBasedFunctor G.source) M
        (quotientSelfProductTangentEquiv G hG hU hR M wv) =
      (tangentProjPair.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G) (quotientMorphism G) (quotientLeg_isDeformationCategory G hU)
        (quotientLeg_isDeformationCategory G hU)
        (quotient_isDeformationCategory.{u, v, w, t} G hG hU hR) M wv).2 :=
  tangentMapAt_quotientSelfProductTangentEquiv_of_value_eq G hG hU hR M G.source
    (productSnd.{u, v, w} (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
      (quotientMorphism G))
    (fun X => elementsFiberValue_source_productArrow G X.1 X.2) wv

/-- The differential of the target map, read through the comparison with the `2`-fibre
product. -/
public theorem tangentMapAt_target_quotientSelfProductTangentEquiv
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor.{u, v, w} G.objects)
    (hR : IsDeformationFunctor.{u, v, w} G.arrows) (M : FGModuleCat.{max v w} k)
    (wv : ↥(tangentModuleAt.{u, v, w}
      (productBased.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G) (quotientMorphism G))
      (quotientSelfProduct_isDeformationCategory G hG hU hR) M)) :
    tangentMapAt.{u, v, w} (arrowsBasedDeformationCategory G hR)
        (objectsBasedDeformationCategory G hU) (elementsBasedFunctor G.target) M
        (quotientSelfProductTangentEquiv G hG hU hR M wv) =
      (tangentProjPair.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G) (quotientMorphism G) (quotientLeg_isDeformationCategory G hU)
        (quotientLeg_isDeformationCategory G hU)
        (quotient_isDeformationCategory.{u, v, w, t} G hG hU hR) M wv).1 :=
  tangentMapAt_quotientSelfProductTangentEquiv_of_value_eq G hG hU hR M G.target
    (productFst.{u, v, w} (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G)
      (quotientMorphism G))
    (fun X => elementsFiberValue_target_productArrow G X.1 X.2) wv

/-- **Stacks Project, Tag 06KU, part (3).** Let `(U, R, s, t, c)` be a smooth groupoid in
functors on `𝒞_Λ` whose functors of objects and of arrows are deformation functors. Then the
space of infinitesimal automorphisms of the quotient is the kernel of the differential of the
source-and-target map,

`Inf([U/R]) = Ker(ds ⊕ dt : TR → TU ⊕ TU)`,

in the form of the exact sequence of `k`-vector spaces

`0 → Inf([U/R]) → TR → TU ⊕ TU`:

the boundary map is injective and its image is the kernel of the pair of the two differentials.

The identification is the one of Tag 06L6 part (2) for the quotient morphism `q : U → [U/R]`,
whose self `2`-fibre product `U ×_{q, [U/R], q} U` is the arrow functor: an arrow of the groupoid
over `A` with source `x` and target `y` is an isomorphism over `A` between the images of `x` and
of `y` in the quotient, and that comparison is an equivalence on every strict fibre, hence an
isomorphism of tangent modules. -/
@[stacks 06KU "part (3): Inf([U/R]) = Ker(ds ⊕ dt : TR → TU ⊕ TU), as the exactness of \
0 → Inf([U/R]) → TR → TU ⊕ TU. The two differentials are the maps on tangent modules induced by \
s and t at an arbitrary coordinate module M, and Inf([U/R]) is the value at M of the k-linear \
lift of the infinitesimal automorphisms of the image in [U/R] of a point y₀ of U, taken with an \
arbitrary choice PF of pushforwards there. No hypothesis is carried beyond the tag's own: G \
smooth, U and R deformation functors"]
public theorem quotientInfinitesimalBoundary_exact
    (hG : GroupoidInFunctors.IsSmooth G)
    (hU : IsDeformationFunctor.{u, v, w} G.objects)
    (hR : IsDeformationFunctor.{u, v, w} G.arrows) {y₀ : G.objects.Elements}
    (PF : ChosenPushforwardsAt (Grothendieck.forget (evaluationFunctor G))
      ((quotientMorphism G).obj y₀))
    (M : FGModuleCat.{max v w} k) :
    Function.Injective (quotientInfinitesimalBoundary.{u, v, w, t} G hG hU hR PF M) ∧
      Function.Exact (quotientInfinitesimalBoundary.{u, v, w, t} G hG hU hR PF M)
        (LinearMap.prod
          (tangentMapAt.{u, v, w} (arrowsBasedDeformationCategory G hR)
            (objectsBasedDeformationCategory G hU) (elementsBasedFunctor G.source) M)
          (tangentMapAt.{u, v, w} (arrowsBasedDeformationCategory G hR)
            (objectsBasedDeformationCategory G hU)
            (elementsBasedFunctor G.target) M)) := by
  obtain ⟨hinj, hex⟩ := exact_selfBoundaryLinearMap_tangentProjPair.{u, v, w} G.objects
    (Grothendieck.forget (evaluationFunctor G)) (quotientMorphism G) (quotientMorphism_over G)
    hU (quotient_isDeformationCategory.{u, v, w, t} G hG hU hR)
    (chosenPushforwardsAtOfCofibered
      (quotientLeg_isDeformationCategory G hU).predeformation.cofibered y₀) PF M
  refine ⟨(quotientSelfProductTangentEquiv G hG hU hR M).injective.comp hinj, fun b => ?_⟩
  obtain ⟨wv, rfl⟩ := (quotientSelfProductTangentEquiv G hG hU hR M).surjective b
  refine ⟨fun hb => ?_, fun ⟨α, hα⟩ => ?_⟩
  · have h1 : (tangentProjPair.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        (quotientMorphism G) (quotientMorphism G) (quotientLeg_isDeformationCategory G hU)
        (quotientLeg_isDeformationCategory G hU)
        (quotient_isDeformationCategory.{u, v, w, t} G hG hU hR) M wv) = 0 :=
      Prod.ext
        ((tangentMapAt_target_quotientSelfProductTangentEquiv G hG hU hR M wv).symm.trans
          (congrArg Prod.snd hb))
        ((tangentMapAt_source_quotientSelfProductTangentEquiv G hG hU hR M wv).symm.trans
          (congrArg Prod.fst hb))
    obtain ⟨α, hα⟩ := (hex wv).1 h1
    exact ⟨α, congrArg (quotientSelfProductTangentEquiv G hG hU hR M) hα⟩
  · have h1 : wv = selfBoundaryLinearMap.{u, v, w} (Grothendieck.forget (evaluationFunctor G))
        G.objects (quotientMorphism G) (quotientLeg_isDeformationCategory G hU)
        (quotient_isDeformationCategory.{u, v, w, t} G hG hU hR)
        (chosenPushforwardsAtOfCofibered
          (quotientLeg_isDeformationCategory G hU).predeformation.cofibered y₀) PF M α :=
      (quotientSelfProductTangentEquiv G hG hU hR M).injective hα.symm
    have h2 := (hex wv).2 ⟨α, h1.symm⟩
    exact Prod.ext
      ((tangentMapAt_source_quotientSelfProductTangentEquiv G hG hU hR M wv).trans
        (congrArg Prod.snd h2))
      ((tangentMapAt_target_quotientSelfProductTangentEquiv G hG hU hR M wv).trans
        (congrArg Prod.fst h2))

end

end Deformation
