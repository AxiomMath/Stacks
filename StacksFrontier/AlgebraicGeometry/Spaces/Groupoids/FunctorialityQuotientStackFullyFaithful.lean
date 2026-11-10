module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliaryPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentationFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonFullness
public import StacksFrontier.CategoryTheory.Sites.Stack.FullyFaithfulOfLocalEssImage

/-!
# Full faithfulness of the comparison 1-morphism of Stacks 04Y4

Let `φ : G ⟶ G'` be a morphism of groupoids in algebraic spaces over an algebraic space `B` over
a scheme `S` of a big fppf site, written `f : U ⟶ U'` on object spaces and `f : R ⟶ R'` on arrow
spaces, and let `(U'', R'', s'', t'', c'')` be the groupoid of Section 78.21 attached to it, with
`U'' = U ×_{f, U', t'} R'` and `R'' = R ×_{f ∘ s, U', t'} R'`. This file proves that the
comparison 1-morphism

```
[U''/R''] ⟶ [U/R] ×_{[φ], [U'/R'], π'} 𝒮_{U'}
```

of `AlgebraicGeometry.Stack.auxQuotientComparison` is **full and faithful**. With local essential
surjectivity on fibres this is what
`AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquare_of` turns into the assertion that the
square of Section 78.21 is a 2-fibre product.

## Main results

* `AlgebraicGeometry.Stack.fullyFaithful_auxQuotientComparison`: the comparison 1-morphism of
  Stacks 04Y4 is fully faithful.
* `AlgebraicGeometry.Stack.auxQuotientComparison_full` and
  `AlgebraicGeometry.Stack.auxQuotientComparison_faithful`: the two halves of that statement.

## Implementation notes

*The reduction to the presentation.* Every object of `[U''/R'']` is locally in the essential image
of the stackification map out of the presentation, which is fully faithful by Stacks 044X (2)
(`AlgebraicGeometry.Stack.fullyFaithfulToQuotientStack`), and the morphism presheaves of the
quotient stack and of the 2-fibre product are sheaves — condition (2) of Stacks 026F. So
`CategoryTheory.Functor.fullyFaithful_of_locallyEssImage_of_isMorSheaf` reduces the statement to
full faithfulness of the composite of the comparison 1-morphism with the stackification map of the
presentation, which is the content of this file.

*The fibrewise check.* That composite is strictly over the site, so by Stacks 003Z (1) in the form
`CategoryTheory.Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber` it is enough to
check it on the fibre over each test object `T`, where every morphism in sight is **vertical** over
`𝟙 T`. An object of the presentation over `T` is a `T`-point `(u, r')` of `U''`, and a vertical
morphism of it is an arrow of the evaluated auxiliary groupoid, that is a `T`-point `(r, r')` of
`R''`.

*Faithfulness.* The `[U/R]`-component of the image of a vertical morphism is, after the unit of the
universal property of the stackification, the image in `[U/R]` of the corresponding arrow of the
evaluated groupoid `G(T)`; `AlgebraicGeometry.Stack.pointwiseToQuotientStack_map_inj` cancels the
stackification map, `CategoryTheory.Pseudofunctor.CoGrothendieck.ι_faithful` the fibre inclusion,
and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxHom_evaluation_faithful` the projection `g`: an
arrow of the evaluated auxiliary groupoid out of a fixed point is determined by its first
component, the second being the second projection of its source.

*Fullness.* Given a vertical morphism `Φ` of the 2-fibre product between the images of two points
`P` and `Q` of `U''` over `T`, Stacks 044X (2) in the form
`AlgebraicGeometry.Stack.exists_evaluationArrow` produces an arrow `r` of `G(T)` whose image is the
`[U/R]`-component of `Φ`. The commuting square of `Φ` is read on the pointwise presentation of
`[U'/R']` through
`AlgebraicGeometry.Stack.auxSquareCell_hom_app_toQuotientStack`, which identifies the filler at a
presented object with the comparison built on the presentation, whose component at `(u, r')` is the
arrow `r'` of `G'(T)`; the `𝒮_{U'}`-component of `Φ` contributes an identity, the fibres of the
object-space fibration being discrete. What comes out is the `T`-point identity
`c'(f(r), r'_P) = r'_Q`, which is exactly the hypothesis of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxEvaluationArrow`; the arrow of the evaluated
auxiliary groupoid it builds is the preimage of `Φ`.

*Why the generic helpers.* Each cancellation of isomorphisms below is a lemma over **plain
variables**, instantiated with `exact`: `rw` and `simp only` do not fire on a composite of
morphisms of a quotient stack, the two `≫`s of a nested composite reaching their `Category`
instance by different paths, and `Lean.Meta.kabstract` declines to abstract over goals mentioning
a point of the presentation, which are not type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04W9](https://stacks.math.columbia.edu/tag/04W9)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### Cancellations over plain variables -/

/- generic -/
private theorem map_eq_of_natIso {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
    {F K : D₁ ⥤ D₂} (u : F ≅ K) {x y : D₁} {m n : x ⟶ y} (h : F.map m = F.map n) :
    K.map m = K.map n := by
  have e : ∀ p : x ⟶ y, K.map p = u.inv.app x ≫ F.map p ≫ u.hom.app y := fun p => by
    rw [u.hom.naturality p]
    simp
  rw [e m, e n, h]

/- generic: recovering the image under one of two isomorphic functors -/
private theorem map_eq_of_natIso_conj {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
    {F K : D₁ ⥤ D₂} (u : F ≅ K) {x y : D₁} (m : x ⟶ y) (a : F.obj x ⟶ F.obj y)
    (h : K.map m = u.inv.app x ≫ a ≫ u.hom.app y) : F.map m = a := by
  have hn : F.map m ≫ u.hom.app y = u.hom.app x ≫ K.map m := u.hom.naturality m
  rw [h] at hn
  simpa using congrArg (fun k => k ≫ u.inv.app y) hn

/- generic: the cancellation turning the commuting square into a pointwise equation -/
private theorem aux_square_cancel {D : Type*} [Category* D]
    {a₁ a₂ q₁ q₂ r₁ r₂ e₁ e₂ b₁ b₂ : D}
    (lu₁ : a₁ ≅ q₁) (lu₂ : a₂ ≅ q₂) (c₁ : q₁ ≅ r₁) (c₂ : q₂ ≅ r₂)
    (L₁ : a₁ ≅ r₁) (L₂ : a₂ ≅ r₂) (M₁ : e₁ ≅ r₁) (M₂ : e₂ ≅ r₂)
    (U₁ : b₁ ≅ e₁) (U₂ : b₂ ≅ e₂)
    {Fa : a₁ ⟶ a₂} {Gb : b₁ ⟶ b₂} {K : r₁ ⟶ r₂}
    (hL₁ : L₁.hom = lu₁.hom ≫ c₁.hom) (hL₂ : L₂.hom = lu₂.hom ≫ c₂.hom)
    (hnat : K ≫ c₂.inv = c₁.inv ≫ lu₁.inv ≫ Fa ≫ lu₂.hom)
    (hw : Fa ≫ L₂.hom ≫ M₂.inv ≫ U₂.inv = (L₁.hom ≫ M₁.inv ≫ U₁.inv) ≫ Gb) :
    M₁.hom ≫ K = (U₁.inv ≫ Gb ≫ U₂.hom) ≫ M₂.hom := by
  have hK : K = c₁.inv ≫ lu₁.inv ≫ Fa ≫ lu₂.hom ≫ c₂.hom := by
    simpa only [Category.assoc] using (Iso.comp_inv_eq c₂).1 hnat
  have h0 : Fa ≫ lu₂.hom ≫ c₂.hom ≫ M₂.inv ≫ U₂.inv =
      lu₁.hom ≫ c₁.hom ≫ M₁.inv ≫ U₁.inv ≫ Gb := by
    simpa only [hL₁, hL₂, Category.assoc] using hw
  have hFa : Fa ≫ lu₂.hom ≫ c₂.hom =
      lu₁.hom ≫ c₁.hom ≫ M₁.inv ≫ U₁.inv ≫ Gb ≫ U₂.hom ≫ M₂.hom := by
    calc Fa ≫ lu₂.hom ≫ c₂.hom
        = (Fa ≫ lu₂.hom ≫ c₂.hom ≫ M₂.inv ≫ U₂.inv) ≫ U₂.hom ≫ M₂.hom := by simp
      _ = (lu₁.hom ≫ c₁.hom ≫ M₁.inv ≫ U₁.inv ≫ Gb) ≫ U₂.hom ≫ M₂.hom := by rw [h0]
      _ = _ := by simp only [Category.assoc]
  rw [hK, hFa]
  simp

/- generic: two parallel vertical morphisms over the same test object agree when the structure
functor is faithful -/
private theorem hom_eq_of_vertical {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
    (p : D₂ ⥤ D₁) [p.Faithful] {T : D₁} {a b : D₂} (f g : a ⟶ b)
    (hf : p.IsHomLift (𝟙 T) f) (hg : p.IsHomLift (𝟙 T) g) : f = g :=
  p.map_injective ((IsHomLift.fac' p (𝟙 T) f).trans (IsHomLift.fac' p (𝟙 T) g).symm)

/- generic: the inverse of a component of a natural isomorphism lying over an identity also lies
over that identity -/
private theorem isHomLift_inv_app {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
    {D₃ : Type*} [Category* D₃] (p : D₂ ⥤ D₁) {F K : D₃ ⥤ D₂} (α : F ≅ K) (X : D₃) {T : D₁}
    (h : p.IsHomLift (𝟙 T) (α.hom.app X)) : p.IsHomLift (𝟙 T) (α.inv.app X) := by
  have : p.IsHomLift (𝟙 T) (α.app X).hom := h
  rw [← Iso.app_inv]
  exact IsHomLift.lift_id_inv p T (α.app X)


/- generic: conjugating a vertical morphism by the components of a natural isomorphism whose
components are vertical gives a vertical morphism -/
private theorem isHomLift_inv_app_comp_comp {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
    {D₃ : Type*} [Category* D₃] (p : D₂ ⥤ D₁) {F K : D₃ ⥤ D₂} (α : F ≅ K) {X Y : D₃} {T : D₁}
    {m : F.obj X ⟶ F.obj Y} (hX : p.IsHomLift (𝟙 T) (α.hom.app X))
    (hY : p.IsHomLift (𝟙 T) (α.hom.app Y)) (hm : p.IsHomLift (𝟙 T) m) :
    p.IsHomLift (𝟙 T) (α.inv.app X ≫ m ≫ α.hom.app Y) := by
  have : p.IsHomLift (𝟙 T) (α.app X).hom := hX
  have hXi : p.IsHomLift (𝟙 T) (α.inv.app X) := by
    rw [← Iso.app_inv]
    exact IsHomLift.lift_id_inv p T (α.app X)
  exact @IsHomLift.comp_of_lift_id _ _ _ _ p _ _ _ _ _ _ hXi
    (@IsHomLift.comp_of_lift_id _ _ _ _ p _ _ _ _ _ _ hm hY)

/-! ### Arrows of the evaluated groupoid inside a fibre -/

/- the inclusion of the fibre over a test object into the pointwise groupoid fibration -/
private noncomputable abbrev auxIota (K : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) :=
  CoGrothendieck.ι
    (evaluationGroupoidFunctor K.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor' T

section Iota

/- The presenting pseudofunctor of the pointwise groupoid fibration is reached through
`CategoryTheory.Functor.toPseudofunctor'` and the groupoid-to-category inclusion, none of which
the `implicit` transparency level unfolds; naming that chain is what lets the identity transport
of the pseudofunctor reduce. -/
attribute [local implicit_reducible] CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc
  CategoryTheory.BasedCategory.ofFunctor Grpd.forgetToCat Grpd.of

/- the element of the arrow space of the image of an arrow under the fibre inclusion -/
private theorem iota_arrow (K : GroupoidInAlgebraicSpaces C S hS B) (T : BigFppfOver C S hS)
    {x y : K.toGroupoidInFunctors.Evaluation (op T)} (arr : x ⟶ y) :
    (K.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _
        ((auxIota K T).map arr).fiber).1 =
      (K.toGroupoidInFunctors.evaluationArrowEquiv (op T) x y arr).1 := by
  have h : ((auxIota K T).map arr).fiber =
      arr ≫ ((evaluationGroupoidFunctor K.toGroupoidInFunctors ⋙
        Grpd.forgetToCat).toPseudofunctor'.mapId ⟨op T⟩).inv.toNatTrans.app y := rfl
  rw [h, Functor.toPseudofunctor'_mapId_inv_app]
  exact evaluationArrow_comp_eqToHom K.toGroupoidInFunctors (op T) arr _

end Iota

/- vertical morphisms of the pointwise fibration come from the evaluated groupoid -/
private theorem exists_pointwiseArrow (K : GroupoidInAlgebraicSpaces C S hS B)
    (T : BigFppfOver C S hS) (x y : K.objects.obj.obj (op T))
    (m : (⟨T, x⟩ : (presheafOfGroupoids
        (evaluationGroupoidFunctor K.toGroupoidInFunctors)).obj) ⟶ ⟨T, y⟩)
    (hm : (presheafOfGroupoids (evaluationGroupoidFunctor K.toGroupoidInFunctors)).p.IsHomLift
      (𝟙 T) m) :
    ∃ arr : (show K.toGroupoidInFunctors.Evaluation (op T) from x) ⟶ y,
      (auxIota K T).map arr = m := by
  have hc := CoGrothendieck.comp_const
    (evaluationGroupoidFunctor K.toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor' T
  have hK : (Functor.Fiber.inducedFunctor hc).Full := inferInstance
  have hKP : (Functor.Fiber.inducedFunctor
      (p := (presheafOfGroupoids (evaluationGroupoidFunctor K.toGroupoidInFunctors)).p) hc).Full :=
    hK
  have := hm
  obtain ⟨arr, harr⟩ := hKP.map_surjective
    (Functor.Fiber.homMk
      (presheafOfGroupoids (evaluationGroupoidFunctor K.toGroupoidInFunctors)).p T m)
  exact ⟨arr, congrArg (fun k => Functor.Fiber.fiberInclusion.map k) harr⟩

/-! ### The composite of the presentation with the comparison 1-morphism -/

/- a `T`-point of `U''`, as an object of the presentation of `[U''/R'']` -/
private noncomputable def auxPresentedPoint (φ : Hom G G') (T : BigFppfOver C S hS)
    (P : (auxObjects φ).obj.obj (op T)) : (quotientPrestack (auxGroupoid φ)).obj :=
  ⟨T, P⟩

/- the same point, read in the unlifted pointwise groupoid fibration -/
private noncomputable abbrev auxPresentedDown (φ : Hom G G') (T : BigFppfOver C S hS)
    (P : (auxObjects φ).obj.obj (op T)) :=
  (quotientPrestackDown (auxGroupoid φ)).obj (auxPresentedPoint φ T P)

/- the unit of the universal property of the stackification for the upper leg -/
private noncomputable abbrev auxInvariantUnit (φ : Hom G G') :=
  quotientStackOfInvariantUnit (auxGroupoid φ) (auxToTargetObjects φ)
    (auxToTargetObjects_invariant φ)

/- the comparison 1-morphism restricted along the stackification map of the presentation -/
private noncomputable def auxPresentedFunctor (φ : Hom G G') :
    (quotientPrestack (auxGroupoid φ)).obj ⥤ functorialityTwoFibreProductObj φ :=
  toQuotientStack (auxGroupoid φ) ⋙ auxQuotientComparison φ

/- that composite is strictly over the big fppf site -/
private theorem comp_toQuotientStack_auxQuotientComparison (φ : Hom G G') :
    (toQuotientStack (auxGroupoid φ) ⋙ auxQuotientComparison φ) ⋙
        functorialityTwoFibreProduct φ = (quotientPrestack (auxGroupoid φ)).p := by
  rw [Functor.assoc, auxQuotientComparison_comp,
    (isFibredOneMorphism_toQuotientStack (auxGroupoid φ)).comp_eq]

/- the `[U/R]`-component of the image of a morphism of the presentation -/
private theorem auxPresentedFunctor_map_a (φ : Hom G G')
    {X Y : (quotientPrestack (auxGroupoid φ)).obj} (m : X ⟶ Y) :
    ((auxPresentedFunctor φ).map m).a =
      (toQuotientStack (auxGroupoid φ) ⋙ quotientMapExtension (auxHom φ)).map m := rfl

/- the `𝒮_{U'}`-component of the image of a morphism of the presentation -/
private theorem auxPresentedFunctor_map_b (φ : Hom G G')
    {X Y : (quotientPrestack (auxGroupoid φ)).obj} (m : X ⟶ Y) :
    ((auxPresentedFunctor φ).map m).b =
      (auxLiftedQuotientStackToObjects φ).map ((toQuotientStack (auxGroupoid φ)).map m) := rfl

/-! ### Faithfulness on a fibre -/

/- a vertical morphism of the presentation comes from the evaluated auxiliary groupoid -/
private theorem auxPresented_exists_arrow (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (m : auxPresentedPoint φ T P ⟶ auxPresentedPoint φ T Q)
    (hm : (quotientPrestack (auxGroupoid φ)).p.IsHomLift (𝟙 T) m) :
    ∃ arr : (show (auxGroupoid φ).toGroupoidInFunctors.Evaluation (op T) from P) ⟶ Q,
      (auxIota (auxGroupoid φ) T).map arr =
        (quotientPrestackEquivalence (auxGroupoid φ)).inverse.map m := by
  have hmb : ((quotientPrestackEquivalence (auxGroupoid φ)).inverse.map m).base = 𝟙 T :=
    (map_eq_eqToHom_of_isHomLift (quotientPrestack (auxGroupoid φ)).p m (𝟙 T) hm rfl rfl
      rfl).trans (eqToHom_refl T rfl)
  exact exists_pointwiseArrow (auxGroupoid φ) T P Q
    ((quotientPrestackEquivalence (auxGroupoid φ)).inverse.map m)
    (CoGrothendieck.isHomLift_of_base_eq_id T
      ((quotientPrestackEquivalence (auxGroupoid φ)).inverse.map m) hmb)

/- faithfulness on vertical morphisms -/
private theorem auxPresented_map_injective (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (m n : auxPresentedPoint φ T P ⟶ auxPresentedPoint φ T Q)
    (hm : (quotientPrestack (auxGroupoid φ)).p.IsHomLift (𝟙 T) m)
    (hn : (quotientPrestack (auxGroupoid φ)).p.IsHomLift (𝟙 T) n)
    (h : (auxPresentedFunctor φ).map m = (auxPresentedFunctor φ).map n) : m = n := by
  have ha : (toQuotientStack (auxGroupoid φ) ⋙
        (quotientStackMap (auxHom φ)).toFunctor).map m =
      (toQuotientStack (auxGroupoid φ) ⋙ (quotientStackMap (auxHom φ)).toFunctor).map n :=
    congrArg (fun k => TwoFibreProductOver.Hom.a k) h
  have hu := map_eq_of_natIso (quotientMapExtensionUnit (auxHom φ)) ha
  obtain ⟨am, ham⟩ := auxPresented_exists_arrow φ T P Q m hm
  obtain ⟨an, han⟩ := auxPresented_exists_arrow φ T P Q n hn
  have hkey : (pointwiseToQuotientStack G).map ((quotientPointwiseMap (auxHom φ)).map
        ((CoGrothendieck.ι (evaluationGroupoidFunctor
            (auxGroupoid φ).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor' T).map
          am)) =
      (pointwiseToQuotientStack G).map ((quotientPointwiseMap (auxHom φ)).map
        ((CoGrothendieck.ι (evaluationGroupoidFunctor
            (auxGroupoid φ).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor' T).map
          an)) := by
    rwa [ham, han]
  have h₁ := CoGrothendieck.isHomLift_of_base_eq_id T
    ((quotientPointwiseMap (auxHom φ)).map
      ((CoGrothendieck.ι (evaluationGroupoidFunctor
        (auxGroupoid φ).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor' T).map am)) rfl
  have h₂ := CoGrothendieck.isHomLift_of_base_eq_id T
    ((quotientPointwiseMap (auxHom φ)).map
      ((CoGrothendieck.ι (evaluationGroupoidFunctor
        (auxGroupoid φ).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor' T).map an)) rfl
  have heq := pointwiseToQuotientStack_map_inj G T _ _ h₁ h₂ hkey
  rw [quotientPointwiseMap_map_ι (auxHom φ) T am,
    quotientPointwiseMap_map_ι (auxHom φ) T an] at heq
  have hif := CoGrothendieck.ι_faithful
    (F := (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor') T
  have harr := Functor.Faithful.map_injective heq
  have hev := auxHom_evaluation_faithful φ (op T)
  have hae : am = an := Functor.Faithful.map_injective harr
  have hmn : (quotientPrestackEquivalence (auxGroupoid φ)).inverse.map m =
      (quotientPrestackEquivalence (auxGroupoid φ)).inverse.map n :=
    ham.symm.trans ((congrArg (fun k => (CoGrothendieck.ι (evaluationGroupoidFunctor
      (auxGroupoid φ).toGroupoidInFunctors ⋙ Grpd.forgetToCat).toPseudofunctor' T).map k)
      hae).trans han)
  have := (quotientPrestackEquivalence (auxGroupoid φ)).fullyFaithfulInverse.faithful
  exact Functor.Faithful.map_injective hmn

/-! ### The filler of the square at a presented object -/

/- the lower leg of the restricted square, at an object of the presentation -/
private noncomputable def auxLowerIsoAt (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :=
  (((BasedNatTrans.forgetful (quotientPrestack (auxGroupoid φ))
    (quotientStack G')).mapIso (auxRestrictedLowerIso φ)).app X)

/- the upper leg of the restricted square, at an object of the presentation -/
private noncomputable def auxUpperIsoAt (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :=
  (((BasedNatTrans.forgetful (quotientPrestack (auxGroupoid φ))
    (quotientStack G')).mapIso (auxRestrictedUpperIso φ)).app X)

/- the comparison arrow of the restricted square, at an object of the presentation -/
private noncomputable def auxMiddleIsoAt (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :=
  (pointwiseToQuotientStack G').mapIso
    ((auxComparisonIso φ).app ((quotientPrestackDown (auxGroupoid φ)).obj X))

/- the unit of the universal property for the left leg, at an object of the presentation -/
private noncomputable def auxUnitLIsoAt (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :=
  (quotientStackMap φ).toFunctor.mapIso ((quotientMapExtensionUnit (auxHom φ)).app X)

/- the 2-isomorphism of Stacks 046Q, at an object of the presentation -/
private noncomputable def auxCommutesIsoAt (φ : Hom G G')
    (X : (quotientPrestack (auxGroupoid φ)).obj) :=
  (((BasedNatTrans.forgetful
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors))
      (quotientStack G')).mapIso (quotientStackMap_commutes φ)).app
    ((quotientPointwiseMap (auxHom φ)).obj ((quotientPrestackDown (auxGroupoid φ)).obj X))).symm

/- the filler, at an object of the presentation, as a composite of the three isomorphisms -/
private theorem auxFiller_hom_app (φ : Hom G G') (X : (quotientPrestack (auxGroupoid φ)).obj) :
    ((auxPresentedFunctor φ).obj X).iso.hom =
      (auxLowerIsoAt φ X).hom ≫ (auxMiddleIsoAt φ X).inv ≫ (auxUpperIsoAt φ X).inv :=
  auxSquareCell_hom_app_toQuotientStack φ X

/- the lower leg splits as the unit followed by the 2-isomorphism of Stacks 046Q -/
private theorem auxLowerIsoAt_hom (φ : Hom G G') (X : (quotientPrestack (auxGroupoid φ)).obj) :
    (auxLowerIsoAt φ X).hom = (auxUnitLIsoAt φ X).hom ≫ (auxCommutesIsoAt φ X).hom := rfl

/-! ### Fullness on a fibre -/

/- the `𝒮_{U'}`-component of a vertical morphism, transported to the presentation -/
private noncomputable abbrev auxLiftedComponent (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q)) :=
  (auxInvariantUnit φ).inv.app (auxPresentedPoint φ T P) ≫ Φ.b ≫
    (auxInvariantUnit φ).hom.app (auxPresentedPoint φ T Q)

/- the same component, in the un-enlarged fibred category of `U'` -/
private noncomputable abbrev auxDownComponent (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q)) :=
  (liftedFibredCategoryDown G'.objects).map (auxLiftedComponent φ T P Q Φ)

/- the same component, in the pointwise groupoid fibration of `G'` -/
private noncomputable abbrev auxPointwiseComponent (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q)) :=
  (pointwiseObjectInclusion G').map (auxDownComponent φ T P Q Φ)

/- the candidate preimage: an arrow of the evaluated auxiliary groupoid, read in the
presentation of `[U''/R'']` -/
private noncomputable abbrev auxPresentedArrow (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (arr : (show G.toGroupoidInFunctors.Evaluation (op T) from
        (auxObjectsFst φ).hom.app (op T) P) ⟶ (auxObjectsFst φ).hom.app (op T) Q)
    (hcond : (auxTargetSnd φ).hom.app (op T) (auxArrowOfHom φ (op T) arr) =
      (auxObjectsSnd φ).hom.app (op T) Q) :=
  (quotientPrestackEquivalence (auxGroupoid φ)).functor.map
    ((auxIota (auxGroupoid φ) T).map (auxEvaluationArrow φ (op T) P Q arr hcond))

/- the `[U/R]`-component of a vertical morphism, conjugated by the unit, is vertical -/
private theorem auxPresented_isHomLift_conj (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q))
    (hb : Φ.hbase = 𝟙 T) :
    (quotientStack G).p.IsHomLift (𝟙 T)
      ((quotientMapExtensionUnit (auxHom φ)).inv.app (auxPresentedPoint φ T P) ≫ Φ.a ≫
        (quotientMapExtensionUnit (auxHom φ)).hom.app (auxPresentedPoint φ T Q)) := by
  have hΦa : (quotientStack G).p.IsHomLift (𝟙 T) Φ.a := by rw [← hb]; exact Φ.ha
  exact isHomLift_inv_app_comp_comp (quotientStack G).p (quotientMapExtensionUnit (auxHom φ))
    (quotientMapExtensionUnit_hom_isHomLift (auxHom φ) (auxPresentedPoint φ T P))
    (quotientMapExtensionUnit_hom_isHomLift (auxHom φ) (auxPresentedPoint φ T Q)) hΦa

/- the 2-isomorphism of Stacks 046Q, at the arrow lifting the `[U/R]`-component -/
private theorem auxPresented_naturality (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q))
    (arr : (show G.toGroupoidInFunctors.Evaluation (op T) from
        (auxObjectsFst φ).hom.app (op T) P) ⟶ (auxObjectsFst φ).hom.app (op T) Q)
    (harr : (pointwiseToQuotientStack G).map ((auxIota G T).map arr) =
      (quotientMapExtensionUnit (auxHom φ)).inv.app (auxPresentedPoint φ T P) ≫ Φ.a ≫
        (quotientMapExtensionUnit (auxHom φ)).hom.app (auxPresentedPoint φ T Q)) :
    (pointwiseToQuotientStack G').map ((quotientPointwiseMap φ).map
          ((auxIota G T).map arr)) ≫
        (auxCommutesIsoAt φ (auxPresentedPoint φ T Q)).inv =
      (auxCommutesIsoAt φ (auxPresentedPoint φ T P)).inv ≫
        (auxUnitLIsoAt φ (auxPresentedPoint φ T P)).inv ≫ (quotientStackMap φ).map Φ.a ≫
          (auxUnitLIsoAt φ (auxPresentedPoint φ T Q)).hom := by
  refine (quotientStackMap_commutes_naturality φ
    ((auxIota G T).map arr)).trans ?_
  refine congrArg (fun k => (auxCommutesIsoAt φ (auxPresentedPoint φ T P)).inv ≫ k) ?_
  refine (congrArg (fun k => (quotientStackMap φ).toFunctor.map k) harr).trans ?_
  refine ((quotientStackMap φ).toFunctor.map_comp _ _).trans ?_
  exact congrArg (fun k => (quotientStackMap φ).toFunctor.map
    ((quotientMapExtensionUnit (auxHom φ)).inv.app (auxPresentedPoint φ T P)) ≫ k)
    ((quotientStackMap φ).toFunctor.map_comp _ _)

/- the commuting square of a morphism of the 2-fibre product, with the filler expanded -/
private theorem auxPresented_square (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q)) :
    (quotientStackMap φ).map Φ.a ≫ (auxLowerIsoAt φ (auxPresentedPoint φ T Q)).hom ≫
        (auxMiddleIsoAt φ (auxPresentedPoint φ T Q)).inv ≫
          (auxUpperIsoAt φ (auxPresentedPoint φ T Q)).inv =
      ((auxLowerIsoAt φ (auxPresentedPoint φ T P)).hom ≫
        (auxMiddleIsoAt φ (auxPresentedPoint φ T P)).inv ≫
          (auxUpperIsoAt φ (auxPresentedPoint φ T P)).inv) ≫
        (liftedQuotientStackProjection G').map Φ.b := by
  have h := Φ.w
  rwa [auxFiller_hom_app φ (auxPresentedPoint φ T P),
    auxFiller_hom_app φ (auxPresentedPoint φ T Q)] at h

/- the `𝒮_{U'}`-component of a vertical morphism, read in the fibred category of `U'`, lies
over the identity -/
private theorem auxDownComponent_base (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q))
    (hb : Φ.hbase = 𝟙 T) :
    (auxDownComponent φ T P Q Φ).base = 𝟙 T := by
  have hΦb : (liftedFibredCategory G'.objects).p.IsHomLift (𝟙 T) Φ.b := by rw [← hb]; exact Φ.hb
  have hΦbc : (liftedFibredCategory G'.objects).p.IsHomLift (𝟙 T) (auxLiftedComponent φ T P Q Φ) :=
    isHomLift_inv_app_comp_comp (liftedFibredCategory G'.objects).p (auxInvariantUnit φ)
      (isHomLift_quotientStackOfInvariantUnit_app (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ) (auxPresentedPoint φ T P))
      (isHomLift_quotientStackOfInvariantUnit_app (auxGroupoid φ) (auxToTargetObjects φ)
        (auxToTargetObjects_invariant φ) (auxPresentedPoint φ T Q)) hΦb
  have hβlift : (fibredCategory C S hS G'.objects.obj).val.p.IsHomLift (𝟙 T)
      (auxDownComponent φ T P Q Φ) := by
    have := hΦbc
    exact Functor.isHomLift_map_of_comp_eq (liftedFibredCategoryDown G'.objects).w (𝟙 T)
      (auxLiftedComponent φ T P Q Φ)
  exact (map_eq_eqToHom_of_isHomLift (fibredCategory C S hS G'.objects.obj).val.p
    (auxDownComponent φ T P Q Φ) (𝟙 T) hβlift rfl rfl rfl).trans (eqToHom_refl T rfl)

/- the arrow of `G'(T)` underlying the comparison followed by the image of `arr` -/
private theorem auxPresented_arrow_left (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (arr : (show G.toGroupoidInFunctors.Evaluation (op T) from
        (auxObjectsFst φ).hom.app (op T) P) ⟶ (auxObjectsFst φ).hom.app (op T) Q) :
    (G'.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _
        (auxComparisonArrow φ (auxPresentedDown φ T P) ≫
          (quotientPointwiseMap φ).map ((auxIota G T).map arr)).fiber).1 =
      (auxTargetSnd φ).hom.app (op T) (auxArrowOfHom φ (op T) arr) := by
  refine (pointwiseComp_arrow G'.toGroupoidInFunctors
    (auxComparisonArrow φ (auxPresentedDown φ T P))
    ((quotientPointwiseMap φ).map ((auxIota G T).map arr))).trans ?_
  refine (Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp _ (op T) _ _).trans ?_
  refine Eq.trans ?_ (auxTargetSnd_app φ (op T) (auxArrowOfHom φ (op T) arr)).symm
  refine Deformation.GroupoidInFunctors.compose_congr G'.toGroupoidInFunctors (op T) _ _ ?_ ?_
  · refine (Deformation.evaluationMap_map_arrow G'.toGroupoidInFunctors _ _).trans ?_
    refine (G'.toGroupoidInFunctors.arrows.map_id_apply (op T) _).trans ?_
    refine (quotientPointwiseMap_arrow φ ((auxIota G T).map arr)).trans ?_
    exact congrArg (φ.toGroupoidHom.mapArrows.app (op T))
      ((iota_arrow G T arr).trans (auxArrowOfHom_fst φ (op T) arr).symm)
  · exact (auxComparisonArrow_arrow φ (auxPresentedDown φ T P)).trans
      (auxArrowOfHom_snd φ (op T) arr).symm

/- the arrow of `G'(T)` underlying the `𝒮_{U'}`-component followed by the comparison -/
private theorem auxPresented_arrow_right (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q))
    (hb : Φ.hbase = 𝟙 T) :
    (G'.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _
        ((auxPointwiseComponent φ T P Q Φ) ≫
          auxComparisonArrow φ (auxPresentedDown φ T Q)).fiber).1 =
      (auxObjectsSnd φ).hom.app (op T) Q := by
  have hinclbase : (auxPointwiseComponent φ T P Q Φ).base = 𝟙 T :=
    auxDownComponent_base φ T P Q Φ hb
  refine (pointwiseComp_arrow_of_left_identity G'.toGroupoidInFunctors
    (auxPointwiseComponent φ T P Q Φ)
    (auxComparisonArrow φ (auxPresentedDown φ T Q))
    (evaluationArrow_eqToHom_identity G'.toGroupoidInFunctors (op T)
      (Discrete.eq_of_hom (auxDownComponent φ T P Q Φ).fiber))).trans ?_
  rw [hinclbase]
  exact (G'.toGroupoidInFunctors.arrows.map_id_apply (op T) _).trans
    (auxComparisonArrow_arrow φ (auxPresentedDown φ T Q))

/- the `T`-point identity `c'(f(r), r'_P) = r'_Q` read off the commuting square of `Φ` -/
private theorem auxPresented_cond (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q))
    (hb : Φ.hbase = 𝟙 T)
    (arr : (show G.toGroupoidInFunctors.Evaluation (op T) from
        (auxObjectsFst φ).hom.app (op T) P) ⟶ (auxObjectsFst φ).hom.app (op T) Q)
    (harr : (pointwiseToQuotientStack G).map ((auxIota G T).map arr) =
      (quotientMapExtensionUnit (auxHom φ)).inv.app (auxPresentedPoint φ T P) ≫ Φ.a ≫
        (quotientMapExtensionUnit (auxHom φ)).hom.app (auxPresentedPoint φ T Q)) :
    (auxTargetSnd φ).hom.app (op T) (auxArrowOfHom φ (op T) arr) =
      (auxObjectsSnd φ).hom.app (op T) Q := by
  have hsq := aux_square_cancel (auxUnitLIsoAt φ (auxPresentedPoint φ T P))
    (auxUnitLIsoAt φ (auxPresentedPoint φ T Q))
    (auxCommutesIsoAt φ (auxPresentedPoint φ T P))
    (auxCommutesIsoAt φ (auxPresentedPoint φ T Q))
    (auxLowerIsoAt φ (auxPresentedPoint φ T P)) (auxLowerIsoAt φ (auxPresentedPoint φ T Q))
    (auxMiddleIsoAt φ (auxPresentedPoint φ T P)) (auxMiddleIsoAt φ (auxPresentedPoint φ T Q))
    (auxUpperIsoAt φ (auxPresentedPoint φ T P)) (auxUpperIsoAt φ (auxPresentedPoint φ T Q))
    (auxLowerIsoAt_hom φ (auxPresentedPoint φ T P))
    (auxLowerIsoAt_hom φ (auxPresentedPoint φ T Q))
    (auxPresented_naturality φ T P Q Φ arr harr) (auxPresented_square φ T P Q Φ)
  have hU : (liftedQuotientStackProjection G').map (auxLiftedComponent φ T P Q Φ) =
      (auxUpperIsoAt φ (auxPresentedPoint φ T P)).inv ≫ (liftedQuotientStackProjection G').map Φ.b ≫
        (auxUpperIsoAt φ (auxPresentedPoint φ T Q)).hom :=
    ((liftedQuotientStackProjection G').toFunctor.map_comp _ _).trans
      (congrArg (fun k => (auxUpperIsoAt φ (auxPresentedPoint φ T P)).inv ≫ k)
        ((liftedQuotientStackProjection G').toFunctor.map_comp _ _))
  have hsq2 : (pointwiseToQuotientStack G').map (auxComparisonArrow φ (auxPresentedDown φ T P) ≫
        (quotientPointwiseMap φ).map ((auxIota G T).map arr)) =
      (pointwiseToQuotientStack G').map ((auxPointwiseComponent φ T P Q Φ) ≫
        auxComparisonArrow φ (auxPresentedDown φ T Q)) :=
    ((pointwiseToQuotientStack G').map_comp _ _).trans
      (hsq.trans ((congrArg (fun k => k ≫ (auxMiddleIsoAt φ (auxPresentedPoint φ T Q)).hom)
        hU.symm).trans
        ((pointwiseToQuotientStack G').map_comp _ _).symm))
  have h₁ := CoGrothendieck.isHomLift_of_base_eq_id T
    (auxComparisonArrow φ (auxPresentedDown φ T P) ≫
      (quotientPointwiseMap φ).map ((auxIota G T).map arr))
    ((pointwiseComp_base _ _).trans (Category.id_comp (𝟙 T)))
  have h₂ := CoGrothendieck.isHomLift_of_base_eq_id T ((auxPointwiseComponent φ T P Q Φ) ≫
      auxComparisonArrow φ (auxPresentedDown φ T Q))
    ((pointwiseComp_base _ _).trans ((congrArg (fun k => k ≫ 𝟙 T)
      (auxDownComponent_base φ T P Q Φ hb)).trans (Category.id_comp (𝟙 T))))
  have hfinal := pointwiseToQuotientStack_map_inj G' T _ _ h₁ h₂ hsq2
  have hval := congrArg (fun k => (G'.toGroupoidInFunctors.evaluationArrowEquiv (op T) _ _
    (Pseudofunctor.CoGrothendieck.Hom.fiber k)).1) hfinal
  exact (auxPresented_arrow_left φ T P Q arr).symm.trans
    (hval.trans (auxPresented_arrow_right φ T P Q Φ hb))

/- two vertical morphisms between presented points have the same `𝒮_{U'}`-component -/
private theorem auxPresentedFunctor_map_b_eq (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q))
    (hb : Φ.hbase = 𝟙 T) (χ : auxPresentedPoint φ T P ⟶ auxPresentedPoint φ T Q)
    (hχv : (quotientPrestack (auxGroupoid φ)).p.IsHomLift (𝟙 T) χ) :
    ((auxPresentedFunctor φ).map χ).b = Φ.b := by
  refine (auxPresentedFunctor_map_b φ χ).trans ?_
  have hΦb : (liftedFibredCategory G'.objects).p.IsHomLift (𝟙 T) Φ.b := by rw [← hb]; exact Φ.hb
  have h1 : (quotientStack (auxGroupoid φ)).p.IsHomLift (𝟙 T)
      ((toQuotientStack (auxGroupoid φ)).map χ) := by
    have := hχv
    exact Functor.isHomLift_map_of_comp_eq
      (isFibredOneMorphism_toQuotientStack (auxGroupoid φ)).comp_eq (𝟙 T) χ
  have h2 : (liftedFibredCategory G'.objects).p.IsHomLift (𝟙 T)
      ((auxLiftedQuotientStackToObjects φ).map ((toQuotientStack (auxGroupoid φ)).map χ)) := by
    have := h1
    exact Functor.isHomLift_map_of_comp_eq (auxLiftedQuotientStackToObjects φ).w (𝟙 T) _
  have := liftedFibredCategory_faithful G'.objects
  exact hom_eq_of_vertical (liftedFibredCategory G'.objects).p _ _ h2 hΦb

/- fullness on vertical morphisms -/
private theorem auxPresented_exists_hom (φ : Hom G G') (T : BigFppfOver C S hS)
    (P Q : (auxObjects φ).obj.obj (op T))
    (Φ : (auxPresentedFunctor φ).obj (auxPresentedPoint φ T P) ⟶
      (auxPresentedFunctor φ).obj (auxPresentedPoint φ T Q))
    (hb : Φ.hbase = 𝟙 T) :
    ∃ χ : auxPresentedPoint φ T P ⟶ auxPresentedPoint φ T Q,
      (auxPresentedFunctor φ).map χ = Φ := by
  obtain ⟨arr, harr⟩ := exists_evaluationArrow G T ((auxObjectsFst φ).hom.app (op T) P)
    ((auxObjectsFst φ).hom.app (op T) Q)
    ((quotientMapExtensionUnit (auxHom φ)).inv.app (auxPresentedPoint φ T P) ≫ Φ.a ≫
      (quotientMapExtensionUnit (auxHom φ)).hom.app (auxPresentedPoint φ T Q))
    (auxPresented_isHomLift_conj φ T P Q Φ hb)
  have hcond := auxPresented_cond φ T P Q Φ hb arr harr
  refine ⟨(auxPresentedArrow φ T P Q arr hcond), TwoFibreProductOver.Hom.ext' ?_ ?_⟩
  · refine (auxPresentedFunctor_map_a φ (auxPresentedArrow φ T P Q arr hcond)).trans ?_
    refine map_eq_of_natIso_conj (quotientMapExtensionUnit (auxHom φ)) _ Φ.a ?_
    refine Eq.trans ?_ harr
    refine congrArg (fun k => (pointwiseToQuotientStack G).map k) ?_
    refine (quotientPointwiseMap_map_ι (auxHom φ) T
      (auxEvaluationArrow φ (op T) P Q arr hcond)).trans ?_
    exact congrArg (fun k => (auxIota G T).map k)
      (auxEvaluationArrow_map φ (op T) P Q arr hcond)
  · refine auxPresentedFunctor_map_b_eq φ T P Q Φ hb _ ?_
    have hm := IsHomLift.map (quotientPrestack (auxGroupoid φ)).p
      (auxPresentedArrow φ T P Q arr hcond)
    rwa [show (quotientPrestack (auxGroupoid φ)).p.map
      (auxPresentedArrow φ T P Q arr hcond) = 𝟙 T from rfl] at hm

/-! ### Stacks 003Z (1): the fibrewise criterion -/

/- Stacks 003Z (1) for fullness, on one fibre -/
private theorem full_fibre_auxPresentedFunctor (φ : Hom G G') (T : BigFppfOver C S hS) :
    (Functor.Fiber.mapOfComp (quotientPrestack (auxGroupoid φ)).p
      (functorialityTwoFibreProduct φ) (auxPresentedFunctor φ)
      (comp_toQuotientStack_auxQuotientComparison φ) T).Full := by
  constructor
  intro W₁ W₂ Ψ
  obtain ⟨⟨b₁, P⟩, h₁⟩ := W₁
  obtain ⟨⟨b₂, Q⟩, h₂⟩ := W₂
  have e₁ : b₁ = T := h₁
  subst e₁
  have e₂ : b₂ = b₁ := h₂
  subst e₂
  have hlift : (functorialityTwoFibreProduct φ).IsHomLift (𝟙 b₂)
    (Functor.Fiber.fiberInclusion.map Ψ) := Ψ.2
  have hbase : (Functor.Fiber.fiberInclusion.map Ψ).hbase = 𝟙 b₂ :=
    (map_eq_eqToHom_of_isHomLift (functorialityTwoFibreProduct φ)
      (Functor.Fiber.fiberInclusion.map Ψ) (𝟙 b₂) hlift rfl rfl rfl).trans
      (eqToHom_refl b₂ rfl)
  obtain ⟨χ, hχ⟩ := auxPresented_exists_hom φ b₂ P Q (Functor.Fiber.fiberInclusion.map Ψ) hbase
  have hχlift : (quotientPrestack (auxGroupoid φ)).p.IsHomLift (𝟙 b₂) χ :=
    (Functor.isHomLift_map_iff_of_comp_eq (quotientPrestack (auxGroupoid φ)).p
      (functorialityTwoFibreProduct φ) (auxPresentedFunctor φ)
      (comp_toQuotientStack_auxQuotientComparison φ) (𝟙 b₂) χ).mp (by rwa [hχ])
  refine ⟨Functor.Fiber.homMk (quotientPrestack (auxGroupoid φ)).p b₂ χ,
    Functor.Fiber.hom_ext ?_⟩
  exact (Functor.Fiber.fiberInclusion_map_mapOfComp_map (quotientPrestack (auxGroupoid φ)).p
    (functorialityTwoFibreProduct φ) (auxPresentedFunctor φ)
    (comp_toQuotientStack_auxQuotientComparison φ) b₂ _).trans
    ((congrArg (fun k => (auxPresentedFunctor φ).map k)
      (Functor.Fiber.fiberInclusion_homMk (quotientPrestack (auxGroupoid φ)).p b₂ χ)).trans hχ)

/- Stacks 003Z (1) for faithfulness, on one fibre -/
private theorem faithful_fibre_auxPresentedFunctor (φ : Hom G G') (T : BigFppfOver C S hS) :
    (Functor.Fiber.mapOfComp (quotientPrestack (auxGroupoid φ)).p
      (functorialityTwoFibreProduct φ) (auxPresentedFunctor φ)
      (comp_toQuotientStack_auxQuotientComparison φ) T).Faithful := by
  constructor
  intro W₁ W₂ m n h
  obtain ⟨⟨b₁, P⟩, h₁⟩ := W₁
  obtain ⟨⟨b₂, Q⟩, h₂⟩ := W₂
  have e₁ : b₁ = T := h₁
  subst e₁
  have e₂ : b₂ = b₁ := h₂
  subst e₂
  have hmn := (Functor.Fiber.fiberInclusion_map_mapOfComp_map
    (quotientPrestack (auxGroupoid φ)).p (functorialityTwoFibreProduct φ)
    (auxPresentedFunctor φ) (comp_toQuotientStack_auxQuotientComparison φ) b₂ m).symm.trans
    ((congrArg (fun k => Functor.Fiber.fiberInclusion.map k) h).trans
      (Functor.Fiber.fiberInclusion_map_mapOfComp_map (quotientPrestack (auxGroupoid φ)).p
        (functorialityTwoFibreProduct φ) (auxPresentedFunctor φ)
        (comp_toQuotientStack_auxQuotientComparison φ) b₂ n))
  exact Functor.Fiber.hom_ext (auxPresented_map_injective φ b₂ P Q
    (Functor.Fiber.fiberInclusion.map m) (Functor.Fiber.fiberInclusion.map n) m.2 n.2 hmn)

/-! ### Full faithfulness -/

/- **The comparison 1-morphism of Stacks 04Y4, restricted along the stackification map of the
presentation of `[U''/R'']`, is fully faithful.** It is strictly over the site, and full and
faithful on every fibre, so Stacks 003Z (1) applies. -/
private noncomputable def fullyFaithful_toQuotientStack_comp_auxQuotientComparison
    (φ : Hom G G') :
    (toQuotientStack (auxGroupoid φ) ⋙ auxQuotientComparison φ).FullyFaithful := by
  have h := (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber
    (quotientPrestack (auxGroupoid φ)).p (functorialityTwoFibreProduct φ)
    (isFiberedInGroupoids_quotientPrestack (auxGroupoid φ))
    (isFiberedInGroupoids_functorialityTwoFibreProduct φ)
    (auxPresentedFunctor φ)
    (comp_toQuotientStack_auxQuotientComparison φ)).2
    (fun T => ⟨full_fibre_auxPresentedFunctor φ T, faithful_fibre_auxPresentedFunctor φ T⟩)
  have : (auxPresentedFunctor φ).Full := h.1
  have : (auxPresentedFunctor φ).Faithful := h.2
  exact Functor.FullyFaithful.ofFullyFaithful (auxPresentedFunctor φ)

/-- **The comparison 1-morphism `[U''/R''] ⟶ [U/R] ×_{[U'/R']} 𝒮_{U'}` of Stacks 04Y4 is fully
faithful.**

Every object of `[U''/R'']` is, locally on the test object, in the essential image of the
stackification map out of the presentation, which is fully faithful by Stacks 044X (2); the
composite of that map with the comparison 1-morphism is fully faithful by Stacks 003Z (1), checked
on each fibre; and the morphism presheaves of the quotient stack and of the 2-fibre product are
sheaves, which is condition (2) of Stacks 026F. Those are exactly the hypotheses of
`CategoryTheory.Functor.fullyFaithful_of_locallyEssImage_of_isMorSheaf`. -/
theorem fullyFaithful_auxQuotientComparison (φ : Hom G G') :
    Nonempty (auxQuotientComparison φ).FullyFaithful := by
  have := isFibered_functorialityTwoFibreProduct φ
  exact Functor.fullyFaithful_of_locallyEssImage_of_isMorSheaf
    (toQuotientStack (auxGroupoid φ))
    (isFibredOneMorphism_toQuotientStack (auxGroupoid φ)).comp_eq
    (fullyFaithfulToQuotientStack (auxGroupoid φ))
    (isFibredOneMorphism_auxQuotientComparison φ)
    (fullyFaithful_toQuotientStack_comp_auxQuotientComparison φ)
    (isFiberedInGroupoids_quotientStack (auxGroupoid φ))
    (isFiberedInGroupoids_functorialityTwoFibreProduct φ)
    (BigFppfOver.topology C S hS)
    (fun T x y => (isStack_quotientStack (auxGroupoid φ)).isMorSheaf T x y)
    (isMorSheaf_functorialityTwoFibreProduct φ)
    (fun T x => by
      obtain ⟨R, hR, h⟩ := essImage_toQuotientStack (auxGroupoid φ) T x
      exact ⟨R, hR, fun f hf => h hf⟩)

/-- **The comparison 1-morphism of Stacks 04Y4 is full.** -/
theorem auxQuotientComparison_full (φ : Hom G G') : (auxQuotientComparison φ).Full :=
  (fullyFaithful_auxQuotientComparison φ).some.full

/-- **The comparison 1-morphism of Stacks 04Y4 is faithful.** -/
theorem auxQuotientComparison_faithful (φ : Hom G G') : (auxQuotientComparison φ).Faithful :=
  (fullyFaithful_auxQuotientComparison φ).some.faithful

end AlgebraicGeometry.Stack

end
