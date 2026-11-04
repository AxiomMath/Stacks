module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.QuotientLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSite
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The site of affine ind-étale objects over an affine base as a category of algebras

For an affine scheme `X` with ring of global sections `A`, taking `Spec` is an equivalence from
the opposite of the category of ind-étale `A`-algebras onto the full subcategory of the small
pro-étale site of `X` on the affine objects whose ring of global sections is ind-étale over `A`.

## Main definitions

* `AlgebraicGeometry.ProEtale.indEtaleAlgebraBaseChange` — extension of scalars on ind-étale
  algebras along an arbitrary morphism of commutative rings.
* `AlgebraicGeometry.ProEtale.specUnderOp` — `Spec` as a functor from the opposite of the
  category of rings under `R` to schemes over `Spec R`.
* `AlgebraicGeometry.ProEtale.appSpec` — `Spec` as a functor from the opposite of the category
  of ind-étale algebras over the global sections of an affine scheme `X` to the full subcategory
  `AlgebraicGeometry.ProEtale.AppSmallProetale` of its small pro-étale site.

## Main results

* `AlgebraicGeometry.ProEtale.indEtale_iff_ind_underObj` — being an ind-étale algebra is
  membership in the object property whose full subcategory is the category of ind-étale
  algebras.
* `AlgebraicGeometry.ProEtale.indEtaleAlgebraBaseChange_quotient` — along a quotient map that
  extension of scalars is the quotient base change of Stacks 097P.
* `AlgebraicGeometry.ProEtale.appSpecEquivalence` — `appSpec` is an equivalence of categories.

The object property cutting out `AlgebraicGeometry.ProEtale.AppSmallProetale` is also recorded as
closed under isomorphisms.

## Implementation notes

An ind-étale algebra is a commutative ring under the base ring whose structure morphism is an
ind-étale morphism of rings, in the form `CategoryTheory.ObjectProperty.ind` of the object
property `CategoryTheory.MorphismProperty.underObj` of `CommRingCat.etale`. Relating this to
`StacksDraft.IndEtale` goes through the spelling by `CommAlgCat` and then through
`CategoryTheory.MorphismProperty.ind_iff_ind_underMk`.

The functor is the composite of `Spec` on under categories with `CategoryTheory.Over.map` along
the inverse of `AlgebraicGeometry.Scheme.isoSpec`, lifted to the subcategory of the pro-étale
site. Full faithfulness is inherited from that composite, both subcategory inclusions being
fully faithful. Essential surjectivity sends an affine object to its ring of global sections;
the two structure morphisms are identified by
`AlgebraicGeometry.Scheme.isoSpec_inv_naturality`.

Weak étaleness of the structure morphism of `Spec` of an ind-étale algebra combines Stacks 097N
with the affine criterion for weak étaleness, and ind-étaleness of the ring of global sections
of that `Spec` is transported along the unit of the `Γ`-`Spec` adjunction.

Extension of scalars is pushout in the under category, restricted to the ind-étale full
subcategories using stability of ind-étaleness under cobase change; for a quotient map it is
definitionally the functor of Stacks 097P.

## References

* [Stacks Project, Tag 097N](https://stacks.math.columbia.edu/tag/097N)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.ProEtale

/-- **Ind-étaleness as membership in the category of ind-étale algebras.** An algebra is a
filtered colimit of étale algebras exactly when the object it determines in the under category
of its base ring satisfies the object property whose full subcategory is `IndEtaleAlgebra`. -/
public theorem indEtale_iff_ind_underObj {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] :
    StacksDraft.IndEtale A B ↔
      ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj (X := CommRingCat.of A))
        (Under.mk (CommRingCat.ofHom (algebraMap A B))) :=
  StacksDraft.indEtale_iff.trans
    (CommAlgCat.ind_etale_iff_ind_algebraMap.trans
      (MorphismProperty.ind_iff_ind_underMk _))

/-- An ind-étale algebra as an object of the category of ind-étale algebras over its base. -/
public def IndEtaleAlgebra.ofIndEtale (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (h : StacksDraft.IndEtale A B) : IndEtaleAlgebra A :=
  ⟨Under.mk (CommRingCat.ofHom (algebraMap A B)), indEtale_iff_ind_underObj.mp h⟩

/-- An object of the category of ind-étale algebras over `A` is an ind-étale `A`-algebra. -/
public theorem indEtale_of_indEtaleAlgebra {A : Type u} [CommRing A] (V : IndEtaleAlgebra A) :
    @StacksDraft.IndEtale A V.obj.right _ _ V.obj.hom.hom.toAlgebra := by
  let : Algebra A V.obj.right := V.obj.hom.hom.toAlgebra
  exact indEtale_iff_ind_underObj.mpr V.property

/-- **Extension of scalars on ind-étale algebras.** Along an arbitrary morphism of commutative
rings `A →+* B`, pushout carries ind-étale `A`-algebras to ind-étale `B`-algebras. -/
public noncomputable def indEtaleAlgebraBaseChange {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : IndEtaleAlgebra A ⥤ IndEtaleAlgebra B :=
  (ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of B))).lift
    ((ObjectProperty.ι _) ⋙ Under.pushout (CommRingCat.ofHom φ))
    (fun V ↦ MorphismProperty.ind_underObj_pushout (CommRingCat.ofHom φ) V.property)

/-- Extension of scalars along a quotient map is the quotient base change of Stacks 097P. -/
public theorem indEtaleAlgebraBaseChange_quotient (A : Type u) [CommRing A] (I : Ideal A) :
    indEtaleAlgebraBaseChange (Ideal.Quotient.mk I) = indEtaleQuotientBaseChange A I :=
  rfl

variable (S : Scheme.{u})

/-- An object of the small pro-étale site isomorphic to an affine object with ind-étale ring of
global sections is again one. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms (IsAppSmall S) where
  of_iso {U U'} e hU := by
    let eL : U.left ≅ U'.left := (Scheme.ProEt.forget S ⋙ Over.forget S).mapIso e
    let : IsAffine U.left := hU.1
    let e' : Γ(U'.left, ⊤) ≅ Γ(U.left, ⊤) :=
      { hom := eL.hom.appTop
        inv := eL.inv.appTop
        hom_inv_id := by rw [← Scheme.Hom.comp_appTop, eL.inv_hom_id]; rfl
        inv_hom_id := by rw [← Scheme.Hom.comp_appTop, eL.hom_inv_id]; rfl }
    have hw : U.hom.appTop = U'.hom.appTop ≫ e'.hom := by
      rw [show U.hom = eL.hom ≫ U'.hom from (MorphismProperty.Over.w e.hom).symm,
        Scheme.Hom.comp_appTop]
    have hΓ : U'.hom.appTop = U.hom.appTop ≫ e'.inv := by
      rw [hw, Category.assoc, e'.hom_inv_id]
      exact (Category.comp_id _).symm
    refine ⟨IsAffine.of_isIso eL.inv, ?_⟩
    let : Algebra Γ(S, ⊤) Γ(U.left, ⊤) := U.hom.appTop.hom.toAlgebra
    let : Algebra Γ(S, ⊤) Γ(U'.left, ⊤) := U'.hom.appTop.hom.toAlgebra
    exact StacksDraft.indEtale_of_equiv (RingEquiv.refl Γ(S, ⊤))
      e'.symm.commRingCatIsoToRingEquiv
      (fun a ↦ (congrArg (fun f : Γ(S, ⊤) ⟶ _ ↦ f.hom a) hΓ).symm) hU.2

variable {S}

/-- A composite of weakly étale morphisms is weakly étale, as a lemma rather than an instance. -/
private theorem weaklyEtale_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : WeaklyEtale f) (hg : WeaklyEtale g) : WeaklyEtale (f ≫ g) :=
  inferInstance

/-- `Spec` as a functor from the opposite of the category of commutative rings under `R` to the
category of schemes over `Spec R`. -/
public noncomputable def specUnderOp (R : CommRingCat.{u}) : (Under R)ᵒᵖ ⥤ Over (Spec R) :=
  (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- The functor `specUnderOp R` is full. -/
instance (R : CommRingCat.{u}) : (specUnderOp R).Full :=
  inferInstanceAs <| Functor.Full <|
    (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- The functor `specUnderOp R` is faithful. -/
instance (R : CommRingCat.{u}) : (specUnderOp R).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

variable (X : Scheme.{u}) [IsAffine X]

/-- `Spec` of an ind-étale algebra over the global sections of an affine scheme `X`, as a scheme
over `X`. -/
public noncomputable def appSpecOver : (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ ⥤ Over X :=
  (ObjectProperty.ι _).op ⋙ specUnderOp Γ(X, ⊤) ⋙ Over.map X.isoSpec.inv

/-- The functor `appSpecOver X` is full. -/
instance : (appSpecOver X).Full :=
  inferInstanceAs <| Functor.Full <|
    (ObjectProperty.ι _).op ⋙ specUnderOp Γ(X, ⊤) ⋙ Over.map X.isoSpec.inv

/-- The functor `appSpecOver X` is faithful. -/
instance : (appSpecOver X).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    (ObjectProperty.ι _).op ⋙ specUnderOp Γ(X, ⊤) ⋙ Over.map X.isoSpec.inv

/-- The scheme underlying `Spec` of an ind-étale algebra is the spectrum of that algebra. -/
public theorem appSpecOver_obj_left (V : (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ) :
    ((appSpecOver X).obj V).left = Spec V.unop.obj.right :=
  rfl

/-- The structure morphism of `Spec` of an ind-étale algebra over the global sections of `X`. -/
public theorem appSpecOver_obj_hom (V : (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ) :
    ((appSpecOver X).obj V).hom = Spec.map V.unop.obj.hom ≫ X.isoSpec.inv :=
  rfl

/-- The structure morphism of `Spec` of an ind-étale algebra over the global sections of `X` is
weakly étale. -/
public theorem weaklyEtale_appSpecOver_hom (V : (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ) :
    WeaklyEtale ((appSpecOver X).obj V).hom := by
  have h : WeaklyEtale (Spec.map V.unop.obj.hom) :=
    weaklyEtale_specMap _
      (Algebra.weaklyEtale_of_ind_etale (indEtale_of_indEtaleAlgebra V.unop))
  rw [appSpecOver_obj_hom]
  exact weaklyEtale_comp _ _ h inferInstance

/-- The ring of global sections of `Spec` of an ind-étale algebra over the global sections of
`X` is ind-étale over the latter. -/
private theorem indEtale_appSpecOver_appTop (V : (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ) :
    @StacksDraft.IndEtale Γ(X, ⊤) Γ(((appSpecOver X).obj V).left, ⊤) _ _
      ((appSpecOver X).obj V).hom.appTop.hom.toAlgebra := by
  let : Algebra Γ(X, ⊤) V.unop.obj.right := V.unop.obj.hom.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(((appSpecOver X).obj V).left, ⊤) :=
    ((appSpecOver X).obj V).hom.appTop.hom.toAlgebra
  have key : V.unop.obj.hom ≫ (Scheme.ΓSpecIso V.unop.obj.right).inv =
      ((appSpecOver X).obj V).hom.appTop := by
    rw [appSpecOver_obj_hom, Scheme.Hom.comp_appTop, Stacks.RelativeSpec.isoSpec_inv_appTop,
      ← Scheme.ΓSpecIso_inv_naturality]
  exact StacksDraft.indEtale_of_equiv (RingEquiv.refl Γ(X, ⊤))
    (Scheme.ΓSpecIso V.unop.obj.right).symm.commRingCatIsoToRingEquiv
    (fun a ↦ congrArg (fun f : Γ(X, ⊤) ⟶ _ ↦ f.hom a) key) (indEtale_of_indEtaleAlgebra V.unop)

/-- `Spec` as a functor from the opposite of the category of ind-étale algebras over the global
sections of an affine scheme `X` to the small pro-étale site of `X`. -/
public noncomputable def appSpecProEt : (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ ⥤ X.ProEt :=
  MorphismProperty.Comma.lift (appSpecOver X) (weaklyEtale_appSpecOver_hom X)
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- `Spec` of an ind-étale algebra over the global sections of `X` is an affine object of the
small pro-étale site of `X` with ind-étale ring of global sections. -/
public theorem isAppSmall_appSpecProEt (V : (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ) :
    IsAppSmall X ((appSpecProEt X).obj V) :=
  ⟨inferInstanceAs (IsAffine (Spec V.unop.obj.right)), indEtale_appSpecOver_appTop X V⟩

/-- **`Spec` as a functor onto the site of affine ind-étale objects.** For an affine scheme `X`,
taking `Spec` sends an ind-étale algebra over the global sections of `X` to an affine object of
the small pro-étale site of `X` with ind-étale ring of global sections. -/
public noncomputable def appSpec : (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ ⥤ AppSmallProetale X :=
  (IsAppSmall X).lift (appSpecProEt X) (isAppSmall_appSpecProEt X)

/-- The composite of `appSpec` with both subcategory inclusions is `appSpecOver`. -/
public theorem appSpec_comp_forget :
    appSpec X ⋙ AppSmallProetale.inclusion X ⋙ Scheme.ProEt.forget X = appSpecOver X :=
  rfl

/-- The functor `appSpec X` is faithful. -/
instance : (appSpec X).Faithful :=
  Functor.Faithful.of_comp_eq (G := AppSmallProetale.inclusion X ⋙ Scheme.ProEt.forget X)
    (appSpec_comp_forget X)

/-- The functor `appSpec X` is full. -/
instance : (appSpec X).Full :=
  Functor.Full.of_comp_faithful_iso (G := AppSmallProetale.inclusion X ⋙ Scheme.ProEt.forget X)
    (eqToIso (appSpec_comp_forget X))

/-- The functor `appSpec X` is essentially surjective: every affine object of the small pro-étale
site of `X` with ind-étale ring of global sections is isomorphic to `Spec` of an ind-étale algebra
over the global sections of `X`. -/
instance : (appSpec X).EssSurj where
  mem_essImage U := by
    let : IsAffine U.obj.left := U.property.1
    let : Algebra Γ(X, ⊤) Γ(U.obj.left, ⊤) := U.obj.hom.appTop.hom.toAlgebra
    refine ⟨op (IndEtaleAlgebra.ofIndEtale Γ(X, ⊤) Γ(U.obj.left, ⊤) U.property.2), ⟨?_⟩⟩
    refine (AppSmallProetale.inclusion X ⋙ Scheme.ProEt.forget X).preimageIso
      (Over.isoMk U.obj.left.isoSpec.symm ?_)
    exact (Scheme.isoSpec_inv_naturality (X := U.obj.left) (Y := X) U.obj.hom).symm

/-- The functor `appSpec X` is an equivalence of categories. -/
instance : (appSpec X).IsEquivalence where

/-- **The site of affine ind-étale objects over an affine base is a category of algebras.** For
an affine scheme `X`, taking `Spec` is an equivalence from the opposite of the category of
ind-étale algebras over the global sections of `X` onto the full subcategory of its small
pro-étale site on the affine objects with ind-étale ring of global sections. -/
public noncomputable def appSpecEquivalence :
    (IndEtaleAlgebra Γ(X, ⊤))ᵒᵖ ≌ AppSmallProetale X :=
  (appSpec X).asEquivalence

end AlgebraicGeometry.ProEtale

end
