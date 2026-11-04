module

public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafHomContravariant
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.OverPushPull
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPull
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Sheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite

/-!
# Stacks 0D86 is natural in the semi-representable object

For a semi-representable object `K` of a site `(C, J)`, Stacks 0D86 identifies the product of
the push-pull functors of the components of `K` with the internal hom out of the sheafification
`F(K)^#`,

`∏ i, j_{K_i,*} j_{K_i}^{-1} ≅ SheafHom(F(K)^#, -)`,

naturally in the sheaf. This file proves that the identification is also natural in `K`: a
morphism `f : K ⟶ L` of semi-representable objects induces a restriction map on the left and
`SheafHom(F(f)^#, -)` on the right, and the square commutes.

The file also identifies the left-hand side above with a single push-pull. The componentwise
localization functor `j_K : C/K ⥤ C` is continuous and cocontinuous, so it has a morphism of
topoi whose push-pull `j_{K,*} j_K^{-1}` is a functor on sheaves on `(C, J)`; under the product
description of sheaves on `C/K` it is the product of the push-pulls of the components, hence by
Stacks 0D86 it is `SheafHom(F(K)^#, -)`.

## Main definitions

* `CategoryTheory.SemiRepresentable.pushPullContraMap`: restriction along `g : U ⟶ V` on
  push-pull, `j_{V,*} j_V^{-1} ⟶ j_{U,*} j_U^{-1}`, the conjugate of `h_g^# × -` under the two
  push-pull adjunctions of Stacks 0D7X.
* `CategoryTheory.SemiRepresentable.piPushPullMap`: the induced map on the product over the
  components, the left-hand vertical of the naturality square.
* `CategoryTheory.SemiRepresentable.piSheafHomMap` and `.coproductProdFunctorMap`: the
  corresponding maps on the product of internal homs and on the coproduct of the left adjoints.
* `CategoryTheory.SemiRepresentable.selfLocalizationSites`: the localization datum of a
  semi-representable object against itself, whose localization functor is `j_K`.
* `CategoryTheory.SemiRepresentable.componentPushforwardSliceIso`: the product of the
  componentwise pushforwards is pushforward along `j_K`, read through the product description of
  sheaves on `C/K`.
* `CategoryTheory.SemiRepresentable.pushPullProductIso`: push-pull along `j_K` is the product of
  the push-pulls of the components of `K`, the left-hand side of Stacks 0D86.
* `CategoryTheory.SemiRepresentable.pushPullSheafHomIso`: push-pull along `j_K` is
  `SheafHom(F(K)^#, -)`.

## Main results

* `CategoryTheory.SemiRepresentable.localizationPushforwardPullbackNatIsoSheafHom_naturality`:
  **the naturality square**, that the Stacks 0D86 isomorphism carries `piPushPullMap f` to
  `SheafHom(F(f)^#, -)`.
* `CategoryTheory.SemiRepresentable.pushPullContraMap_comp_sheafHomYonedaSheafify`: the
  single-object case, Stacks 0D7X natural in the object.
* `CategoryTheory.SemiRepresentable.pushPullContraMap_id`, `.pushPullContraMap_comp` and
  `.piPushPullMap_id`: functoriality, which is what identifies these maps as restriction rather
  than something degenerate.
* `CategoryTheory.SemiRepresentable.componentOverForget_isContinuous` and
  `.componentOverForget_isCocontinuous`: the componentwise localization functor `j_K` is
  continuous and cocontinuous for the componentwise localized topology, which is Stacks 0D85
  read through `selfLocalizationSites`.
* `CategoryTheory.SemiRepresentable.componentPushforwardSliceIso_inv_app_counit`: the counit
  property that characterises `componentPushforwardSliceIso`, i.e. uniqueness of adjoints in the
  form a diagram chase can use.
* `CategoryTheory.SemiRepresentable.pushPullProductIso_hom_app`: the component of
  `pushPullProductIso`, which is `rfl` because the isomorphism is built as a single composite of
  two whiskerings rather than as a chain through associators.

## Implementation notes

This is an input of the *source's* fork proof of the fullness clause of Stacks 0D8E: the fork
exhibiting `a_* a^{-1} G` as an equalizer has its two legs indexed by the two face maps
`K_1 ⟶ K_0`, and without naturality in the semi-representable object those face maps cannot be
carried across the Stacks 0D86 isomorphism. For a hypercovering of the final presheaf that
clause is proved from local fullness of `j_total` instead, in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringUnit.lean`; what the fork route is
still wanted for is the hypercovering-of-an-object setting of Stacks 0D8K, where that input is
not available and the gap is recorded in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringObjectDescent.lean`.

Every map here is a mate: `pushPullContraMap` is the conjugate of `h_g^# × -`, and the proof of
the naturality square is the corresponding `CategoryTheory.conjugateEquiv` calculus, reduced to
two computations — that the internal-hom transition is the mate of the coproduct transition
(`piSheafHomMap_eq_conjugateEquiv`), and that the coproduct transition corresponds to
`F(f)^# × -` (`coproductProdFunctorMap_comp_coproductProdFunctorIso`).

Proofs here must `show` the fully unfolded `∏ᶜ` or `∐` form before applying
`CategoryTheory.Limits.Pi.hom_ext` or `.Sigma.hom_ext`: `Pi.functor` and `Sigma.functor` are
semireducible, so `rw` and `simp` otherwise refuse to fire on a goal mixing
`(productPushPullFunctor J K).obj X` with `∏ᶜ (fun i ↦ …)`. This is the discipline
`StacksFrontier/CategoryTheory/Sites/SemiRepresentable/PushPull.lean` itself uses.

`pushPullProductIso` takes the topology of `C/K` as a parameter together with a proof that it is
the componentwise localized topology, rather than using that topology directly. The reason is
the intended consumer: the component site of a simplicial semi-representable object carries its
topology as the topology generated by a family of coverings, which is only *propositionally* the
componentwise localized one, so a statement about the latter would not apply to it without a
transport of the whole isomorphism. With the topology as a parameter the transport is the single
`subst` at the head of the proof.

Three `example`s record the definitional identifications the construction of
`pushPullProductIso` relies on: that restriction along `j_K` followed by the product description
of sheaves on `C/K` *is* the family of componentwise restrictions, that the functor of
`formalCoproductSliceSheavesEquivalence` *is* `restrictSheaf`, and that the composite of the
componentwise restrictions with the product of the componentwise pushforwards *is*
`productPushPullFunctor`. None of the three is provable by `simp`, and each is silently relied on,
so a change to any of the definitions involved should fail here rather than inside the proof.

## References

* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D7X](https://stacks.math.columbia.edu/tag/0D7X)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.OverShriek

universe u₁ u₂ v₁ v₂ u

namespace Stacks.CategoryTheory

open CategoryTheory

/-- Conjugation and transport of both adjunctions along isomorphisms of their left adjoints. -/
theorem conjugateEquiv_ofNatIsoLeft {A : Type u₁} {B : Type u₂} [Category.{v₁} A]
    [Category.{v₂} B] {L₁ L₁' L₂ L₂' : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (α : L₂' ⟶ L₁') :
    conjugateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α =
      conjugateEquiv adj₁ adj₂ (e₂.hom ≫ α ≫ e₁.inv) := by
  ext d
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]

/-- A transformation of right adjoints whose adjunct is the obvious one is the conjugate. -/
theorem eq_conjugateEquiv {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) (t : R₁ ⟶ R₂)
    (h : ∀ d, L₂.map (t.app d) ≫ adj₂.counit.app d = α.app (R₁.obj d) ≫ adj₁.counit.app d) :
    t = conjugateEquiv adj₁ adj₂ α := by
  ext d
  refine (adj₂.homEquiv (R₁.obj d) d).symm.injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, h d,
    conjugateEquiv_counit adj₁ adj₂ α d]

/-- Conjugating by `α` and comparing two right adjoints of each left adjoint commutes. -/
private theorem conjugateEquiv_comp_comm_of_id {A : Type u₁} {B : Type u₂} [Category.{v₁} A]
    [Category.{v₂} B] {L₁ L₂ : A ⥤ B} {R₁ R₂ R₃ R₄ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : L₂ ⊣ R₃) (adj₄ : L₁ ⊣ R₄) (α : L₂ ⟶ L₁) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ (𝟙 _) =
      conjugateEquiv adj₁ adj₄ (𝟙 _) ≫ conjugateEquiv adj₄ adj₃ α := by
  rw [conjugateEquiv_comp, conjugateEquiv_comp, Category.id_comp, Category.comp_id]

end Stacks.CategoryTheory

namespace CategoryTheory.SemiRepresentable

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek
open Stacks.CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### Naming the data of Stacks 0D86 -/

/-- The sheafified representable of a component. -/
abbrev componentSheafifiedYoneda (K : FormalCoproduct.{u} C) (i : K.I) : Sheaf J (Type u) :=
  (presheafToSheaf J (Type u)).obj ((yoneda (C := C)).obj (K.obj i))

/-- `F(K)^#`. -/
abbrev formalCoproductSheafifiedYoneda (K : FormalCoproduct.{u} C) : Sheaf J (Type u) :=
  (presheafToSheaf J (Type u)).obj ((FormalCoproduct.yoneda (C := C)).obj K)

/-- `L_K = ∐ i, (F(K_i)^# × -)`. -/
abbrev coproductProdFunctor (K : FormalCoproduct.{u} C) : Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
  Functor.pi' (fun i ↦ prod.functor.obj (componentSheafifiedYoneda J K i)) ⋙ Sigma.functor K.I

/-- `R_K = ∏ i, SheafHom(F(K_i)^#, -)`. -/
abbrev productSheafHomFunctor (K : FormalCoproduct.{u} C) : Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
  Functor.pi' (fun i ↦ SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K i)) ⋙
    Pi.functor K.I

/-- `PP_K = ∏ i, j_{i,*} j_i^{-1}`, the left-hand side of Stacks 0D86. -/
abbrev productPushPullFunctor (K : FormalCoproduct.{u} C) : Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
  Functor.pi' (fun i : K.I ↦
      localizationPullback (K.obj i) J ⋙ localizationPushforward (K.obj i) J) ⋙
    Pi.functor K.I

/-- The push-pull adjunction at a single object, Stacks 0D7X's left adjoint. -/
abbrev prodPushPullAdjunctionObj (U : C) :
    prod.functor.obj ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) ⊣
      localizationPullback U J ⋙ localizationPushforward U J :=
  prodOverPullbackOverPushforwardAdjunction U J

/-- The internal-hom adjunction at a single object. -/
abbrev prodSheafHomAdjunctionObj (U : C) :
    prod.functor.obj ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) ⊣
      SheafHomAdj.sheafHomFunctor ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) :=
  SheafHomAdj.prodSheafHomAdjunction _

/-- The coproduct/product adjunction of Stacks 0D86. -/
abbrev coproductProductAdjunction (K : FormalCoproduct.{u} C) :
    coproductProdFunctor J K ⊣ productSheafHomFunctor J K :=
  localizationProductSheafHomAdjunction J K (fun i ↦ componentSheafifiedYoneda J K i)

/-- The comparison of the two left adjoints used in Stacks 0D86. -/
abbrev coproductProdFunctorIso (K : FormalCoproduct.{u} C) :
    coproductProdFunctor J K ≅ prod.functor.obj (formalCoproductSheafifiedYoneda J K) :=
  coproductOfProductsNatIso J (fun i ↦ componentSheafifiedYoneda J K i) ≪≫ NatIso.ofComponents
    (fun X ↦ (show (prod.functor.obj (∐ (fun i ↦ componentSheafifiedYoneda J K i))).obj X ≅
        (prod.functor.obj (formalCoproductSheafifiedYoneda J K)).obj X from
      Limits.prod.mapIso (sheafifiedFormalCoproductIso J K).symm (Iso.refl X))) (by
      intro X Y f
      exact Limits.prod.map_swap f (sheafifiedFormalCoproductIso J K).symm.hom)

/-- The internal-hom adjunction out of `F(K)^#`. -/
abbrev prodSheafHomAdjunctionTotal (K : FormalCoproduct.{u} C) :
    prod.functor.obj (formalCoproductSheafifiedYoneda J K) ⊣
      SheafHomAdj.sheafHomFunctor (formalCoproductSheafifiedYoneda J K) :=
  SheafHomAdj.prodSheafHomAdjunction (formalCoproductSheafifiedYoneda J K)

/-- The internal-hom adjunction out of `F(K)^#`, with its left adjoint spelled as a coproduct. -/
abbrev coproductSheafHomAdjunction (K : FormalCoproduct.{u} C) :
    coproductProdFunctor J K ⊣ SheafHomAdj.sheafHomFunctor (formalCoproductSheafifiedYoneda J K) :=
  (prodSheafHomAdjunctionTotal J K).ofNatIsoLeft (coproductProdFunctorIso J K).symm

/-- The product of the Stacks 0D7X isomorphisms. -/
abbrev productPushPullIsoSheafHom (K : FormalCoproduct.{u} C) :
    productPushPullFunctor J K ≅ productSheafHomFunctor J K :=
  Functor.isoWhiskerRight
    (NatIso.pi' (fun i ↦ (OverShriek.sheafHomYonedaSheafifyNatIso (K.obj i) J).symm))
    (Pi.functor K.I)

/-- The isomorphism `localizationPushforwardPullbackNatIsoSheafHom J K` is the composite of the
product of the componentwise isomorphisms `productPushPullIsoSheafHom J K` with the comparison of
the right adjoints of `coproductProductAdjunction J K` and `coproductSheafHomAdjunction J K`. -/
theorem localizationPushforwardPullbackNatIsoSheafHom_eq (K : FormalCoproduct.{u} C) :
    localizationPushforwardPullbackNatIsoSheafHom J K =
      productPushPullIsoSheafHom J K ≪≫
        Adjunction.rightAdjointUniq (coproductProductAdjunction J K)
          (coproductSheafHomAdjunction J K) :=
  rfl

/-! ### Stacks 0D7X is natural in the object -/

/-- The sheafified representable morphism attached to `g : U ⟶ V`. -/
abbrev sheafifiedYonedaMap {U V : C} (g : U ⟶ V) :
    (presheafToSheaf J (Type u)).obj (yoneda.obj U) ⟶
      (presheafToSheaf J (Type u)).obj (yoneda.obj V) :=
  (presheafToSheaf J (Type u)).map ((yoneda (C := C)).map g)

/-- **Restriction along `g : U ⟶ V`, on push-pull.** The conjugate, under the two push-pull
adjunctions of Stacks 0D7X, of `h_g^# × - : h_U^# × - ⟶ h_V^# × -`. -/
def pushPullContraMap {U V : C} (g : U ⟶ V) :
    localizationPullback V J ⋙ localizationPushforward V J ⟶
      localizationPullback U J ⋙ localizationPushforward U J :=
  conjugateEquiv (prodPushPullAdjunctionObj J V) (prodPushPullAdjunctionObj J U)
    (prod.functor.map (sheafifiedYonedaMap J g))

/-- **Stacks 0D7X, naturally in the object.** -/
theorem pushPullContraMap_comp_sheafHomYonedaSheafify {U V : C} (g : U ⟶ V) :
    pushPullContraMap J g ≫ (sheafHomYonedaSheafifyNatIso U J).inv =
      (sheafHomYonedaSheafifyNatIso V J).inv ≫
        SheafHomAdj.sheafHomContraMap (sheafifiedYonedaMap J g) := by
  exact conjugateEquiv_comp_comm_of_id (prodPushPullAdjunctionObj J V)
    (prodPushPullAdjunctionObj J U) (prodSheafHomAdjunctionObj J U)
    (prodSheafHomAdjunctionObj J V) (prod.functor.map (sheafifiedYonedaMap J g))

/-- Restriction along an identity is the identity. -/
theorem pushPullContraMap_id (U : C) :
    pushPullContraMap J (𝟙 U) =
      𝟙 (localizationPullback U J ⋙ localizationPushforward U J) := by
  rw [pushPullContraMap, show sheafifiedYonedaMap J (𝟙 U) =
      𝟙 ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) by
    rw [sheafifiedYonedaMap, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id],
    CategoryTheory.Functor.map_id, conjugateEquiv_id]

/-- Restriction along a composite is the composite of the restrictions, in the other order. -/
theorem pushPullContraMap_comp {U V W : C} (g : U ⟶ V) (h : V ⟶ W) :
    pushPullContraMap J (g ≫ h) =
      pushPullContraMap J h ≫ pushPullContraMap J g := by
  rw [pushPullContraMap, pushPullContraMap, pushPullContraMap,
    show sheafifiedYonedaMap J (g ≫ h) = sheafifiedYonedaMap J g ≫ sheafifiedYonedaMap J h by
      rw [sheafifiedYonedaMap, sheafifiedYonedaMap, sheafifiedYonedaMap,
        CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp],
    CategoryTheory.Functor.map_comp,
    conjugateEquiv_comp (prodPushPullAdjunctionObj J W) (prodPushPullAdjunctionObj J V)
      (prodPushPullAdjunctionObj J U)]

/-! ### The three transitions attached to a morphism of semi-representable objects -/

variable {K L : FormalCoproduct.{u} C}

/-- The component of `f` as a map of sheafified representables. -/
abbrev phiSheafify (f : K ⟶ L) (i : K.I) :
    componentSheafifiedYoneda J K i ⟶ componentSheafifiedYoneda J L (f.f i) :=
  sheafifiedYonedaMap J (f.φ i)

/-- `F(f)^# : F(K)^# ⟶ F(L)^#`. -/
abbrev totSheafify (f : K ⟶ L) :
    formalCoproductSheafifiedYoneda J K ⟶ formalCoproductSheafifiedYoneda J L :=
  (presheafToSheaf J (Type u)).map ((FormalCoproduct.yoneda (C := C)).map f)

/-- **The transition on push-pull induced by a morphism of semi-representable objects.**
Project to the component `f.f i`, then restrict along `f.φ i`. -/
def piPushPullMap (f : K ⟶ L) : productPushPullFunctor J L ⟶ productPushPullFunctor J K where
  app X := Pi.lift (fun i : K.I ↦
    Pi.π (fun j : L.I ↦ (localizationPullback (L.obj j) J ⋙
      localizationPushforward (L.obj j) J).obj X) (f.f i) ≫
      (pushPullContraMap J (f.φ i)).app X)
  naturality X Y h := by
    change Limits.Pi.map (fun j : L.I ↦ (localizationPullback (L.obj j) J ⋙
          localizationPushforward (L.obj j) J).map h) ≫
        Pi.lift (fun i : K.I ↦
          Pi.π (fun j : L.I ↦ (localizationPullback (L.obj j) J ⋙
            localizationPushforward (L.obj j) J).obj Y) (f.f i) ≫
            (pushPullContraMap J (f.φ i)).app Y) =
      Pi.lift (fun i : K.I ↦
          Pi.π (fun j : L.I ↦ (localizationPullback (L.obj j) J ⋙
            localizationPushforward (L.obj j) J).obj X) (f.f i) ≫
            (pushPullContraMap J (f.φ i)).app X) ≫
        Limits.Pi.map (fun j : K.I ↦ (localizationPullback (K.obj j) J ⋙
          localizationPushforward (K.obj j) J).map h)
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, Limits.Pi.lift_π, Limits.Pi.map_π, Limits.Pi.lift_π_assoc,
      Limits.Pi.map_π_assoc]
    rw [(pushPullContraMap J (f.φ i)).naturality h]

/-- The `i`-th component of the push-pull transition. -/
@[reassoc]
theorem piPushPullMap_app_π (f : K ⟶ L) (X : Sheaf J (Type u)) (i : K.I) :
    (piPushPullMap J f).app X ≫
        Pi.π (fun j : K.I ↦ (localizationPullback (K.obj j) J ⋙
          localizationPushforward (K.obj j) J).obj X) i =
      Pi.π (fun j : L.I ↦ (localizationPullback (L.obj j) J ⋙
        localizationPushforward (L.obj j) J).obj X) (f.f i) ≫
        (pushPullContraMap J (f.φ i)).app X :=
  Limits.Pi.lift_π _ _

/-- **The transition on internal homs induced by a morphism of semi-representable objects.** -/
def piSheafHomMap (f : K ⟶ L) : productSheafHomFunctor J L ⟶ productSheafHomFunctor J K where
  app X := Pi.lift (fun i : K.I ↦
    Pi.π (fun j : L.I ↦
      (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L j)).obj X) (f.f i) ≫
      (SheafHomAdj.sheafHomContraMap (phiSheafify J f i)).app X)
  naturality X Y h := by
    change Limits.Pi.map (fun j : L.I ↦
          (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L j)).map h) ≫
        Pi.lift (fun i : K.I ↦
          Pi.π (fun j : L.I ↦
            (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L j)).obj Y) (f.f i) ≫
            (SheafHomAdj.sheafHomContraMap (phiSheafify J f i)).app Y) =
      Pi.lift (fun i : K.I ↦
          Pi.π (fun j : L.I ↦
            (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L j)).obj X) (f.f i) ≫
            (SheafHomAdj.sheafHomContraMap (phiSheafify J f i)).app X) ≫
        Limits.Pi.map (fun j : K.I ↦
          (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K j)).map h)
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, Limits.Pi.lift_π, Limits.Pi.map_π, Limits.Pi.lift_π_assoc,
      Limits.Pi.map_π_assoc]
    rw [(SheafHomAdj.sheafHomContraMap (phiSheafify J f i)).naturality h]

/-- The `i`-th component of the internal-hom transition. -/
@[reassoc]
theorem piSheafHomMap_app_π (f : K ⟶ L) (X : Sheaf J (Type u)) (i : K.I) :
    (piSheafHomMap J f).app X ≫
        Pi.π (fun j : K.I ↦
          (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K j)).obj X) i =
      Pi.π (fun j : L.I ↦
        (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L j)).obj X) (f.f i) ≫
        (SheafHomAdj.sheafHomContraMap (phiSheafify J f i)).app X :=
  Limits.Pi.lift_π _ _

/-- The transition on the coproduct left adjoints. -/
def coproductProdFunctorMap (f : K ⟶ L) : coproductProdFunctor J K ⟶ coproductProdFunctor J L where
  app X := Limits.Sigma.desc (fun i : K.I ↦
    (prod.functor.map (phiSheafify J f i)).app X ≫
      Limits.Sigma.ι (fun j : L.I ↦
        (prod.functor.obj (componentSheafifiedYoneda J L j)).obj X) (f.f i))
  naturality X Y h := by
    change Limits.Sigma.map (fun j : K.I ↦
          (prod.functor.obj (componentSheafifiedYoneda J K j)).map h) ≫
        Limits.Sigma.desc (fun i : K.I ↦
          (prod.functor.map (phiSheafify J f i)).app Y ≫
            Limits.Sigma.ι (fun j : L.I ↦
              (prod.functor.obj (componentSheafifiedYoneda J L j)).obj Y) (f.f i)) =
      Limits.Sigma.desc (fun i : K.I ↦
          (prod.functor.map (phiSheafify J f i)).app X ≫
            Limits.Sigma.ι (fun j : L.I ↦
              (prod.functor.obj (componentSheafifiedYoneda J L j)).obj X) (f.f i)) ≫
        Limits.Sigma.map (fun j : L.I ↦ (prod.functor.obj (componentSheafifiedYoneda J L j)).map h)
    apply Limits.Sigma.hom_ext
    intro i
    simp only [Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_map,
      Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_map_assoc]
    rw [NatTrans.naturality_assoc]

/-- The `i`-th component of the coproduct transition. -/
@[reassoc]
theorem coproductProdFunctorMap_ι_app (f : K ⟶ L) (X : Sheaf J (Type u)) (i : K.I) :
    Limits.Sigma.ι (fun j : K.I ↦ (prod.functor.obj (componentSheafifiedYoneda J K j)).obj X) i ≫
        (coproductProdFunctorMap J f).app X =
      (prod.functor.map (phiSheafify J f i)).app X ≫
        Limits.Sigma.ι (fun j : L.I ↦
          (prod.functor.obj (componentSheafifiedYoneda J L j)).obj X) (f.f i) :=
  Limits.Sigma.ι_desc _ _

/-! ### The three squares -/

/-- The `i`-th component of the product of the Stacks 0D7X isomorphisms. -/
theorem productPushPullIsoSheafHom_hom_app_π
    (K : FormalCoproduct.{u} C) (X : Sheaf J (Type u)) (i : K.I) :
    (productPushPullIsoSheafHom J K).hom.app X ≫
        Pi.π (fun j : K.I ↦
          (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K j)).obj X) i =
      Pi.π (fun j : K.I ↦ (localizationPullback (K.obj j) J ⋙
        localizationPushforward (K.obj j) J).obj X) i ≫
        (OverShriek.sheafHomYonedaSheafifyNatIso (K.obj i) J).inv.app X :=
  Limits.Pi.map_π _ i

/-- **The `productPushPullIsoSheafHom` square.** The push-pull transition and the internal-hom
transition agree under the product of the Stacks 0D7X isomorphisms. -/
theorem piPushPullMap_comp_productPushPullIsoSheafHom (f : K ⟶ L) :
    piPushPullMap J f ≫ (productPushPullIsoSheafHom J K).hom =
      (productPushPullIsoSheafHom J L).hom ≫ piSheafHomMap J f := by
  apply NatTrans.ext
  funext X
  show Pi.lift (fun i : K.I ↦
        Pi.π (fun j : L.I ↦ (localizationPullback (L.obj j) J ⋙
          localizationPushforward (L.obj j) J).obj X) (f.f i) ≫
          (pushPullContraMap J (f.φ i)).app X) ≫
      Limits.Pi.map (fun j : K.I ↦
        (OverShriek.sheafHomYonedaSheafifyNatIso (K.obj j) J).inv.app X) =
    Limits.Pi.map (fun j : L.I ↦
        (OverShriek.sheafHomYonedaSheafifyNatIso (L.obj j) J).inv.app X) ≫
      Pi.lift (fun i : K.I ↦
        Pi.π (fun j : L.I ↦
          (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L j)).obj X) (f.f i) ≫
          (SheafHomAdj.sheafHomContraMap (phiSheafify J f i)).app X)
  apply Limits.Pi.hom_ext
  intro i
  have key : (pushPullContraMap J (f.φ i)).app X ≫
        (OverShriek.sheafHomYonedaSheafifyNatIso (K.obj i) J).inv.app X =
      (OverShriek.sheafHomYonedaSheafifyNatIso (L.obj (f.f i)) J).inv.app X ≫
        (SheafHomAdj.sheafHomContraMap (phiSheafify J f i)).app X :=
    congrFun (congrArg NatTrans.app
      (pushPullContraMap_comp_sheafHomYonedaSheafify J (f.φ i))) X
  simp only [Category.assoc, Limits.Pi.lift_π, Limits.Pi.map_π, Limits.Pi.lift_π_assoc,
    Limits.Pi.map_π_assoc]
  rw [key]

/-- The counit of the coproduct/product adjunction of Stacks 0D86, written out. -/
theorem coproductProductAdjunction_counit_eq (K : FormalCoproduct.{u} C) (X : Sheaf J (Type u)) :
    (coproductProductAdjunction J K).counit.app X =
      Limits.Sigma.desc (fun j : K.I ↦
        (prod.functor.obj (componentSheafifiedYoneda J K j)).map
            (Pi.π (fun l : K.I ↦
              (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K l)).obj X) j) ≫
          (SheafHomAdj.prodSheafHomAdjunction (componentSheafifiedYoneda J K j)).counit.app X) := by
  have h : (coproductProductAdjunction J K).counit.app X =
      Limits.Sigma.desc (fun j : K.I ↦
        (prod.functor.obj (componentSheafifiedYoneda J K j)).map
            (𝟙 (∏ᶜ fun l : K.I ↦
                (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K l)).obj X) ≫
              Pi.π (fun l : K.I ↦
                (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K l)).obj X) j) ≫
          (SheafHomAdj.prodSheafHomAdjunction (componentSheafifiedYoneda J K j)).counit.app X) :=
    rfl
  rw [h]
  simp only [Category.id_comp]
  rfl

/-- The counit form of the contravariant action of the internal hom. -/
theorem sheafHomContraMap_counit {G G' : Sheaf J (Type u)} (g : G ⟶ G')
    (X : Sheaf J (Type u)) :
    (prod.functor.obj G).map ((SheafHomAdj.sheafHomContraMap g).app X) ≫
        (SheafHomAdj.prodSheafHomAdjunction G).counit.app X =
      (prod.functor.map g).app ((SheafHomAdj.sheafHomFunctor G').obj X) ≫
        (SheafHomAdj.prodSheafHomAdjunction G').counit.app X :=
  conjugateEquiv_counit (SheafHomAdj.prodSheafHomAdjunction G')
    (SheafHomAdj.prodSheafHomAdjunction G) (prod.functor.map g) X

/-- **The internal-hom transition is the conjugate of the coproduct transition.** -/
theorem piSheafHomMap_eq_conjugateEquiv (f : K ⟶ L) :
    piSheafHomMap J f = conjugateEquiv (coproductProductAdjunction J L)
      (coproductProductAdjunction J K) (coproductProdFunctorMap J f) := by
  refine eq_conjugateEquiv _ _ _ _ (fun X ↦ ?_)
  show Limits.Sigma.map (fun j : K.I ↦ (prod.functor.obj (componentSheafifiedYoneda J K j)).map
        (Pi.lift (fun i : K.I ↦
          Pi.π (fun l : L.I ↦
            (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L l)).obj X) (f.f i) ≫
            (SheafHomAdj.sheafHomContraMap (phiSheafify J f i)).app X))) ≫
      Limits.Sigma.desc (fun j : K.I ↦
        (prod.functor.obj (componentSheafifiedYoneda J K j)).map
            (𝟙 (∏ᶜ fun l : K.I ↦
                (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K l)).obj X) ≫
              Pi.π (fun l : K.I ↦
                (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J K l)).obj X) j) ≫
          (SheafHomAdj.prodSheafHomAdjunction (componentSheafifiedYoneda J K j)).counit.app X) =
    Limits.Sigma.desc (fun i : K.I ↦
        (prod.functor.map (phiSheafify J f i)).app
            (∏ᶜ fun l : L.I ↦
              (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L l)).obj X) ≫
          Limits.Sigma.ι
            (fun j : L.I ↦ (prod.functor.obj (componentSheafifiedYoneda J L j)).obj
              (∏ᶜ fun l : L.I ↦
                (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L l)).obj X)) (f.f i)) ≫
      Limits.Sigma.desc (fun j : L.I ↦
        (prod.functor.obj (componentSheafifiedYoneda J L j)).map
            (𝟙 (∏ᶜ fun l : L.I ↦
                (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L l)).obj X) ≫
              Pi.π (fun l : L.I ↦
                (SheafHomAdj.sheafHomFunctor (componentSheafifiedYoneda J L l)).obj X) j) ≫
          (SheafHomAdj.prodSheafHomAdjunction (componentSheafifiedYoneda J L j)).counit.app X)
  apply Limits.Sigma.hom_ext
  intro i
  simp only [Category.id_comp, Category.assoc, Limits.Sigma.ι_map_assoc,
    Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc]
  rw [← Functor.map_comp_assoc, Limits.Pi.lift_π, Functor.map_comp, Category.assoc,
    sheafHomContraMap_counit, NatTrans.naturality_assoc]

/-! ### Compatibility of the coproduct transition with the comparison of left adjoints -/

/-- The sheafified coproduct injections are compatible with `F(f)^#`. -/
theorem sheafifiedFormalCoproductIso_inv_map (f : K ⟶ L) (i : K.I) :
    phiSheafify J f i ≫ Limits.Sigma.ι (fun j : L.I ↦ componentSheafifiedYoneda J L j) (f.f i) ≫
        (sheafifiedFormalCoproductIso J L).inv =
      Limits.Sigma.ι (fun j : K.I ↦ componentSheafifiedYoneda J K j) i ≫
        (sheafifiedFormalCoproductIso J K).inv ≫ totSheafify J f := by
  have hinv : ∀ (M : FormalCoproduct.{u} C) (j : M.I) {Z : Sheaf J (Type u)}
      (g : formalCoproductSheafifiedYoneda J M ⟶ Z),
      Limits.Sigma.ι (fun l : M.I ↦ componentSheafifiedYoneda J M l) j ≫
          (sheafifiedFormalCoproductIso J M).inv ≫ g =
        (presheafToSheaf J (Type u)).map
            (Limits.Sigma.ι (fun l : M.I ↦ (yoneda (C := C)).obj (M.obj l)) j) ≫ g := by
    intro M j Z g
    rw [← Category.assoc]
    exact congrArg (· ≫ g) (ι_comp_sigmaComparison (presheafToSheaf J (Type u))
      (fun l : M.I ↦ (yoneda (C := C)).obj (M.obj l)) j)
  rw [hinv K i (totSheafify J f)]
  refine Eq.trans (congrArg (phiSheafify J f i ≫ ·)
    (ι_comp_sigmaComparison (presheafToSheaf J (Type u))
      (fun l : L.I ↦ (yoneda (C := C)).obj (L.obj l)) (f.f i))) ?_
  show (presheafToSheaf J (Type u)).map ((yoneda (C := C)).map (f.φ i)) ≫
      (presheafToSheaf J (Type u)).map
        (Limits.Sigma.ι (fun l : L.I ↦ (yoneda (C := C)).obj (L.obj l)) (f.f i)) =
    (presheafToSheaf J (Type u)).map
        (Limits.Sigma.ι (fun l : K.I ↦ (yoneda (C := C)).obj (K.obj l)) i) ≫
      (presheafToSheaf J (Type u)).map ((FormalCoproduct.yoneda (C := C)).map f)
  have hyon : Limits.Sigma.ι (fun l : K.I ↦ (yoneda (C := C)).obj (K.obj l)) i ≫
        (FormalCoproduct.yoneda (C := C)).map f =
      (yoneda (C := C)).map (f.φ i) ≫
        Limits.Sigma.ι (fun l : L.I ↦ (yoneda (C := C)).obj (L.obj l)) (f.f i) :=
    Limits.Sigma.ι_desc _ i
  rw [← Functor.map_comp]
  exact (congrArg (presheafToSheaf J (Type u)).map hyon.symm).trans
    ((presheafToSheaf J (Type u)).map_comp _ _)

/-- **The coproduct transition corresponds to `F(f)^# × -`.** -/
theorem coproductProdFunctorMap_comp_coproductProdFunctorIso (f : K ⟶ L) :
    (coproductProdFunctorIso J K).inv ≫ coproductProdFunctorMap J f ≫
      (coproductProdFunctorIso J L).hom =
      prod.functor.map (totSheafify J f) := by
  have hcop : ∀ (M : FormalCoproduct.{u} C) (j : M.I) (X : Sheaf J (Type u))
      {Z : Sheaf J (Type u)}
      (g : (prod.functor.obj (∐ (fun l : M.I ↦ componentSheafifiedYoneda J M l))).obj X ⟶ Z),
      Limits.Sigma.ι (fun l : M.I ↦ (prod.functor.obj (componentSheafifiedYoneda J M l)).obj X) j ≫
          (coproductOfProductsIso J (fun l : M.I ↦ componentSheafifiedYoneda J M l) X).hom ≫ g =
        (prod.functor.map
          (Limits.Sigma.ι (fun l : M.I ↦ componentSheafifiedYoneda J M l) j)).app X ≫ g := by
    intro M j X Z g
    rw [← Category.assoc]
    exact congrArg (· ≫ g)
      (coproductOfProductsIso_ι_hom J (fun l : M.I ↦ componentSheafifiedYoneda J M l) X j)
  rw [Iso.inv_comp_eq]
  apply NatTrans.ext
  funext X
  show Limits.Sigma.desc (fun i : K.I ↦ (prod.functor.map (phiSheafify J f i)).app X ≫
          Limits.Sigma.ι (fun j : L.I ↦
            (prod.functor.obj (componentSheafifiedYoneda J L j)).obj X) (f.f i)) ≫
        (coproductOfProductsIso J (fun l : L.I ↦ componentSheafifiedYoneda J L l) X).hom ≫
          (prod.functor.map (sheafifiedFormalCoproductIso J L).inv).app X =
      ((coproductOfProductsIso J (fun l : K.I ↦ componentSheafifiedYoneda J K l) X).hom ≫
          (prod.functor.map (sheafifiedFormalCoproductIso J K).inv).app X) ≫
        (prod.functor.map (totSheafify J f)).app X
  apply Limits.Sigma.hom_ext
  intro i
  rw [Limits.Sigma.ι_desc_assoc, Category.assoc, hcop L (f.f i) X, Category.assoc,
    hcop K i X]
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  exact congrArg (fun h ↦ (prod.functor.map h).app X)
    (sheafifiedFormalCoproductIso_inv_map J f i)

/-! ### Stacks 0D86, naturally in the semi-representable object -/

/-- The conjugate of the coproduct transition, read through the internal-hom adjunctions, is the
contravariant action of the internal hom on `F(f)^#`. -/
theorem conjugateEquiv_coproductSheafHomAdjunction_coproductProdFunctorMap (f : K ⟶ L) :
    conjugateEquiv (coproductSheafHomAdjunction J L) (coproductSheafHomAdjunction J K)
        (coproductProdFunctorMap J f) =
      SheafHomAdj.sheafHomContraMap (totSheafify J f) := by
  rw [show coproductSheafHomAdjunction J L =
        (prodSheafHomAdjunctionTotal J L).ofNatIsoLeft (coproductProdFunctorIso J L).symm from rfl,
    show coproductSheafHomAdjunction J K =
        (prodSheafHomAdjunctionTotal J K).ofNatIsoLeft (coproductProdFunctorIso J K).symm from rfl,
    conjugateEquiv_ofNatIsoLeft]
  exact congrArg
    (conjugateEquiv (prodSheafHomAdjunctionTotal J L) (prodSheafHomAdjunctionTotal J K))
    (coproductProdFunctorMap_comp_coproductProdFunctorIso J f)

/-- **Stacks 0D86, natural in the semi-representable object.** For a morphism `f : K ⟶ L` of
semi-representable objects of a small site `(C, J)`, the square

```
∏ j, j_{L_j,*} j_{L_j}^{-1} ----≅----> SheafHom(F(L)^#, -)
         |                                    |
   piPushPullMap f                 SheafHom(F(f)^#, -)
         v                                    v
∏ i, j_{K_i,*} j_K_i^{-1} ----≅----> SheafHom(F(K)^#, -)
```

commutes, the two horizontal isomorphisms being
`CategoryTheory.SemiRepresentable.localizationPushforwardPullbackNatIsoSheafHom`, i.e. Stacks
0D86 at `L` and at `K`. -/
theorem localizationPushforwardPullbackNatIsoSheafHom_naturality (f : K ⟶ L) :
    piPushPullMap J f ≫ (localizationPushforwardPullbackNatIsoSheafHom J K).hom =
      (localizationPushforwardPullbackNatIsoSheafHom J L).hom ≫
        SheafHomAdj.sheafHomContraMap (totSheafify J f) := by
  have hK : (localizationPushforwardPullbackNatIsoSheafHom J K).hom =
      (productPushPullIsoSheafHom J K).hom ≫
        (Adjunction.rightAdjointUniq (coproductProductAdjunction J K)
          (coproductSheafHomAdjunction J K)).hom := rfl
  have hL : (localizationPushforwardPullbackNatIsoSheafHom J L).hom =
      (productPushPullIsoSheafHom J L).hom ≫
        (Adjunction.rightAdjointUniq (coproductProductAdjunction J L)
          (coproductSheafHomAdjunction J L)).hom := rfl
  have hsq : piSheafHomMap J f ≫
        (Adjunction.rightAdjointUniq (coproductProductAdjunction J K)
          (coproductSheafHomAdjunction J K)).hom =
      (Adjunction.rightAdjointUniq (coproductProductAdjunction J L)
        (coproductSheafHomAdjunction J L)).hom ≫
        SheafHomAdj.sheafHomContraMap (totSheafify J f) := by
    rw [piSheafHomMap_eq_conjugateEquiv,
      ← conjugateEquiv_coproductSheafHomAdjunction_coproductProdFunctorMap]
    exact conjugateEquiv_comp_comm_of_id (coproductProductAdjunction J L)
      (coproductProductAdjunction J K) (coproductSheafHomAdjunction J K)
      (coproductSheafHomAdjunction J L) (coproductProdFunctorMap J f)
  rw [hK, hL, ← Category.assoc, piPushPullMap_comp_productPushPullIsoSheafHom, Category.assoc,
    hsq, ← Category.assoc]

/-- The push-pull transition of an identity morphism is the identity: the transition is not
degenerate. -/
theorem piPushPullMap_id (K : FormalCoproduct.{u} C) :
    piPushPullMap J (𝟙 K) = 𝟙 (productPushPullFunctor J K) := by
  apply NatTrans.ext
  funext X
  show Pi.lift (fun i : K.I ↦
      Pi.π (fun j : K.I ↦ (localizationPullback (K.obj j) J ⋙
        localizationPushforward (K.obj j) J).obj X) i ≫
        (pushPullContraMap J (𝟙 (K.obj i))).app X) =
    𝟙 (∏ᶜ fun j : K.I ↦ (localizationPullback (K.obj j) J ⋙
      localizationPushforward (K.obj j) J).obj X)
  apply Limits.Pi.hom_ext
  intro i
  rw [Limits.Pi.lift_π, pushPullContraMap_id, NatTrans.id_app, Category.comp_id,
    Category.id_comp]

/-! ### Push-pull along the componentwise localization functor -/

/-- The localization datum of a semi-representable object against itself: the site `(C, J)`, the
object `M` in both slots and the identity morphism between them. Its localization functor is the
componentwise localization functor `j_M : C/M ⥤ C` and its source topology is the componentwise
localized topology, so it is what produces the continuity and cocontinuity of `j_M`. -/
abbrev selfLocalizationSites (M : FormalCoproduct.{u} C) : LocalizationSites.{u} C J :=
  ⟨M, M, 𝟙 M⟩

/-- **Stacks 0D85.** The componentwise localization functor `j_M : C/M ⥤ C` is continuous for the
componentwise localized topology. -/
instance componentOverForget_isContinuous (M : FormalCoproduct.{u} C) :
    (componentOverForget M).IsContinuous (componentwiseTopology J M) J :=
  LocalizationSites.localizationFunctor_isContinuous (selfLocalizationSites J M)

/-- **Stacks 0D85.** The componentwise localization functor `j_M : C/M ⥤ C` is cocontinuous for
the componentwise localized topology. -/
instance componentOverForget_isCocontinuous (M : FormalCoproduct.{u} C) :
    (componentOverForget M).IsCocontinuous (componentwiseTopology J M) J :=
  LocalizationSites.localizationFunctor_isCocontinuous (selfLocalizationSites J M)

section DefinitionalProbes

variable (M : FormalCoproduct.{u} C)

example : (componentOverForget M).sheafPushforwardContinuous (Type u)
      (componentwiseTopology J M) J ⋙ restrictSheaf J M (Type u) =
    Functor.pi' (fun i : M.I => localizationPullback (M.obj i) J) := rfl

example : (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor =
    restrictSheaf J M (Type u) := rfl

example : Functor.pi' (fun i : M.I => localizationPullback (M.obj i) J) ⋙
      (Functor.pi (fun i : M.I => localizationPushforward (M.obj i) J) ⋙ Pi.functor M.I) =
    productPushPullFunctor J M := rfl

end DefinitionalProbes

/-- **The product of the componentwise pushforwards is pushforward along `j_M`, read through the
product description of sheaves on `C/M`.** Restriction along `j_M` followed by the product
description is the family of componentwise restrictions, so the two functors here are both right
adjoint to that family and therefore agree. -/
def componentPushforwardSliceIso (M : FormalCoproduct.{u} C) :
    Functor.pi (fun i : M.I => localizationPushforward (M.obj i) J) ⋙ Pi.functor M.I ≅
      (formalCoproductSliceSheavesEquivalence J M (Type u)).1.inverse ⋙
        (componentOverForget M).sheafPushforwardCocontinuous (Type u)
          (componentwiseTopology J M) J :=
  (componentLocalizationAdjunction J M).rightAdjointUniq
    ((((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
          (componentwiseTopology J M) J).comp
        (formalCoproductSliceSheavesEquivalence J M (Type u)).1.toAdjunction).ofNatIsoLeft
      (Iso.refl _))

/-- **The defining property of `componentPushforwardSliceIso`**: it is the comparison of two
right adjoints of the family of componentwise restrictions, so its inverse carries the counit of
the componentwise localization adjunction to the counit of push-pull along `j_M` composed with
the counit of the product description of sheaves on `C/M`. -/
theorem componentPushforwardSliceIso_inv_app_counit (M : FormalCoproduct.{u} C)
    (Z : (i : M.I) → Sheaf (J.over (M.obj i)) (Type u)) :
    (Functor.pi' fun i : M.I => localizationPullback (M.obj i) J).map
          ((componentPushforwardSliceIso J M).inv.app Z) ≫
        (componentLocalizationAdjunction J M).counit.app Z =
      (formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.map
          (((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
              (componentwiseTopology J M) J).counit.app
            ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.inverse.obj Z)) ≫
        (formalCoproductSliceSheavesEquivalence J M (Type u)).1.counit.app Z := by
  have h : (Functor.pi' fun i : M.I => localizationPullback (M.obj i) J).map
        ((componentPushforwardSliceIso J M).inv.app Z) ≫
      (componentLocalizationAdjunction J M).counit.app Z =
      ((((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
            (componentwiseTopology J M) J).comp
          (formalCoproductSliceSheavesEquivalence J M (Type u)).1.toAdjunction).ofNatIsoLeft
        (Iso.refl _)).counit.app Z :=
    Adjunction.rightAdjointUniq_hom_app_counit _ _ Z
  rw [h]
  simp only [Adjunction.ofNatIsoLeft_counit, Iso.refl_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, NatTrans.id_app, Adjunction.comp_counit_app,
    Equivalence.toAdjunction_counit, Functor.comp_obj, Category.id_comp]
  rfl

/-- **Push-pull along `j_M` is the left-hand side of Stacks 0D86.** Push-pull along the
componentwise localization functor `j_M : C/M ⥤ C` of a semi-representable object `M` is the
product of the push-pull functors of the components of `M`.

It is the unit of the product description of sheaves on `C/M`, inserted between the restriction
and the pushforward, followed by `componentPushforwardSliceIso`; the latter is where uniqueness
of adjoints is used.

The topology on `C/M` is a parameter, together with a proof that it is the componentwise
localized topology, so that the statement applies verbatim to a site whose topology is only
propositionally that one. -/
def pushPullProductIso (M : FormalCoproduct.{u} C)
    (Jc : GrothendieckTopology (ComponentOver M)) (hJc : Jc = componentwiseTopology J M)
    [(componentOverForget M).IsContinuous Jc J]
    [(componentOverForget M).IsCocontinuous Jc J] :
    (componentOverForget M).sheafPushforwardContinuous (Type u) Jc J ⋙
        (componentOverForget M).sheafPushforwardCocontinuous (Type u) Jc J ≅
      productPushPullFunctor J M := by
  subst hJc
  exact Functor.isoWhiskerLeft
        ((componentOverForget M).sheafPushforwardContinuous (Type u)
          (componentwiseTopology J M) J)
        (Functor.isoWhiskerRight (formalCoproductSliceSheavesEquivalence J M (Type u)).1.unitIso
          ((componentOverForget M).sheafPushforwardCocontinuous (Type u)
            (componentwiseTopology J M) J)) ≪≫
      Functor.isoWhiskerLeft (Functor.pi' fun i : M.I => localizationPullback (M.obj i) J)
        (componentPushforwardSliceIso J M).symm

/-- The component of `pushPullProductIso` at the componentwise localized topology: the unit of
the product description of sheaves on `C/M`, pushed forward along `j_M`, then
`componentPushforwardSliceIso`. -/
theorem pushPullProductIso_hom_app (M : FormalCoproduct.{u} C) (X : Sheaf J (Type u)) :
    (pushPullProductIso J M (componentwiseTopology J M) rfl).hom.app X =
      ((componentOverForget M).sheafPushforwardCocontinuous (Type u)
            (componentwiseTopology J M) J).map
          ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.unitIso.hom.app
            (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).obj X)) ≫
        (componentPushforwardSliceIso J M).inv.app
          ((formalCoproductSliceSheavesEquivalence J M (Type u)).1.functor.obj
            (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).obj X)) :=
  rfl

/-- **Push-pull along `j_M` is the internal hom out of `F(M)^#`.** Composing
`pushPullProductIso` with Stacks 0D86 identifies push-pull along the componentwise localization
functor of a semi-representable object `M` with `SheafHom(F(M)^#, -)`. -/
def pushPullSheafHomIso (M : FormalCoproduct.{u} C)
    (Jc : GrothendieckTopology (ComponentOver M)) (hJc : Jc = componentwiseTopology J M)
    [(componentOverForget M).IsContinuous Jc J]
    [(componentOverForget M).IsCocontinuous Jc J] :
    (componentOverForget M).sheafPushforwardContinuous (Type u) Jc J ⋙
        (componentOverForget M).sheafPushforwardCocontinuous (Type u) Jc J ≅
      SheafHomAdj.sheafHomFunctor (formalCoproductSheafifiedYoneda J M) :=
  pushPullProductIso J M Jc hJc ≪≫ localizationPushforwardPullbackNatIsoSheafHom J M

end CategoryTheory.SemiRepresentable

end
