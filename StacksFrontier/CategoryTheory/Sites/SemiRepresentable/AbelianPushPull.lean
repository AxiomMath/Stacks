module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPull
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation

/-!
# Push-pull along the localization at a semi-representable object, for abelian coefficients

Let `(C, J)` be a small site and `K = {U i}` a semi-representable object of `C`. Stacks 0D86
identifies, for a sheaf of sets `F`, the result of restricting `F` to the localized sites
`C / U i` and pushing it forward again, one component at a time, with the internal hom out of
the sheafification of the semi-representable presheaf `F(K)`. This file records the same formula
for abelian coefficients:
`∏ i, j_{i,*} j_i^{-1} F ≅ ℋom'(F(K)^#, F)` for `F` an abelian sheaf, naturally in `F`,
where `ℋom'(G, F)` is, in the primed notation of Stacks 04TP, the sheaf
`V ↦ Mor_{Sh(C/V)}(G|_V, F|_V)` carrying the abelian-group structure of `F`. This is the form in
which Stacks 0D8F invokes Stacks 0D86.

## Main definitions

* `CategoryTheory.AbelianSheafReading.endofunctor`: the abelian reading of an endofunctor of
  sheaves of sets which preserves finite products — internalize the group operations, apply the
  functor to commutative group objects, and read the resulting operations off on sections again.
  This is the passage of Stacks 04DB, and the same construction by which the terms of the Čech
  complex of Stacks 0D79 are built from the direct images of sheaves of sets.
* `CategoryTheory.SemiRepresentable.abelianLocalizationPushPull`: the abelian reading of
  `∏ i, j_{i,*} j_i^{-1}`.
* `CategoryTheory.SemiRepresentable.abelianSheafHomPrime`: the abelian reading of
  `SheafHom(F(K)^#, -)`, i.e. the source's `ℋom'(F(K)^#, -)` on abelian sheaves.

## Main results

* `CategoryTheory.AbelianSheafReading.endofunctorNatTrans` and
  `CategoryTheory.AbelianSheafReading.endofunctorNatIso`: the abelian reading is functorial, so a
  natural transformation, resp. isomorphism, of finite-product-preserving endofunctors of sheaves
  of sets induces one of their abelian readings.
* `CategoryTheory.AbelianSheafReading.endofunctor_add`: the addition on the sections of an abelian
  reading, in terms of the lax-monoidal structure of the endofunctor and the addition of the
  coefficient sheaf.
* `CategoryTheory.SemiRepresentable.abelianLocalizationPushforwardPullbackNatIsoSheafHomPrime`:
  **Stacks 0D86 for abelian coefficients.**

## Implementation notes

Both sides of Stacks 0D86 are right adjoints, hence preserve finite products, hence act on
commutative group objects of the topos of sheaves of sets; since an abelian sheaf is the same
thing as such a commutative group object (Stacks 04DB, here
`CategoryTheory.Sites.AbelianSheaf.equivalence`), both sides act on abelian sheaves,
and the isomorphism of Stacks 0D86 is carried along, because taking commutative group objects is
functorial in the finite-product-preserving functor.

The reading used here is the one of
`CategoryTheory.SimplicialSiteSituation.Augmentation.abelianConjugation`, which is how the terms
`a_{n,*}a_n^{-1}F` of the Čech complex of Stacks 0D79 are produced from the direct images of
sheaves of sets; there is a single `internalSheaf` and `externalSheaf`, so the two readings agree.
That is why the formula is stated for the source's primed internal hom `ℋom'(F(K)^#, -)` rather
than for the abelian internal hom `ℋom(ℤ_{F(K)}^#, -)` of Stacks 0D7X: passing from one to the
other is the separate comparison `ℋom'(G, F) = ℋom(ℤ_G, F)`, which is not carried out here.

The underlying sheaf of sets of the abelian reading is the original functor applied to the
underlying sheaf of sets; this is `CategoryTheory.AbelianSheafReading.endofunctor_forget`.

## References

* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 04TP](https://stacks.math.columbia.edu/tag/04TP)
* [Stacks Project, Tag 0D8F](https://stacks.math.columbia.edu/tag/0D8F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

attribute [local instance] CategoryTheory.sheafTypeCartesian CategoryTheory.sheafTypeBraided

attribute [local instance] Functor.Braided.ofChosenFiniteProducts

/-- `SheafHom(G, -)` preserves finite products, being a right adjoint by Stacks 0BWQ. -/
noncomputable instance preservesFiniteProducts_sheafHomFunctor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (𝒢 : Sheaf J (Type u)) :
    PreservesFiniteProducts (SheafHomAdj.sheafHomFunctor 𝒢) :=
  have : PreservesLimitsOfSize.{u, u} (SheafHomAdj.sheafHomFunctor 𝒢) :=
    (SheafHomAdj.prodSheafHomAdjunction 𝒢).rightAdjoint_preservesLimits
  inferInstance

namespace AbelianSheafReading

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- The abelian reading of an endofunctor `P` of sheaves of sets which preserves finite products:
internalize the group operations of an abelian sheaf, apply `P` to the resulting commutative
group object, and read the operations of the result off on sections again. This is the passage of
Stacks 04DB, and it is the single-site case of
`CategoryTheory.SimplicialSiteSituation.Augmentation.abelianConjugation`. -/
def endofunctor (P : Sheaf J (Type u) ⥤ Sheaf J (Type u)) [P.Braided] :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  Sites.AbelianSheaf.internalSheaf J ⋙ P.mapCommGrp ⋙ Sites.AbelianSheaf.externalSheaf J

/-- The underlying sheaf of sets of the abelian reading of `P` at an abelian sheaf `F` is `P`
applied to the underlying sheaf of sets of `F`. -/
theorem endofunctor_forget (P : Sheaf J (Type u) ⥤ Sheaf J (Type u)) [P.Braided]
    (F : Sheaf J AddCommGrpCat.{u}) :
    (sheafCompose J (forget AddCommGrpCat.{u})).obj ((endofunctor J P).obj F) =
      P.obj ((sheafCompose J (forget AddCommGrpCat.{u})).obj F) := rfl

/-- The abelian reading is functorial in the endofunctor: a natural transformation of
finite-product-preserving endofunctors of sheaves of sets induces a natural transformation of
their abelian readings. -/
def endofunctorNatTrans {P Q : Sheaf J (Type u) ⥤ Sheaf J (Type u)} [P.Braided] [Q.Braided]
    (f : P ⟶ Q) : endofunctor J P ⟶ endofunctor J Q :=
  Functor.whiskerLeft (Sites.AbelianSheaf.internalSheaf J)
    (Functor.whiskerRight (Functor.mapCommGrpNatTrans f) (Sites.AbelianSheaf.externalSheaf J))

/-- The abelian reading of the identity transformation is the identity. -/
@[simp]
theorem endofunctorNatTrans_id (P : Sheaf J (Type u) ⥤ Sheaf J (Type u)) [P.Braided] :
    endofunctorNatTrans J (𝟙 P) = 𝟙 (endofunctor J P) := by
  rw [endofunctorNatTrans, show Functor.mapCommGrpNatTrans (𝟙 P) = 𝟙 P.mapCommGrp from rfl,
    Functor.whiskerRight_id', Functor.whiskerLeft_id']
  rfl

/-- The abelian reading of a composite of transformations is the composite of their abelian
readings. -/
theorem endofunctorNatTrans_comp {P Q R : Sheaf J (Type u) ⥤ Sheaf J (Type u)} [P.Braided]
    [Q.Braided] [R.Braided] (f : P ⟶ Q) (g : Q ⟶ R) :
    endofunctorNatTrans J (f ≫ g) =
      endofunctorNatTrans J f ≫ endofunctorNatTrans J g := by
  rw [endofunctorNatTrans, endofunctorNatTrans, endofunctorNatTrans,
    show Functor.mapCommGrpNatTrans (f ≫ g) =
      Functor.mapCommGrpNatTrans f ≫ Functor.mapCommGrpNatTrans g from rfl,
    Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
  rfl

/-- The abelian reading is functorial in the endofunctor: a natural isomorphism of
finite-product-preserving endofunctors of sheaves of sets induces a natural isomorphism of their
abelian readings. -/
def endofunctorNatIso {P Q : Sheaf J (Type u) ⥤ Sheaf J (Type u)} [P.Braided] [Q.Braided]
    (e : P ≅ Q) : endofunctor J P ≅ endofunctor J Q where
  hom := endofunctorNatTrans J e.hom
  inv := endofunctorNatTrans J e.inv
  hom_inv_id := by rw [← endofunctorNatTrans_comp, e.hom_inv_id, endofunctorNatTrans_id]
  inv_hom_id := by rw [← endofunctorNatTrans_comp, e.inv_hom_id, endofunctorNatTrans_id]

section Add

open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Sites.AbelianSheaf

/-- The lax-monoidal comparison of the underlying-presheaf functor on sheaves of sets is the
formation of a section of a product of sheaves from its two components: it is inverse to the
product comparison, whose components are the two projections. -/
theorem laxMonoidal_μ_sheafToPresheaf_app (X Y : Sheaf J (Type u)) (U : Cᵒᵖ) (x : X.obj.obj U)
    (y : Y.obj.obj U) :
    (Functor.LaxMonoidal.μ (sheafToPresheaf J (Type u)) X Y).app U (x, y) =
      SheafHomAdj.pair X Y x y := by
  set z := (Functor.LaxMonoidal.μ (sheafToPresheaf J (Type u)) X Y).app U (x, y) with hz
  have hfst : (prod.fst : X ⨯ Y ⟶ X).hom.app U z = x :=
    congrFun (congrArg (fun f => (ConcreteCategory.hom f).toFun) (NatTrans.congr_app
      (Functor.Monoidal.μ_fst (F := sheafToPresheaf J (Type u)) X Y) U)) (x, y)
  have hsnd : (prod.snd : X ⨯ Y ⟶ Y).hom.app U z = y :=
    congrFun (congrArg (fun f => (ConcreteCategory.hom f).toFun) (NatTrans.congr_app
      (Functor.Monoidal.μ_snd (F := sheafToPresheaf J (Type u)) X Y) U)) (x, y)
  refine Eq.trans (SheafHomAdj.pair_fst_snd X Y z).symm ?_
  rw [hfst, hsnd]

/-- The addition on the sections of the abelian sheaf read off a commutative group object in
sheaves of sets is the internal multiplication, evaluated on the pair of the two sections. -/
theorem externalSheaf_add (R : CommGrp (Sheaf J (Type u))) (U : Cᵒᵖ)
    (a b : ((externalSheaf J).obj R).obj.obj U) :
    Additive.toMul (a + b) =
      (MonObj.mul (X := R.X)).hom.app U
        (SheafHomAdj.pair R.X R.X (Additive.toMul a) (Additive.toMul b)) := by
  rw [← laxMonoidal_μ_sheafToPresheaf_app]
  rfl

/-- **The addition on the sections of the abelian reading of an endofunctor `P` of sheaves of
sets.** The sections of `(endofunctor J P).obj F` over `U` are the sections of `P` applied to the
underlying sheaf of sets of `F`, and their addition is obtained by pairing them into a section of
the product and then applying `P` to the addition of `F`. -/
theorem endofunctor_add (P : Sheaf J (Type u) ⥤ Sheaf J (Type u)) [P.Braided]
    (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (a b : ((endofunctor J P).obj F).obj.obj U) :
    Additive.toMul (a + b) =
      (Functor.LaxMonoidal.μ P _ _ ≫
          P.map (MonObj.mul (X := ((internalSheaf J).obj F).X))).hom.app U
        (SheafHomAdj.pair _ _ (Additive.toMul a) (Additive.toMul b)) :=
  externalSheaf_add J (P.mapCommGrp.obj ((internalSheaf J).obj F)) U a b

/-- The abelian reading of a transformation of endofunctors acts on sections by the
transformation itself, applied to the underlying sheaf of sets of the coefficient sheaf. -/
theorem endofunctorNatTrans_app_hom_app {P Q : Sheaf J (Type u) ⥤ Sheaf J (Type u)} [P.Braided]
    [Q.Braided] (f : P ⟶ Q) (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (a : ((endofunctor J P).obj F).obj.obj U) :
    Additive.toMul (((endofunctorNatTrans J f).app F).hom.app U a) =
      (f.app ((internalSheaf J).obj F).X).hom.app U (Additive.toMul a) := rfl

/-- The internal multiplication of the commutative group object attached to an abelian sheaf is
the addition of the abelian sheaf, read on the pair of two sections. -/
theorem internalSheaf_mul_pair_app (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (a b : F.obj.obj U) :
    (MonObj.mul (X := ((internalSheaf J).obj F).X)).hom.app U
        (SheafHomAdj.pair _ _ a b) = a + b := by
  set g := ((internalExternalIso J).inv.app F).hom.app U
  have h := externalSheaf_add J ((internalSheaf J).obj F) U (g a) (g b)
  have h' := map_add ((((internalExternalIso J).hom.app F).hom.app U).hom) (g a) (g b)
  exact h.symm.trans h'

end Add

end AbelianSheafReading

namespace SemiRepresentable

open CategoryTheory.OverShriek CategoryTheory.AbelianSheafReading

variable {C : Type u} [SmallCategory C]

/-- The product over the components of `K` of the localization push-pull functors
`j_{i,*} j_i^{-1}`, as an endofunctor of sheaves of sets: the left-hand side of Stacks 0D86. -/
abbrev localizationPushPull (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) :
    Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
  Functor.pi' (fun i : K.I =>
    localizationPullback (K.obj i) J ⋙ localizationPushforward (K.obj i) J) ⋙ Pi.functor K.I

/-- The internal-hom functor `SheafHom(F(K)^#, -)` of sheaves of sets: the right-hand side of
Stacks 0D86. -/
@[sga "3 I 1.7.3" "special case"]
abbrev sheafHomSemiRepresentable (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) :
    Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
  SheafHomAdj.sheafHomFunctor
    ((presheafToSheaf J (Type u)).obj ((FormalCoproduct.yoneda (C := C)).obj K))

/-- `∏ i, j_{i,*} j_i^{-1}` preserves finite products: by Stacks 0D86 it is isomorphic to
`SheafHom(F(K)^#, -)`, which does. -/
noncomputable local instance preservesFiniteProducts_localizationPushPull
    (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) :
    PreservesFiniteProducts (localizationPushPull J K) :=
  ⟨fun _ => preservesLimitsOfShape_of_natIso
    (localizationPushforwardPullbackNatIsoSheafHom J K).symm⟩

/-- The abelian reading of `∏ i, j_{i,*} j_i^{-1}`: restriction to the localized sites `C / U i`
followed by direct image, one component at a time, for abelian coefficients. -/
def abelianLocalizationPushPull (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  endofunctor J (localizationPushPull J K)

/-- The abelian reading of `SheafHom(F(K)^#, -)`: the source's `ℋom'(F(K)^#, -)` of Stacks 04TP,
whose value at an abelian sheaf `F` is the sheaf `V ↦ Mor_{Sh(C/V)}(F(K)^#|_V, F|_V)` with the
abelian-group structure of `F`. -/
def abelianSheafHomPrime (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  endofunctor J (sheafHomSemiRepresentable J K)

/-- **Stacks 0D86 for abelian coefficients.** For a semi-representable object `K = {U i}` of a
small site `(C, J)`, the product of the localization push-pull functors `j_{i,*} j_i^{-1}` on
abelian sheaves is naturally isomorphic to `ℋom'(F(K)^#, -)`.

This is the source's `j_* j^{-1} F = ℋom'(F(K)^#, F)` under the product description of sheaves on
`C / K`, for `F` an abelian sheaf and naturally in `F`, which is the form in which Stacks 0D8F
uses Stacks 0D86. Both sides are the abelian readings of Stacks 04DB of the corresponding
functors of sheaves of sets — the same reading by which the terms `a_{n,*}a_n^{-1}F` of the Čech
complex of Stacks 0D79 are built — and the isomorphism is the one of Stacks 0D86 carried through
that reading, which is possible because both functors preserve finite products and the reading is
functorial in the finite-product-preserving functor. -/
@[stacks 0D86 "the abelian form: abelian-sheaf coefficients, primed internal hom"]
def abelianLocalizationPushforwardPullbackNatIsoSheafHomPrime
    (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) :
    abelianLocalizationPushPull J K ≅ abelianSheafHomPrime J K :=
  endofunctorNatIso J (localizationPushforwardPullbackNatIsoSheafHom J K)

/-- The underlying sheaf of sets of the abelian `∏ i, j_{i,*} j_i^{-1}` is the one of sheaves of
sets applied to the underlying sheaf of sets. -/
theorem abelianLocalizationPushPull_forget (J : GrothendieckTopology C)
    (K : FormalCoproduct.{u} C) (F : Sheaf J AddCommGrpCat.{u}) :
    (sheafCompose J (forget AddCommGrpCat.{u})).obj
        ((abelianLocalizationPushPull J K).obj F) =
      (localizationPushPull J K).obj
        ((sheafCompose J (forget AddCommGrpCat.{u})).obj F) := rfl

/-- The underlying sheaf of sets of `ℋom'(F(K)^#, F)` is `SheafHom(F(K)^#, -)` applied to the
underlying sheaf of sets of `F`. -/
theorem abelianSheafHomPrime_forget (J : GrothendieckTopology C)
    (K : FormalCoproduct.{u} C) (F : Sheaf J AddCommGrpCat.{u}) :
    (sheafCompose J (forget AddCommGrpCat.{u})).obj ((abelianSheafHomPrime J K).obj F) =
      (sheafHomSemiRepresentable J K).obj
        ((sheafCompose J (forget AddCommGrpCat.{u})).obj F) := rfl

end SemiRepresentable

end CategoryTheory

end
