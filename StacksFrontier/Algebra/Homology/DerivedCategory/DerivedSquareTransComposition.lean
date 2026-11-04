module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# Derived comparison maps along exact pullbacks, and their composition

Let `Γ₀ : 𝒞₀ ⥤ ℳ₀` and `Γ : 𝒞 ⥤ ℳ` be additive functors ("global sections"), let `P : 𝒞₀ ⥤ 𝒞`
and `r : ℳ ⥤ ℳ₀` be exact ("pullback" and "restriction of scalars"), and let
`α : Γ₀ ⟶ P ⋙ Γ ⋙ r` be a natural transformation.  Deriving `α`, splitting the right derived
functor of the composite by the canonical transformation of [Stacks, Tag 05T2], and replacing
the derived functors of the exact functors by the induced ones gives a transformation

`derivedSquareTrans α : RΓ₀ ⟶ P ⋙ RΓ ⋙ r`

of functors `D⁺(𝒞₀) ⥤ D⁺(ℳ₀)`.

**The construction is compatible with composition**: for two such squares
`α₁ : Γ₀ ⟶ P₁ ⋙ Γ₁ ⋙ r₁` and `α₂ : Γ₁ ⟶ P₂ ⋙ Γ₂ ⋙ r₂`, and a third `α : Γ₀ ⟶ P ⋙ Γ₂ ⋙ r` which
is their pasting along isomorphisms `P₁ ⋙ P₂ ≅ P` and `r₂ ⋙ r₁ ≅ r`, the derived transformation
of `α` is the pasting of the two derived transformations
(`derivedSquareTrans'_comp`), and the same holds for the maps they induce on a single object
placed in degree zero (`derivedSquareMap_comp`).

## Main definitions

* `CategoryTheory.Functor.derivedSquareTrans`, `derivedSquareTrans'` — the derived transformation
  of a square, with `RP` respectively with the induced functor of `P`.
* `CategoryTheory.Functor.derivedSquareMap` — the same at a single object placed in degree zero.

## Main results

* `CategoryTheory.Functor.derivedSquareTrans'_comp` — the derived transformation of a pasted
  square is the pasting of the derived transformations.
* `CategoryTheory.Functor.derivedSquareMap_comp` — the same at a single object placed in degree
  zero.

## References

* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

section Exact

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- **The comparison `RF ≅ F` of an exact functor, after the unit.**  The unit of `RF` at a
complex followed by the comparison is the inverse of the factorization of the induced functor
through the localization. -/
theorem unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app
    (K : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F).hom.app
          (DerivedCategory.Plus.Qh.obj K) =
      F.mapDerivedCategoryPlusFactorsh.inv.app K := by
  have : IsIso F.rightDerivedFunctorPlusUnit :=
    isIso_rightDerivedFunctorPlusUnit_of_preservesHomology F
  have : Localization.Lifting (DerivedCategory.Plus.Qh (C := A))
      (HomotopyCategory.Plus.quasiIso A)
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) F.rightDerivedFunctorPlus :=
    ⟨(asIso F.rightDerivedFunctorPlusUnit).symm⟩
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K) :=
    NatIso.isIso_app_of_isIso F.rightDerivedFunctorPlusUnit K
  have h : (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F).hom.app
      (DerivedCategory.Plus.Qh.obj K) =
        CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app K) ≫
          F.mapDerivedCategoryPlusFactorsh.inv.app K := by
    simp only [rightDerivedFunctorPlusIsoMapDerivedCategoryPlus, Localization.liftNatIso_hom,
      Localization.liftNatTrans_app]
    rw [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
    rfl
  rw [h, IsIso.hom_inv_id_assoc]

/-- **`F̄(X[0]) ≅ F(X)[0]`** for an exact `F`, where `F̄` is the functor `F` induces on bounded
below derived categories: `CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIso` read
through `RF ≅ F̄`. -/
def mapDerivedCategoryPlusObjSingleIso (X : A) :
    F.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X) :=
  ((rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F).app _).symm ≪≫
    F.rightDerivedFunctorPlusObjSingleIso X

/-- The inverse of the comparison `RF ≅ F̄` at a complex, followed by the inverse of the unit, is
the factorization of `F̄` through the localization. -/
theorem rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_inv_app_comp_inv_unit
    (K : HomotopyCategory.Plus A) [IsIso (F.rightDerivedFunctorPlusUnit.app K)] :
    (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F).inv.app
        (DerivedCategory.Plus.Qh.obj K) ≫ CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app K) =
      F.mapDerivedCategoryPlusFactorsh.hom.app K := by
  rw [← cancel_mono (F.mapDerivedCategoryPlusFactorsh.inv.app K), Category.assoc,
    Iso.hom_inv_id_app, ← unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app,
    IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app]
  rfl

/-- **The closed form of `mapDerivedCategoryPlusObjSingleIso`**: the factorization of `F̄` through
the localization at the single complex, read through the factorization of the single functor
through the bounded below homotopy category on each side. -/
theorem mapDerivedCategoryPlusObjSingleIso_hom (X : A) :
    (F.mapDerivedCategoryPlusObjSingleIso X).hom =
      F.mapDerivedCategoryPlus.map ((singleFunctorPlusIsoCompQh (A := A) 0).hom.app X) ≫
        F.mapDerivedCategoryPlusFactorsh.hom.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X) ≫
        DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫
        (singleFunctorPlusIsoCompQh (A := B) 0).inv.app (F.obj X) := by
  have : IsIso F.rightDerivedFunctorPlusUnit :=
    isIso_rightDerivedFunctorPlusUnit_of_preservesHomology F
  have : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) :=
    NatIso.isIso_app_of_isIso F.rightDerivedFunctorPlusUnit _
  show (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F).inv.app _ ≫
    F.rightDerivedFunctorPlus.map ((singleFunctorPlusIsoCompQh (A := A) 0).hom.app X) ≫
    CategoryTheory.inv (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) ≫
    DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫
    (singleFunctorPlusIsoCompQh (A := B) 0).inv.app (F.obj X) = _
  rw [← NatTrans.naturality_assoc]
  exact CategoryTheory.whisker_eq _
    ((reassoc_of% (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_inv_app_comp_inv_unit F
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X))) _)

/-- **The identity comparison `RF ≅ 𝟭` of an exact `F ≅ 𝟭`, read on induced functors**: the
factorization of `F̄` through the localization, followed by `F̄ ≅ RF ≅ 𝟭`, is `e` applied
degreewise. -/
theorem mapDerivedCategoryPlusFactorsh_inv_comp_idIso_hom_app {A : Type*} [Category* A]
    [Abelian A] [HasDerivedCategory A] [EnoughInjectives A] (F : A ⥤ A) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : F ≅ 𝟭 A)
    (L : HomotopyCategory.Plus A) :
    F.mapDerivedCategoryPlusFactorsh.inv.app L ≫
        (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F).inv.app
          (DerivedCategory.Plus.Qh.obj L) ≫
        (rightDerivedFunctorPlusIdIsoOf F e).hom.app (DerivedCategory.Plus.Qh.obj L) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans e.hom).app L) := by
  have h1 : F.mapDerivedCategoryPlusFactorsh.inv.app L ≫
      (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F).inv.app
        (DerivedCategory.Plus.Qh.obj L) = F.rightDerivedFunctorPlusUnit.app L := by
    rw [← unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app, Category.assoc,
      Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [reassoc_of% h1, rightDerivedFunctorPlusIdIsoOf_hom, Functor.rightDerivedNatTrans_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app]
  refine ((Category.comp_id _).trans (Category.comp_id _)).trans
    (congrArg DerivedCategory.Plus.Qh.map ?_)
  show (mapHomotopyCategoryPlusNatIso e).hom.app L ≫
    (mapHomotopyCategoryPlusIdIso A).hom.app L = _
  rw [mapHomotopyCategoryPlusIdIso_comp_hom]
  apply (HomotopyCategory.Plus.ι A).map_injective
  rfl

/-- **The compatibility hypothesis of `derivedSquareTrans'_comp` for a restriction that is the
identity up to isomorphism**: for `r₂ ≅ 𝟭` exact, the transformation `r̄₂ ⋙ r̄₁ ⟶ r̄₁` built from
the comparison `r̄₂ ≅ Rr₂ ≅ 𝟭` is compatible with the underived `r₂ ⋙ r₁ ⟶ r₁`. -/
theorem idIso_compatible {M₀ : Type*} [Category* M₀] [Abelian M₀] [hM₀ : HasDerivedCategory M₀]
    {M₁ : Type*} [Category* M₁] [Abelian M₁] [hM₁ : HasDerivedCategory M₁] [EnoughInjectives M₁]
    (r₁ : M₁ ⥤ M₀) [r₁.Additive] [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
    (r₂ : M₁ ⥤ M₁) [r₂.Additive] [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
    (e : r₂ ≅ 𝟭 M₁) (L : HomotopyCategory.Plus M₁) :
    r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
        r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
          (Functor.whiskerRight ((rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r₂).symm ≪≫
            rightDerivedFunctorPlusIdIsoOf r₂ e).hom r₁.mapDerivedCategoryPlus).app
            (DerivedCategory.Plus.Qh.obj L) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans
          (Functor.whiskerRight e.hom r₁ : r₂ ⋙ r₁ ⟶ r₁)).app L) ≫
        r₁.mapDerivedCategoryPlusFactorsh.inv.app L :=
  (CategoryTheory.whisker_eq _ ((r₁.mapDerivedCategoryPlus.map_comp _ _).symm.trans
    (congrArg r₁.mapDerivedCategoryPlus.map
      (mapDerivedCategoryPlusFactorsh_inv_comp_idIso_hom_app r₂ e L)))).trans
    (r₁.mapDerivedCategoryPlusFactorsh.inv.naturality
      ((mapHomotopyCategoryPlusNatTrans e.hom).app L)).symm

end Exact

section NatTransHelpers

variable {A : Type*} [Category* A] [Preadditive A] {B : Type*} [Category* B] [Preadditive B]
  {E : Type*} [Category* E] [Preadditive E]

/-- The degreewise action of a composite of natural transformations is the composite. -/
theorem mapHomotopyCategoryPlusNatTrans_comp_app {F G H : A ⥤ B} [F.Additive] [G.Additive]
    [H.Additive] (α : F ⟶ G) (β : G ⟶ H) (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusNatTrans (α ≫ β)).app K =
      (mapHomotopyCategoryPlusNatTrans α).app K ≫ (mapHomotopyCategoryPlusNatTrans β).app K := by
  ext
  exact congrArg (fun t => NatTrans.app t K.obj) (NatTrans.mapHomotopyCategory_comp (.up ℤ) α β)

/-- The degreewise action of a left whiskering is read at the image of the complex. -/
theorem mapHomotopyCategoryPlusNatTrans_whiskerLeft_app (P : A ⥤ B) {F G : B ⥤ E} [P.Additive]
    [F.Additive] [G.Additive] (β : F ⟶ G) (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusNatTrans (Functor.whiskerLeft P β)).app K =
      (mapHomotopyCategoryPlusNatTrans β).app (P.mapHomotopyCategoryPlus.obj K) := by
  rfl

/-- The degreewise action of a right whiskering is the image of the degreewise action. -/
theorem mapHomotopyCategoryPlusNatTrans_whiskerRight_app {F G : A ⥤ B} (r : B ⥤ E) [F.Additive]
    [G.Additive] [r.Additive] (β : F ⟶ G) (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusNatTrans (Functor.whiskerRight β r)).app K =
      r.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatTrans β).app K) := by
  rfl

end NatTransHelpers

section One

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory C₀] [EnoughInjectives C₀]
  {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
  {M₀ : Type*} [Category* M₀] [Abelian M₀] [HasDerivedCategory M₀]
  {M : Type*} [Category* M] [Abelian M] [HasDerivedCategory M] [EnoughInjectives M]
  {Γ₀ : C₀ ⥤ M₀} {Γ : C ⥤ M} {P : C₀ ⥤ C} {r : M ⥤ M₀}
  [Γ₀.Additive] [Γ.Additive] [P.Additive] [r.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

variable (Γ r) in
/-- **The splitting `R(Γ ⋙ r) ≅ RΓ ⋙ r`** for an exact `r`: the canonical transformation of
[Stacks, Tag 05T2], invertible because every object is right acyclic for `r`, followed by the
replacement of `Rr` by the functor `r` induces. -/
def derivedSquareSplitting :
    (Γ ⋙ r).rightDerivedFunctorPlus ⟶ Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus :=
  (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic Γ r
      (fun _ _ => Functor.rightAcyclic_of_exact _ _)).hom ≫
    Functor.whiskerLeft Γ.rightDerivedFunctorPlus
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r).hom

/-- **The derived transformation of a square** `α : Γ₀ ⟶ P ⋙ Γ ⋙ r`, for exact `P` and `r`:

`RΓ₀ ⟶ R(P ⋙ Γ ⋙ r) ⟶ RP ⋙ R(Γ ⋙ r) ≅ RP ⋙ RΓ ⋙ Rr ≅ RP ⋙ RΓ ⋙ r`.

The second arrow is the canonical transformation of [Stacks, Tag 05T2]; the third is an
isomorphism because `r` is exact, so every object is right acyclic for it. -/
def derivedSquareTrans (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) :
    Γ₀.rightDerivedFunctorPlus ⟶
      P.rightDerivedFunctorPlus ⋙ Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus :=
  Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans α ≫
    Stacks.DerivedIndexing.rightDerivedPlusCompTrans P (Γ ⋙ r) ≫
    Functor.whiskerLeft P.rightDerivedFunctorPlus (derivedSquareSplitting Γ r)

/-- **The derived transformation of a square, with `RP` replaced by the functor `P` induces on
bounded below derived categories.** -/
def derivedSquareTrans' (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) :
    Γ₀.rightDerivedFunctorPlus ⟶
      P.mapDerivedCategoryPlus ⋙ Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus :=
  derivedSquareTrans α ≫ Functor.whiskerRight
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus P).hom
    (Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus)

variable (Γ r) in
/-- **The canonical map `r(Γ(L)) ⟶ r(RΓ(L))`** in `D⁺(ℳ₀)`, for a bounded below complex `L`: the
unit of `RΓ` followed by `r`, read through the factorization of the induced functor of `r`
through the localization. -/
def derivedSquareNu (L : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.Qh.obj (r.mapHomotopyCategoryPlus.obj (Γ.mapHomotopyCategoryPlus.obj L)) ⟶
      r.mapDerivedCategoryPlus.obj
        (Γ.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj L)) :=
  r.mapDerivedCategoryPlusFactorsh.inv.app (Γ.mapHomotopyCategoryPlus.obj L) ≫
    r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlusUnit.app L)

variable (Γ r) in
/-- The unit of `R(Γ ⋙ r)` followed by the splitting `R(Γ ⋙ r) ≅ RΓ ⋙ r` is `derivedSquareNu`. -/
theorem unit_comp_splitting_app (L : HomotopyCategory.Plus C) :
    (Γ ⋙ r).rightDerivedFunctorPlusUnit.app L ≫
        (derivedSquareSplitting Γ r).app (DerivedCategory.Plus.Qh.obj L) =
      derivedSquareNu Γ r L := by
  have h1 := rightDerivedFunctorPlusComp_fac_app Γ r L
  show (Γ ⋙ r).rightDerivedFunctorPlusUnit.app L ≫
      (rightDerivedFunctorPlusComp Γ r).app (DerivedCategory.Plus.Qh.obj L) ≫
        (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus r).hom.app
          (Γ.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj L)) = _
  rw [reassoc_of% h1]
  refine (qhMapCompIsoReflInv_comp Γ r L _).trans ?_
  rw [NatTrans.naturality,
    reassoc_of% unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app]
  rfl

/-- **The derived transformation of a square, after the unit of `RΓ₀`**: at a bounded below
complex `K`, it is `α` applied degreewise followed by `derivedSquareNu` at `P(K)`, read through
the factorization of the induced functor of `P` through the localization. -/
theorem unit_comp_derivedSquareTrans'_app (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) (K : HomotopyCategory.Plus C₀) :
    Γ₀.rightDerivedFunctorPlusUnit.app K ≫
        (derivedSquareTrans' α).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) ≫
        derivedSquareNu Γ r (P.mapHomotopyCategoryPlus.obj K) ≫
          r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlus.map
            (P.mapDerivedCategoryPlusFactorsh.inv.app K)) := by
  simp only [derivedSquareTrans', derivedSquareTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [reassoc_of% (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans_app α K),
    reassoc_of% (Stacks.DerivedIndexing.rightDerivedPlusCompTrans_fac_app P (Γ ⋙ r) K)]
  refine CategoryTheory.whisker_eq _ ?_
  simp only [Stacks.DerivedIndexing.rightDerivedPlusCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  refine (qhMapCompIsoReflInv_comp P (Γ ⋙ r) K _).trans ?_
  have e1 := (derivedSquareSplitting Γ r).naturality (P.rightDerivedFunctorPlusUnit.app K)
  have e3 : (Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus).map
        (P.rightDerivedFunctorPlusUnit.app K) ≫
      (Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus).map
        ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus P).hom.app
          (DerivedCategory.Plus.Qh.obj K)) =
      (Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus).map
        (P.mapDerivedCategoryPlusFactorsh.inv.app K) :=
    ((Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus).map_comp _ _).symm.trans
      (congrArg _ (unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app P K))
  exact (CategoryTheory.whisker_eq _ ((Category.assoc _ _ _).symm.trans
    ((CategoryTheory.eq_whisker e1 _).trans ((Category.assoc _ _ _).trans
      (CategoryTheory.whisker_eq _ e3))))).trans
    ((Category.assoc _ _ _).symm.trans (CategoryTheory.eq_whisker
      (unit_comp_splitting_app Γ r (P.mapHomotopyCategoryPlus.obj K)) _))

end One

section Abstract

variable {𝒦 : Type*} [Category* 𝒦]

/-- Pasting six commutative squares `F1`, …, `F6` in an arbitrary category identifies the composite
`a ≫ (n ≫ g) ≫ t ≫ ρT` with `a' ≫ z ≫ k ≫ w'`. -/
private lemma pasteLeft {A0 A1 A2 A3 A4 A5 B1 B2 B3 B4 B5 B6 B7 : 𝒦}
    (a : A0 ⟶ A1) (n : A1 ⟶ A2) (g : A2 ⟶ A3) (t : A3 ⟶ A4) (ρT : A4 ⟶ A5)
    (t' : A2 ⟶ B1) (hh : B1 ⟶ A4) (F1 : g ≫ t = t' ≫ hh)
    (b : A1 ⟶ B2) (c : B2 ⟶ B3) (m : B3 ⟶ B1) (F2 : n ≫ t' = b ≫ c ≫ m)
    (d : B3 ⟶ B4) (w : B4 ⟶ A4) (F3 : m ≫ hh = d ≫ w)
    (ρL : B4 ⟶ B5) (w' : B5 ⟶ A5) (F4 : w ≫ ρT = ρL ≫ w')
    (e : B2 ⟶ B6) (k : B6 ⟶ B5) (F5 : c ≫ d ≫ ρL = e ≫ k)
    (a' : A0 ⟶ B7) (z : B7 ⟶ B6) (F6 : a ≫ b ≫ e = a' ≫ z) :
    a ≫ (n ≫ g) ≫ t ≫ ρT = a' ≫ z ≫ k ≫ w' := by
  calc a ≫ (n ≫ g) ≫ t ≫ ρT = a ≫ (n ≫ t') ≫ hh ≫ ρT := by
        simp only [Category.assoc, reassoc_of% F1]
    _ = a ≫ b ≫ c ≫ (m ≫ hh) ≫ ρT := by simp only [F2, Category.assoc]
    _ = a ≫ b ≫ (c ≫ d ≫ ρL) ≫ w' := by simp only [F3, Category.assoc, F4]
    _ = (a ≫ b ≫ e) ≫ k ≫ w' := by simp only [F5, Category.assoc]
    _ = a' ≫ z ≫ k ≫ w' := by rw [F6, Category.assoc]

/-- Pasting the commutative squares `G1`, `G2`, `G3` in an arbitrary category identifies the
composite `((p ≫ q) ≫ x) ≫ y` with `z ≫ k ≫ W`, where `W = v2 ≫ u2`. -/
private lemma pasteRight {A B C D E B' D' G : 𝒦} (p : A ⟶ B) (q : B ⟶ C) (x : C ⟶ D)
    (y : D ⟶ E) (u1 : C ⟶ D') (u2 : D' ⟶ E) (G1 : x ≫ y = u1 ≫ u2)
    (v1 : B ⟶ B') (v2 : B' ⟶ D') (G2 : q ≫ u1 = v1 ≫ v2)
    (z : A ⟶ G) (k : G ⟶ B') (G3 : p ≫ v1 = z ≫ k)
    (W : B' ⟶ E) (G4 : W = v2 ≫ u2) :
    ((p ≫ q) ≫ x) ≫ y = z ≫ k ≫ W := by
  rw [G4, Category.assoc, Category.assoc, G1, reassoc_of% G2, reassoc_of% G3]

/-- Pasting the commutative squares `H1`, …, `H7` in an arbitrary category, with `m` a split
monomorphism with retraction `m'`, identifies `(a ≫ b ≫ c ≫ d) ≫ e` with `t ≫ g ≫ h`. -/
private lemma pasteSingle {A B C C' C'' D E F G G' H H' K₁ K₂ : 𝒦}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : E ⟶ F)
    (t : A ⟶ G) (g : G ⟶ H) (h : H ⟶ F) (m : G ⟶ G') (m' : G' ⟶ G) (hm : m ≫ m' = 𝟙 G)
    (t' : B ⟶ G') (H1 : t ≫ m = a ≫ t')
    (q : C ⟶ C') (k₂ : C' ⟶ C'') (n₁ : C'' ⟶ G') (H2 : t' = b ≫ q ≫ k₂ ≫ n₁)
    (u₁ : C'' ⟶ H') (u₂ : H' ⟶ H) (H3 : n₁ ≫ m' ≫ g = u₁ ≫ u₂)
    (v₁ : H' ⟶ K₁) (v₂ : K₁ ⟶ K₂) (v₃ : K₂ ⟶ F) (H4 : u₂ ≫ h = v₁ ≫ v₂ ≫ v₃)
    (w : C' ⟶ K₁) (H5 : k₂ ≫ u₁ ≫ v₁ = w)
    (z : D ⟶ K₂) (H6 : d ≫ e = z ≫ v₃) (H7 : c ≫ z = q ≫ w ≫ v₂) :
    (a ≫ b ≫ c ≫ d) ≫ e = t ≫ g ≫ h := by
  have : t ≫ g ≫ h = t ≫ m ≫ m' ≫ g ≫ h := by rw [reassoc_of% hm]
  simp only [Category.assoc]
  rw [this, reassoc_of% H1, H2]
  simp only [Category.assoc]
  rw [reassoc_of% H3, H4, reassoc_of% H5, H6, reassoc_of% H7]

/-- Two cancellations in a composite, in an arbitrary category. -/
private lemma cancelFour {A B C E F : 𝒦} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ B) (d : B ⟶ A)
    (e : A ⟶ E) (g : E ⟶ F) (hbc : b ≫ c = 𝟙 B) (had : a ≫ d = 𝟙 A) :
    a ≫ b ≫ c ≫ d ≫ e ≫ g = e ≫ g := by
  rw [reassoc_of% hbc, reassoc_of% had]

/-- Pasting the commutative squares `N1`, …, `N4` in an arbitrary category, with `m = t2 ≫ g2`,
identifies `(t1 ≫ g1) ≫ m ≫ ρE` with `(θ ≫ x) ≫ s`. -/
private lemma pasteMap {A B C D D' E F F' G H : 𝒦} (t1 : A ⟶ B) (g1 : B ⟶ C) (m : C ⟶ E)
    (ρE : E ⟶ F) (t2 : C ⟶ D) (g2 : D ⟶ E) (hm : m = t2 ≫ g2)
    (t2' : B ⟶ D') (h1 : D' ⟶ D) (N1 : g1 ≫ t2 = t2' ≫ h1)
    (ρD' : D' ⟶ F') (rY : F' ⟶ F) (N2 : h1 ≫ g2 ≫ ρE = ρD' ≫ rY)
    (θ : A ⟶ G) (pπ : G ⟶ F') (N3 : t1 ≫ t2' ≫ ρD' = θ ≫ pπ)
    (x : G ⟶ H) (s : H ⟶ F) (N4 : pπ ≫ rY = x ≫ s) :
    (t1 ≫ g1) ≫ m ≫ ρE = (θ ≫ x) ≫ s := by
  rw [hm, Category.assoc, Category.assoc, reassoc_of% N1, N2, reassoc_of% N3, N4,
    Category.assoc]

end Abstract

section Composition

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [hC₀ : HasDerivedCategory C₀]
  [EnoughInjectives C₀]
  {C₁ : Type*} [Category* C₁] [Abelian C₁] [hC₁ : HasDerivedCategory C₁] [EnoughInjectives C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [hC₂ : HasDerivedCategory C₂] [EnoughInjectives C₂]
  {M₀ : Type*} [Category* M₀] [Abelian M₀] [hM₀ : HasDerivedCategory M₀]
  {M₁ : Type*} [Category* M₁] [Abelian M₁] [hM₁ : HasDerivedCategory M₁] [EnoughInjectives M₁]
  {M₂ : Type*} [Category* M₂] [Abelian M₂] [hM₂ : HasDerivedCategory M₂] [EnoughInjectives M₂]
  {Γ₀ : C₀ ⥤ M₀} {Γ₁ : C₁ ⥤ M₁} {Γ₂ : C₂ ⥤ M₂} [Γ₀.Additive] [Γ₁.Additive] [Γ₂.Additive]
  {P₁ : C₀ ⥤ C₁} {P₂ : C₁ ⥤ C₂} {P : C₀ ⥤ C₂} [P₁.Additive] [P₂.Additive] [P.Additive]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {r₁ : M₁ ⥤ M₀} {r₂ : M₂ ⥤ M₁} {r : M₂ ⥤ M₀} [r₁.Additive] [r₂.Additive] [r.Additive]
  [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
  [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

variable (P₁ P₂) in
/-- The composite of the induced functors of two exact functors lifts the composite of the
induced functors on bounded below homotopy categories. -/
def mapDerivedCategoryPlusCompFactorsh :
    DerivedCategory.Plus.Qh ⋙ P₁.mapDerivedCategoryPlus ⋙ P₂.mapDerivedCategoryPlus ≅
      (P₁.mapHomotopyCategoryPlus ⋙ P₂.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh :=
  isoWhiskerRight P₁.mapDerivedCategoryPlusFactorsh P₂.mapDerivedCategoryPlus ≪≫
    isoWhiskerLeft P₁.mapHomotopyCategoryPlus P₂.mapDerivedCategoryPlusFactorsh

variable (P₁ P₂) in
/-- `mapDerivedCategoryPlusCompFactorsh` as a lifting. -/
instance mapDerivedCategoryPlusCompLifting :
    Localization.Lifting DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C₀)
      ((P₁.mapHomotopyCategoryPlus ⋙ P₂.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh)
      (P₁.mapDerivedCategoryPlus ⋙ P₂.mapDerivedCategoryPlus) :=
  ⟨mapDerivedCategoryPlusCompFactorsh P₁ P₂⟩

/-- **The transformation `P̄ ⟶ P̄₁ ⋙ P̄₂` of induced functors** induced by a transformation
`τ : P ⟶ P₁ ⋙ P₂` of exact functors. -/
def mapDerivedCategoryPlusCompTrans (τ : P ⟶ P₁ ⋙ P₂) :
    P.mapDerivedCategoryPlus ⟶ P₁.mapDerivedCategoryPlus ⋙ P₂.mapDerivedCategoryPlus :=
  Localization.liftNatTrans DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C₀)
    (P.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    ((P₁.mapHomotopyCategoryPlus ⋙ P₂.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh)
    P.mapDerivedCategoryPlus (P₁.mapDerivedCategoryPlus ⋙ P₂.mapDerivedCategoryPlus)
    (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans τ ≫
      (mapHomotopyCategoryPlusCompIso (Iso.refl (P₁ ⋙ P₂))).inv) DerivedCategory.Plus.Qh)

omit [EnoughInjectives C₀] [EnoughInjectives C₁] [EnoughInjectives C₂] in
/-- `mapDerivedCategoryPlusCompTrans` at a complex: the degreewise action of `τ`, read through
the factorizations of the induced functors through the localization. -/
theorem mapDerivedCategoryPlusCompTrans_app (τ : P ⟶ P₁ ⋙ P₂) (K : HomotopyCategory.Plus C₀) :
    (mapDerivedCategoryPlusCompTrans τ).app (DerivedCategory.Plus.Qh.obj K) =
      P.mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans τ).app K) ≫
          P₂.mapDerivedCategoryPlusFactorsh.inv.app (P₁.mapHomotopyCategoryPlus.obj K) ≫
            P₂.mapDerivedCategoryPlus.map (P₁.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  rw [mapDerivedCategoryPlusCompTrans, Localization.liftNatTrans_app]
  show P.mapDerivedCategoryPlusFactorsh.hom.app K ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans τ).app K ≫
        (mapHomotopyCategoryPlusCompIso (Iso.refl (P₁ ⋙ P₂))).inv.app K) ≫
      (P₂.mapDerivedCategoryPlusFactorsh.inv.app (P₁.mapHomotopyCategoryPlus.obj K) ≫
        P₂.mapDerivedCategoryPlus.map (P₁.mapDerivedCategoryPlusFactorsh.inv.app K)) = _
  rw [Functor.map_comp, Category.assoc]
  exact CategoryTheory.whisker_eq _ (CategoryTheory.whisker_eq _
    (qhMapCompIsoReflInv_comp P₁ P₂ K _))

/-- The underlying complex morphism of `mapHomotopyCategoryPlusObjSingleIso` is the class of the
canonical isomorphism. -/
private theorem mapHomotopyCategoryPlusObjSingleIso_hom_hom {A B : Type*} [Category* A]
    [Abelian A] [Category* B] [Abelian B] (F : A ⥤ B) [F.Additive] (X : A) :
    (F.mapHomotopyCategoryPlusObjSingleIso 0 X).hom.hom =
      (HomotopyCategory.quotient B _).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app X) :=
  (HomotopyCategory.Plus.ι B).map_preimage _

omit hC₀ [EnoughInjectives C₀] hC₁ [EnoughInjectives C₁] hC₂ [EnoughInjectives C₂]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁] [PreservesFiniteLimits P₂]
  [PreservesFiniteColimits P₂] [PreservesFiniteLimits P] [PreservesFiniteColimits P] in
/-- **The single complex and a transformation of exact functors**, on bounded below homotopy
categories: the comparison `P(X[0]) ≅ P(X)[0]` is natural for `τ : P ⟶ P₁ ⋙ P₂`. -/
theorem mapHomotopyCategoryPlusObjSingleIso_comp (τ : P ⟶ P₁ ⋙ P₂) (X : C₀) :
    (Functor.mapHomotopyCategoryPlusNatTrans τ).app
        ((HomotopyCategory.Plus.singleFunctor C₀ 0).obj X) ≫
      P₂.mapHomotopyCategoryPlus.map (P₁.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫
        (P₂.mapHomotopyCategoryPlusObjSingleIso 0 (P₁.obj X)).hom =
      (P.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫
        (HomotopyCategory.Plus.singleFunctor C₂ 0).map (τ.app X) := by
  have t1 : ((HomotopyCategory.Plus.singleFunctor C₂ 0).map (τ.app X)).hom =
      (HomotopyCategory.quotient C₂ _).map
        ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) 0).map (τ.app X)) := rfl
  have t2 : ((Functor.mapHomotopyCategoryPlusNatTrans τ).app
        ((HomotopyCategory.Plus.singleFunctor C₀ 0).obj X)).hom =
      (HomotopyCategory.quotient C₂ _).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single C₀ (ComplexShape.up ℤ) 0).obj X)) := rfl
  have t4 : (P₂.mapHomotopyCategoryPlus.map (P₁.mapHomotopyCategoryPlusObjSingleIso 0 X).hom).hom =
      (HomotopyCategory.quotient C₂ _).map ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex P₁ (ComplexShape.up ℤ) 0).hom.app
            X)) :=
    (congrArg (P₂.mapHomotopyCategory _).map
      (mapHomotopyCategoryPlusObjSingleIso_hom_hom P₁ X)).trans rfl
  ext
  show ((Functor.mapHomotopyCategoryPlusNatTrans τ).app
        ((HomotopyCategory.Plus.singleFunctor C₀ 0).obj X)).hom ≫
      (P₂.mapHomotopyCategoryPlus.map (P₁.mapHomotopyCategoryPlusObjSingleIso 0 X).hom).hom ≫
        (P₂.mapHomotopyCategoryPlusObjSingleIso 0 (P₁.obj X)).hom.hom =
    (P.mapHomotopyCategoryPlusObjSingleIso 0 X).hom.hom ≫
      ((HomotopyCategory.Plus.singleFunctor C₂ 0).map (τ.app X)).hom
  rw [t1, t2, mapHomotopyCategoryPlusObjSingleIso_hom_hom, t4,
    mapHomotopyCategoryPlusObjSingleIso_hom_hom]
  refine ((congrArg (fun t => _ ≫ t) ((HomotopyCategory.quotient C₂ _).map_comp _ _).symm).trans
    ((HomotopyCategory.quotient C₂ _).map_comp _ _).symm).trans
    ((congrArg (HomotopyCategory.quotient C₂ _).map ?_).trans
      ((HomotopyCategory.quotient C₂ _).map_comp _ _))
  rw [← cancel_epi
      ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app X),
    Iso.inv_hom_id_app_assoc]
  refine HomologicalComplex.from_single_hom_ext ?_
  simp [HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf]

/-- **The derived transformation of a pasted square is the pasting of the derived
transformations.**  Given squares `α₁ : Γ₀ ⟶ P₁ ⋙ Γ₁ ⋙ r₁` and `α₂ : Γ₁ ⟶ P₂ ⋙ Γ₂ ⋙ r₂`, a third
square `α : Γ₀ ⟶ P ⋙ Γ₂ ⋙ r`, transformations `τ : P ⟶ P₁ ⋙ P₂` and `ρ₀ : r₂ ⋙ r₁ ⟶ r` of
underived functors relating them (`hα`), and a transformation `ρ : r̄₂ ⋙ r̄₁ ⟶ r̄` of induced
functors compatible with `ρ₀` (`hρ`), the derived transformation of `α`, followed by the
transformation induced by `τ`, is the derived transformation of `α₁` followed by that of `α₂`
and by `ρ`. -/
theorem derivedSquareTrans'_comp (α₁ : Γ₀ ⟶ P₁ ⋙ Γ₁ ⋙ r₁) (α₂ : Γ₁ ⟶ P₂ ⋙ Γ₂ ⋙ r₂)
    (α : Γ₀ ⟶ P ⋙ Γ₂ ⋙ r) (τ : P ⟶ P₁ ⋙ P₂) (ρ₀ : r₂ ⋙ r₁ ⟶ r)
    (ρ : r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus ⟶ r.mapDerivedCategoryPlus)
    (hρ : ∀ L : HomotopyCategory.Plus M₂,
      r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
          r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
            ρ.app (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L) ≫
          r.mapDerivedCategoryPlusFactorsh.inv.app L)
    (hα : ∀ X : C₀, α₁.app X ≫ r₁.map (α₂.app (P₁.obj X)) ≫
        ρ₀.app (Γ₂.obj (P₂.obj (P₁.obj X))) = α.app X ≫ r.map (Γ₂.map (τ.app X))) :
    derivedSquareTrans' α₁ ≫
        Functor.whiskerLeft P₁.mapDerivedCategoryPlus
          (Functor.whiskerRight (derivedSquareTrans' α₂) r₁.mapDerivedCategoryPlus) ≫
        Functor.whiskerLeft (P₁.mapDerivedCategoryPlus ⋙ P₂.mapDerivedCategoryPlus ⋙
          Γ₂.rightDerivedFunctorPlus) ρ =
      derivedSquareTrans' α ≫ Functor.whiskerRight (mapDerivedCategoryPlusCompTrans τ)
        (Γ₂.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus) := by
  refine Functor.rightDerived_ext Γ₀.rightDerivedFunctorPlus Γ₀.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C₀) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [reassoc_of% unit_comp_derivedSquareTrans'_app α₁ K,
    reassoc_of% unit_comp_derivedSquareTrans'_app α K]
  let L := P₁.mapHomotopyCategoryPlus.obj K
  let L₂ := P₂.mapHomotopyCategoryPlus.obj L
  let f₁ := P₁.mapDerivedCategoryPlusFactorsh.inv.app K
  let f₂ := P₂.mapDerivedCategoryPlusFactorsh.inv.app L
  have s1 : r₁.mapDerivedCategoryPlus.map (Γ₁.rightDerivedFunctorPlus.map f₁) ≫
        r₁.mapDerivedCategoryPlus.map ((derivedSquareTrans' α₂).app
          (P₁.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K))) =
      r₁.mapDerivedCategoryPlus.map ((derivedSquareTrans' α₂).app (DerivedCategory.Plus.Qh.obj L)) ≫
        r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlus.map
          (Γ₂.rightDerivedFunctorPlus.map (P₂.mapDerivedCategoryPlus.map f₁))) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg r₁.mapDerivedCategoryPlus.map ((derivedSquareTrans' α₂).naturality f₁)
  have s2 : derivedSquareNu Γ₁ r₁ L ≫
        r₁.mapDerivedCategoryPlus.map
          ((derivedSquareTrans' α₂).app (DerivedCategory.Plus.Qh.obj L)) =
      DerivedCategory.Plus.Qh.map (r₁.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans α₂).app L)) ≫
        r₁.mapDerivedCategoryPlusFactorsh.inv.app
          (r₂.mapHomotopyCategoryPlus.obj (Γ₂.mapHomotopyCategoryPlus.obj L₂)) ≫
        r₁.mapDerivedCategoryPlus.map (derivedSquareNu Γ₂ r₂ L₂ ≫
          r₂.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlus.map f₂)) := by
    have hA := unit_comp_derivedSquareTrans'_app α₂ L
    have hN := r₁.mapDerivedCategoryPlusFactorsh.inv.naturality
      ((Functor.mapHomotopyCategoryPlusNatTrans α₂).app L)
    calc derivedSquareNu Γ₁ r₁ L ≫
          r₁.mapDerivedCategoryPlus.map
            ((derivedSquareTrans' α₂).app (DerivedCategory.Plus.Qh.obj L))
        = r₁.mapDerivedCategoryPlusFactorsh.inv.app (Γ₁.mapHomotopyCategoryPlus.obj L) ≫
            r₁.mapDerivedCategoryPlus.map (Γ₁.rightDerivedFunctorPlusUnit.app L ≫
              (derivedSquareTrans' α₂).app (DerivedCategory.Plus.Qh.obj L)) := by
          rw [derivedSquareNu, Category.assoc, Functor.map_comp]
      _ = r₁.mapDerivedCategoryPlusFactorsh.inv.app (Γ₁.mapHomotopyCategoryPlus.obj L) ≫
            r₁.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
              ((Functor.mapHomotopyCategoryPlusNatTrans α₂).app L)) ≫
            r₁.mapDerivedCategoryPlus.map (derivedSquareNu Γ₂ r₂ L₂ ≫
              r₂.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlus.map f₂)) := by
          rw [hA, Functor.map_comp]
      _ = _ := ((reassoc_of% hN) _).symm
  let τK := (Functor.mapHomotopyCategoryPlusNatTrans τ).app K
  let W := Γ₂.rightDerivedFunctorPlusUnit.app L₂ ≫
    Γ₂.rightDerivedFunctorPlus.map (f₂ ≫ P₂.mapDerivedCategoryPlus.map f₁)
  have hαK : (Functor.mapHomotopyCategoryPlusNatTrans α₁).app K ≫
      r₁.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatTrans α₂).app L) ≫
        (Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app (Γ₂.mapHomotopyCategoryPlus.obj L₂) =
      (Functor.mapHomotopyCategoryPlusNatTrans α).app K ≫
        r.mapHomotopyCategoryPlus.map (Γ₂.mapHomotopyCategoryPlus.map τK) := by
    have e : α₁ ≫ Functor.whiskerLeft P₁ (Functor.whiskerRight α₂ r₁) ≫
        Functor.whiskerLeft (P₁ ⋙ P₂ ⋙ Γ₂) ρ₀ =
          α ≫ Functor.whiskerRight τ (Γ₂ ⋙ r) := by
      ext X
      exact hα X
    have e' := congrArg (fun t => (Functor.mapHomotopyCategoryPlusNatTrans t).app K) e
    simp only [mapHomotopyCategoryPlusNatTrans_comp_app,
      mapHomotopyCategoryPlusNatTrans_whiskerLeft_app,
      mapHomotopyCategoryPlusNatTrans_whiskerRight_app] at e'
    exact e'
  have F3 : r₁.mapDerivedCategoryPlus.map (derivedSquareNu Γ₂ r₂ L₂ ≫
          r₂.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlus.map f₂)) ≫
        r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlus.map
          (Γ₂.rightDerivedFunctorPlus.map (P₂.mapDerivedCategoryPlus.map f₁))) =
      r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app
          (Γ₂.mapHomotopyCategoryPlus.obj L₂)) ≫
        (r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus).map W := by
    simp only [derivedSquareNu, W, Functor.comp_map, Functor.map_comp, Category.assoc]
  have F6 : DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans α₁).app K) ≫
        DerivedCategory.Plus.Qh.map (r₁.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans α₂).app L)) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app (Γ₂.mapHomotopyCategoryPlus.obj L₂)) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) ≫
        DerivedCategory.Plus.Qh.map (r.mapHomotopyCategoryPlus.map
          (Γ₂.mapHomotopyCategoryPlus.map τK)) :=
    ((congrArg (fun t => DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans α₁).app K) ≫ t)
        (DerivedCategory.Plus.Qh.map_comp _ _).symm).trans
      (DerivedCategory.Plus.Qh.map_comp _ _).symm).trans
    ((congrArg DerivedCategory.Plus.Qh.map hαK).trans (DerivedCategory.Plus.Qh.map_comp _ _))
  have F7 : (derivedSquareNu Γ₂ r (P.mapHomotopyCategoryPlus.obj K) ≫
        r.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlus.map
          (P.mapDerivedCategoryPlusFactorsh.inv.app K))) ≫
        (Γ₂.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus).map
          ((mapDerivedCategoryPlusCompTrans τ).app (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map (r.mapHomotopyCategoryPlus.map
          (Γ₂.mapHomotopyCategoryPlus.map τK)) ≫
        r.mapDerivedCategoryPlusFactorsh.inv.app (Γ₂.mapHomotopyCategoryPlus.obj L₂) ≫
          r.mapDerivedCategoryPlus.map W := by
    refine pasteRight (r.mapDerivedCategoryPlusFactorsh.inv.app
          (Γ₂.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)))
      (r.mapDerivedCategoryPlus.map
          (Γ₂.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj K))) _ _
      (r.mapDerivedCategoryPlus.map
        (Γ₂.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map τK)))
      (r.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlus.map
        (f₂ ≫ P₂.mapDerivedCategoryPlus.map f₁))) ?_
      (r.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        (Γ₂.mapHomotopyCategoryPlus.map τK)))
      (r.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlusUnit.app L₂)) ?_ _ _ ?_ _ ?_
    · rw [mapDerivedCategoryPlusCompTrans_app, Functor.comp_map, ← Functor.map_comp,
        ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
    · rw [← Functor.map_comp]
      exact (congrArg r.mapDerivedCategoryPlus.map
        (Γ₂.rightDerivedFunctorPlusUnit.naturality τK).symm).trans
        (r.mapDerivedCategoryPlus.map_comp _ _)
    · exact (r.mapDerivedCategoryPlusFactorsh.inv.naturality
        (Γ₂.mapHomotopyCategoryPlus.map τK)).symm
    · exact r.mapDerivedCategoryPlus.map_comp _ _
  have hρL := hρ (Γ₂.mapHomotopyCategoryPlus.obj L₂)
  exact pasteLeft _ _ _ _ _ _ _ s1 _ _ _ s2 _ _ F3 _ _ (ρ.naturality W) _ _
    hρL _ _ F6 |>.trans
    (CategoryTheory.whisker_eq _ F7.symm)

omit [EnoughInjectives C₂] in
/-- **The single objects and a transformation of exact functors**, on bounded below derived
categories: the comparison `P̄(X[0]) ≅ P(X)[0]` is natural for `τ : P ⟶ P₁ ⋙ P₂`. -/
theorem mapDerivedCategoryPlusObjSingleIso_comp (τ : P ⟶ P₁ ⋙ P₂) (X : C₀) :
    (P.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (DerivedCategory.Plus.singleFunctor C₂ 0).map (τ.app X) =
      (mapDerivedCategoryPlusCompTrans τ).app ((DerivedCategory.Plus.singleFunctor C₀ 0).obj X) ≫
        P₂.mapDerivedCategoryPlus.map (P₁.mapDerivedCategoryPlusObjSingleIso X).hom ≫
          (P₂.mapDerivedCategoryPlusObjSingleIso (P₁.obj X)).hom := by
  let sK := (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X
  let sA := (singleFunctorPlusIsoCompQh (A := C₀) 0).app X
  rw [mapDerivedCategoryPlusObjSingleIso_hom]
  refine pasteSingle _ _ _ _ _ _ _ _
    ((P₁.mapDerivedCategoryPlus ⋙ P₂.mapDerivedCategoryPlus).map sA.hom)
    ((P₁.mapDerivedCategoryPlus ⋙ P₂.mapDerivedCategoryPlus).map sA.inv)
    (by rw [← Functor.map_comp, Iso.hom_inv_id, Functor.map_id])
    ((mapDerivedCategoryPlusCompTrans τ).app (DerivedCategory.Plus.Qh.obj sK))
    ((mapDerivedCategoryPlusCompTrans τ).naturality sA.hom).symm
    (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans τ).app sK))
    (P₂.mapDerivedCategoryPlusFactorsh.inv.app (P₁.mapHomotopyCategoryPlus.obj sK))
    (P₂.mapDerivedCategoryPlus.map (P₁.mapDerivedCategoryPlusFactorsh.inv.app sK))
    (by rw [mapDerivedCategoryPlusCompTrans_app])
    (P₂.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
      (P₁.mapHomotopyCategoryPlusObjSingleIso 0 X).hom))
    (P₂.mapDerivedCategoryPlus.map ((singleFunctorPlusIsoCompQh (A := C₁) 0).inv.app (P₁.obj X)))
    ?_
    (P₂.mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.singleFunctor C₁ 0).obj (P₁.obj X)))
    (DerivedCategory.Plus.Qh.map (P₂.mapHomotopyCategoryPlusObjSingleIso 0 (P₁.obj X)).hom)
    ((singleFunctorPlusIsoCompQh (A := C₂) 0).inv.app (P₂.obj (P₁.obj X)))
    ?_
    (DerivedCategory.Plus.Qh.map (P₂.mapHomotopyCategoryPlus.map
      (P₁.mapHomotopyCategoryPlusObjSingleIso 0 X).hom))
    ?_
    (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor C₂ 0).map (τ.app X)))
    ((singleFunctorPlusIsoCompQh (A := C₂) 0).inv.naturality (τ.app X)).symm
    ?_
  · simp only [Functor.comp_map, ← Functor.map_comp, mapDerivedCategoryPlusObjSingleIso_hom]
    congr 1
    exact cancelFour _ _ _ _ _ _
      ((P₁.mapDerivedCategoryPlus.map_comp _ _).symm.trans
        ((congrArg P₁.mapDerivedCategoryPlus.map
          ((singleFunctorPlusIsoCompQh (A := C₀) 0).inv_hom_id_app X)).trans
          (P₁.mapDerivedCategoryPlus.map_id _)))
      (P₁.mapDerivedCategoryPlusFactorsh.inv_hom_id_app sK)
  · rw [mapDerivedCategoryPlusObjSingleIso_hom, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    exact (congrArg (· ≫ _) (P₂.mapDerivedCategoryPlus.map_id _)).trans (Category.id_comp _)
  · exact (P₂.mapDerivedCategoryPlusFactorsh.inv.naturality_assoc _ _).symm.trans
      (by rw [Iso.inv_hom_id_app, Category.comp_id]; rfl)
  · exact (DerivedCategory.Plus.Qh.map_comp _ _).symm.trans <|
      (congrArg DerivedCategory.Plus.Qh.map
        (mapHomotopyCategoryPlusObjSingleIso_comp τ X).symm).trans
      ((DerivedCategory.Plus.Qh.map_comp _ _).trans
        (CategoryTheory.whisker_eq _ (DerivedCategory.Plus.Qh.map_comp _ _)))

variable (α₁ : Γ₀ ⟶ P₁ ⋙ Γ₁ ⋙ r₁) in
/-- **The derived comparison of a square at a single object**:
`RΓ₀(X[0]) ⟶ r̄(RΓ(P(X)[0]))`, `derivedSquareTrans'` at `X[0]` read through
`P̄(X[0]) ≅ P(X)[0]`. -/
def derivedSquareMap (X : C₀) :
    Γ₀.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C₀ 0).obj X) ⟶
      r₁.mapDerivedCategoryPlus.obj (Γ₁.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C₁ 0).obj (P₁.obj X))) :=
  (derivedSquareTrans' α₁).app ((DerivedCategory.Plus.singleFunctor C₀ 0).obj X) ≫
    (Γ₁.rightDerivedFunctorPlus ⋙ r₁.mapDerivedCategoryPlus).map
      (P₁.mapDerivedCategoryPlusObjSingleIso X).hom

/-- `derivedSquareMap` in terms of `derivedSquareTrans` and the comparison
`RP(X[0]) ≅ P(X)[0]` of the right derived functor of `P`. -/
theorem derivedSquareMap_eq (α₁ : Γ₀ ⟶ P₁ ⋙ Γ₁ ⋙ r₁) (X : C₀) :
    derivedSquareMap α₁ X =
      (derivedSquareTrans α₁).app ((DerivedCategory.Plus.singleFunctor C₀ 0).obj X) ≫
        (Γ₁.rightDerivedFunctorPlus ⋙ r₁.mapDerivedCategoryPlus).map
          (P₁.rightDerivedFunctorPlusObjSingleIso X).hom := by
  rw [derivedSquareMap, derivedSquareTrans', NatTrans.comp_app, Category.assoc,
    Functor.whiskerRight_app, ← Functor.map_comp, mapDerivedCategoryPlusObjSingleIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.hom_inv_id_app_assoc]

/-- **The derived comparison of a pasted square, at a single object, is the pasting of the
derived comparisons**: the single-object form of `derivedSquareTrans'_comp`. -/
theorem derivedSquareMap_comp (α₁ : Γ₀ ⟶ P₁ ⋙ Γ₁ ⋙ r₁) (α₂ : Γ₁ ⟶ P₂ ⋙ Γ₂ ⋙ r₂)
    (α : Γ₀ ⟶ P ⋙ Γ₂ ⋙ r) (τ : P ⟶ P₁ ⋙ P₂) (ρ₀ : r₂ ⋙ r₁ ⟶ r)
    (ρ : r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus ⟶ r.mapDerivedCategoryPlus)
    (hρ : ∀ L : HomotopyCategory.Plus M₂,
      r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
          r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
            ρ.app (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L) ≫
          r.mapDerivedCategoryPlusFactorsh.inv.app L)
    (hα : ∀ X : C₀, α₁.app X ≫ r₁.map (α₂.app (P₁.obj X)) ≫
        ρ₀.app (Γ₂.obj (P₂.obj (P₁.obj X))) = α.app X ≫ r.map (Γ₂.map (τ.app X)))
    (X : C₀) :
    derivedSquareMap α₁ X ≫ r₁.mapDerivedCategoryPlus.map (derivedSquareMap α₂ (P₁.obj X)) ≫
        ρ.app (Γ₂.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor C₂ 0).obj (P₂.obj (P₁.obj X)))) =
      derivedSquareMap α X ≫ r.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C₂ 0).map (τ.app X))) := by
  let X₀ := (DerivedCategory.Plus.singleFunctor C₀ 0).obj X
  have hB := NatTrans.congr_app
    (derivedSquareTrans'_comp α₁ α₂ α τ ρ₀ ρ hρ hα) X₀
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hB
  refine pasteMap _ _ _ _
    (r₁.mapDerivedCategoryPlus.map ((derivedSquareTrans' α₂).app
      ((DerivedCategory.Plus.singleFunctor C₁ 0).obj (P₁.obj X))))
    (r₁.mapDerivedCategoryPlus.map ((Γ₂.rightDerivedFunctorPlus ⋙ r₂.mapDerivedCategoryPlus).map
      (P₂.mapDerivedCategoryPlusObjSingleIso (P₁.obj X)).hom))
    (r₁.mapDerivedCategoryPlus.map_comp _ _)
    (r₁.mapDerivedCategoryPlus.map ((derivedSquareTrans' α₂).app
      (P₁.mapDerivedCategoryPlus.obj X₀)))
    (r₁.mapDerivedCategoryPlus.map ((P₂.mapDerivedCategoryPlus ⋙ Γ₂.rightDerivedFunctorPlus ⋙
      r₂.mapDerivedCategoryPlus).map (P₁.mapDerivedCategoryPlusObjSingleIso X).hom)) ?_
    (ρ.app ((P₁.mapDerivedCategoryPlus ⋙ P₂.mapDerivedCategoryPlus ⋙
      Γ₂.rightDerivedFunctorPlus).obj X₀))
    (r.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlus.map
      (P₂.mapDerivedCategoryPlus.map (P₁.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (P₂.mapDerivedCategoryPlusObjSingleIso (P₁.obj X)).hom))) ?_ _ _ hB _ _ ?_
  · exact (r₁.mapDerivedCategoryPlus.map_comp _ _).symm.trans
      ((congrArg r₁.mapDerivedCategoryPlus.map
        ((derivedSquareTrans' α₂).naturality (P₁.mapDerivedCategoryPlusObjSingleIso X).hom)).trans
        (r₁.mapDerivedCategoryPlus.map_comp _ _))
  · have hn := ρ.naturality (Γ₂.rightDerivedFunctorPlus.map
      (P₂.mapDerivedCategoryPlus.map (P₁.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (P₂.mapDerivedCategoryPlusObjSingleIso (P₁.obj X)).hom))
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hn ⊢
    exact hn
  · simp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← mapDerivedCategoryPlusObjSingleIso_comp]

end Composition

end CategoryTheory.Functor
