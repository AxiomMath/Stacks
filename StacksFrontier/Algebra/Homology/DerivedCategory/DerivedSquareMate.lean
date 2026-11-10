module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareCochain
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompQh
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.DerivedAdjunctionOfExactLeftAdjoint
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# The derived transformation of a mate is the mate of the derived square

Let `Lf ⊣ F` and `Lf' ⊣ F'` be adjunctions of additive functors between abelian categories
with exact left adjoints, `F : A ⥤ B`, `F' : A' ⥤ B'`, and let `E : A ⥤ A'`, `E' : B ⥤ B'` be
exact. A 2-square `α : E' ⋙ Lf' ⟶ Lf ⋙ E` of the left adjoints has a mate
`c : F ⋙ E' ⟶ E ⋙ F'`, and `Stacks.Homology.DerivedSquare.derivedSquare` derives `c` to
`RF ⋙ E' ⟶ E ⋙ RF'` by descent along a derived-functor unit. On the other hand `α` descends
directly to the derived categories, the left adjoints being exact, and the descended square has
a mate under the derived adjunctions `Lf ⊣ RF` and `Lf' ⊣ RF'`
(`Stacks.DerivedFunctor.derivedAdjunction`). The two agree.

This is the abstract form of the identification of a derived base change map, built as a
descent, with the mate of the comparison of two composite derived inverse images, which is what
lets the formal calculus of mates be applied to a derived base change map.

## Main definitions

* `Stacks.Homology.DerivedSquare.homotopyTwoSquare`: a 2-square of additive functors, applied
  degreewise and passed to the homotopy categories.
* `Stacks.Homology.DerivedSquare.derivedTwoSquare`: a 2-square of exact functors, descended to
  the unbounded derived categories.

## Main results

* `Stacks.Homology.DerivedSquare.derivedTwoSquare_app_Qh`: its component at an object
  represented by a complex.
* `Stacks.Homology.DerivedSquare.derivedTwoSquare_eq_pullbackComparison`: the derived 2-square of
  a comparison of two composites with a third functor is the comparison of the derived
  composites.
* `Stacks.Homology.DerivedSquare.mateEquiv_derivedTwoSquare_fac`: the defining property of the
  derived transformation of the mate of `α`, for arbitrary right derived functors along `Q_h`,
  holds for the mate of the derived 2-square.
* `Stacks.Homology.DerivedSquare.derivedSquare_mateEquiv`: **the derived transformation of the
  mate of `α` is the mate of the derived 2-square of `α`.**
* `Stacks.Homology.DerivedSquare.cochainDerivedSquare_mateEquiv`: the same for right derived
  functors along the localization `Q` of cochain complexes (`cochainDerivedSquare`).

## Implementation notes

Both sides are transformations out of `RF ⋙ E'`, which is a right derived functor of
`K(F) ⋙ Q_h ⋙ E'`, so they are compared after precomposition with its unit, at an object
`Q_h K` (`CategoryTheory.Functor.rightDerived_ext`). There the two maps land in `RF'`, so they
are compared through the derived adjunction `Lf' ⊣ RF'`: their adjoint transposes are both
computed by the descriptions of the derived counits
(`Stacks.DerivedFunctor.derivedAdjunction_counit_app`), and reduce to the degreewise identity
`Lf'(c) ≫ ε' = α ≫ E(ε)` (`CategoryTheory.mateEquiv_counit`). That half is proved once, for any
right derived functors along `Q_h` (`mateEquiv_derivedTwoSquare_fac`); the version along `Q`
reads it at the class of a complex, where the units along `Q_h` given by
`Stacks.DerivedAdjunction.homotopyUnitOfComplex` are the units along `Q`
(`homotopyUnitOfComplex_app_quotient`, `fac_Q_of_fac_Qh`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedCompUnit
  isRightDerivedFunctor_totalRightDerived_comp totalRightDerivedCompUnit_app)

universe w vA vA' vB vB' uA uA' uB uB' wG

namespace Stacks.Homology.DerivedSquare

section Square

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{w} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{w} B']
  {Lf : B ⥤ A} [Lf.Additive] [PreservesFiniteLimits Lf] [PreservesFiniteColimits Lf]
  {Lf' : B' ⥤ A'} [Lf'.Additive] [PreservesFiniteLimits Lf'] [PreservesFiniteColimits Lf']
  {E : A ⥤ A'} [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  {E' : B ⥤ B'} [E'.Additive] [PreservesFiniteLimits E'] [PreservesFiniteColimits E']

/-- A 2-square `E' ⋙ Lf' ⟶ Lf ⋙ E` of additive functors, applied degreewise to unbounded
complexes and passed to the homotopy categories. -/
def homotopyTwoSquare (α : TwoSquare E' Lf Lf' E) :
    TwoSquare (E'.mapHomotopyCategory (ComplexShape.up ℤ))
      (Lf.mapHomotopyCategory (ComplexShape.up ℤ)) (Lf'.mapHomotopyCategory (ComplexShape.up ℤ))
      (E.mapHomotopyCategory (ComplexShape.up ℤ)) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl (E' ⋙ Lf')) (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (Lf ⋙ E)) (ComplexShape.up ℤ)).inv

/-- The degreewise 2-square of an invertible 2-square is invertible. -/
instance isIso_homotopyTwoSquare (α : TwoSquare E' Lf Lf' E) [IsIso α] :
    IsIso (homotopyTwoSquare α) := by
  have : IsIso (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)) :=
    ⟨NatTrans.mapHomotopyCategory (inv α) (ComplexShape.up ℤ), by
      rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id], by
      rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩
  dsimp only [homotopyTwoSquare]
  infer_instance

/-- **The derived 2-square of a 2-square of exact functors.** A 2-square
`α : E' ⋙ Lf' ⟶ Lf ⋙ E` of exact functors, applied degreewise and descended along the
localization `Q_h` to a 2-square `E' ⋙ Lf' ⟶ Lf ⋙ E` of the induced functors on the unbounded
derived categories. -/
def derivedTwoSquare (α : TwoSquare E' Lf Lf' E) :
    TwoSquare E'.mapDerivedCategory Lf.mapDerivedCategory Lf'.mapDerivedCategory
      E.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    (E'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (Lf'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (Lf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    (E'.mapDerivedCategory ⋙ Lf'.mapDerivedCategory)
    (Lf.mapDerivedCategory ⋙ E.mapDerivedCategory)
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (homotopyTwoSquare α) DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom)

/-- **The component of the derived 2-square at an object represented by a complex**: the
degreewise 2-square, conjugated by the exactness comparisons of the four functors. -/
theorem derivedTwoSquare_app_Qh (α : TwoSquare E' Lf Lf' E)
    (X : HomotopyCategory B (ComplexShape.up ℤ)) :
    (derivedTwoSquare α).app (DerivedCategory.Qh.obj X) =
      Lf'.mapDerivedCategory.map (E'.mapDerivedCategoryFactorsh.hom.app X) ≫
        Lf'.mapDerivedCategoryFactorsh.hom.app
          ((E'.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((homotopyTwoSquare α).app X) ≫
        E.mapDerivedCategoryFactorsh.inv.app
          ((Lf.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        E.mapDerivedCategory.map (Lf.mapDerivedCategoryFactorsh.inv.app X) := by
  simp [derivedTwoSquare, Localization.liftNatTrans_app, Localization.Lifting.iso]

/-- The derived 2-square of an invertible 2-square is invertible. -/
instance isIso_derivedTwoSquare (α : TwoSquare E' Lf Lf' E) [IsIso α] :
    IsIso (derivedTwoSquare α) := by
  let τ : E'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (Lf'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      Lf.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (homotopyTwoSquare α) DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom
  have : IsIso τ := by dsimp only [τ]; infer_instance
  exact (Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) _ _
    (E'.mapDerivedCategory ⋙ Lf'.mapDerivedCategory)
    (Lf.mapDerivedCategory ⋙ E.mapDerivedCategory) (asIso τ)).isIso_hom


/-- **The derived 2-square of a comparison of composites is the comparison of the derived
composites.** If `E' ⋙ Lf'` and `Lf ⋙ E` are both identified with an exact functor `K`, the
derived 2-square of the comparison `E' ⋙ Lf' ≅ K ≅ Lf ⋙ E` is the comparison of the two composite
derived functors with `K.mapDerivedCategory` through `Functor.mapDerivedCategoryCompIsoOfIso`. -/
theorem derivedTwoSquare_eq_pullbackComparison {K : B ⥤ A'} [K.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (c₁ : E' ⋙ Lf' ≅ K) (c₂ : Lf ⋙ E ≅ K) :
    derivedTwoSquare (TwoSquare.mk _ _ _ _ (c₁.hom ≫ c₂.inv)) =
      Stacks.CategoryTheory.BaseChange.pullbackComparison
        (Functor.mapDerivedCategoryCompIsoOfIso c₁).symm
        (Functor.mapDerivedCategoryCompIsoOfIso c₂).symm := by
  have hh : ∀ X : HomotopyCategory B (ComplexShape.up ℤ),
      (homotopyTwoSquare (TwoSquare.mk _ _ _ _ (c₁.hom ≫ c₂.inv))).app X =
        (Functor.mapHomotopyCategoryCompIso c₁ (ComplexShape.up ℤ)).hom.app X ≫
          (Functor.mapHomotopyCategoryCompIso c₂ (ComplexShape.up ℤ)).inv.app X := by
    rintro ⟨X⟩
    have h : (Functor.mapHomologicalComplexCompIso (Iso.refl (E' ⋙ Lf'))
          (ComplexShape.up ℤ)).hom.app X ≫
        (NatTrans.mapHomologicalComplex (c₁.hom ≫ c₂.inv) (ComplexShape.up ℤ)).app X ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (Lf ⋙ E))
            (ComplexShape.up ℤ)).inv.app X =
        (NatTrans.mapHomologicalComplex c₁.hom (ComplexShape.up ℤ)).app X ≫
          (NatTrans.mapHomologicalComplex c₂.inv (ComplexShape.up ℤ)).app X := by
      ext n
      simp
    exact congrArg (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map h
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) (fun X => ?_)
  rw [derivedTwoSquare_app_Qh, hh]
  simp only [Stacks.CategoryTheory.BaseChange.pullbackComparison, NatTrans.comp_app,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryCompIsoOfIso_inv_app,
    Functor.mapDerivedCategoryCompIsoOfIso_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]

end Square

section Mate

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{w} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{w} B']
  {F : A ⥤ B} [F.Additive] {F' : A' ⥤ B'} [F'.Additive]
  {Lf : B ⥤ A} [Lf.Additive] [PreservesFiniteLimits Lf] [PreservesFiniteColimits Lf]
  {Lf' : B' ⥤ A'} [Lf'.Additive] [PreservesFiniteLimits Lf'] [PreservesFiniteColimits Lf']
  {E : A ⥤ A'} [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  {E' : B ⥤ B'} [E'.Additive] [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
  (adjf : Lf ⊣ F) (adjf' : Lf' ⊣ F') (α : TwoSquare E' Lf Lf' E)

omit [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [PreservesFiniteLimits Lf] [PreservesFiniteColimits Lf] [PreservesFiniteLimits Lf']
  [PreservesFiniteColimits Lf'] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  [PreservesFiniteLimits E'] [PreservesFiniteColimits E'] in
/-- **The degreewise counit identity of a mate, on the homotopy categories.** For the mate `c`
of `α`, applied degreewise and passed to the homotopy categories,
`Lf'(c_K) ≫ ε'_{E K} = α_{F K} ≫ E(ε_K)`. Read at the class of a complex and in a single degree
it is `CategoryTheory.mateEquiv_counit`. -/
theorem homotopy_mateEquiv_counit (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (Lf'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E')) (ComplexShape.up ℤ)).hom ≫
          NatTrans.mapHomotopyCategory (mateEquiv adjf adjf' α) (ComplexShape.up ℤ) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F'))
            (ComplexShape.up ℤ)).inv).app K) ≫
      (Adjunction.mapHomotopyCategoryAdjunction adjf' (ComplexShape.up ℤ)).counit.app
        ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
    (homotopyTwoSquare α).app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (E.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Adjunction.mapHomotopyCategoryAdjunction adjf (ComplexShape.up ℤ)).counit.app K) := by
  obtain ⟨K⟩ := K
  have h : (Lf'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E')) (ComplexShape.up ℤ)).hom ≫
          NatTrans.mapHomologicalComplex (mateEquiv adjf adjf' α)
            (ComplexShape.up ℤ) ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F'))
            (ComplexShape.up ℤ)).inv).app K) ≫
      (Adjunction.mapHomologicalComplexAdjunction adjf' (ComplexShape.up ℤ)).counit.app
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (E' ⋙ Lf')) (ComplexShape.up ℤ)).hom ≫
          NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ) ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (Lf ⋙ E))
            (ComplexShape.up ℤ)).inv).app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (E.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Adjunction.mapHomologicalComplexAdjunction adjf (ComplexShape.up ℤ)).counit.app K) := by
    ext n
    dsimp [Adjunction.mapHomologicalComplexAdjunction]
    simp
  exact congrArg (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map h

section General

variable {RF : DerivedCategory A ⥤ DerivedCategory B}
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  {RF' : DerivedCategory A' ⥤ DerivedCategory B'}
  (β' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')
  [RF'.IsRightDerivedFunctor β' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
    I.IsKInjective ∧ QuasiIso q)
  (hA' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (q : K ⟶ I),
    I.IsKInjective ∧ QuasiIso q)

/-- **The mate of the derived 2-square, precomposed with `E'` of the unit of `RF`**, at an object
`Q_h K`: it is the degreewise mate `c` of `α`, followed by the unit of `RF'`, up to the
exactness comparisons of `E` and `E'`. This holds for arbitrary right derived functors `RF`, `RF'`
of `F`, `F'` along `Q_h`, and is the defining property of the derived transformation of `c`,
whichever way that is formed. -/
theorem mateEquiv_derivedTwoSquare_fac (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    E'.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E')) (ComplexShape.up ℤ)).hom ≫
            NatTrans.mapHomotopyCategory (mateEquiv adjf adjf' α) (ComplexShape.up ℤ) ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F'))
              (ComplexShape.up ℤ)).inv).app K) ≫
        β'.app ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        RF'.map (E.mapDerivedCategoryFactorsh.inv.app K) =
      E'.mapDerivedCategory.map (β.app K) ≫
        (mateEquiv (Stacks.DerivedFunctor.derivedAdjunction adjf RF β hA)
          (Stacks.DerivedFunctor.derivedAdjunction adjf' RF' β' hA')
          (derivedTwoSquare α)).app (DerivedCategory.Qh.obj K) := by
  -- the two maps land in `RF'`; compare their transposes across `Lf' ⊣ RF'`
  apply ((Stacks.DerivedFunctor.derivedAdjunction adjf' RF' β' hA').homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    Functor.map_comp _ (E'.mapDerivedCategory.map (β.app K)), Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [mateEquiv_counit]
  -- the right-hand side
  have hnat := (derivedTwoSquare α).naturality (β.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hnat
  have hcounit := Stacks.DerivedFunctor.derivedAdjunction_counit_app adjf RF β hA K
  have hE := E.mapDerivedCategoryFactorsh.inv.naturality
    ((Adjunction.mapHomotopyCategoryAdjunction adjf (ComplexShape.up ℤ)).counit.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hE
  rw [reassoc_of% hnat, ← E.mapDerivedCategory.map_comp, hcounit, derivedTwoSquare_app_Qh]
  simp only [Category.assoc, Functor.map_comp]
  rw [← E.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← hE]
  -- the left-hand side
  have hcounit' := Stacks.DerivedFunctor.derivedAdjunction_counit_app adjf' RF' β' hA'
    ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have hL := Lf'.mapDerivedCategoryFactorsh.hom.naturality
    (((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E')) (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory (mateEquiv adjf adjf' α) (ComplexShape.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F'))
        (ComplexShape.up ℤ)).inv).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hL
  rw [Adjunction.counit_naturality, reassoc_of% hcounit', reassoc_of% hL,
    ← DerivedCategory.Qh.map_comp_assoc, homotopy_mateEquiv_counit, Functor.map_comp,
    Category.assoc]
  rfl

end General

section Total

variable [IsGrothendieckAbelian.{wG} A]
  [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
    I.IsKInjective ∧ QuasiIso q)
  (hA' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (q : K ⟶ I),
    I.IsKInjective ∧ QuasiIso q)

/-- **The derived transformation of a mate is the mate of the derived 2-square.** For
adjunctions `Lf ⊣ F` and `Lf' ⊣ F'` with exact left adjoints and a 2-square
`α : E' ⋙ Lf' ⟶ Lf ⋙ E` of exact functors, the derived transformation
`RF ⋙ E' ⟶ E ⋙ RF'` of the mate of `α` is the mate, under the derived adjunctions
`Lf ⊣ RF` and `Lf' ⊣ RF'`, of the derived 2-square of `α`. -/
theorem derivedSquare_mateEquiv :
    derivedSquare (mateEquiv adjf adjf' α) =
      (mateEquiv
        (Stacks.DerivedFunctor.derivedAdjunction adjf (totalRightDerived F)
          (totalRightDerivedUnit F) hA)
        (Stacks.DerivedFunctor.derivedAdjunction adjf' (totalRightDerived F')
          (totalRightDerivedUnit F') hA')
        (derivedTwoSquare α)) := by
  have := isRightDerivedFunctor_totalRightDerived_comp
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory
  refine Functor.rightDerived_ext (totalRightDerived F ⋙ E'.mapDerivedCategory)
    (totalRightDerivedCompUnit (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      E'.mapDerivedCategory)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [totalRightDerivedCompUnit_app, derivedSquare_fac_app]
  have hβ : (derivedSquareBeta (mateEquiv adjf adjf' α)).app K =
      E'.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E')) (ComplexShape.up ℤ)).hom ≫
            NatTrans.mapHomotopyCategory (mateEquiv adjf adjf' α) (ComplexShape.up ℤ) ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F'))
              (ComplexShape.up ℤ)).inv).app K) ≫
        (totalRightDerivedUnit F').app ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (totalRightDerived F').map (E.mapDerivedCategoryFactorsh.inv.app K) := by
    simp only [derivedSquareBeta, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [hβ]
  exact mateEquiv_derivedTwoSquare_fac adjf adjf' α (totalRightDerivedUnit F)
    (totalRightDerivedUnit F') hA hA' K

end Total


section Conversion

variable {RF : DerivedCategory A ⥤ DerivedCategory B}
  (αR : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)
  {RF' : DerivedCategory A' ⥤ DerivedCategory B'}
  (αR' : F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF')

/-- The unit along `Q_h` attached by `Stacks.DerivedAdjunction.homotopyUnitOfComplex` to a unit
`αR` along `Q`, at the class of a complex: it is `αR`, through the identifications of the two
localizations. -/
theorem homotopyUnitOfComplex_app_quotient (K : CochainComplex A ℤ) :
    (Stacks.DerivedAdjunction.homotopyUnitOfComplex F RF αR).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ αR.app K ≫
        RF.map ((DerivedCategory.quotientCompQhIso A).inv.app K) := by
  have h := NatTrans.congr_app (((Functor.whiskeringLeft _ _ (DerivedCategory B)).obj
      (HomotopyCategory.quotient A (ComplexShape.up ℤ))).map_preimage
    ((Stacks.DerivedAdjunction.rightDerivedSourceIso F).hom ≫ αR ≫
      (Stacks.DerivedAdjunction.quotientFactorIso RF).inv)) K
  refine h.trans ?_
  simp only [Stacks.DerivedAdjunction.rightDerivedSourceIso,
    Stacks.DerivedAdjunction.quotientFactorIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  exact Category.id_comp _

/-- **From the defining property along `Q_h` to the one along `Q`.** A transformation
`τ : RF ⋙ E' ⟶ E ⋙ RF'` that, precomposed with `E'` of the unit of `RF` along `Q_h`, is the
degreewise `c` followed by the unit of `RF'`, at the class of a complex `K`, satisfies the same
identity along `Q` at `K`, for the units along `Q` from which the units along `Q_h` are made by
`Stacks.DerivedAdjunction.homotopyUnitOfComplex`. It is stated for a variable `τ`. -/
theorem fac_Q_of_fac_Qh (c : F ⋙ E' ⟶ E ⋙ F')
    (τ : RF ⋙ E'.mapDerivedCategory ⟶ E.mapDerivedCategory ⋙ RF') (K : CochainComplex A ℤ)
    (h : E'.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        DerivedCategory.Qh.map
          (((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E')) (ComplexShape.up ℤ)).hom ≫
            NatTrans.mapHomotopyCategory c (ComplexShape.up ℤ) ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F'))
              (ComplexShape.up ℤ)).inv).app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        (Stacks.DerivedAdjunction.homotopyUnitOfComplex F' RF' αR').app
          ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        RF'.map (E.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      E'.mapDerivedCategory.map ((Stacks.DerivedAdjunction.homotopyUnitOfComplex F RF αR).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        τ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) :
    E'.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        E'.mapDerivedCategory.map (αR.app K) ≫ τ.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E'))
              (ComplexShape.up ℤ)).hom.app K ≫
            (NatTrans.mapHomologicalComplex c (ComplexShape.up ℤ)).app K ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F'))
              (ComplexShape.up ℤ)).inv.app K) ≫
        αR'.app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          RF'.map (E.mapDerivedCategoryFactors.inv.app K) := by
  have hn := τ.naturality ((DerivedCategory.quotientCompQhIso A).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [homotopyUnitOfComplex_app_quotient] at h
  simp only [Functor.map_comp, Category.assoc] at h
  rw [hn] at h
  -- solve `h` for `E'(αR K) ≫ τ (Q K)`
  have hP := congrArg (fun t => E'.mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso B).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      E'.mapDerivedCategory.map (DerivedCategory.Qh.map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K)) ≫ t ≫
      RF'.map (E.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app K))) h
  simp only [Category.assoc] at hP
  rw [← E'.mapDerivedCategory.map_comp_assoc (DerivedCategory.Qh.map _)
      (DerivedCategory.Qh.map _), ← DerivedCategory.Qh.map_comp, Iso.inv_hom_id_app] at hP
  dsimp only [Functor.comp_obj] at hP
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← E'.mapDerivedCategory.map_comp_assoc ((DerivedCategory.quotientCompQhIso B).inv.app _)
      ((DerivedCategory.quotientCompQhIso B).hom.app _), Iso.inv_hom_id_app] at hP
  rw [CategoryTheory.Functor.map_id, Category.id_comp,
    ← RF'.map_comp (E.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).inv.app K)),
    ← E.mapDerivedCategory.map_comp, Iso.inv_hom_id_app] at hP
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id] at hP
  rw [← hP]
  -- the comparison of `E'` along the two localizations
  have n1 := E'.mapDerivedCategoryFactorsh.hom.naturality
    ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at n1
  rw [reassoc_of% n1, Functor.mapDerivedCategoryFactorsh_hom_app E']
  simp only [Category.assoc]
  rw [← E'.mapDerivedCategory.map_comp_assoc ((DerivedCategory.quotientCompQhIso B).inv.app _)
    ((DerivedCategory.quotientCompQhIso B).hom.app _), Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  -- the degreewise `c`, read on the homotopy category of `B'`
  have hC : (E'.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (E'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
      (((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E')) (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory c (ComplexShape.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ F')) (ComplexShape.up ℤ)).inv).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E'))
              (ComplexShape.up ℤ)).hom.app K ≫
            (NatTrans.mapHomologicalComplex c (ComplexShape.up ℤ)).app K ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F'))
              (ComplexShape.up ℤ)).inv.app K) ≫
        (F'.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (F'.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) := by
    change (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
          (𝟙 ((E'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
        (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
          ((E'.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
        ((HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E'))
              (ComplexShape.up ℤ)).hom.app K) ≫
          (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex c (ComplexShape.up ℤ)).app K) ≫
          (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F'))
              (ComplexShape.up ℤ)).inv.app K)) =
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E'))
              (ComplexShape.up ℤ)).hom.app K ≫
            (NatTrans.mapHomologicalComplex c (ComplexShape.up ℤ)).app K ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F'))
              (ComplexShape.up ℤ)).inv.app K) ≫
        (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
          (𝟙 ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) ≫
        (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
          ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (𝟙 ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      Functor.map_comp]
    exact (Category.comp_id _).symm
  have hC' := congrArg DerivedCategory.Qh.map hC
  simp only [Functor.map_comp] at hC'
  rw [reassoc_of% hC', ← DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
    ← DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
    ← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  congr 3
  -- the unit of `RF'` along the two localizations
  have n2 := (Stacks.DerivedAdjunction.homotopyUnitOfComplex F' RF' αR').naturality
    ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at n2
  rw [reassoc_of% n2, homotopyUnitOfComplex_app_quotient]
  simp only [Category.assoc]
  rw [← DerivedCategory.Qh.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  congr 1
  simp only [← RF'.map_comp]
  congr 1
  -- the comparison of `E` along the two localizations
  rw [← cancel_epi (E.mapDerivedCategoryFactors.hom.app K), Iso.hom_inv_id_app,
    ← cancel_epi (E.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app K))]
  have m := (E.mapDerivedCategoryFactorsh_hom_app K).symm
  rw [reassoc_of% m, Iso.hom_inv_id_app_assoc]
  exact (Category.comp_id _).symm

end Conversion


section Cochain

variable [IsGrothendieckAbelian.{wG} A] {RF : DerivedCategory A ⥤ DerivedCategory B}
  (αR : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)
  [RF.IsRightDerivedFunctor αR (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  {RF' : DerivedCategory A' ⥤ DerivedCategory B'}
  (αR' : F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF')
  [RF'.IsRightDerivedFunctor αR' (HomologicalComplex.quasiIso A' (ComplexShape.up ℤ))]
  (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : K ⟶ I),
    I.IsKInjective ∧ QuasiIso q)
  (hA' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (q : K ⟶ I),
    I.IsKInjective ∧ QuasiIso q)

/-- **The derived transformation of a mate along `Q` is the mate of the derived 2-square.** For
adjunctions `Lf ⊣ F` and `Lf' ⊣ F'` with exact left adjoints, a 2-square
`α : E' ⋙ Lf' ⟶ Lf ⋙ E` of exact functors, and right derived functors `RF`, `RF'` of `F`, `F'`
formed along the localization `Q` of cochain complexes with units `αR`, `αR'`, the derived
transformation `RF ⋙ E' ⟶ E ⋙ RF'` of the mate of `α` (`cochainDerivedSquare`) is the mate,
under the derived adjunctions `Lf ⊣ RF` and `Lf' ⊣ RF'` (read along `Q_h` by
`Stacks.DerivedAdjunction.homotopyUnitOfComplex`), of the derived 2-square of `α`.

This is `Stacks.Homology.DerivedSquare.derivedSquare_mateEquiv` for right derived functors along
`Q`, such as the unbounded derived direct images of sheaves of modules. -/
theorem cochainDerivedSquare_mateEquiv :
    cochainDerivedSquare αR αR' (mateEquiv adjf adjf' α) =
      haveI := Stacks.DerivedAdjunction.homotopyUnitOfComplex_isRightDerivedFunctor F RF αR
      haveI := Stacks.DerivedAdjunction.homotopyUnitOfComplex_isRightDerivedFunctor F' RF' αR'
      (mateEquiv
        (Stacks.DerivedFunctor.derivedAdjunction adjf RF
          (Stacks.DerivedAdjunction.homotopyUnitOfComplex F RF αR) hA)
        (Stacks.DerivedFunctor.derivedAdjunction adjf' RF'
          (Stacks.DerivedAdjunction.homotopyUnitOfComplex F' RF' αR') hA')
        (derivedTwoSquare α)) := by
  have := Stacks.DerivedAdjunction.homotopyUnitOfComplex_isRightDerivedFunctor F RF αR
  have := Stacks.DerivedAdjunction.homotopyUnitOfComplex_isRightDerivedFunctor F' RF' αR'
  refine Functor.rightDerived_ext (RF ⋙ E'.mapDerivedCategory) (cochainDerivedSquareUnit αR)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  have e₁ : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ E'))
      (ComplexShape.up ℤ)).inv.app K = 𝟙 _ := by ext; simp
  have hu : (cochainDerivedSquareUnit (E' := E') αR).app K =
      E'.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        E'.mapDerivedCategory.map (αR.app K) := by
    simp only [cochainDerivedSquareUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, e₁, CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  rw [hu, Category.assoc, Category.assoc, cochainDerivedSquare_fac_app']
  exact (fac_Q_of_fac_Qh αR αR' _ _ K (mateEquiv_derivedTwoSquare_fac adjf adjf' α _ _ hA hA'
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).symm

end Cochain

end Mate

end Stacks.Homology.DerivedSquare

end
