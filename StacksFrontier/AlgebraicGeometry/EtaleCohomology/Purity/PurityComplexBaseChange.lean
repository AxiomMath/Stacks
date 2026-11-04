module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityInput
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ConstantFiniteModule
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# Base change of `R j_*(j⁻¹ H)` along a cartesian square, from purity

Let `j : U₀ ⟶ U` be an open immersion, `u' : U' ⟶ U` a morphism and `j' : U₀' ⟶ U'`,
`u₀ : U₀' ⟶ U₀` the pullback of `j` along `u'`. For a sheaf `H` of `Λ`-modules on `U` the base
change map `β : u'⁻¹ R j_*(j⁻¹ H) ⟶ R j'_*(u₀⁻¹ j⁻¹ H)`
(`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange`) is an isomorphism as soon as

* the units `H ⟶ j_* j⁻¹ H` and `u'⁻¹ H ⟶ j'_* j'⁻¹ u'⁻¹ H` are invertible (`(P0)` on `U` and on
  `U'`),
* `H¹(β)` is invertible (`(BC1)`), and
* `R^q j_*(j⁻¹ H) = 0` and `R^q j'_*(j'⁻¹ u'⁻¹ H) = 0` for `q ≥ 2` (`(P2)` on `U` and on `U'`).

An isomorphism of `D⁺` is one on every cohomology sheaf. In degrees `q < 0` and `q ≥ 2` both
sides vanish. In degree `0`, `H⁰(β)` is read through the derived-functor units of `j_*` and
`j'_*`, which are invertible on `H⁰` as both functors are left exact
(`CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`),
as the underived base change map `u'⁻¹ j_* (j⁻¹ H) ⟶ j'_* u₀⁻¹ (j⁻¹ H)`; that map is invertible
because its restriction to `U₀'` is (the counits of open immersions are invertible) and its
source is `j'`-local (it is `u'⁻¹ H` by `(P0)` on `U`, and `(P0)` on `U'`).

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImageFullyFaithfulOfMono`: the direct image along an
  étale monomorphism is fully faithful.
* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_app_restriction`: the underived base change
  map at `j⁻¹ H`.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_app_single_restriction`: the derived
  base change map at `j⁻¹ H`.

## Implementation notes

The statements are made in the standard model `HasDerivedCategory.standard`, in which
`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange` and the purity propositions are stated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

section FullyFaithful

variable (Λ : Type r) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [Mono j]

/-- **The direct image along an étale monomorphism is fully faithful**: it is isomorphic to the
right Kan extension along composition with `j`, whose counit is invertible
(`Stacks.EtaleCohomology.etaleModuleEtaleDirectImageAdj_counit_isIso`). -/
def etaleModuleDirectImageFullyFaithfulOfMono :
    (etaleModuleDirectImage.{u, r} Λ j).FullyFaithful :=
  (etaleModuleEtaleDirectImageAdj.{u, r} Λ j).fullyFaithfulROfIsIsoCounit.ofIso
    ((etaleModuleEtaleDirectImageAdj.{u, r} Λ j).rightAdjointUniq
      (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j))

/-- The direct image along an étale monomorphism is full. -/
instance etaleModuleDirectImage_full_of_mono : (etaleModuleDirectImage.{u, r} Λ j).Full :=
  (etaleModuleDirectImageFullyFaithfulOfMono Λ j).full

/-- The direct image along an étale monomorphism is faithful. -/
instance etaleModuleDirectImage_faithful_of_mono : (etaleModuleDirectImage.{u, r} Λ j).Faithful :=
  (etaleModuleDirectImageFullyFaithfulOfMono Λ j).faithful

/-- **A map into a direct image along an étale monomorphism `j` is invertible when its source is
`j`-local and its restriction along `j` is invertible.** -/
theorem isIso_of_isIso_unit_of_isIso_inverseImage_map {A : EtaleModules.{u, r} Λ X}
    {B : EtaleModules.{u, r} Λ U} (φ : A ⟶ (etaleModuleDirectImage.{u, r} Λ j).obj B)
    (hA : IsIso ((etaleModuleInverseImageAdj.{u, r} Λ j).unit.app A))
    (hφ : IsIso ((etaleModuleInverseImage.{u, r} Λ j).map φ)) : IsIso φ := by
  set adj := etaleModuleInverseImageAdj.{u, r} Λ j
  have hB : IsIso (adj.unit.app ((etaleModuleDirectImage.{u, r} Λ j).obj B)) := by
    have h := adj.right_triangle_components B
    have : IsIso (adj.unit.app ((etaleModuleDirectImage.{u, r} Λ j).obj B) ≫
        (etaleModuleDirectImage.{u, r} Λ j).map (adj.counit.app B)) := by
      rw [h]; exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ ((etaleModuleDirectImage.{u, r} Λ j).map (adj.counit.app B))
  have hn := adj.unit.naturality φ
  rw [CategoryTheory.Functor.id_map] at hn
  have : IsIso (φ ≫ adj.unit.app ((etaleModuleDirectImage.{u, r} Λ j).obj B)) := by
    rw [hn]
    show IsIso (adj.unit.app A ≫ (etaleModuleDirectImage.{u, r} Λ j).map
      ((etaleModuleInverseImage.{u, r} Λ j).map φ))
    infer_instance
  exact IsIso.of_isIso_comp_right φ (adj.unit.app ((etaleModuleDirectImage.{u, r} Λ j).obj B))

end FullyFaithful

section Underived

variable (Λ : Type) [Ring Λ] {U U₀ U' U₀' : Scheme.{u}} (j : U₀ ⟶ U) [IsOpenImmersion j]
  (j' : U₀' ⟶ U') [IsOpenImmersion j'] (u' : U' ⟶ U) (u₀ : U₀' ⟶ U₀) (w : j' ≫ u' = u₀ ≫ j)

/-- The unit of `j⁻¹ ⊣ j_*` is invertible at `A` exactly when the unit of restriction along `j`
is: the two left adjoints of `j_*` are isomorphic. -/
theorem isIso_inverseImageAdj_unit_app_iff (A : EtaleModules.{u, 0} Λ U) :
    IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ j).unit.app A) ↔
      IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app A) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (etaleModuleInverseImageAdj.{u, 0} Λ j)
    (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j) A
  constructor
  · intro _; rw [← h]; infer_instance
  · intro h'
    rw [← h] at h'
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h'

/-- **The underived base change map at `j⁻¹ H`, from `(P0)` on `U` and on `U'`.** If the units
`H ⟶ j_* j⁻¹ H` and `u'⁻¹ H ⟶ j'_* j'⁻¹ u'⁻¹ H` are invertible, so is the base change map
`u'⁻¹ j_*(j⁻¹ H) ⟶ j'_* u₀⁻¹ (j⁻¹ H)`. -/
theorem isIso_etaleModuleBaseChange_app_restriction (H : EtaleModules.{u, 0} Λ U)
    (h0 : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app H))
    (h0' : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j').unit.app
      ((etaleModuleInverseImage.{u, 0} Λ u').obj H))) :
    IsIso ((etaleModuleBaseChange Λ j j' u' u₀ w).app
      ((etaleModuleRestriction.{u, 0} Λ j).obj H)) := by
  set X := (etaleModuleRestriction.{u, 0} Λ j).obj H
  refine isIso_of_isIso_unit_of_isIso_inverseImage_map Λ j' _ ?_ ?_
  · have h1 : IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ j').unit.app
        ((etaleModuleInverseImage.{u, 0} Λ u').obj H)) :=
      (isIso_inverseImageAdj_unit_app_iff Λ j' _).2 h0'
    exact (NatTrans.isIso_app_iff_of_iso (etaleModuleInverseImageAdj.{u, 0} Λ j').unit
      ((etaleModuleInverseImage.{u, 0} Λ u').mapIso (asIso
        ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app H)))).1 h1
  · have h := inverseImage_map_etaleModuleBaseChange_comp_counit Λ j j' u' u₀ w X
    have : IsIso ((etaleModuleInverseImage.{u, 0} Λ j').map
        ((etaleModuleBaseChange Λ j j' u' u₀ w).app X) ≫
        (etaleModuleInverseImageAdj.{u, 0} Λ j').counit.app
          ((etaleModuleInverseImage.{u, 0} Λ u₀).obj X)) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((etaleModuleInverseImageAdj.{u, 0} Λ j').counit.app
      ((etaleModuleInverseImage.{u, 0} Λ u₀).obj X))

end Underived

section Single

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- **A transformation invertible at `M` is invertible at the complex `M[0]`** of the bounded
below homotopy category: the induced map of complexes is `α_M` in degree `0` and a map of zero
objects elsewhere. -/
theorem isIso_mapHomotopyCategoryPlusNatTrans_app_single {F G : A ⥤ B} [F.Additive]
    [G.Additive] (α : F ⟶ G) (M : A) (hM : IsIso (α.app M)) :
    IsIso ((Functor.mapHomotopyCategoryPlusNatTrans α).app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M)) := by
  have : ∀ n : ℤ, IsIso (((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)).f n) := by
    intro n
    rw [NatTrans.mapHomologicalComplex_app_f]
    by_cases hn : n = 0
    · subst hn
      exact (NatTrans.isIso_app_iff_of_iso α (HomologicalComplex.singleObjXSelf _ 0 M)).2 hM
    · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn
      exact ⟨0, (F.map_isZero hz).eq_of_src _ _, (G.map_isZero hz).eq_of_src _ _⟩
  have : IsIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((HomotopyCategory.Plus.ι B).map ((Functor.mapHomotopyCategoryPlusNatTrans α).app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M))) := by
    show IsIso ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)))
    infer_instance
  exact isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι B)

end Single

section Derived

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [EnoughInjectives A] [EnoughInjectives A']
  (F : A ⥤ B) (F' : A' ⥤ B') (G : B ⥤ B') (G' : A ⥤ A')
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F] [PreservesFiniteLimits F']
  (α : F ⋙ G ⟶ G' ⋙ F')

/-- **`H⁰` of the derived base change map at `M[0]` is invertible when `α` is invertible at `M`,
for left exact `F` and `F'`.** The base change map, precomposed with `G` of the derived-functor
unit of `RF`, is the degreewise `α` followed by the derived-functor unit of `RF'`
(`Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus_fac`), and both units are
invertible on `H⁰` as `F` and `F'` are left exact
(`CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`). -/
theorem _root_.Stacks.Cohomology.DerivedBaseChangePlus.isIso_homology_zero_derivedBaseChangePlus_app_single
    (M : A) (hM : IsIso (α.app M)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B' 0).map
      ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus F F' G G' α).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M))) := by
  set K := (HomotopyCategory.Plus.singleFunctor A 0).obj M
  set β := Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus F F' G G' α
  set H0 := DerivedCategory.Plus.homologyFunctor B' 0
  refine (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight β H0)
    ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).app M).symm).1 ?_
  show IsIso (H0.map (β.app (DerivedCategory.Plus.Qh.obj K)))
  have hfac := congrArg H0.map
    (Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus_fac F F' G G' α K)
  rw [Functor.map_comp] at hfac
  have h1 :
      IsIso (H0.map (G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnit.app K))) := by
    let e : G.mapDerivedCategoryPlus ⋙ H0 ≅ DerivedCategory.Plus.homologyFunctor B 0 ⋙ G :=
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι (Stacks.Homology.derivedHomologyIso G 0)
    have h0 := (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
      F _ F.rightDerivedFunctorPlusUnit).2.2.2 inferInstance M
    have : IsIso (G.map ((DerivedCategory.Plus.homologyFunctor B 0).map
        (F.rightDerivedFunctorPlusUnit.app K))) := inferInstance
    exact (NatIso.isIso_map_iff e _).2 this
  have hα := isIso_mapHomotopyCategoryPlusNatTrans_app_single α M hM
  have h2 : IsIso (H0.map (F'.rightDerivedFunctorPlusUnit.app
      (G'.mapHomotopyCategoryPlus.obj K))) := by
    have h0 := (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
      F' _ F'.rightDerivedFunctorPlusUnit).2.2.2 inferInstance (G'.obj M)
    exact (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight F'.rightDerivedFunctorPlusUnit H0)
      ((Functor.mapHomotopyCategoryPlusSingleFunctor G' 0).app M)).2 h0
  have h3 : IsIso (H0.map
      ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusAux F F' G G' α).app K)) := by
    rw [Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusAux_app]
    simp only [Functor.map_comp]
    infer_instance
  rw [← hfac] at h3
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 h3

variable (Λ : Type) [Ring Λ]

/-- **`H⁰` of the derived base change map at a sheaf is the underived base change map**: if
`g⁻¹ f_* M ⟶ f'_* g'⁻¹ M` is invertible, so is `H⁰` of `g⁻¹ Rf_*(M[0]) ⟶ Rf'_* g'⁻¹(M[0])`
(`Stacks.Cohomology.DerivedBaseChangePlus.isIso_homology_zero_derivedBaseChangePlus_app_single`;
`f_*` and `f'_*` are left exact). -/
theorem isIso_homology_zero_etaleModuleDerivedBaseChange_app_single {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X) (w : f' ≫ g = g' ≫ f)
    (M : EtaleModules.{u, 0} Λ X) (hM : IsIso ((etaleModuleBaseChange Λ f f' g g' w).app M)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ Y') 0).map
      ((etaleModuleDerivedBaseChange.{u, 0} Λ f f' g g' w).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) := by
  have := etaleModules_enoughInjectives.{u, 0} Λ X
  have := etaleModules_enoughInjectives.{u, 0} Λ X'
  exact Stacks.Cohomology.DerivedBaseChangePlus.isIso_homology_zero_derivedBaseChangePlus_app_single
    _ _ _ _ _ M hM

/-- The restriction of `j⁻¹ H` along the pullback `u₀` of `u'` is the restriction along `j'` of
`u'⁻¹ H`, for `j' ≫ u' = u₀ ≫ j`. -/
def etaleModuleInverseImageRestrictionSquareIso {U U₀ U' U₀' : Scheme.{u}} (j : U₀ ⟶ U)
    [IsOpenImmersion j] (j' : U₀' ⟶ U') [IsOpenImmersion j'] (u' : U' ⟶ U) (u₀ : U₀' ⟶ U₀)
    (w : j' ≫ u' = u₀ ≫ j) (H : EtaleModules.{u, 0} Λ U) :
    (etaleModuleInverseImage.{u, 0} Λ u₀).obj ((etaleModuleRestriction.{u, 0} Λ j).obj H) ≅
      (etaleModuleRestriction.{u, 0} Λ j').obj ((etaleModuleInverseImage.{u, 0} Λ u').obj H) :=
  (etaleModuleInverseImage.{u, 0} Λ u₀).mapIso
      ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app H).symm ≪≫
    (etaleModuleBaseChangeComparison Λ j j' u' u₀ w).app H ≪≫
    (etaleModuleInverseImageCompIso.{u, 0} Λ j' u').app H ≪≫
    (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').app
      ((etaleModuleInverseImage.{u, 0} Λ u').obj H)

/-- `H^m(R h_*(Y[0]))` vanishes for `m < 0`, and for `m ≥ 2` when `R^q h_* Y` does. -/
theorem isZero_homology_etaleModuleDerivedDirectImage_single {T S : Scheme.{u}} (h : T ⟶ S)
    (Y : EtaleModules.{u, 0} Λ T)
    (hY : ∀ q : ℕ, 2 ≤ q → IsZero (((etaleModuleDirectImage.{u, 0} Λ h).rightDerived q).obj Y))
    (m : ℤ) (hm : m < 0 ∨ 2 ≤ m) : IsZero ((DerivedCategory.Plus.homologyFunctor _ m).obj
      ((etaleModuleDerivedDirectImage.{u, 0} Λ h).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj Y))) := by
  rcases hm with hm | hm
  · exact ((Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
      (etaleModuleDirectImage.{u, 0} Λ h) _
      (etaleModuleDirectImage.{u, 0} Λ h).rightDerivedFunctorPlusUnit).1 m hm).obj Y
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, m = q := ⟨m.toNat, by omega⟩
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
      (etaleModuleDirectImage.{u, 0} Λ h) rfl Y).2 (hY q (by omega))

/-- `H^m(u⁻¹ R j_*(X[0]))` vanishes for `m < 0`, and for `m ≥ 2` when `R^q j_* X` does. -/
theorem isZero_homology_inverseImage_derivedDirectImage_single {U U₀ U' : Scheme.{u}}
    (j : U₀ ⟶ U) (u' : U' ⟶ U) (X : EtaleModules.{u, 0} Λ U₀)
    (h2 : ∀ q : ℕ, 2 ≤ q → IsZero (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj X))
    (m : ℤ) (hm : m < 0 ∨ 2 ≤ m) : IsZero ((DerivedCategory.Plus.homologyFunctor _ m).obj
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ u').obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj X)))) :=
  ((etaleModuleInverseImage.{u, 0} Λ u').map_isZero
    (isZero_homology_etaleModuleDerivedDirectImage_single Λ j X h2 m hm)).of_iso
    (nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ u' _ m).some

/-- `H^m(R j'_*(u₀⁻¹ (j⁻¹ H)[0]))` vanishes for `m < 0`, and for `m ≥ 2` when
`R^q j'_*(j'⁻¹ u'⁻¹ H)` does. -/
theorem isZero_homology_derivedDirectImage_inverseImage_single {U U₀ U' U₀' : Scheme.{u}}
    (j : U₀ ⟶ U) [IsOpenImmersion j] (j' : U₀' ⟶ U') [IsOpenImmersion j'] (u' : U' ⟶ U)
    (u₀ : U₀' ⟶ U₀) (w : j' ≫ u' = u₀ ≫ j) (H : EtaleModules.{u, 0} Λ U)
    (h2' : ∀ q : ℕ, 2 ≤ q → IsZero (((etaleModuleDirectImage.{u, 0} Λ j').rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ j').obj ((etaleModuleInverseImage.{u, 0} Λ u').obj H))))
    (m : ℤ) (hm : m < 0 ∨ 2 ≤ m) : IsZero ((DerivedCategory.Plus.homologyFunctor _ m).obj
      ((etaleModuleDerivedDirectImage.{u, 0} Λ j').obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ u₀).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleRestriction.{u, 0} Λ j).obj H))))) :=
  (isZero_homology_etaleModuleDerivedDirectImage_single Λ j' _ h2' m hm).of_iso
    ((DerivedCategory.Plus.homologyFunctor _ m).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ j').mapIso
        ((etaleModuleInverseImage.{u, 0} Λ u₀).mapDerivedCategoryPlusObjSingleIso _ ≪≫
          (DerivedCategory.Plus.singleFunctor _ 0).mapIso
            (etaleModuleInverseImageRestrictionSquareIso Λ j j' u' u₀ w H))))

/-- `H⁰` of the base change map of `R j_*(j⁻¹ H)`, from `(P0)` on `U` and `U'`. -/
theorem isIso_homology_zero_etaleModuleDerivedBaseChange_app_single_restriction
    {U U₀ U' U₀' : Scheme.{u}} (j : U₀ ⟶ U) [IsOpenImmersion j] (j' : U₀' ⟶ U')
    [IsOpenImmersion j'] (u' : U' ⟶ U)
    (u₀ : U₀' ⟶ U₀) (sq : IsPullback u₀ j' j u') (H : EtaleModules.{u, 0} Λ U)
    (h0 : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app H))
    (h0' : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j').unit.app
      ((etaleModuleInverseImage.{u, 0} Λ u').obj H))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ U') 0).map
      ((etaleModuleDerivedBaseChange.{u, 0} Λ j j' u' u₀ sq.w.symm).app
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ U₀) 0).obj
          ((etaleModuleRestriction.{u, 0} Λ j).obj H)))) :=
  isIso_homology_zero_etaleModuleDerivedBaseChange_app_single Λ j j' u' u₀ sq.w.symm _
    (isIso_etaleModuleBaseChange_app_restriction Λ j j' u' u₀ sq.w.symm H h0 h0')

/-- **The base change of `R j_*(j⁻¹ H)` along a cartesian square, from purity.** For the pullback
`j' : U₀' ⟶ U'` of the open immersion `j : U₀ ⟶ U` along `u' : U' ⟶ U`, the base change map
`u'⁻¹ R j_*(j⁻¹ H) ⟶ R j'_*(u₀⁻¹ j⁻¹ H)` is an isomorphism when the units of `j` at `H` and of
`j'` at `u'⁻¹ H` are invertible (`(P0)` on `U` and `U'`), its `H¹` is invertible (`(BC1)`), and
`R^q j_*(j⁻¹ H)` and `R^q j'_*(j'⁻¹ u'⁻¹ H)` vanish for `q ≥ 2` (`(P2)` on `U` and `U'`). -/
theorem isIso_etaleModuleDerivedBaseChange_app_single_restriction {U U₀ U' U₀' : Scheme.{u}}
    (j : U₀ ⟶ U) [IsOpenImmersion j] (j' : U₀' ⟶ U') [IsOpenImmersion j'] (u' : U' ⟶ U)
    (u₀ : U₀' ⟶ U₀) (sq : IsPullback u₀ j' j u') (H : EtaleModules.{u, 0} Λ U)
    (h0 : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app H))
    (h0' : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j').unit.app
      ((etaleModuleInverseImage.{u, 0} Λ u').obj H)))
    (h1 : IsIso ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ U') 1).map
      ((etaleModuleDerivedBaseChange.{u, 0} Λ j j' u' u₀ sq.w.symm).app
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ U₀) 0).obj
          ((etaleModuleRestriction.{u, 0} Λ j).obj H)))))
    (h2 : ∀ q : ℕ, 2 ≤ q → IsZero (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ j).obj H)))
    (h2' : ∀ q : ℕ, 2 ≤ q → IsZero (((etaleModuleDirectImage.{u, 0} Λ j').rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ j').obj ((etaleModuleInverseImage.{u, 0} Λ u').obj H)))) :
    IsIso ((etaleModuleDerivedBaseChange.{u, 0} Λ j j' u' u₀ sq.w.symm).app
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ U₀) 0).obj
        ((etaleModuleRestriction.{u, 0} Λ j).obj H))) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  by_cases hn : n < 0 ∨ 2 ≤ n
  · exact ⟨0, (isZero_homology_inverseImage_derivedDirectImage_single Λ j u' _ h2 n hn).eq_of_src
      _ _, (isZero_homology_derivedDirectImage_inverseImage_single Λ j j' u' u₀ sq.w.symm H h2' n
      hn).eq_of_src _ _⟩
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact isIso_homology_zero_etaleModuleDerivedBaseChange_app_single_restriction Λ j j' u' u₀
        sq H h0 h0'
    · exact h1

end Derived

end Stacks.EtaleCohomology

end
