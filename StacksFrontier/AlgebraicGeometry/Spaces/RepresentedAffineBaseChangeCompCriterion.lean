module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapMate

/-!
# The base change map of affine representables through the ring comparison

For a commutative square `g₀' ≫ f₀ = f₀' ≫ g₀` of objects of the big fppf site with affine
underlying schemes, with rings of global functions `R = Γ(V)`, `A = Γ(U)`, `R' = Γ(V')` and
`A' = Γ(U')`, the composite `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K ⟶ Rf'_* K'` of Stacks 0DKH at
`K = Φ_A M`, `K' = Φ_{A'} M'` and the map `L(g')^* Φ_A M ≅ Φ_{A'}(M ⊗ᴸ_A A') ⟶ Φ_{A'} M'`
induced by `φ : M ⊗ᴸ_A A' ⟶ M'` is invertible exactly when the comparison of Stacks 065Z for the
square of rings at `M` followed by `φ` is.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAffineBaseChangeComp_iff`
* `AlgebraicGeometry.Space.isIso_representedAffineBaseChangeComp_iff_forall_cohomology`: the same
  with the comparison read on cohomology, for the algebra structures given by the maps of global
  functions.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/- The filtered colimits used to form the étale sheafification, through Mathlib's instance, so that
the derived categories of `𝒪`-modules below are spelled as in the files of the derived pullback. -/
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)

/-- The transposed unit of an affine morphism of affine representables is an isomorphism. -/
private theorem isIso_representedAffineTransportUnit_of_isAffine {U' U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) :
    IsIso (Stacks.CategoryTheory.BaseChange.transportUnit
      (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
        (representedAffineCommRingCatHom B S hS g).hom)
      (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS g))
      (representedAffineToposDerivedAssociated B S hS U)
      (representedAffineToposDerivedAssociated B S hS U')
      (representedAffineToposDerivedBaseChangeIso B S hS g) M) :=
  isIso_representedAffineTransportUnit B S hS g
    (isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U' inferInstance)
      (isAffineSpace_yoneda B S hS U inferInstance)) M

include w₀ in
/-- **The base change map of affine representables is the ring comparison.**  The composite of
Stacks 0DKH at `Φ_A M`, `Φ_{A'} M'` and the map induced by `φ : M ⊗ᴸ_A A' ⟶ M'` is invertible
if and only if the comparison of Stacks 065Z at `M` followed by `φ` is. -/
theorem isIso_representedAffineBaseChangeComp_iff
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (M' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    (φ : (representedAffineDerivedExtension B S hS g₀').functor.obj M ⟶ M') :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        ((representedAffineToposDerivedAssociated B S hS U).obj M)
        ((representedAffineToposDerivedAssociated B S hS U').obj M')
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app M ≫
          (representedAffineToposDerivedAssociated B S hS U').map φ)) ↔
      IsIso ((RingTheory.TorIndependence.ringHomSquareComparison
          (representedAffineCommRingCatHom B S hS f₀).hom
          (representedAffineCommRingCatHom B S hS g₀).hom
          (representedAffineCommRingCatHom B S hS g₀').hom
          (representedAffineCommRingCatHom B S hS f₀').hom
          ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
            (representedAffineRingHom_comp B S hS f₀' g₀))).app M ≫
        (ModuleCat.restrictScalars
            (representedAffineCommRingCatHom B S hS f₀').hom).mapDerivedCategory.map
          φ) := by
  refine (exists_isUnit_representedAffinePath B S hS f₀ g₀ f₀' g₀' w₀).elim fun c hch => ?_
  have hc := hch.1
  have hpath := hch.2
  have := isIso_representedAffineTransportUnit_of_isAffine B S hS f₀ M
  have := isIso_representedAffineTransportUnit_of_isAffine B S hS f₀' M'
  have : (representedAffineToposDerivedAssociated B S hS V').ReflectsIsomorphisms :=
    (representedAffineDerivedAdjunction B S hS V').fullyFaithfulLOfIsIsoUnit.reflectsIsomorphisms
  refine (Stacks.CategoryTheory.BaseChange.isIso_map_comp_iff_of_central
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS f₀).hom)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS f₀').hom)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
      (representedAffineCommRingCatHom B S hS g₀).hom
      (representedAffineCommRingCatHom B S hS f₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_comp B S hS f₀' g₀).symm)
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
      (representedAffineCommRingCatHom B S hS f₀).hom
      (representedAffineCommRingCatHom B S hS g₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀))
    (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS f₀))
    (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS f₀'))
    (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀))
    (smallEtaleDerivedModulePullbackSquareIso B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
      (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀))
    (representedAffineToposDerivedAssociated B S hS V)
    (representedAffineToposDerivedAssociated B S hS U)
    (representedAffineToposDerivedAssociated B S hS V')
    (representedAffineToposDerivedAssociated B S hS U')
    (representedAffineToposDerivedBaseChangeIso B S hS f₀)
    (representedAffineToposDerivedBaseChangeIso B S hS f₀')
    (representedAffineToposDerivedBaseChangeIso B S hS g₀)
    (representedAffineToposDerivedBaseChangeIso B S hS g₀') (unitCentralIso c hc)
    (Stacks.CategoryTheory.BaseChange.hhex_of_comp_eq (t := unitCentralIso c hc)
      (h := representedAffineToposDerivedBaseChange_compat_of_path B S hS f₀ g₀ f₀' g₀' w₀ c hc
        (NatTrans.ext (funext fun M => (hpath M).trans rfl)))) φ).trans ?_
  rw [RingTheory.TorIndependence.ringHomSquareComparison_app_eq_map _ _ _ _ _
    (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀)
    (representedAffineRingHom_comp B S hS f₀' g₀).symm]


include w₀ in
/-- **The base change map of affine representables, on cohomology.**  With the algebra
structures given by the maps of rings of global functions, the composite of Stacks 0DKH at
`Φ_A M`, `Φ_{A'} M'` and the map induced by `φ` is invertible if and only if every comparison
`H^n(M ⊗ᴸ_R R') ⟶ H^n(M')` of Stacks 065Z followed by `φ` is. -/
theorem isIso_representedAffineBaseChangeComp_iff_forall_cohomology
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (M' : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)))
    (φ : (representedAffineDerivedExtension B S hS g₀').functor.obj M ⟶ M') :
    letI := (representedAffineCommRingCatHom B S hS f₀).hom.toAlgebra
    letI := (representedAffineCommRingCatHom B S hS g₀).hom.toAlgebra
    letI := (representedAffineCommRingCatHom B S hS g₀').hom.toAlgebra
    letI := (representedAffineCommRingCatHom B S hS f₀').hom.toAlgebra
    letI := ((representedAffineCommRingCatHom B S hS f₀').hom.comp
      (representedAffineCommRingCatHom B S hS g₀).hom).toAlgebra
    haveI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
      IsScalarTower.of_algebraMap_eq'
        ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
          (representedAffineRingHom_comp B S hS f₀' g₀)).symm
    haveI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
      IsScalarTower.of_algebraMap_eq' rfl
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        ((representedAffineToposDerivedAssociated B S hS U).obj M)
        ((representedAffineToposDerivedAssociated B S hS U').obj M')
        ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app M ≫
          (representedAffineToposDerivedAssociated B S hS U').map φ)) ↔
      ∀ n, IsIso (RingTheory.TorIndependence.cohomologyComparisonMap
        (R := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
        (R' := Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)) M M' φ n) :=
  (isIso_representedAffineBaseChangeComp_iff B S hS f₀ g₀ f₀' g₀' w₀ M M' φ).trans
    (RingTheory.TorIndependence.isIso_ringHomSquareComparison_comp_iff_forall_cohomology
      _ _ _ _ _ M M' φ)

section Sections


/-- The map `RΓ(U, K) ⊗ᴸ_{𝒪(U)} 𝒪(U') ⟶ RΓ(U', K')` attached to `φ : L(g')^*K ⟶ K'` for a
morphism `g' : U' ⟶ U` of affine objects: the transpose under `Φ ⊣ RΓ` of
`Φ(RΓ(U, K) ⊗ᴸ 𝒪(U')) ≅ L(g')^*Φ(RΓ(U, K)) ⟶ L(g')^*K ⟶ K'`. -/
noncomputable def representedAffineSectionsBaseChangeMap
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K') :
    (representedAffineDerivedExtension B S hS g₀').functor.obj
        ((representedAffineDerivedSections B S hS U).obj K) ⟶
      (representedAffineDerivedSections B S hS U').obj K' :=
  (representedAffineDerivedAdjunction B S hS U').homEquiv _ _
    ((representedAffineToposDerivedBaseChangeIso B S hS g₀').inv.app _ ≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
        ((representedAffineDerivedAdjunction B S hS U).counit.app K) ≫ φ)

/-- The map `RΓ(U, K) ⊗ᴸ 𝒪(U') ⟶ RΓ(U', K')` recovers `φ` through the counits of `Φ ⊣ RΓ`. -/
theorem representedAffineSectionsBaseChangeMap_spec
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K') :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
        ((representedAffineDerivedAdjunction B S hS U).counit.app K) ≫ φ =
      (representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app _ ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          (representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ) ≫
        (representedAffineDerivedAdjunction B S hS U').counit.app K' := by
  have h : (representedAffineToposDerivedBaseChangeIso B S hS g₀').inv.app _ ≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
        ((representedAffineDerivedAdjunction B S hS U).counit.app K) ≫ φ =
      (representedAffineToposDerivedAssociated B S hS U').map
          (representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ) ≫
        (representedAffineDerivedAdjunction B S hS U').counit.app K' := by
    have h0 := (representedAffineDerivedAdjunction B S hS U').homEquiv_counit
      (g := representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ)
    rw [representedAffineSectionsBaseChangeMap, Equiv.symm_apply_apply] at h0
    exact h0
  exact (Iso.inv_comp_eq ((representedAffineToposDerivedBaseChangeIso B S hS g₀').app _)).mp h

/-- The composite `RΓ(U, K) ⊗ᴸ_{𝒪(V)} 𝒪(V') ⟶ RΓ(U, K) ⊗ᴸ_{𝒪(U)} 𝒪(U') ⟶ RΓ(U', K')` of the
comparison of Stacks 065Z for the square of rings of global functions with the map induced by
`φ : L(g')^*K ⟶ K'`: the map of condition (2) of Stacks 0DJ8. -/
noncomputable def representedAffineSectionsBaseChangeComp (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K') :=
  (RingTheory.TorIndependence.ringHomSquareComparison
      (representedAffineCommRingCatHom B S hS f₀).hom
      (representedAffineCommRingCatHom B S hS g₀).hom
      (representedAffineCommRingCatHom B S hS g₀').hom
      (representedAffineCommRingCatHom B S hS f₀').hom
      ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
        (representedAffineRingHom_comp B S hS f₀' g₀))).app
      ((representedAffineDerivedSections B S hS U).obj K) ≫
    (ModuleCat.restrictScalars
        (representedAffineCommRingCatHom B S hS f₀').hom).mapDerivedCategory.map
      (representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ)

end Sections


include w₀ in
/-- **The base change map of Stacks 0DKH on affine representables, for quasi-coherent
complexes.** For `K ∈ D_QCoh(𝒪_U)`, `K' ∈ D_QCoh(𝒪_{U'})` and any `φ : L(g')^*K ⟶ K'`, the
composite `Lg^*Rf_*K ⟶ Rf'_*K'` is invertible if and only if the composite
`RΓ(U, K) ⊗ᴸ_{𝒪(V)} 𝒪(V') ⟶ RΓ(U, K) ⊗ᴸ_{𝒪(U)} 𝒪(U') ⟶ RΓ(U', K')` of Stacks 065Z with the map
induced by `φ` is. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_representedAffine_iff
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)))
    (hK : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩)))
    (hK' : QcohDerived B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ K')
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K ⟶ K') :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
        K K' φ) ↔
      IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K K' φ) := by
  have hε := isIso_representedAffineDerivedAdjunction_counit_app B S hS U K hK
  have hε' := isIso_representedAffineDerivedAdjunction_counit_app B S hS U' K' hK'
  refine (isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS _ _ _ _
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)
    ((representedAffineToposDerivedAssociated B S hS U).obj
      ((representedAffineDerivedSections B S hS U).obj K))
    ((representedAffineToposDerivedAssociated B S hS U').obj
      ((representedAffineDerivedSections B S hS U').obj K'))
    ((representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app _ ≫
      (representedAffineToposDerivedAssociated B S hS U').map
        (representedAffineSectionsBaseChangeMap B S hS g₀' K K' φ)) K K' φ
    (@asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U).counit.app K) hε)
    (@asIso _ _ _ _ ((representedAffineDerivedAdjunction B S hS U').counit.app K') hε')
    ((representedAffineSectionsBaseChangeMap_spec B S hS g₀' K K' φ).trans
      (Category.assoc _ _ _).symm)).symm.trans ?_
  exact isIso_representedAffineBaseChangeComp_iff B S hS f₀ g₀ f₀' g₀' w₀ _ _ _


section Condition

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **Condition (2) of Stacks 0DKG.** For every commutative diagram of affine schemes
`U ⟶ V ⟵ V'` étale over `X ⟶ Y ⟵ Y'` (through `a : U ⟶ X`, `b : V ⟶ Y`, `c : V' ⟶ Y'`) and every
`U' = V' ×_V U` with its induced morphism `a' : U' ⟶ X'`, the composite

`RΓ(U, a^*K) ⊗ᴸ_{𝒪(V)} 𝒪(V') ⟶ RΓ(U, a^*K) ⊗ᴸ_{𝒪(U)} 𝒪(U') ⟶ RΓ(U', (a')^*K')`

of Stacks 065Z with the map induced by `φ` is an isomorphism in `D(𝒪(V'))`: condition (2) of
Stacks 0DJ8 for the square of affine schemes. -/
structure AffineChartwiseBaseChange (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') : Prop where
  /-- The composite of Stacks 065Z with the map induced by `φ` at every affine quadruple is an
  isomorphism. -/
  isIso :
    ∀ (U V V' U' : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
      (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀),
      IsEtale B S hS a.hom → IsEtale B S hS b.hom → IsEtale B S hS c.hom →
      IsPullback g₀' f₀' f₀ g₀ →
      representedSpaceMap B S hS f₀ ≫ b = a ≫ f →
      representedSpaceMap B S hS g₀ ≫ b = c ≫ g →
      representedSpaceMap B S hS f₀' ≫ c = a' ≫ f' →
      ∀ (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g'),
      IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀
        ((smallEtaleDerivedModulePullback B S hS a).obj K)
        ((smallEtaleDerivedModulePullback B S hS a').obj K')
        ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
            a).hom.app K ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS a').map φ))

end Condition

end AlgebraicGeometry.Space
