module

public import StacksFrontier.AlgebraicGeometry.Smooth.TildeTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedStrictlyPerfectModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationSplittingCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummandsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowFlatRepresentative
public import StacksFrontier.Cotangent.KoszulRegularQuotient

/-!
# The degree-zero base change map of `RΓ(Spec A, Rf_*𝒪_X)` at a prime

Let `f : X ⟶ Spec A` be quasi-compact and quasi-separated, `𝔭 ⊂ A` a prime, and `X' ⟶ Spec A'`
the base change of `f` along `Spec A' ⟶ Spec A` with `A' ≅ κ(𝔭)`. If `𝒪 ⟶ f'_*𝒪_{X'}` is an
isomorphism and the base change map `Lg^* Rf_*𝒪_X ⟶ Rf'_*𝒪_{X'}` is an isomorphism, then the
degree-zero base change map `H⁰(K) ⊗ κ(𝔭) ⟶ H⁰(K ⊗^L κ(𝔭))` of `K = RΓ(Spec A, Rf_*𝒪_X)` is
surjective: the unit `A ⟶ K` already hits `H⁰(K ⊗^L κ(𝔭)) = H⁰(X', 𝒪) = κ(𝔭)`. Combined with
cohomology and base change, this gives that for `f` proper, flat and of finite presentation with
`k = H⁰(X_k, 𝒪_{X_k})` for every field-valued point, `Rf_*𝒪_X ≅ 𝒪_Y ⊕ P` étale locally on `Y`
with `P` perfect of Tor amplitude in `[1, ∞)`.

## Main results

* `AlgebraicGeometry.Space.cohomologyBaseChangeSurjective_of_isIso_smallEtaleDerivedBaseChangeMap`:
  the degree-zero base change map of `RΓ(Spec A, Rf_*𝒪_X)` at `𝔭` is surjective.
* `AlgebraicGeometry.Space.exists_presieve_isPerfect_hasTorAmplitudeGE_iso_etaleRestrict`:
  étale locally on `Y`, `Rf_*𝒪_X ≅ 𝒪_Y ⊕ P` with `P` perfect of Tor amplitude in `[1, ∞)`.

## Implementation notes

The unit `η : A[0] ⟶ K` is the transpose of the unit `𝒪_{Spec A}[0] ⟶ Rf_*𝒪_X[0]` of
`Lf^* ⊣ Rf_*`. Its derived base change to `A'` is nonzero: after the affine base change
`Lg^*Φ ≅ Φ'(- ⊗^L A')`, it becomes `Lg^*` of that unit, whose composite with the base change map
has invertible transpose `Lf'^*Lg^*𝒪[0] ≅ Lg'^*𝒪_X[0]`, a nonzero object. A nonzero map
`A'[0] ⟶ N` with `H⁰(N) ≅ A'` is surjective on `H⁰` because `A'` is a field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 5000] SheafOfModules.instAbelian

-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance] HasDerivedCategory.standard

variable {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U)
  {X X' : AlgebraicSpaces B S hS} (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (i : X' ⟶ X)

/-- The unit `𝒪_Y[0] ⟶ Rf_*𝒪_X[0]` of `Lf^* ⊣ Rf_*` at the structure sheaf, read through
`Lf^*𝒪_Y[0] ≅ 𝒪_X[0]`. -/
def derivedModulePushforwardStructureUnit {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor _ 0).obj (structureModule Y) ⟶
      (derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)) :=
  (smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _
    (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) f).hom

/-- The transpose of `derivedModulePushforwardStructureUnit` is the isomorphism
`Lf^*𝒪_Y[0] ≅ 𝒪_X[0]`. -/
theorem homEquiv_symm_derivedModulePushforwardStructureUnit {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    ((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm
        (derivedModulePushforwardStructureUnit B S hS f) =
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) f).hom :=
  Equiv.symm_apply_apply _ _

/-- Transport of the transpose `A ⟶ Γ E` of `Φ A ⟶ M ⟶ E` along a base change `D` with
`Φ ⋙ Lg ≅ D ⋙ Φ'`: after the unit of `Φ' ⊣ Γ'`, it is `Γ'` of `Lg` of the original map. -/
theorem _root_.CategoryTheory.Adjunction.map_homEquiv_comp_unit_comp_map_eq
    {DA DU DL DU' : Type*} [Category DA] [Category DU] [Category DL] [Category DU']
    {Φ : DA ⥤ DU} {Γ : DU ⥤ DA} (adjU : Φ ⊣ Γ) {Φ' : DL ⥤ DU'} {Γ' : DU' ⥤ DL}
    (adjU' : Φ' ⊣ Γ') {D : DA ⥤ DL} {Lg : DU ⥤ DU'} (β : Φ ⋙ Lg ≅ D ⋙ Φ') {A₀ : DA}
    {M E : DU} {T : DU'} (e₀ : Φ.obj A₀ ⟶ M) (u : M ⟶ E) (c : Lg.obj E ⟶ T) :
    D.map (adjU.homEquiv _ _ (e₀ ≫ u)) ≫ adjU'.unit.app (D.obj (Γ.obj E)) ≫
        Γ'.map (β.inv.app _ ≫ Lg.map (adjU.counit.app E) ≫ c) =
      adjU'.unit.app _ ≫ Γ'.map (β.inv.app A₀ ≫ Lg.map e₀ ≫ Lg.map u ≫ c) := by
  have h1 := adjU'.unit.naturality (D.map (adjU.homEquiv _ _ (e₀ ≫ u)))
  have h2 := β.inv.naturality (adjU.homEquiv _ _ (e₀ ≫ u))
  have h3 := adjU.homEquiv_counit (g := adjU.homEquiv _ _ (e₀ ≫ u))
  rw [Equiv.symm_apply_apply] at h3
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h1 h2
  rw [reassoc_of% h1, ← Γ'.map_comp, reassoc_of% h2, ← Lg.map_comp_assoc, ← h3, Lg.map_comp,
    Category.assoc]

/-- A morphism `w : F X ⟶ Y` whose transpose `X ⟶ G Y` vanishes is zero. -/
theorem _root_.CategoryTheory.Adjunction.eq_zero_of_unit_comp_map_eq_zero
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.PreservesZeroMorphisms] {X : C} {Y : D}
    (w : F.obj X ⟶ Y) (h : adj.unit.app X ≫ G.map w = 0) : w = 0 := by
  rw [← (adj.homEquiv _ _).symm_apply_apply w, adj.homEquiv_unit, h, Adjunction.homEquiv_counit,
    Functor.map_zero, zero_comp]

/-- If `v : P ⟶ G T` is zero and its transpose `F P ⟶ T` is invertible, then `T` is zero. -/
theorem _root_.CategoryTheory.Adjunction.isZero_of_eq_zero_of_isIso_homEquiv_symm
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.PreservesZeroMorphisms] {P : C} {T : D}
    (v : P ⟶ G.obj T) [IsIso ((adj.homEquiv _ _).symm v)] (hv : v = 0) : IsZero T := by
  have hT : (adj.homEquiv _ _).symm v = 0 := by
    rw [hv, Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id ((adj.homEquiv _ _).symm v)]
  exact (congrArg (inv ((adj.homEquiv _ _).symm v) ≫ ·) hT).trans comp_zero

/-- An object `N` of `D(R)` with `H⁰(N) ≅ R` is nonzero when `R` is a field. -/
private theorem _root_.DerivedCategory.not_isZero_of_homologyFunctor_zero_iso_of_isField
    {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)] (hR : IsField R)
    {N : DerivedCategory (ModuleCat.{u} R)}
    (eN : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj N ≅ ModuleCat.of R R) :
    ¬IsZero N := fun hN =>
  have := hR.nontrivial
  not_subsingleton R (ModuleCat.isZero_iff_subsingleton.1
    (IsZero.of_iso ((DerivedCategory.homologyFunctor _ 0).map_isZero hN) eN.symm))

/-- **The degree-zero base change map of `RΓ(Spec A, Rf_*𝒪_X)` at `𝔭` is surjective** as soon as
the derived base change map of `Rf_*𝒪_X` along `Spec A' ⟶ Spec A` is invertible, for `A' ≅ κ(𝔭)`
and `𝒪 ⟶ f'_*𝒪_{X'}` invertible on the base change. -/
theorem cohomologyBaseChangeSurjective_of_isIso_smallEtaleDerivedBaseChangeMap
    (sq : IsPullback i f' f (representedSpaceMap B S hS g))
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (hqc' : IsQuasiCompact B S hS f'.hom) (hqs' : IsQuasiSeparated B S hS f'.hom)
    [IsIso (structureSharp B S hS f')]
    (p : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) [p.IsPrime]
    (e : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) ≃+* p.ResidueField)
    (he : (e : _ →+* p.ResidueField).comp (representedAffineCommRingCatHom B S hS g).hom =
      algebraMap _ p.ResidueField)
    (hbc : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f (representedSpaceMap B S hS g) f' i
      sq.w ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))))) :
    StacksDraft.Perfect.CohomologyBaseChangeSurjective.{u, u} p
      ((representedAffineDerivedSections B S hS U).obj ((derivedModulePushforward B S hS f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X)))) 0 := by
  let O := (DerivedCategory.singleFunctor _ 0).obj (structureModule X)
  let E := (derivedModulePushforward B S hS f).obj O
  let K := (representedAffineDerivedSections B S hS U).obj E
  let adjU := representedAffineDerivedAdjunction B S hS U
  let adjU' := representedAffineDerivedAdjunction B S hS U'
  let eU := representedAffineDerivedAssociatedSingleUnitIso B S hS U 0
  let ε := derivedModulePushforwardStructureUnit B S hS f
  let η : (DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ⟶ K :=
    adjU.homEquiv _ _ (eU.hom ≫ ε)
  refine StacksDraft.Perfect.cohomologyBaseChangeSurjective_zero_of_epi_homology_map p K hK η ?_
  rw [← he]
  refine StacksDraft.Perfect.epi_homologyFunctor_map_totalDerivedExtensionScalars_comp_ringEquiv
    _ e η 0 ?_
  let φ := (representedAffineCommRingCatHom B S hS g).hom
  let D := representedAffineDerivedExtension B S hS g
  let Lg := smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)
  let β := representedAffineDerivedBaseChangeIso B S hS g
  have hcounit : IsIso (adjU.counit.app E) :=
    isIso_representedAffineDerivedAdjunction_counit_app B S hS U E
      (qcohDerived_derivedModulePushforward_structureModule B S hS U f hqc hqs)
  let RΓ' := representedAffineDerivedSections B S hS U'
  let Rf' := derivedModulePushforward B S hS f'
  let bc := smallEtaleDerivedModuleBaseChangeMap B S hS f (representedSpaceMap B S hS g) f' i sq.w O
  let chain1 : D.functor.obj K ≅ RΓ'.obj (Rf'.obj ((smallEtaleDerivedModulePullback B S hS i).obj
      O)) :=
    asIso (adjU'.unit.app _) ≪≫
      RΓ'.mapIso ((β.app K).symm ≪≫ Lg.mapIso (@asIso _ _ _ _ _ hcounit) ≪≫ @asIso _ _ _ _ bc hbc)
  let eN := (DerivedCategory.homologyFunctor _ 0).mapIso (chain1 ≪≫ RΓ'.mapIso (Rf'.mapIso
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) i))) ≪≫
    homologyZeroDerivedSectionsDerivedModulePushforwardIso B S hS U' f' hqc' hqs'
  have hfield : IsField Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
    e.toMulEquiv.isField (Field.toIsField _)
  let ι := CommAlgCat.totalDerivedExtensionScalarsSingleIsoOfProjective φ D
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) 0 ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (ModuleCat.ExtendScalars.objSelfIso φ)
  let adjf := smallEtaleDerivedModuleAdjunction B S hS f
  let adjf' := smallEtaleDerivedModuleAdjunction B S hS f'
  have hε : IsIso ((adjf.homEquiv _ _).symm ε) := by
    rw [homEquiv_symm_derivedModulePushforwardStructureUnit]
    exact ⟨_, Iso.hom_inv_id _, Iso.inv_hom_id _⟩
  have hv : IsIso ((adjf'.homEquiv _ _).symm (Lg.map ε ≫ bc)) :=
    Stacks.CategoryTheory.BaseChange.isIso_homEquiv_symm_map_comp_map adjf adjf' _ _ ε
  have hne : ι.inv ≫ D.functor.map η ≠ 0 := by
    intro h0
    have : Rf'.IsRightAdjoint := adjf'.isRightAdjoint
    have : (representedAffineDerivedAssociated B S hS U').IsLeftAdjoint := adjU'.isLeftAdjoint
    have : (smallEtaleDerivedModulePullback B S hS f').IsLeftAdjoint := adjf'.isLeftAdjoint
    have hw := Adjunction.eq_zero_of_unit_comp_map_eq_zero adjU' _
      ((Adjunction.map_homEquiv_comp_unit_comp_map_eq adjU adjU' β eU.hom ε bc).symm.trans
        ((congrArg (· ≫ chain1.hom) ((cancel_epi ι.inv).1 (h0.trans comp_zero.symm))).trans
          zero_comp))
    have hZ := Adjunction.isZero_of_eq_zero_of_isIso_homEquiv_symm adjf' (Lg.map ε ≫ bc) (by
      rw [← cancel_epi ((β.app _).symm ≪≫ Lg.mapIso eU).hom, comp_zero]
      exact (Category.assoc _ _ _).trans hw)
    exact DerivedCategory.not_isZero_of_homologyFunctor_zero_iso_of_isField hfield eN
      (IsZero.of_iso (RΓ'.map_isZero (Rf'.map_isZero hZ)) chain1)
  have := StacksDraft.Perfect.epi_homologyFunctor_map_of_ne_zero hfield eN _ hne
  exact epi_of_epi_fac
    ((DerivedCategory.homologyFunctor _ 0).map_comp ι.inv (D.functor.map η)).symm

section ResidueField

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (p : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) [p.IsPrime]

/-- `U ⟶ S` read through `U ≅ Spec Γ(U)`, as a scheme over `S`. -/
abbrev specGlobalSectionsOver : Over S :=
  Over.mk (((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv ≫ B.inclusion.map U.hom)

/-- The prime `𝔭` as a point of `Spec Γ(U)`. -/
abbrev specGlobalSectionsPoint : (specGlobalSectionsOver B S hS U).left := ⟨p, inferInstance⟩

/-- The spectrum of the residue field `κ(𝔭)` is an object of the big fppf site `B`. -/
theorem contains_spec_residueField_specGlobalSectionsPoint :
    B.Contains (Spec ((specGlobalSectionsOver B S hS U).left.residueField
      (specGlobalSectionsPoint B S hS U p))) := by
  have hT : ((BigFppfOver.toScheme B S hS).obj U).size < B.cutoff := U.left.property
  rw [Scheme.size_congr ((BigFppfOver.toScheme B S hS).obj U).isoSpec] at hT
  exact B.residueField_spec_contains hT _

/-- The site object `Spec κ(𝔭)` is affine. -/
instance : IsAffine ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObject B hS
    (specGlobalSectionsPoint B S hS U p)
    (contains_spec_residueField_specGlobalSectionsPoint B S hS U p))) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The map `Spec κ(𝔭) ⟶ U` in the big fppf site, for a prime `𝔭` of `Γ(U)`. -/
def residueFieldSiteMapOfIsAffine :
    residueFieldSiteObject B hS (specGlobalSectionsPoint B S hS U p)
      (contains_spec_residueField_specGlobalSectionsPoint B S hS U p) ⟶ U :=
  Over.homMk ⟨(specGlobalSectionsOver B S hS U).left.fromSpecResidueField
      (specGlobalSectionsPoint B S hS U p) ≫
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv⟩ rfl

/-- The global functions of `Spec κ(𝔭)` are `κ(𝔭)`. -/
def residueFieldSiteObjectRingEquivOfIsAffine :
    Γ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObject B hS
      (specGlobalSectionsPoint B S hS U p)
      (contains_spec_residueField_specGlobalSectionsPoint B S hS U p)), ⊤) ≃+* p.ResidueField :=
  (Scheme.ΓSpecIso _ ≪≫ Scheme.Spec.residueFieldIso _ _).commRingCatIsoToRingEquiv

/-- Under `Γ(Spec κ(𝔭)) ≃ κ(𝔭)`, the ring map `Γ(U) ⟶ Γ(Spec κ(𝔭))` induced by
`residueFieldSiteMapOfIsAffine` is the canonical map `Γ(U) ⟶ κ(𝔭)`. -/
theorem residueFieldSiteObjectRingEquivOfIsAffine_comp :
    ((residueFieldSiteObjectRingEquivOfIsAffine B S hS U p : _ ≃+* p.ResidueField) :
        _ →+* _).comp
        (representedAffineCommRingCatHom B S hS (residueFieldSiteMapOfIsAffine B S hS U p)).hom =
      algebraMap _ p.ResidueField := by
  have h : representedAffineCommRingCatHom B S hS (residueFieldSiteMapOfIsAffine B S hS U p) ≫
      (Scheme.ΓSpecIso _ ≪≫ Scheme.Spec.residueFieldIso _ _).hom =
        CommRingCat.ofHom (algebraMap _ p.ResidueField) := by
    have hrw := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (specGlobalSectionsPoint B S hS U p)
    change ((Spec Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).fromSpecResidueField
      (specGlobalSectionsPoint B S hS U p) ≫
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv).appTop ≫
      (Scheme.ΓSpecIso _ ≪≫
        Scheme.Spec.residueFieldIso _ (specGlobalSectionsPoint B S hS U p)).hom = _
    rw [← hrw, ← Spec.map_comp,
      Scheme.Hom.comp_appTop, Stacks.Modules.isoSpec_inv_appTop, Category.assoc, Iso.trans_hom,
      Scheme.ΓSpecIso_naturality_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Iso.inv_hom_id_assoc (Scheme.ΓSpecIso _) _
  exact congrArg CommRingCat.Hom.hom h

end ResidueField

section Assembly

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_*𝒪_X = 𝒪_Y ⊕ P` étale locally, from cohomology and base change.**  Let `f : X ⟶ Y`
satisfy the hypotheses of Stacks 0E6B, and assume the conclusions of cohomology and base change
(Stacks 0CTM, part (1), at `E = 𝒪`) for the base change `f_V` of `f` to every étale chart `V` of
`Y`: `Rf_{V*}𝒪` is perfect, and its formation commutes with base change along every morphism of
affine objects into `V`.  Then every chart `U` of `Y` has a covering family of charts `V` over
which `Rf_{V*}𝒪 ≅ 𝒪 ⊕ P` with `P` strictly perfect in degrees `≥ 1`. -/
theorem exists_presieve_isStrictlyPerfect_iso_derivedModulePushforward_of_baseChange (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (h : ∀ p : FieldValuedPoint B S hS Y.1, Function.Bijective (algebraMap p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f.hom p))))
    (hperf : ∀ (V : SmallEtale B S hS Y.1),
      (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2).IsPerfect
        ((derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (structureModule (pullback f (chartToSpace B S hS Y V))))))
    (hbc : ∀ (V : SmallEtale B S hS Y.1) {U' : BigFppfOver B S hS}
      [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (g : U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V) {X' : AlgebraicSpaces B S hS}
      (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (i : X' ⟶ pullback f
        (chartToSpace B S hS Y V))
      (sq : IsPullback i f' (pullback.snd f (chartToSpace B S hS Y V))
        (representedSpaceMap B S hS g)),
      IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS (pullback.snd f (chartToSpace B S hS Y V))
        (representedSpaceMap B S hS g) f' i sq.w
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule (pullback f
          (chartToSpace B S hS Y V))))))
    (U : SmallEtale B S hS Y.1) :
    ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS Y.1 U ∧
      ∀ ⦃V : SmallEtale B S hS Y.1⦄ (g : V ⟶ U), R g →
        ∃ P : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS Y V).1
            (chartSpace B S hS Y V).2) ℤ,
          IsStrictlyPerfect.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1
                (chartSpace B S hS Y V).2).O)) P ∧ P.IsStrictlyGE 1 ∧
          Nonempty ((derivedModulePushforward B S hS
              (pullback.snd f (chartToSpace B S hS Y V))).obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  (structureModule (pullback f (chartToSpace B S hS Y V)))) ≅
            (DerivedCategory.singleFunctor _ 0).obj (structureModule (chartSpace B S hS Y V)) ⊞
              DerivedCategory.Q.obj P) := by
  have H := fun {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) =>
    isQuasiCompact_and_isQuasiSeparated_and_isIso_structureSharp_pullback_snd B S hS f hf hfl hfp
      h g
  refine exists_presieve_isStrictlyPerfect_iso_derivedModulePushforward_of_affine B S hS f
    (fun V => (H _).1) (fun V => (H _).2.1) (fun V => (H _).2.2) hperf ?_ U
  intro V _ p _
  let U₀ := (SmallEtale.toOver B S hS Y.1).obj V
  let g := residueFieldSiteMapOfIsAffine B S hS U₀ p
  let g'' := representedSpaceMap B S hS g ≫ chartToSpace B S hS Y V
  let i : pullback f g'' ⟶ pullback f (chartToSpace B S hS Y V) :=
    pullback.lift (pullback.fst f g'') (pullback.snd f g'' ≫ representedSpaceMap B S hS g)
      ((pullback.condition).trans (Category.assoc _ _ _).symm)
  have sq : IsPullback i (pullback.snd f g'') (pullback.snd f (chartToSpace B S hS Y V))
      (representedSpaceMap B S hS g) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback _ _
  have := (H g'').2.2
  have hK := StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
    (isPerfect_representedAffineDerivedSections_obj B S hS U₀ _ (hperf V))
  exact cohomologyBaseChangeSurjective_of_isIso_smallEtaleDerivedBaseChangeMap B S hS g
    (pullback.snd f (chartToSpace B S hS Y V)) (pullback.snd f g'') i sq (H _).1 (H _).2.1
    (H g'').1 (H g'').2.1 p (residueFieldSiteObjectRingEquivOfIsAffine B S hS U₀ p)
    (residueFieldSiteObjectRingEquivOfIsAffine_comp B S hS U₀ p) (hbc V g _ i sq) hK

end Assembly

section Restriction

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {X Y : AlgebraicSpaces B S hS}

/-- **The restriction of `Rf_*𝒪_X` to an étale chart `V` of `Y` is `Rf_{V*}𝒪`** for the base change
`f_V : X ×_Y V ⟶ V`, by étale base change (Stacks 08GE). -/
def etaleRestrictDerivedModulePushforwardStructureModuleIso (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))) ≅
      (derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (structureModule (pullback f (chartToSpace B S hS Y V)))) :=
  let sq := IsPullback.of_hasPullback f (chartToSpace B S hS Y V)
  let hi := isEtale_of_isPullback B S hS (pullback.snd f (chartToSpace B S hS Y V))
    (pullback.fst f (chartToSpace B S hS Y V)) (chartToSpace B S hS Y V) f sq.flip
    (isEtale_chartToSpace B S hS Y V)
  (derivedPushforwardEtaleBaseChangeIso B S hS sq (isEtale_chartToSpace B S hS Y V)).app _ ≪≫
    (derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V))).mapIso
      (((etaleModulePullback.{u, u} B S hS _ hi).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          (etaleModulePullbackStructureModuleIso B S hS _ hi))

/-- The étale restriction of the structure sheaf of `Y` to a chart `V` is the structure sheaf
of `V`, in degree zero of the derived category. -/
def etaleRestrictSingleStructureModuleIso (V : SmallEtale B S hS Y.1) :
    (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (structureModule (chartSpace B S hS Y V)) :=
  ((etaleModulePullback.{u, u} B S hS _
      (isEtale_chartToSpace B S hS Y V)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (etaleModulePullbackStructureModuleIso B S hS _ (isEtale_chartToSpace B S hS Y V))

/-- **`Rf_*𝒪_X = 𝒪_Y ⊕ P` étale locally on `Y`, from cohomology and base change**: the form of
`exists_presieve_isStrictlyPerfect_iso_derivedModulePushforward_of_baseChange` read on the
restriction of `Rf_*𝒪_X` to the charts of a covering family. -/
theorem exists_presieve_isStrictlyPerfect_iso_etaleRestrict_of_baseChange (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (h : ∀ p : FieldValuedPoint B S hS Y.1, Function.Bijective (algebraMap p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f.hom p))))
    (hperf : ∀ (V : SmallEtale B S hS Y.1),
      (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2).IsPerfect
        ((derivedModulePushforward B S hS (pullback.snd f (chartToSpace B S hS Y V))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (structureModule (pullback f (chartToSpace B S hS Y V))))))
    (hbc : ∀ (V : SmallEtale B S hS Y.1) {U' : BigFppfOver B S hS}
      [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (g : U' ⟶ (SmallEtale.toOver B S hS Y.1).obj V) {X' : AlgebraicSpaces B S hS}
      (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (i : X' ⟶ pullback f
        (chartToSpace B S hS Y V))
      (sq : IsPullback i f' (pullback.snd f (chartToSpace B S hS Y V))
        (representedSpaceMap B S hS g)),
      IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS (pullback.snd f (chartToSpace B S hS Y V))
        (representedSpaceMap B S hS g) f' i sq.w
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule (pullback f
          (chartToSpace B S hS Y V))))))
    (U : SmallEtale B S hS Y.1) :
    ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS Y.1 U ∧
      ∀ ⦃V : SmallEtale B S hS Y.1⦄ (g : V ⟶ U), R g →
        ∃ P : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS Y V).1
            (chartSpace B S hS Y V).2) ℤ,
          IsStrictlyPerfect.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1
                (chartSpace B S hS Y V).2).O)) P ∧ P.IsStrictlyGE 1 ∧
          Nonempty ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
              (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
              ((derivedModulePushforward B S hS f).obj
                ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))) ≅
            (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
              (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj (structureModule Y)) ⊞
              DerivedCategory.Q.obj P) := by
  obtain ⟨R, hR, hP⟩ := exists_presieve_isStrictlyPerfect_iso_derivedModulePushforward_of_baseChange
    B S hS f hf hfl hfp h hperf hbc U
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨P, hP, hP1, ⟨e⟩⟩ := hP g hg
  exact ⟨P, hP, hP1, ⟨etaleRestrictDerivedModulePushforwardStructureModuleIso B S hS f V ≪≫ e ≪≫
    biprod.mapIso (etaleRestrictSingleStructureModuleIso B S hS V).symm (Iso.refl _)⟩⟩

/-- **Stacks 0E6B, part (b).** Let `f : X ⟶ Y` be proper, flat and of finite presentation, such
that `k = H⁰(X_k, 𝒪_{X_k})` for every morphism `Spec k ⟶ Y` from the spectrum of a field. Then
étale locally on `Y` we have `Rf_*𝒪_X ≅ 𝒪_Y ⊕ P` in `D(𝒪_Y)` with `P` perfect of Tor amplitude in
`[1, ∞)`: every étale chart `U` of `Y` has a covering family of charts `V` over which the
restrictions satisfy `(Rf_*𝒪_X)|_V ≅ 𝒪_Y|_V ⊕ P`. -/
@[stacks 0E6B "(b)"]
theorem exists_presieve_isPerfect_hasTorAmplitudeGE_iso_etaleRestrict (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (h : ∀ p : FieldValuedPoint B S hS Y.1, Function.Bijective (algebraMap p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f.hom p))))
    (U : SmallEtale B S hS Y.1) :
    ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS Y.1 U ∧
      ∀ ⦃V : SmallEtale B S hS Y.1⦄ (g : V ⟶ U), R g →
        ∃ P : DerivedCategory (Modules.{u, u} B S hS (chartSpace B S hS Y V).1
            (chartSpace B S hS Y V).2),
          (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1
            (chartSpace B S hS Y V).2).IsPerfect P ∧
          Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
            (smallEtaleDerivedTensorProduct B S hS (chartSpace B S hS Y V)) P 1 ∧
          Nonempty ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
              (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
              ((derivedModulePushforward B S hS f).obj
                ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))) ≅
            (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V)
              (isEtale_chartToSpace B S hS Y V)).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj (structureModule Y)) ⊞ P) := by
  have sq := fun V : SmallEtale B S hS Y.1 => IsPullback.of_hasPullback f (chartToSpace B S hS Y V)
  have H := fun V : SmallEtale B S hS Y.1 =>
    isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat
      (pullback.snd f (chartToSpace B S hS Y V))
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback (sq V) hf)
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback (sq V) hfl)
      ((isFinitePresentation_isStableUnderBaseChange (B := B) (S := S) (hS := hS)).of_isPullback
        (sq V) hfp)
      _ (isPerfect_unit (pullback f (chartToSpace B S hS Y V)))
  obtain ⟨R, hR, hP⟩ := exists_presieve_isStrictlyPerfect_iso_etaleRestrict_of_baseChange B S hS f
    hf hfl hfp h (fun V => (H V).1) (fun V _ _ g _ f' i sq => (H V).2 _ f' i sq) U
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨P, hP, hP1, e⟩ := hP g hg
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  have hLE : P.IsStrictlyLE r := by
    refine (CochainComplex.isStrictlyLE_iff P r).2 fun i hi => ?_
    by_contra hri
    exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using hri)) (by omega)
  refine ⟨DerivedCategory.Q.obj P,
    RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect _ P hP,
    Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_kFlatRepresentative
      (smallEtaleDerivedTensorProduct B S hS (chartSpace B S hS Y V)) _ 1 P
      (Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat
        (smallEtaleRingedSite B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2).O
        P ⟨r, hLE⟩ fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect_general hP i)
      (fun i hi => P.isZero_of_isStrictlyGE 1 i hi) (Iso.refl _), e⟩

end Restriction

end AlgebraicGeometry.Space
