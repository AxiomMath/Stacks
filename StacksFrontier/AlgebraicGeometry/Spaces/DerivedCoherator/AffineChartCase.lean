module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartTildeExact
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.AffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.DerivedLimitBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness

/-!
# The affine case of the coherator

Let `Y` be an algebraic space whose small étale site has a terminal object `A` with affine scheme,
and let `R = 𝒪_Y(A)`. The associated-module functor `Φ : Mod(R) ⥤ Mod(𝒪_Y)` of
`AlgebraicGeometry.Space.affineChartTilde` is exact and left adjoint to `Γ(A, -)`, so it induces
`T : D(R) ⥤ D(𝒪_Y)`, left adjoint to `RΓ(A, -)` (Stacks 09T5). The unit of `T ⊣ RΓ(A, -)` is
invertible and so is its counit on `D_QCoh(𝒪_Y)`, because `𝒪_Y` is a weak generator of
`D_QCoh(𝒪_Y)` (`AlgebraicGeometry.Space.isZero_of_forall_homFromUnit_eq_zero`). This is the
affine case of Stacks 08H0 and 09T5, and gives the affine case of the coherator
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.AffineCoheratorCase`.

## Main results

* `AlgebraicGeometry.Space.affineChartDerivedAdjunction`: `T ⊣ RΓ(A, -)`.
* `AlgebraicGeometry.Space.isIso_affineChartDerivedAdjunction_unit`: its unit is invertible.
* `AlgebraicGeometry.Space.isIso_affineChartDerivedAdjunction_counit_app`: its counit is
  invertible on `D_QCoh(𝒪_Y)`.
* `AlgebraicGeometry.Space.affineCoheratorCase`: the affine case of the coherator.

## Implementation notes

The results are stated for any algebraic space `Y` with a terminal affine chart, not only for the
represented spaces `yoneda.obj U`, since `AffineCoheratorCase` quantifies over affine algebraic
spaces and an affine algebraic space is only isomorphic to a represented one.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 0CSG](https://stacks.math.columbia.edu/tag/0CSG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- Restriction of scalars along a ring isomorphism `θ : R' ≃ R` carries the free module of rank
one over `R` to the free module of rank one over `R'`, as a linear equivalence. -/
def restrictScalarsSelfLinearEquiv {R R' : Type u} [Ring R] [Ring R'] (θ : R' ≃+* R) :
    ((ModuleCat.restrictScalars.{u} θ.toRingHom).obj (ModuleCat.of R R)) ≃ₗ[R'] R' where
  toFun x := θ.symm (show R from x)
  invFun x := show R from θ x
  map_add' x y := map_add θ.symm (show R from x) (show R from y)
  map_smul' r x := by
    change θ.symm (θ r * (show R from x)) = r * θ.symm (show R from x)
    rw [map_mul, RingEquiv.symm_apply_apply]
  left_inv x := θ.apply_symm_apply (show R from x)
  right_inv x := θ.symm_apply_apply x

/-- `restrictScalarsSelfLinearEquiv`, as an isomorphism of modules. -/
def restrictScalarsSelfIso {R R' : Type u} [Ring R] [Ring R'] (θ : R' ≃+* R) :
    (ModuleCat.restrictScalars.{u} θ.toRingHom).obj (ModuleCat.of R R) ≅ ModuleCat.of R' R' :=
  (restrictScalarsSelfLinearEquiv θ).toModuleIso

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Y : AlgebraicSpaces B S hS) {A : SmallEtale B S hS Y.1}
  (hA : IsTerminal A) [IsAffine (chartScheme A)]

/-- The ring `R = 𝒪_Y(A)` of sections over the terminal chart. -/
abbrev affineChartRing : RingCat.{u} := (structureRingSheaf B S hS Y).obj.obj (op A)

/-- The sections `Γ(A, -) : Mod(𝒪_Y) ⥤ Mod(R)` over the terminal chart. -/
abbrev affineChartSections (A : SmallEtale B S hS Y.1) :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ ModuleCat.{u} (affineChartRing B S hS Y (A := A)) :=
  SheafOfModules.evaluation (structureRingSheaf B S hS Y) (op A)

/-- `Φ(R) ≅ 𝒪_Y`. -/
def affineChartTildeObjUnitIso :
    (affineChartTilde B S hS Y hA).obj
        (ModuleCat.of (affineChartRing B S hS Y (A := A)) (affineChartRing B S hS Y (A := A))) ≅
      SheafOfModules.unit (structureRingSheaf B S hS Y) :=
  (chartTildeFunctor B S hS Y hA).mapIso (restrictScalarsSelfIso _) ≪≫
    chartTildeFunctorUnitIso B S hS Y hA

/-- The sections functor `Γ(A, -)` is additive. -/
instance additive_affineChartSections (A : SmallEtale B S hS Y.1) :
    (affineChartSections B S hS Y A).Additive :=
  inferInstanceAs ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op A)).Additive)

/-- The sections functor `Γ(A, -)` has a total right derived functor with respect to
quasi-isomorphisms. -/
instance hasRightDerivedFunctor_affineChartSections :
    ((affineChartSections B S hS Y A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) :=
  have := Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective
    ((affineChartSections B S hS Y A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _


/-- **`RΓ(A, -) : D(𝒪_Y) ⥤ D(R)`**, the total right derived functor of the sections over the
terminal chart. -/
abbrev affineChartDerivedSections (A : SmallEtale B S hS Y.1) :
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (ModuleCat.{u} (affineChartRing B S hS Y (A := A))) :=
  ((affineChartSections B S hS Y A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))

/-- `RΓ(A, -) : D(𝒪_Y) ⥤ D(R)` is a triangulated functor. -/
instance isTriangulated_affineChartDerivedSections (A : SmallEtale B S hS Y.1) :
    (affineChartDerivedSections B S hS Y A).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)
    _ (affineChartDerivedSections B S hS Y A) (Functor.totalRightDerivedUnit _ _ _)

/-- **`T : D(R) ⥤ D(𝒪_Y)`**, induced on derived categories by the exact functor `Φ`. -/
abbrev affineChartDerivedTilde :
    DerivedCategory (ModuleCat.{u} (affineChartRing B S hS Y (A := A))) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
  (affineChartTilde B S hS Y hA).mapDerivedCategory

/-- **`T ⊣ RΓ(A, -)`**, Stacks 09T5 for the exact functor `Φ`. -/
def affineChartDerivedAdjunction :
    affineChartDerivedTilde B S hS Y hA ⊣ affineChartDerivedSections B S hS Y A :=
  Stacks.DerivedFunctor.derivedAdjunction (affineChartTildeAdjunction B S hS Y hA)
    (affineChartDerivedSections B S hS Y A) (Functor.totalRightDerivedUnit _ _ _)
    (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)

/-- `T(R[q]) ≅ 𝒪_Y[q]`. -/
def affineChartDerivedTildeSingleUnitIso (q : ℤ) :
    (affineChartDerivedTilde B S hS Y hA).obj ((DerivedCategory.singleFunctor _ q).obj
        (ModuleCat.of (affineChartRing B S hS Y (A := A)) (affineChartRing B S hS Y (A := A)))) ≅
      (DerivedCategory.singleFunctor _ q).obj (structureModule Y) :=
  ((affineChartTilde B S hS Y hA).mapDerivedCategorySingleFunctor q).app _ ≪≫
    (DerivedCategory.singleFunctor _ q).mapIso (affineChartTildeObjUnitIso B S hS Y hA)

/-- `Φ` is fully faithful. -/
def affineChartTildeFullyFaithful : (affineChartTilde B S hS Y hA).FullyFaithful :=
  Adjunction.fullyFaithfulLOfIsIsoUnit (affineChartTildeAdjunction B S hS Y hA)

/-- `T M` lies in `D_QCoh(𝒪_Y)`. -/
theorem spaceQuasicoherentProp_affineChartDerivedTilde_obj
    (M : DerivedCategory (ModuleCat.{u} (affineChartRing B S hS Y (A := A)))) :
    spaceQuasicoherentProp B S hS Y ((affineChartDerivedTilde B S hS Y hA).obj M) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((affineChartTilde B S hS Y hA).mapDerivedCategoryHomologyIso n).app M).symm
    (isQuasicoherentOnSite_affineChartTilde_obj B S hS Y hA _)

/-- **`T` is bijective on morphisms out of `R[q]`.** -/
theorem bijective_affineChartDerivedTilde_map_single (q : ℤ)
    (M : DerivedCategory (ModuleCat.{u} (affineChartRing B S hS Y (A := A)))) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ q).obj
        (ModuleCat.of (affineChartRing B S hS Y (A := A))
          (affineChartRing B S hS Y (A := A))) ⟶ M =>
      (affineChartDerivedTilde B S hS Y hA).map f) := by
  set R₀ := ModuleCat.of (affineChartRing B S hS Y (A := A)) (affineChartRing B S hS Y (A := A))
  have : Projective R₀ := ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} _)
  refine bijective_map_of_iso_comp (affineChartDerivedTilde B S hS Y hA)
    (DerivedCategory.homologyFunctor _ q) (DerivedCategory.homologyFunctor _ q)
    (affineChartTilde B S hS Y hA)
    ((affineChartTilde B S hS Y hA).mapDerivedCategoryHomologyIso q) _ M ?_
    ((affineChartTildeFullyFaithful B S hS Y hA).map_bijective _ _) ?_
  · have h := DerivedCategory.bijective_homologyFromSingle_of_projective R₀ M q
    have hk : (fun f : (DerivedCategory.singleFunctor _ q).obj R₀ ⟶ M =>
        (DerivedCategory.homologyFunctor _ q).map f) =
        (fun g => ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app R₀).hom ≫ g) ∘
          DerivedCategory.homologyFromSingle R₀ M q := by
      funext f
      rw [Function.comp_apply, DerivedCategory.homologyFromSingle_apply, ← Category.assoc,
        Iso.app_hom, Iso.hom_inv_id_app, Category.id_comp]
    rw [hk]
    exact (bijective_iso_comp ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app
      R₀)).comp h
  · intro a b hab
    have hab' : (DerivedCategory.homologyFunctor _ q).map a =
        (DerivedCategory.homologyFunctor _ q).map b := hab
    set i := affineChartDerivedTildeSingleUnitIso B S hS Y hA q
    have := homologyFunctor_map_injective_fromUnit (X := Y.1) (hX := Y.2) A hA
      (inferInstanceAs (IsAffine (chartScheme A))) q
      _ (spaceQuasicoherentProp_affineChartDerivedTilde_obj B S hS Y hA M)
      (a₁ := i.inv ≫ a) (a₂ := i.inv ≫ b) (by
        show (DerivedCategory.homologyFunctor _ q).map (i.inv ≫ a) =
          (DerivedCategory.homologyFunctor _ q).map (i.inv ≫ b)
        rw [Functor.map_comp, Functor.map_comp, hab'])
    exact (cancel_epi i.inv).mp this

/-- **The unit of `T ⊣ RΓ(A, -)` is invertible.** -/
instance isIso_affineChartDerivedAdjunction_unit :
    IsIso (affineChartDerivedAdjunction B S hS Y hA).unit := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M => ?_
  set adj := affineChartDerivedAdjunction B S hS Y hA
  set R₀ := ModuleCat.of (affineChartRing B S hS Y (A := A)) (affineChartRing B S hS Y (A := A))
  have : Projective R₀ := ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} _)
  rw [DerivedCategory.isIso_iff]
  intro q
  refine isIso_of_bijective_comp_moduleCat _ ?_
  have hu : Function.Bijective (fun g : (DerivedCategory.singleFunctor _ q).obj R₀ ⟶ M =>
      g ≫ adj.unit.app M) := by
    have hk : (fun g : (DerivedCategory.singleFunctor _ q).obj R₀ ⟶ M => g ≫ adj.unit.app M) =
        (adj.homEquiv _ _) ∘ (fun f => (affineChartDerivedTilde B S hS Y hA).map f) := by
      funext g
      simp only [Function.comp_apply, Adjunction.homEquiv_unit]
      exact adj.unit.naturality g
    rw [hk]
    exact (adj.homEquiv _ _).bijective.comp
      (bijective_affineChartDerivedTilde_map_single B S hS Y hA q M)
  have h₁ := DerivedCategory.bijective_homologyFromSingle_of_projective R₀ M q
  have h₂ := DerivedCategory.bijective_homologyFromSingle_of_projective R₀
    ((affineChartDerivedTilde B S hS Y hA ⋙ affineChartDerivedSections B S hS Y A).obj M) q
  have hk : (DerivedCategory.homologyFromSingle R₀ _ q) ∘
      (fun g : (DerivedCategory.singleFunctor _ q).obj R₀ ⟶ M => g ≫ adj.unit.app M) =
      (fun g => g ≫ (DerivedCategory.homologyFunctor _ q).map (adj.unit.app M)) ∘
        (DerivedCategory.homologyFromSingle R₀ M q) := by
    funext g
    exact DerivedCategory.homologyFromSingle_comp R₀ M q g _
  have := h₂.comp hu
  rw [hk] at this
  exact (Function.Bijective.of_comp_iff _ h₁).mp this


/-! ### The counit on `D_QCoh(𝒪_Y)` -/

/-- `T`, as a functor `D(R) ⥤ D_QCoh(𝒪_Y)`. -/
def affineChartDerivedTildeQcoh :
    DerivedCategory (ModuleCat.{u} (affineChartRing B S hS Y (A := A))) ⥤
      (spaceQuasicoherentProp B S hS Y).FullSubcategory :=
  ObjectProperty.lift _ (affineChartDerivedTilde B S hS Y hA)
    (spaceQuasicoherentProp_affineChartDerivedTilde_obj B S hS Y hA)

/-- `T : D(R) ⥤ D_QCoh(𝒪_Y)` commutes with shifts. -/
instance commShift_affineChartDerivedTildeQcoh :
    (affineChartDerivedTildeQcoh B S hS Y hA).CommShift ℤ :=
  inferInstanceAs ((ObjectProperty.lift _ _ _).CommShift ℤ)

/-- `T : D(R) ⥤ D_QCoh(𝒪_Y)` is a triangulated functor. -/
instance isTriangulated_affineChartDerivedTildeQcoh :
    (affineChartDerivedTildeQcoh B S hS Y hA).IsTriangulated :=
  inferInstanceAs (ObjectProperty.lift _ _ _).IsTriangulated

/-- `RΓ(A, -)`, restricted to `D_QCoh(𝒪_Y)`. -/
abbrev affineChartDerivedSectionsQcoh (A : SmallEtale B S hS Y.1) :
    (spaceQuasicoherentProp B S hS Y).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u} (affineChartRing B S hS Y (A := A))) :=
  ObjectProperty.ι _ ⋙ affineChartDerivedSections B S hS Y A

/-- `T ⊣ RΓ(A, -)` on `D_QCoh(𝒪_Y)`. -/
def affineChartDerivedQcohAdjunction :
    affineChartDerivedTildeQcoh B S hS Y hA ⊣ affineChartDerivedSectionsQcoh B S hS Y A :=
  Adjunction.restrictFullyFaithful (affineChartDerivedAdjunction B S hS Y hA)
    (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι _)
    (Functor.leftUnitor _ ≪≫ (ObjectProperty.liftCompιIso _ _ _).symm)
    (Functor.rightUnitor _).symm

/-- `T` is fully faithful. -/
def affineChartDerivedTildeFullyFaithful : (affineChartDerivedTilde B S hS Y hA).FullyFaithful :=
  Adjunction.fullyFaithfulLOfIsIsoUnit (affineChartDerivedAdjunction B S hS Y hA)

/-- `T : D(R) ⥤ D_QCoh(𝒪_Y)` is faithful. -/
instance faithful_affineChartDerivedTildeQcoh :
    (affineChartDerivedTildeQcoh B S hS Y hA).Faithful :=
  have := (affineChartDerivedTildeFullyFaithful B S hS Y hA).faithful
  have : (affineChartDerivedTildeQcoh B S hS Y hA ⋙ ObjectProperty.ι _).Faithful :=
    inferInstanceAs (affineChartDerivedTilde B S hS Y hA).Faithful
  Functor.Faithful.of_comp _ (ObjectProperty.ι _)

/-- `T : D(R) ⥤ D_QCoh(𝒪_Y)` is full. -/
instance full_affineChartDerivedTildeQcoh :
    (affineChartDerivedTildeQcoh B S hS Y hA).Full :=
  have := (affineChartDerivedTildeFullyFaithful B S hS Y hA).full
  have : (affineChartDerivedTildeQcoh B S hS Y hA ⋙ ObjectProperty.ι _).Full :=
    inferInstanceAs (affineChartDerivedTilde B S hS Y hA).Full
  Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)

include hA in
/-- **`RΓ(A, -)` has zero kernel on `D_QCoh(𝒪_Y)`.** -/
theorem isZero_of_isZero_affineChartDerivedSectionsQcoh_obj
    (E : (spaceQuasicoherentProp B S hS Y).FullSubcategory)
    (hE : IsZero ((affineChartDerivedSectionsQcoh B S hS Y A).obj E)) : IsZero E := by
  refine ObjectProperty.isZero_fullSubcategory_of_isZero_obj ?_
  refine isZero_of_forall_homFromUnit_eq_zero (X := Y.1) (hX := Y.2) A hA
    (inferInstanceAs (IsAffine (chartScheme A))) E.obj E.property fun q g => ?_
  set adj := affineChartDerivedAdjunction B S hS Y hA
  set i := affineChartDerivedTildeSingleUnitIso B S hS Y hA 0
  have hZ : IsZero ((affineChartDerivedSections B S hS Y A).obj (E.obj⟦q⟧)) :=
    IsZero.of_iso ((shiftFunctor _ q).map_isZero hE)
      (((affineChartDerivedSections B S hS Y A).commShiftIso q).app E.obj)
  have h0 : adj.homEquiv _ _ (i.hom ≫ g) = 0 := hZ.eq_of_tgt _ _
  have h1 : i.hom ≫ g = 0 := by
    rw [← (adj.homEquiv _ _).symm_apply_apply (i.hom ≫ g), h0, Adjunction.homEquiv_counit,
      Functor.map_zero, Limits.zero_comp]
  simpa using congrArg (i.inv ≫ ·) h1

/-- `T : D(R) ⥤ D_QCoh(𝒪_Y)` is an equivalence of categories. -/
instance isEquivalence_affineChartDerivedTildeQcoh :
    (affineChartDerivedTildeQcoh B S hS Y hA).IsEquivalence :=
  isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero _ _
    (affineChartDerivedQcohAdjunction B S hS Y hA)
    (isZero_of_isZero_affineChartDerivedSectionsQcoh_obj B S hS Y hA)

/-- **The counit `T RΓ(A, E) ⟶ E` is invertible** for `E` in `D_QCoh(𝒪_Y)`. -/
theorem isIso_affineChartDerivedAdjunction_counit_app
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (hE : spaceQuasicoherentProp B S hS Y E) :
    IsIso ((affineChartDerivedAdjunction B S hS Y hA).counit.app E) := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := affineChartDerivedTildeQcoh B S hS Y hA)
    (⟨E, hE⟩ : (spaceQuasicoherentProp B S hS Y).FullSubcategory)
  have := (affineChartDerivedTildeFullyFaithful B S hS Y hA).full
  have := (affineChartDerivedTildeFullyFaithful B S hS Y hA).faithful
  exact Adjunction.isIso_counit_app_of_iso _ ((ObjectProperty.ι _).mapIso e.symm)


/-! ### Quasi-coherent representatives and degree bounds -/

/-- `T M` is represented by a complex of quasi-coherent modules. -/
theorem exists_quasicoherent_iso_affineChartDerivedTilde_obj
    (M : DerivedCategory (ModuleCat.{u} (affineChartRing B S hS Y (A := A)))) :
    ∃ (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
      (_ : ∀ n, (C.X n).IsQuasicoherentOnSite),
      Nonempty ((spaceDerivedQ B S hS Y).obj C ≅ (affineChartDerivedTilde B S hS Y hA).obj M) :=
  ⟨((affineChartTilde B S hS Y hA).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (DerivedCategory.Q.objPreimage M),
    fun _ => isQuasicoherentOnSite_affineChartTilde_obj B S hS Y hA _,
    ⟨((affineChartTilde B S hS Y hA).mapDerivedCategoryFactors.app
        (DerivedCategory.Q.objPreimage M)).symm ≪≫
      (affineChartDerivedTilde B S hS Y hA).mapIso (DerivedCategory.Q.objObjPreimageIso M)⟩⟩

/-- `T` does not raise top degrees. -/
theorem spaceCohomologyVanishesAbove_affineChartDerivedTilde_obj
    (M : DerivedCategory (ModuleCat.{u} (affineChartRing B S hS Y (A := A)))) (b : ℤ)
    (hM : M.IsLE b) :
    SpaceCohomologyVanishesAbove B S hS Y b ((affineChartDerivedTilde B S hS Y hA).obj M) :=
  fun i hi => IsZero.of_iso ((affineChartTilde B S hS Y hA).map_isZero
      (DerivedCategory.isZero_of_isLE M b i hi))
    (((affineChartTilde B S hS Y hA).mapDerivedCategoryHomologyIso i).app M)

/-- **`RΓ(A, -)` of a K-injective complex of affine amplitude `≤ b` lies in degrees `≤ b`.** -/
theorem isLE_affineChartDerivedSections_obj (b : ℤ)
    (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (hI : I.IsKInjective)
    (hamp : SectionsAmplitudeLE B S hS Y b I) :
    ((affineChartDerivedSections B S hS Y A).obj ((spaceDerivedQ B S hS Y).obj I)).IsLE b := by
  let G := affineChartSections B S hS Y A
  obtain ⟨-, h₂⟩ :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)
  let qI := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  let α := (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  have : IsIso (α.app qI) := h₂ DerivedCategory.Qh _ _ I hI
  let e : (affineChartDerivedSections B S hS Y A).obj ((spaceDerivedQ B S hS Y).obj I) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    (affineChartDerivedSections B S hS Y A).mapIso
        ((DerivedCategory.quotientCompQhIso _).app I).symm ≪≫
      (asIso (α.app qI)).symm ≪≫ (DerivedCategory.quotientCompQhIso _).app _
  have hQ :
      (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).IsLE b := by
    rw [DerivedCategory.isLE_Q_obj_iff, CochainComplex.isLE_iff]
    intro i hi
    have h := hamp A (inferInstanceAs (IsAffine (chartScheme A))) i hi
    rw [← HomologicalComplex.exactAt_iff_isZero_homology] at h
    exact (HomologicalComplex.exactAt_map_iff_of_preservesHomology _
      (forget₂ (ModuleCat.{u} (affineChartRing B S hS Y (A := A))) AddCommGrpCat.{u}) i).1 h
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm b

include hA in
/-- **The affine case of the coherator** at an algebraic space with a terminal affine chart: every
object of `D(𝒪_Y)` is coreflective, every object of `D_QCoh(𝒪_Y)` is represented by a complex of
quasi-coherent modules, and the coreflection of a K-injective complex of affine amplitude at most
`b` lies in degrees `≤ b`. -/
theorem affineCoreflection_of_isTerminal_chart :
    (∀ K, spaceCoreflective B S hS Y K) ∧
    (∀ E, spaceQuasicoherentProp B S hS Y E →
      ∃ (C : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
        (_ : ∀ n, (C.X n).IsQuasicoherentOnSite), Nonempty ((spaceDerivedQ B S hS Y).obj C ≅ E)) ∧
    ∀ (b : ℤ) (I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ), I.IsKInjective →
      SectionsAmplitudeLE B S hS Y b I →
        ∃ (E Q' : spaceDerivedCategory B S hS Y) (a : E ⟶ (spaceDerivedQ B S hS Y).obj I)
          (b' : (spaceDerivedQ B S hS Y).obj I ⟶ Q') (c : Q' ⟶ E⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk a b' c ∈ distTriang _ ∧ spaceQuasicoherentProp B S hS Y E ∧
            (spaceQuasicoherentProp B S hS Y).rightOrthogonal Q' ∧
            SpaceCohomologyVanishesAbove B S hS Y b E :=
  affineCoreflection_of_equivalence Y (affineChartDerivedTilde B S hS Y hA)
    (affineChartDerivedSections B S hS Y A) (affineChartDerivedAdjunction B S hS Y hA)
    (isIso_affineChartDerivedAdjunction_counit_app B S hS Y hA)
    (spaceQuasicoherentProp_affineChartDerivedTilde_obj B S hS Y hA)
    (exists_quasicoherent_iso_affineChartDerivedTilde_obj B S hS Y hA)
    (fun M b => M.IsLE b)
    (fun M b hM => spaceCohomologyVanishesAbove_affineChartDerivedTilde_obj B S hS Y hA M b hM)
    (fun b I hI hamp => isLE_affineChartDerivedSections_obj B S hS Y b I hI hamp)

end Chart

/-- **[Stacks, Tag 08H0, 09T5] The affine case of the coherator**: on an affine algebraic space
every object of `D(𝒪_Y)` is coreflective, every object of `D_QCoh(𝒪_Y)` is represented by a
complex of quasi-coherent modules, and the coreflection of a K-injective complex of affine
amplitude at most `b` lies in degrees `≤ b`. -/
theorem affineCoheratorCase (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    FlatSheafExistenceSituation.AffineCoheratorCase B S hS := by
  intro Y hY
  obtain ⟨A, ⟨hA⟩, hAff⟩ := exists_isTerminal_isAffine_chart B S hS Y hY
  have : IsAffine (chartScheme A) := hAff
  exact affineCoreflection_of_isTerminal_chart B S hS Y hA

end AlgebraicGeometry.Space

end
