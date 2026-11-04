module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.AugmentationDerivedBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteLowerShriek

/-!
# Derived base change of simplicial modules and derived lower shriek on `D(A_•)`

Let `C` be a site and let `A_• ⟶ B_•` be a homomorphism of simplicial sheaves of (commutative)
rings on `C`. The prose of the Stacks project preceding Lemma 09D2 introduces three functors:

* the derived category `D(A_•)` of simplicial `A_•`-modules, i.e. of sheaves of modules over the
  sheaf of rings on `Δ × C` attached to `A_•` (Definition 09D1);
* the derived base change `- ⊗^L_{A_•} B_• : D(A_•) ⥤ D(B_•)`;
* derived lower shriek `Lπ_! : D(A_•) ⥤ D(C)` along the projection `π : Δ × C ⥤ C`, obtained
  by forgetting the module structure and applying `Lπ_!` on abelian sheaves (Remark 09CY).

This file builds all three, the canonical map `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_{A_•} B_•)` whose
invertibility is Lemma 09D2, and the hypothesis of that lemma.

## Main definitions

* `Stacks.SimplicialModules.commRingSheaf`: the sheaf of commutative rings on `Δ × C` attached to
  a simplicial sheaf of commutative rings, and `commRingSheafMap` its functoriality.
* `Stacks.SimplicialModules.Modules`: the category `Mod(A_•)`; its derived category is `D(A_•)`.
* `Stacks.SimplicialModules.toAbelian`: the underlying abelian sheaf on `Δ × C`.
* `Stacks.SimplicialModules.baseChange` and `restrictScalars`: the underived change of rings
  along `A_• ⟶ B_•`, and `baseChangeAdjunction`.
* `Stacks.SimplicialModules.derivedBaseChange`: `- ⊗^L_{A_•} B_• : D(A_•) ⥤ D(B_•)`, the derived
  pullback of Stacks 06YY along the change of coefficient rings, and
  `derivedRestrictScalars` with the adjunction `derivedBaseChangeAdjunction`.
* `Stacks.SimplicialModules.derivedLowerShriek`: `Lπ_! : D(Δ × C) ⥤ D(C)` on abelian sheaves.
* `Stacks.SimplicialModules.moduleDerivedLowerShriek`: `Lπ_! : D(A_•) ⥤ D(C)`.
* `Stacks.SimplicialModules.derivedBaseChangeComparison`: the canonical transformation
  `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_{A_•} B_•)`.
* `Stacks.SimplicialModules.ringAbelianSheafMap`: `A_• ⟶ B_•` read as a morphism of abelian
  sheaves on `Δ × C`; the hypothesis of Stacks 09D2 is that `Lπ_!` inverts it.

## Implementation notes

**Commutative rings.** The rings of the Stacks project are commutative, and the derived tensor
product of the library (Stacks 06YS, 06YU, 06YY) is built for a sheaf of commutative rings; so
here `A_•` is a simplicial object in sheaves of commutative rings. The category `Mod(A_•)` is the
category of sheaves of modules over the sheaf of rings underlying `commRingSheaf J A`, which is
the uncurried presheaf of `A_•` (compare `Stacks.SimplicialModules.ringSheaf`).

**Universes.** The derived pullback of the library is available for a small site whose object,
morphism, ring and module universes all coincide; so `C : Type u` is a `SmallCategory` and the
rings and modules have sections in `Type u`. `Δ × C` is then again a small category in `Type u`.

**The base change.** `derivedBaseChange` is the derived pullback along the morphism of ringed
topoi `(Sh(Δ × C), B_•) ⟶ (Sh(Δ × C), A_•)` presenting the change of coefficient rings
(`Stacks.Cohomology.derivedCoefficientChange`). On a K-flat complex with flat terms it is
computed degreewise by `- ⊗_{A_•} B_•`
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isIso_derivedPullbackComparison_app_kFlat`).
Its right adjoint is the functor induced by restriction of scalars, which is exact; the derived
adjunction is `CategoryTheory.Adjunction.derivedMapDerivedCategoryOfResolutions`, the resolving
class being the K-flat complexes with flat terms of Stacks 06YS.

**`Lπ_!`.** The functor `Lπ_!` on abelian sheaves is the canonical unbounded left derived
functor of `π_!`, whose existence is Stacks 07AC for the projection of a fibred category, proved
in `StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionLowerShriekAcyclic.lean` through `simplicialSituation`. The structure sheaf of the
ringed site required by `simplicialSituation` plays no role in lower shriek on abelian sheaves;
`auxRingedSite` supplies the terminal sheaf of rings there and is only used to discharge the
existence of the derived functor.

**The comparison.** `derivedBaseChangeComparison` is `Lπ_!` applied to the unit
`K ⟶ (K ⊗^L_{A_•} B_•)|_{A_•}` of the derived adjunction, read through the identification of
the underlying derived abelian sheaf of a restriction of scalars with that of the module itself
(restriction of scalars does not change the underlying abelian sheaf).

## References

* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1)
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.SimplicialModules

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

section Rings

/-- **The sheaf of commutative rings on `Δ × C` attached to a simplicial sheaf of commutative
rings** (Stacks 09D0, 09D1). -/
def commRingSheaf (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    Sheaf (simplicialProjectionTopology J) CommRingCat.{u} :=
  ⟨associatedCommRingPresheaf J A, isSheaf_associatedCommRingPresheaf J A⟩

/-- The morphism of sheaves of commutative rings on `Δ × C` attached to a homomorphism of
simplicial sheaves of commutative rings. -/
def commRingSheafMap {A B : SimplicialObject (Sheaf J CommRingCat.{u})} (φ : A ⟶ B) :
    commRingSheaf J A ⟶ commRingSheaf J B :=
  ⟨Functor.whiskerLeft (prodOpEquiv SimplexCategory (D := C)).functor
    (Functor.uncurry.map (Functor.whiskerRight φ (sheafToPresheaf J CommRingCat.{u})))⟩

end Rings

/-- **`Mod(A_•)`**, the category of simplicial `A_•`-modules: sheaves of modules on `Δ × C` over
the sheaf of rings attached to `A_•` (Stacks 09D1). Its derived category is `D(A_•)`. -/
abbrev Modules (A : SimplicialObject (Sheaf J CommRingCat.{u})) :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A))

/-- The underlying abelian sheaf on `Δ × C` of a simplicial module. -/
abbrev toAbelian (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    Modules J A ⥤ Sheaf (simplicialProjectionTopology J) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf _

/-- The underlying abelian sheaf functor preserves finite colimits. -/
instance (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    PreservesFiniteColimits (toAbelian J A) :=
  Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _

/-- The underlying derived abelian sheaf on `Δ × C` of an object of `D(A_•)`. -/
abbrev toAbelianDerived (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    DerivedCategory (Modules J A) ⥤
      DerivedCategory (Sheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}) :=
  (toAbelian J A).mapDerivedCategory

section LowerShriek

/-- The ringed site with underlying site `(C, J)` and structure sheaf the terminal sheaf of
commutative rings. -/
def auxRingedSite : AlgebraicGeometry.RingedSite.{u, u, u} where
  C := C
  J := J
  O := ⊤_ (Sheaf J CommRingCat.{u})

/-- **Stacks 07AC for the projection `Δ × C ⥤ C`.** Degreewise `π_!` on the unbounded homotopy
category of abelian sheaves has a pointwise left derived functor. -/
instance hasPointwiseLeftDerived_lowerShriek :
    (Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekOnHomotopy.{u}
        (simplicialProjectionTopology J)
      J (simplicialProjection (C := C)) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (simplicialProjectionTopology J) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  (simplicialSituation (auxRingedSite J)).hasPointwiseLeftDerivedAbelianLowerShriek
    (simplicialSituation (auxRingedSite J)).abelianLowerShriekAcyclic

/-- **`Lπ_! : D(Δ × C) ⥤ D(C)`**, the unbounded left derived functor of lower shriek on abelian
sheaves along the projection `π : Δ × C ⥤ C` (Remark 09CY). -/
abbrev derivedLowerShriek :
    DerivedCategory (Sheaf (simplicialProjectionTopology J) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{u}) :=
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u}
    (simplicialProjectionTopology J) J
    (simplicialProjection (C := C))

/-- `derivedLowerShriek` is the `Lπ_!` of the fibred-category situation of the projection. -/
theorem derivedLowerShriek_eq :
    derivedLowerShriek J = (simplicialSituation (auxRingedSite J)).derivedAbelianLowerShriek :=
  rfl

/-- **`Lπ_! : D(A_•) ⥤ D(C)`**: the underlying derived abelian sheaf on `Δ × C`, followed by
`Lπ_!` on abelian sheaves. -/
abbrev moduleDerivedLowerShriek (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    DerivedCategory (Modules J A) ⥤ DerivedCategory (Sheaf J AddCommGrpCat.{u}) :=
  toAbelianDerived J A ⋙ derivedLowerShriek J

end LowerShriek

/-- A commutative ring, read as an abelian group. -/
abbrev forgetToAddCommGrp : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}

section BaseChange

variable {A B : SimplicialObject (Sheaf J CommRingCat.{u})} (φ : A ⟶ B)

/-- The change of coefficient rings along `A_• ⟶ B_•`, as a morphism of ringed topoi
`(Sh(Δ × C), B_•) ⟶ (Sh(Δ × C), A_•)`. -/
abbrev coefficientChangeHom :=
  RingedToposSiteHom.coefficientChange.{u, u, u} (simplicialProjectionTopology J)
    (commRingSheafMap J φ)

/-- Extension of scalars `- ⊗_{A_•} B_• : Mod(A_•) ⥤ Mod(B_•)`. -/
abbrev baseChange : Modules J A ⥤ Modules J B :=
  (coefficientChangeHom J φ).pullbackTopos

/-- Restriction of scalars `Mod(B_•) ⥤ Mod(A_•)`. -/
abbrev restrictScalars : Modules J B ⥤ Modules J A :=
  (coefficientChangeHom J φ).pushforwardTopos

/-- The adjunction `- ⊗_{A_•} B_• ⊣ restriction of scalars`. -/
abbrev baseChangeAdjunction : baseChange J φ ⊣ restrictScalars J φ :=
  (coefficientChangeHom J φ).pullbackPushforwardAdjunctionTopos

/-- Extension of scalars is additive. -/
instance baseChange_additive : (baseChange J φ).Additive :=
  RingedToposSiteHom.pullbackTopos_additive _

/-- Restriction of scalars is additive. -/
instance restrictScalars_additive : (restrictScalars J φ).Additive :=
  RingedToposSiteHom.pushforwardTopos_additive _

/-- Restriction of scalars does not change the underlying abelian sheaf. -/
def restrictScalarsCompToAbelianIso :
    restrictScalars J φ ⋙ toAbelian J A ≅ toAbelian J B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Restriction of scalars preserves finite limits. -/
instance restrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (restrictScalars J φ) :=
  letI : PreservesFiniteLimits (restrictScalars J φ ⋙ toAbelian J A) :=
    preservesFiniteLimits_of_natIso (restrictScalarsCompToAbelianIso J φ).symm
  preservesFiniteLimits_of_reflects_of_preserves _ (toAbelian J A)

/-- Restriction of scalars preserves finite colimits. -/
instance restrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (restrictScalars J φ) :=
  letI : PreservesFiniteColimits (restrictScalars J φ ⋙ toAbelian J A) :=
    preservesFiniteColimits_of_natIso (restrictScalarsCompToAbelianIso J φ).symm
  preservesFiniteColimits_of_reflects_of_preserves _ (toAbelian J A)

/-- **`- ⊗^L_{A_•} B_• : D(A_•) ⥤ D(B_•)`**, derived base change of simplicial modules: the
derived pullback of Stacks 06YY along the change of coefficient rings. -/
abbrev derivedBaseChange :
    DerivedCategory (Modules J A) ⥤ DerivedCategory (Modules J B) :=
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback (coefficientChangeHom J φ)

/-- `derivedBaseChange` is the derived change of coefficient rings of the library. -/
theorem derivedBaseChange_eq :
    derivedBaseChange J φ = Stacks.Cohomology.derivedCoefficientChange.{u} (commRingSheafMap J φ) :=
  rfl

/-- Restriction of scalars on derived categories, induced degreewise (it is exact). -/
abbrev derivedRestrictScalars :
    DerivedCategory (Modules J B) ⥤ DerivedCategory (Modules J A) :=
  (restrictScalars J φ).mapDerivedCategory

/-- The comparison from derived base change to degreewise base change, invertible on K-flat
complexes with flat terms. -/
abbrev derivedBaseChangeComparisonh :
    DerivedCategory.Qh ⋙ derivedBaseChange J φ ⟶
      (baseChange J φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison
    (coefficientChangeHom J φ)

/-- `derivedBaseChange` is a left derived functor of degreewise base change, with respect to
`derivedBaseChangeComparisonh`. -/
instance isLeftDerivedFunctor_derivedBaseChange :
    (derivedBaseChange J φ).IsLeftDerivedFunctor (derivedBaseChangeComparisonh J φ)
      (HomotopyCategory.quasiIso (Modules J A) (ComplexShape.up ℤ)) :=
  inferInstance

/-- **Derived base change is left adjoint to derived restriction of scalars.** -/
def derivedBaseChangeAdjunction : derivedBaseChange J φ ⊣ derivedRestrictScalars J φ :=
  (baseChangeAdjunction J φ).derivedMapDerivedCategoryOfResolutions
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ⟨SimplexCategory × C, simplicialProjectionTopology J, commRingSheaf J A⟩))
    (fun X => Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := ⟨SimplexCategory × C, simplicialProjectionTopology J, commRingSheaf J A⟩) X)
    (fun s hs hK hM =>
      Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat
        (coefficientChangeHom J φ) (Functor.isMorphismOfSites_id _) s hs hK hM)

/-- Derived base change stays a left derived functor after composition with derived restriction
of scalars: it is computed by K-flat resolutions. -/
theorem isLeftDerivedFunctor_derivedBaseChange_comp :
    (derivedBaseChange J φ ⋙ derivedRestrictScalars J φ).IsLeftDerivedFunctor
      ((DerivedCategory.Qh.associator (derivedBaseChange J φ) (derivedRestrictScalars J φ)).inv ≫
        Functor.whiskerRight (derivedBaseChangeComparisonh J φ) (derivedRestrictScalars J φ))
      (HomotopyCategory.quasiIso (Modules J A) (ComplexShape.up ℤ)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_comp_of_resolutions
    (HomotopyCategory.quasiIso (Modules J A) (ComplexShape.up ℤ))
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := ⟨SimplexCategory × C, simplicialProjectionTopology J, commRingSheaf J A⟩))
    (fun X => Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := ⟨SimplexCategory × C, simplicialProjectionTopology J, commRingSheaf J A⟩) X)
    _ (fun s hs hK hM =>
      Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat
        (coefficientChangeHom J φ) (Functor.isMorphismOfSites_id _) s hs hK hM)
    DerivedCategory.Qh (derivedBaseChange J φ) (derivedBaseChangeComparisonh J φ)
    (derivedRestrictScalars J φ)

/-- The unit of `derivedBaseChangeAdjunction` is computed by the degreewise unit. -/
theorem derivedBaseChangeAdjunction_unit_fac
    (M : HomotopyCategory (Modules J A) (ComplexShape.up ℤ)) :
    (derivedBaseChangeAdjunction J φ).unit.app (DerivedCategory.Qh.obj M) ≫
        (derivedRestrictScalars J φ).map ((derivedBaseChangeComparisonh J φ).app M) =
      DerivedCategory.Qh.map
          (((baseChangeAdjunction J φ).mapHomotopyCategoryAdjunction
            (ComplexShape.up ℤ)).unit.app M) ≫
        (restrictScalars J φ).mapDerivedCategoryFactorsh.inv.app
          (((baseChange J φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  have := isLeftDerivedFunctor_derivedBaseChange_comp J φ
  have := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact (restrictScalars J φ)
  have := Functor.isRightDerivedFunctor_mapDerivedCategory_comp_of_exact (restrictScalars J φ)
    (derivedBaseChange J φ)
  ((baseChangeAdjunction J φ).mapHomotopyCategoryAdjunction (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso (Modules J A) (ComplexShape.up ℤ))
    (derivedBaseChangeComparisonh J φ) (restrictScalars J φ).mapDerivedCategoryFactorsh.inv M

/-- Derived restriction of scalars does not change the underlying derived abelian sheaf. -/
def derivedRestrictScalarsCompToAbelianIso :
    derivedRestrictScalars J φ ⋙ toAbelianDerived J A ≅ toAbelianDerived J B :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso (restrictScalars J φ)
      (toAbelian J A)).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (restrictScalarsCompToAbelianIso J φ)

/-- The canonical map `K ⟶ K ⊗^L_{A_•} B_•` read on underlying derived abelian sheaves on
`Δ × C`: the unit of the derived adjunction, followed by the identification of the underlying
derived abelian sheaf of a restriction of scalars. -/
def derivedBaseChangeUnitAbelian :
    toAbelianDerived J A ⟶ derivedBaseChange J φ ⋙ toAbelianDerived J B :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (derivedBaseChangeAdjunction J φ).unit (toAbelianDerived J A) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (derivedBaseChange J φ) (derivedRestrictScalarsCompToAbelianIso J φ).hom

/-- The component of `derivedBaseChangeUnitAbelian` at `K` is the underlying map of the unit at
`K`, followed by the identification of the underlying derived abelian sheaf. -/
@[simp]
theorem derivedBaseChangeUnitAbelian_app (K : DerivedCategory (Modules J A)) :
    (derivedBaseChangeUnitAbelian J φ).app K =
      (toAbelianDerived J A).map ((derivedBaseChangeAdjunction J φ).unit.app K) ≫
        (derivedRestrictScalarsCompToAbelianIso J φ).hom.app ((derivedBaseChange J φ).obj K) := by
  simp [derivedBaseChangeUnitAbelian]

/-- **The canonical map `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_{A_•} B_•)`** of Stacks 09D2, natural in `K` in
`D(A_•)`: `Lπ_!` applied to the unit of derived base change, read on underlying derived abelian
sheaves. -/
def derivedBaseChangeComparison :
    moduleDerivedLowerShriek J A ⟶ derivedBaseChange J φ ⋙ moduleDerivedLowerShriek J B :=
  Functor.whiskerRight (derivedBaseChangeUnitAbelian J φ) (derivedLowerShriek J) ≫
    (Functor.associator _ _ _).hom

/-- The component of `derivedBaseChangeComparison` at `K` is `Lπ_!` applied to the component of
`derivedBaseChangeUnitAbelian` at `K`. -/
@[simp]
theorem derivedBaseChangeComparison_app (K : DerivedCategory (Modules J A)) :
    (derivedBaseChangeComparison J φ).app K =
      (derivedLowerShriek J).map ((derivedBaseChangeUnitAbelian J φ).app K) := by
  simp [derivedBaseChangeComparison]

/-- `A_• ⟶ B_•`, read as a morphism of abelian sheaves on `Δ × C`. -/
abbrev ringAbelianSheafMap :
    (sheafCompose (simplicialProjectionTopology J) forgetToAddCommGrp).obj (commRingSheaf J A) ⟶
      (sheafCompose (simplicialProjectionTopology J) forgetToAddCommGrp).obj (commRingSheaf J B) :=
  (sheafCompose (simplicialProjectionTopology J) forgetToAddCommGrp).map (commRingSheafMap J φ)

end BaseChange

end Stacks.SimplicialModules
