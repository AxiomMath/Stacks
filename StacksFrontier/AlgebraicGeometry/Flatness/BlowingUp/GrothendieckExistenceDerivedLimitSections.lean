module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafHypercohomologyOnASpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomAdjunctionOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceCoheratorLimit
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitTriangleTransfer
public import StacksFrontier.AlgebraicGeometry.Perfect.SheafHomFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology

/-!
# Derived limits through `RΓ_A(X, R𝓗om(E, -))` and `RΓ_A(X, - ⊗^L E)` in Situation 0CTC

In Situation [Stacks, Tag 0CTC] let `d` be the data of [Stacks, Tag 0CTD]: a derived limit
`L = R lim iₙ,* Fₙ` in `D(𝒪_X)` and the map `ε : K ⟶ L` universal among maps from objects with
quasi-coherent cohomology.  For `E` perfect, `RΓ_A(X, R𝓗om(E, K))` and `RΓ_A(X, K ⊗^L E)` are
derived limits of the systems `RΓ_A(X, R𝓗om(E, iₙ,* Fₙ))` and `RΓ_A(X, iₙ,* Fₙ ⊗^L E)`, with the
first map of the derived-limit triangle pinned: the image of `ε ≫ p` followed by the product
comparison, for `p` the first map of a given derived-limit triangle of `L`.  These are the
derived-limit steps of the proof of [Stacks, Tag 0CTE].

The argument is the source's.  The cone `C` of `ε` is right orthogonal to `D_QCoh(𝒪_X)`
(`Stacks.Injectives.eq_zero_of_isUniversal_of_distTriang`), so for `B` with `𝒪_X ⊗^L B`
quasi-coherent, `H^n(X, R𝓗om(B, C)) = Hom(𝒪_X ⊗^L B, C[n]) = 0` and `RΓ_A(X, R𝓗om(B, ε))` is
invertible.  `R𝓗om(B, -)` is an exact right adjoint, so it preserves the derived-limit triangle,
and `RΓ_A(X, -)` carries derived limits to derived limits ([Stacks, Tag 08U1]).  For the tensor
product, `- ⊗^L E ≅ R𝓗om(E^∨, -)` by [Stacks, Tag 08DQ].

## Main results

* `AlgebraicGeometry.GrothendieckExistence.isZero_derivedGlobalSectionsOver_derivedSheafHom`:
  `RΓ_A(X, R𝓗om(B, C)) = 0` when `C` is right orthogonal to the shifts of `𝒪_X ⊗^L B`.
* `...ExistenceSituation.isIso_derivedGlobalSectionsOver_map_derivedSheafHom_ε`.
* `...ExistenceSituation.derivedLimitTriangle_globalSectionsSheafHom` and its perfect form
  `...derivedLimitTriangle_globalSectionsSheafHom_of_isPerfect`.
* `...ExistenceSituation.derivedLimitTriangle_globalSectionsTensor_of_isPerfect`.

## Implementation notes

Every declaration is stated at the standard model of the derived categories, through a
`attribute [local instance 10000] HasDerivedCategory.standard in` before it: the derived internal
Hom, the derived tensor products, the identifications of [Stacks, Tag 08DQ] and the
hypercohomology identification of ringed spaces they use are stated there.

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0CTD](https://stacks.math.columbia.edu/tag/0CTD)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (derivedSheafHom derivedDual ringedSite StructureSheafModules)
open Stacks.Cohomology.ModuleSections (derivedModuleGlobalSections)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

namespace AlgebraicGeometry.GrothendieckExistence


attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ_A(X, R𝓗om(B, C))` vanishes when `C` is right orthogonal to every shift of
`𝒪_X ⊗^L B`.**

Stated at the standard model of the derived categories: the derived internal Hom, the derived
tensor product and the hypercohomology identification of ringed spaces it uses are stated there,
and so is the derived limit of Stacks 0CTE that consumes it. -/
theorem isZero_derivedGlobalSectionsOver_derivedSheafHom
    (B C : DerivedCategory (StructureSheafModules X.sheaf))
    (hC : ∀ (n : ℤ) (g : ((Stacks.SheafOfModules.derivedTensorRight X.sheaf B).obj
        (RingedSite.derivedStructureSheaf (ringedSite X.sheaf))) ⟶
          C⟦n⟧), g = 0) :
    IsZero ((derivedGlobalSectionsOver f).obj
      (((derivedSheafHom X.sheaf).obj (op B)).obj C)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  set N := ((derivedSheafHom X.sheaf).obj (op B)).obj C
  -- morphisms `𝒪_X ⟶ N[n]` are morphisms `𝒪_X ⊗^L B ⟶ C[n]`, which all vanish
  have hHom : Subsingleton
      (RingedSite.derivedStructureSheaf (ringedSite X.sheaf) ⟶ N⟦n⟧) := by
    refine ⟨fun a b ↦ ?_⟩
    let := Stacks.SheafOfModules.commShift_derivedSheafHom X.sheaf B
    let i := (((derivedSheafHom X.sheaf).obj (op B)).commShiftIso n).app C
    let adj := Stacks.SheafOfModules.derivedSheafHomTensorAdjunction X.sheaf B
    exact (Iso.cancel_iso_inv_right a b i).1
      ((adj.homEquiv _ _).symm.injective ((hC n _).trans (hC n _).symm))
  -- hence the hypercohomology group of the ringed space vanishes
  have hH : Subsingleton ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj N)) :=
    (Stacks.SheafOfModules.derivedStructureSheafGlobalSectionsDegreeEquiv X.sheaf N
        n).toEquiv.subsingleton
  -- and so does the cohomology `A`-module, its scalars forgotten
  let e : (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj ((derivedGlobalSectionsOver
          f).obj N)) ≅
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
          ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj N) :=
    ((Stacks.Homology.derivedHomologyIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) n).app
        ((derivedGlobalSectionsOver f).obj N)).symm ≪≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
        ((Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso f).app
            N)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1
    (IsZero.of_iso (AddCommGrpCat.isZero_iff_subsingleton.2 hH) e)

namespace ExistenceSituation

open Pretriangulated

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ_A(X, R𝓗om(B, ε))` is invertible**, for `ε : K ⟶ L` the map of [Stacks, Tag 0CTD] and
`B` with `𝒪_X ⊗^L B` quasi-coherent.  The cone of `ε` is right orthogonal to `D_QCoh(𝒪_X)`, so
`RΓ_A(X, R𝓗om(B, -))` kills it (`isZero_derivedGlobalSectionsOver_derivedSheafHom`).

Stated at the standard model of the derived categories, as are the results it consumes. -/
theorem isIso_derivedGlobalSectionsOver_map_derivedSheafHom_ε (d : S.DerivedLimitQCoh)
    (B : DerivedCategory (StructureSheafModules S.X.left.sheaf))
    (hB : ∀ i : ℤ, ((DerivedCategory.homologyFunctor S.X.left.Modules i).obj
      ((Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf B).obj
        (RingedSite.derivedStructureSheaf (ringedSite S.X.left.sheaf)))).IsQuasicoherent) :
    IsIso ((derivedGlobalSectionsOver S.X.hom).map
      (((derivedSheafHom S.X.left.sheaf).obj (op B)).map d.ε)) := by
  let : (Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf B).CommShift ℤ :=
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (ringedSite S.X.left.sheaf)).commShift_left B
  have : (Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf B).IsTriangulated :=
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (ringedSite S.X.left.sheaf)).exact_left B
  let adj := Stacks.SheafOfModules.derivedSheafHomTensorAdjunction S.X.left.sheaf B
  let : ((derivedSheafHom S.X.left.sheaf).obj (op B)).CommShift ℤ :=
    adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  -- the internal Hom read as an endofunctor of `D(𝒪_X)` in the spelling of `X.Modules`
  let G' : DerivedCategory S.X.left.Modules ⥤ DerivedCategory S.X.left.Modules :=
    (derivedSheafHom S.X.left.sheaf).obj (op B)
  let : G'.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : G'.IsTriangulated := adj.isTriangulated_rightAdjoint
  -- the cone of `ε` is right orthogonal to `𝒪_X ⊗^L B` and its shifts
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle d.ε
  have hZ : ∀ (n : ℤ) (φ : (Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf B).obj
      (RingedSite.derivedStructureSheaf (ringedSite S.X.left.sheaf)) ⟶
        Z⟦n⟧), φ = 0 := fun n φ ↦
    Stacks.Injectives.eq_zero_of_isUniversal_of_distTriang
      (DerivedCategoryB.derivedCategoryB (A := S.X.left.Modules)
        (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf))
      (fun M n hM ↦ (DerivedCategoryB.derivedCategoryB (A := S.X.left.Modules)
        (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf)).le_shift n M hM) d.ε
      d.universal (Triangle.mk d.ε g h) hT rfl rfl (by simp)
      (M := (Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf B).obj
        (RingedSite.derivedStructureSheaf (ringedSite S.X.left.sheaf)))
      hB n φ
  let := Functor.IsRightDerivedFunctor.commShift (derivedGlobalSectionsOver S.X.hom)
    (derivedGlobalSectionsOverUnit S.X.hom)
    (HomotopyCategory.quasiIso S.X.left.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Injectives.rightDerivedFunctor_isTriangulated (globalSectionsOver S.X.hom)
    (derivedGlobalSectionsOver S.X.hom) (derivedGlobalSectionsOverUnit S.X.hom)
  have hT' := (derivedGlobalSectionsOver S.X.hom).map_distinguished _ (G'.map_distinguished _ hT)
  exact (Triangle.isZero₃_iff_isIso₁ _ hT').1
    (isZero_derivedGlobalSectionsOver_derivedSheafHom S.X.hom B Z hZ)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RHom_X(B, K)` is the derived limit of `RHom_X(B, iₙ,* Fₙ)`**, for `K` the object of
[Stacks, Tag 0CTD] and `B` with `𝒪_X ⊗^L B` quasi-coherent, with the cone pinned.  Let `d` be the
data of [Stacks, Tag 0CTD] and `p : L ⟶ ∏ iₙ,* Fₙ` the first map of a derived-limit triangle of
`L = R lim iₙ,* Fₙ`.  Then `RΓ_A(X, R𝓗om(B, K))` is a derived limit of the system
`RΓ_A(X, R𝓗om(B, iₙ,* Fₙ))`, with first map `RΓ_A(X, R𝓗om(B, ε ≫ p))` followed by the product
comparison.

This is the step "`RHom_X(E, -)` commutes with derived limits" of the proof of
[Stacks, Tag 0CTE] (2).  `R𝓗om(B, -)` is an exact right adjoint and `RΓ_A(X, -)` carries derived
limits to derived limits ([Stacks, Tag 08U1]); and `RΓ_A(X, R𝓗om(B, ε))` is invertible because
the cone of `ε` is right orthogonal to `D_QCoh(𝒪_X)`.

Stated at the standard model of the derived categories, as are the results it consumes. -/
theorem derivedLimitTriangle_globalSectionsSheafHom (d : S.DerivedLimitQCoh)
    (B : DerivedCategory (StructureSheafModules S.X.left.sheaf))
    (hB : ∀ i : ℤ, ((DerivedCategory.homologyFunctor S.X.left.Modules i).obj
      ((Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf B).obj
        (RingedSite.derivedStructureSheaf (ringedSite S.X.left.sheaf)))).IsQuasicoherent)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ⟶ d.L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj
          ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n + 1) ≫
          S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory S.X.left.Modules)) :
    ∃ h : HasProduct (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj (((derivedSheafHom
        S.X.left.sheaf).obj (op B)).obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj (((derivedSheafHom
          S.X.left.sheaf).obj (op B)).obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))) ⟶
          ((derivedGlobalSectionsOver S.X.hom).obj (((derivedSheafHom S.X.left.sheaf).obj (op
              B)).obj d.K))⟦(1 : ℤ)⟧,
        Triangle.mk ((derivedGlobalSectionsOver S.X.hom).map (((derivedSheafHom
            S.X.left.sheaf).obj (op B)).map (d.ε ≫ p)) ≫
            Pi.lift fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).map (((derivedSheafHom
                S.X.left.sheaf).obj (op B)).map
              (Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) n)))
          (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj
              (((derivedSheafHom S.X.left.sheaf).obj (op B)).obj
              (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))) n -
            Pi.π (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj (((derivedSheafHom
                S.X.left.sheaf).obj (op B)).obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))) (n +
                1) ≫
              (derivedGlobalSectionsOver S.X.hom).map (((derivedSheafHom S.X.left.sheaf).obj (op
                  B)).map (S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op)))
          δ ∈ distTriang _ := by
  let : (Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf B).CommShift ℤ :=
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (ringedSite S.X.left.sheaf)).commShift_left B
  have : (Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf B).IsTriangulated :=
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (ringedSite S.X.left.sheaf)).exact_left B
  let adj := Stacks.SheafOfModules.derivedSheafHomTensorAdjunction S.X.left.sheaf B
  let : ((derivedSheafHom S.X.left.sheaf).obj (op B)).CommShift ℤ :=
    adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let G' : DerivedCategory S.X.left.Modules ⥤ DerivedCategory S.X.left.Modules :=
    (derivedSheafHom S.X.left.sheaf).obj (op B)
  let : G'.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : G'.IsTriangulated := adj.isTriangulated_rightAdjoint
  have : PreservesLimitsOfSize.{0, 0} G' := adj.rightAdjoint_preservesLimits
  have : IsIso ((derivedGlobalSectionsOver S.X.hom).map (G'.map d.ε)) :=
    S.isIso_derivedGlobalSectionsOver_map_derivedSheafHom_ε d B hB
  exact Stacks.Injectives.derivedLimitTriangle_map_comp_rightDerivedFunctor
    (globalSectionsOver S.X.hom) (derivedGlobalSectionsOver S.X.hom)
    (derivedGlobalSectionsOverUnit S.X.hom) G' S.derivedPushforwardSystemOfModel d.ε p hp


attribute [local instance 10000] HasDerivedCategory.standard in
/-- `𝒪_X ⊗^L E` has quasi-coherent cohomology sheaves for `E` perfect: it is isomorphic to `E` by
the unit constraint of [Stacks, Tag 0FPT], and a perfect object is pseudo-coherent, so has
quasi-coherent cohomology ([Stacks, Tag 08E5]).

Stated at the standard model of the derived categories, as is the unit constraint. -/
theorem isQuasicoherent_homology_derivedTensorRight_structureSheaf_of_isPerfect
    (E : DerivedCategory (StructureSheafModules S.X.left.sheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E) (i : ℤ) :
    ((DerivedCategory.homologyFunctor S.X.left.Modules i).obj
      ((Stacks.SheafOfModules.derivedTensorRight S.X.left.sheaf E).obj
        (RingedSite.derivedStructureSheaf (ringedSite S.X.left.sheaf)))).IsQuasicoherent := by
  let := Stacks.SheafOfModules.derivedMonoidalStructure S.X.left.sheaf
  exact (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre
      S.X.left).isClosedUnderIsomorphisms.of_iso
    ((DerivedCategory.homologyFunctor S.X.left.Modules i).mapIso
      (MonoidalCategoryStruct.leftUnitor E).symm)
    (isQuasicoherentDerived_of_isPseudoCoherent S.X.left E
      (RingedSpace.IsPerfect.isPseudoCoherent (X := S.X.left.toRingedSpace) hE) i)


attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RHom_X(E, K)` is the derived limit of `RHom_X(E, iₙ,* Fₙ)` for `E` perfect**, with the cone
pinned.  Let `d` be the data of [Stacks, Tag 0CTD], `E` a perfect object of `D(𝒪_X)` and
`p : L ⟶ ∏ iₙ,* Fₙ` the first map of a derived-limit triangle of `L = R lim iₙ,* Fₙ`.  Then
`RΓ_A(X, R𝓗om(E, K))` is a derived limit of the system `RΓ_A(X, R𝓗om(E, iₙ,* Fₙ))`, with first
map `RΓ_A(X, R𝓗om(E, ε ≫ p))` followed by the product comparison.

This is the step "`RHom_X(E, -)` commutes with derived limits" of the proof of
[Stacks, Tag 0CTE] (2): `derivedLimitTriangle_globalSectionsSheafHom` at `B = E`, where
`𝒪_X ⊗^L E ≅ E` has quasi-coherent cohomology.

Stated at the standard model of the derived categories, as are the results it consumes. -/
theorem derivedLimitTriangle_globalSectionsSheafHom_of_isPerfect (d : S.DerivedLimitQCoh)
    (E : DerivedCategory (StructureSheafModules S.X.left.sheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ⟶ d.L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj
          ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n + 1) ≫
          S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory S.X.left.Modules)) :
    ∃ h : HasProduct (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj (((derivedSheafHom
        S.X.left.sheaf).obj (op E)).obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj (((derivedSheafHom
          S.X.left.sheaf).obj (op E)).obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))) ⟶
          ((derivedGlobalSectionsOver S.X.hom).obj (((derivedSheafHom S.X.left.sheaf).obj (op
              E)).obj d.K))⟦(1 : ℤ)⟧,
        Triangle.mk ((derivedGlobalSectionsOver S.X.hom).map (((derivedSheafHom
            S.X.left.sheaf).obj (op E)).map (d.ε ≫ p)) ≫
            Pi.lift fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).map (((derivedSheafHom
                S.X.left.sheaf).obj (op E)).map
              (Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) n)))
          (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj
              (((derivedSheafHom S.X.left.sheaf).obj (op E)).obj
              (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))) n -
            Pi.π (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj (((derivedSheafHom
                S.X.left.sheaf).obj (op E)).obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩))) (n +
                1) ≫
              (derivedGlobalSectionsOver S.X.hom).map (((derivedSheafHom S.X.left.sheaf).obj (op
                  E)).map (S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op)))
          δ ∈ distTriang _ :=
  S.derivedLimitTriangle_globalSectionsSheafHom d E
    (S.isQuasicoherent_homology_derivedTensorRight_structureSheaf_of_isPerfect E hE) p hp

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ_A(X, K ⊗^L E)` is the derived limit of `RΓ_A(X, iₙ,* Fₙ ⊗^L E)` for `E` perfect**, with
the cone pinned.  Let `d` be the data of [Stacks, Tag 0CTD], `E` a perfect object of `D(𝒪_X)` and
`p : L ⟶ ∏ iₙ,* Fₙ` the first map of a derived-limit triangle of `L = R lim iₙ,* Fₙ`.  Then
`RΓ_A(X, K ⊗^L E)` is a derived limit of the system `RΓ_A(X, iₙ,* Fₙ ⊗^L E)`, with first map
`RΓ_A(X, (ε ≫ p) ⊗^L E)` followed by the product comparison.

This is the derived-limit step of the proof of [Stacks, Tag 0CTE] (1).  By
[Stacks, Tag 08DQ], `- ⊗^L E ≅ - ⊗^L (E^∨)^∨ ≅ R𝓗om(E^∨, -)` with `E^∨` perfect, so `- ⊗^L E` is
an exact functor which preserves products, and `RΓ_A(X, ε ⊗^L E)` is invertible because
`RΓ_A(X, R𝓗om(E^∨, ε))` is (`isIso_derivedGlobalSectionsOver_map_derivedSheafHom_ε`).  The
transfer through `RΓ_A(X, -)` is [Stacks, Tag 08U1].

Stated at the standard model of the derived categories, as are the results it consumes. -/
theorem derivedLimitTriangle_globalSectionsTensor_of_isPerfect (d : S.DerivedLimitQCoh)
    (E : DerivedCategory S.X.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) ⟶ d.L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj
          ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n + 1) ≫
          S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory S.X.left.Modules)) :
    ∃ h : HasProduct (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj
        (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
        (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).obj E)),
      letI := h
      ∃ δ : (∏ᶜ fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj (((derivedTensorProductFunctor
          S.X.left.toRingedSpace.sheaf).obj (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).obj E)) ⟶
          ((derivedGlobalSectionsOver S.X.hom).obj (((derivedTensorProductFunctor
              S.X.left.toRingedSpace.sheaf).obj d.K).obj E))⟦(1 : ℤ)⟧,
        Triangle.mk ((derivedGlobalSectionsOver S.X.hom).map (((derivedTensorProductFunctor
            S.X.left.toRingedSpace.sheaf).map (d.ε ≫ p)).app E) ≫
            Pi.lift fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).map
                (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).map
              (Pi.π (fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩) n)).app E))
          (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj
              (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
              (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).obj E)) n -
            Pi.π (fun n : ℕ ↦ (derivedGlobalSectionsOver S.X.hom).obj
                (((derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).obj
                (S.derivedPushforwardSystemOfModel.obj ⟨n⟩)).obj E)) (n + 1) ≫
              (derivedGlobalSectionsOver S.X.hom).map (((derivedTensorProductFunctor
                  S.X.left.toRingedSpace.sheaf).map (S.derivedPushforwardSystemOfModel.map
                  (homOfLE (Nat.le_succ n)).op)).app E))
          δ ∈ distTriang _ := by
  -- `- ⊗^L E`, an exact endofunctor of `D(𝒪_X)`
  let Gb : DerivedCategory S.X.left.Modules ⥤ DerivedCategory S.X.left.Modules :=
    (derivedTensorProductFunctor S.X.left.toRingedSpace.sheaf).flip.obj E
  let : Gb.CommShift ℤ := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    S.X.left.toRingedSpace.sheaf).commShift_left E
  have : Gb.IsTriangulated := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    S.X.left.toRingedSpace.sheaf).exact_left E
  -- it is `R𝓗om(E^∨, -)`, by Stacks 08DQ
  have hE' := Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace S.X.left.toRingedSpace
    E hE
  let Ga : DerivedCategory S.X.left.Modules ⥤ DerivedCategory S.X.left.Modules :=
    (derivedSheafHom S.X.left.sheaf).obj (op (derivedDual S.X.left.sheaf E))
  let Φ : Gb ≅ Ga :=
    ((flipFunctor _ _ _).mapIso (derivedTensorSpellingIso S.X.left)).app E ≪≫
      (Stacks.SheafOfModules.derivedTensor S.X.left.sheaf).flip.mapIso
        (Stacks.SheafOfModules.derivedBidualIsoOfIsPerfectSpace S.X.left.toRingedSpace E hE) ≪≫
      Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace S.X.left.toRingedSpace _ hE'
  -- so it preserves products
  have : PreservesLimitsOfSize.{0, 0} Ga :=
    (Stacks.SheafOfModules.derivedSheafHomTensorAdjunction S.X.left.sheaf
      (derivedDual S.X.left.sheaf E)).rightAdjoint_preservesLimits
  have : PreservesLimit (Discrete.functor fun n : ℕ ↦ S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
      Gb :=
    preservesLimit_of_natIso _ Φ.symm
  -- and `RΓ_A(X, ε ⊗^L E)` is invertible
  have : IsIso ((derivedGlobalSectionsOver S.X.hom).map (Ga.map d.ε)) :=
    S.isIso_derivedGlobalSectionsOver_map_derivedSheafHom_ε d _
      (S.isQuasicoherent_homology_derivedTensorRight_structureSheaf_of_isPerfect _ hE')
  have : IsIso ((derivedGlobalSectionsOver S.X.hom).map (Gb.map d.ε)) := by
    rw [← NatIso.naturality_1 Φ.symm d.ε, Functor.map_comp, Functor.map_comp]
    infer_instance
  exact Stacks.Injectives.derivedLimitTriangle_map_comp_rightDerivedFunctor
    (globalSectionsOver S.X.hom) (derivedGlobalSectionsOver S.X.hom)
    (derivedGlobalSectionsOverUnit S.X.hom) Gb S.derivedPushforwardSystemOfModel d.ε p hp

end ExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
