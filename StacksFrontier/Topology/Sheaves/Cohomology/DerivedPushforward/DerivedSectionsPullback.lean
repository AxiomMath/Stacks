module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnitCoherence

/-!
# Derived sections along a morphism of ringed spaces

Let `h : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces.  Derived sections over an open
`V ⊆ X` of a derived direct image are derived sections over `h⁻¹V`, with scalars restricted along
`h^♯ : Γ(V, 𝒪_X) ⟶ Γ(h⁻¹V, 𝒪_Y)`:

`RΓ(V, Rh_* E) ≅ RΓ(h⁻¹V, E)` in `D(Γ(V, 𝒪_X))`.

This is the Leray isomorphism of Stacks 0D5W followed by the identification of the derived
functor of sections over `h⁻¹V` with scalars restricted with the derived sections over `h⁻¹V`
followed by restriction of scalars.  Composing with the unit of `Lh^* ⊣ Rh_*` gives the
canonical map

`RΓ(X, N) ⟶ RΓ(Y, Lh^*N)`

of `D(Γ(X, 𝒪_X))`, the map on global sections along which the canonical map of global hom
complexes of Cohomology, Section 0B6A is defined.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsPullback.preimageSectionsIso`: derived sections over `h⁻¹V`
  with scalars restricted along `h^♯` are the derived sections over `h⁻¹V` followed by restriction
  of scalars.
* `Stacks.Cohomology.DerivedSectionsPullback.pushforwardSectionsIso`:
  `Rh_* ⋙ RΓ(V, -) ≅ RΓ(h⁻¹V, -) ⋙ res`.
* `Stacks.Cohomology.DerivedSectionsPullback.derivedScalarSections`: derived global sections
  with scalars in a ring `A` mapping to `Γ(Z, 𝒪_Z)`.
* `Stacks.Cohomology.DerivedSectionsPullback.pushforwardScalarSectionsIso`:
  `Rh_* ⋙ RΓ_A(X, -) ≅ RΓ_A(Y, -)`, the scalars of `Y` acting through `h^♯`.
* `Stacks.Cohomology.DerivedSectionsPullback.sectionsPullback`: the canonical map
  `RΓ(X, N) ⟶ RΓ(Y, Lh^*N)`.
* `Stacks.Cohomology.DerivedSectionsPullback.relSectionsPullback`: the same map for morphisms
  over a fixed base, with scalars in a ring mapping to the global functions of the base.
* `Stacks.Cohomology.DerivedSectionsPullback.squareSectionsPullback`: for a commutative square
  `X' ⟶ X ⟶ S`, `X' ⟶ S' ⟶ S`, the map `RΓ(X, E) ⟶ RΓ(X', L(g')^*E)` read through the bottom of
  the square.
* `Stacks.Cohomology.DerivedSectionsPullback.changeScalarsIso`: derived global sections with
  scalars through `σ ∘ φ` are those with scalars through `σ` followed by restriction along `φ`.

## Main results

* `Stacks.Cohomology.DerivedSectionsPullback.unit_comp_derivedBaseChangeMap`: the unit of
  `Lg^* ⊣ Rg_*` followed by the derived base change map of Stacks 08HY is `Rf_*` of the unit of
  `L(g')^* ⊣ Rg'_*`, read through the composition isomorphisms.
* `Stacks.Cohomology.DerivedSectionsPullback.relSectionsPullback_square`: the map on derived
  global sections along the top of a square is the map along the bottom followed by the derived
  base change map.
* `Stacks.Cohomology.DerivedSectionsPullback.pushforwardScalarSectionsIso_changeScalars`:
  changing the ring of scalars commutes with the identification of derived sections of a
  pushforward.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0B6A](https://stacks.math.columbia.edu/tag/0B6A)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedSectionsPullback

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- Morphisms of ringed spaces, with the quiver structure read off the category structure: the
type of a composite `a ≫ b`.  Lemmas instantiated at composites bind their morphisms at this type,
so that the instantiation is syntactic. -/
local notation "CHom" A:max B:max => @Quiver.Hom RingedSpace (@CategoryStruct.toQuiver RingedSpace
  (@Category.toCategoryStruct RingedSpace
    (@SheafedSpace.instCategory CommRingCat CommRingCat.instCategory))) A B

/-! ### Derived sections over an open with scalars restricted -/

section Restrict

variable (Z : RingedSpace.{u, u}) (U : Opens Z.carrier) {A : Type u} [Ring A]
  (σ : A →+* (structureSheafRing Z).obj.obj (op U))

/-- Restriction of scalars along `σ : A ⟶ Γ(U, 𝒪_Z)`, on derived categories. -/
abbrev derivedRestrict :
    DerivedCategory (ModuleCat.{u} ((structureSheafRing Z).obj.obj (op U))) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory

/-- Termwise, sections over `U` with scalars restricted along `σ` are sections over `U` followed by
restriction of scalars, read on the homotopy category. -/
def homotopyRestrictIso :
    (sectionsOverOpen Z U ⋙ ModuleCat.restrictScalars.{u} σ).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      homotopySectionsOverOpen Z U ⋙ derivedRestrict Z U σ :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (sectionsOverOpen Z U ⋙ ModuleCat.restrictScalars.{u} σ))
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((sectionsOverOpen Z U).mapHomotopyCategory (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The comparison exhibiting derived sections over `U` followed by restriction of scalars as a
right derived functor of sections over `U` with scalars restricted. -/
def restrictComparison :
    (sectionsOverOpen Z U ⋙ ModuleCat.restrictScalars.{u} σ).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedSectionsOverOpen Z U ⋙ derivedRestrict Z U σ) :=
  (homotopyRestrictIso Z U σ).hom ≫
    Functor.whiskerRight (derivedSectionsOverOpenUnit Z U) (derivedRestrict Z U σ) ≫
    (Functor.associator _ _ _).hom

/-- The comparison `restrictComparison` is invertible at a complex as soon as the unit of
derived sections over `U` is. -/
theorem isIso_restrictComparison_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
    (hK : IsIso ((derivedSectionsOverOpenUnit Z U).app K)) :
    IsIso ((restrictComparison Z U σ).app K) := by
  dsimp only [restrictComparison, NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

/-- Derived sections over `U` followed by restriction of scalars along `σ` is a right derived
functor of sections over `U` with scalars restricted, via `restrictComparison`. -/
instance isRightDerivedFunctor_restrictComparison :
    (derivedSectionsOverOpen Z U ⋙ derivedRestrict Z U σ).IsRightDerivedFunctor
      (restrictComparison Z U σ)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ)) := by
  apply isRightDerivedFunctor_of_isIso_app_isKInjective _ (exists_quasiIso_isKInjective Z)
  intro I hI
  apply isIso_restrictComparison_app
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (homotopySectionsOverOpen Z U) (exists_quasiIso_isKInjective Z)).2
      DerivedCategory.Qh (derivedSectionsOverOpen Z U) (derivedSectionsOverOpenUnit Z U) I hI

end Restrict

/-- A K-injective complex computes any right derived functor of a termwise functor. -/
private theorem isIso_app_of_isKInjective {Z : RingedSpace.{u, u}} {H : Type (u + 1)}
    [Category.{u + 1} H]
    (F : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ) ⥤ H)
    (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)) ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ G)
    [G.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))]
    {I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ} (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1} F (exists_quasiIso_isKInjective Z)).2
    DerivedCategory.Qh G α I hI

/-! ### Derived sections of a pushforward are computed termwise at a K-injective complex -/

/-- **A K-injective complex is acyclic for derived sections after pushforward.**  For a morphism of
ringed spaces `h : Y ⟶ X`, an open `V ⊆ X` and a K-injective complex `I` of `𝒪_Y`-modules, the
comparison from termwise sections over `V` of `h_* I` to `RΓ(V, h_* I)` is an isomorphism.  This
is read off the Leray isomorphism of Stacks 0D5W. -/
theorem isIso_derivedSectionsOverOpenUnit_app_pushforward {X Y : RingedSpace.{u, u}} (h : Y ⟶ X)
    (V : Opens X.carrier)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedSectionsOverOpenUnit X V).app
      (((modulePushforward h).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have h₁ := isIso_app_of_isKInjective _ _ (derivedPreimageSectionsUnit h V) hI
  have h₂ := isIso_lerayComparison h V
  have h₃ : IsIso ((lerayUnit h V).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
    rw [← lerayComparison_fac]
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have h₄ := isIso_derivedPushforwardUnit_app_of_isKInjective h I hI
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    at h₃
  have h₅ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h₃
  exact IsIso.of_isIso_comp_right _
    ((derivedSectionsOverOpen X V).map ((derivedPushforwardUnit h).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))

/-! ### A general recognition lemma -/

section Recognition

variable {Z : RingedSpace.{u, u}} {H : Type (u + 1)} [Category.{u + 1} H]

/-- **A right derived functor computed by K-injective resolutions is computed at a complex as soon
as the termwise functor carries one K-injective resolution of it to an isomorphism.**  If
`s : K ⟶ J` is a quasi-isomorphism into a K-injective complex, the comparison of `RF` at `K` is
invertible exactly when `F(s)` is. -/
theorem isIso_app_iff_isIso_map
    (F : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ) ⥤ H)
    (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)) ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ G)
    [G.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))]
    {K J : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ} (s : K ⟶ J)
    [QuasiIso s] (hJ : J.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ↔
      IsIso (F.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) := by
  have hJ' := isIso_app_of_isKInjective F G α hJ
  have hs : IsIso (G.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) := by
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) :=
      Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
        _ ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2
          ((HomologicalComplex.mem_quasiIso_iff s).2 inferInstance))
    infer_instance
  have hnat := α.naturality ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : IsIso (F.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s) ≫
        α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J)) := by
      rw [hnat]
      dsimp only [Functor.comp_map]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J))
  · have : IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.Qh ⋙ G).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) := by
      rw [← hnat]
      infer_instance
    have : IsIso ((DerivedCategory.Qh ⋙ G).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) := hs
    exact IsIso.of_isIso_comp_right _
      ((DerivedCategory.Qh ⋙ G).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))

end Recognition

/-! ### Derived global sections with scalars in a ring mapping to global functions -/

section Scalar

variable (Z : RingedSpace.{u, u}) {A : Type u} [Ring A]
  (σ : A →+* (structureSheafRing Z).obj.obj (op ⊤))

/-- Global sections of a sheaf of `𝒪_Z`-modules, as an `A`-module by restriction of scalars along
a ring map `σ : A ⟶ Γ(Z, 𝒪_Z)`. -/
abbrev scalarSections : SheafOfModules.{u} (structureSheafRing Z) ⥤ ModuleCat.{u} A :=
  sectionsOverOpen Z ⊤ ⋙ ModuleCat.restrictScalars.{u} σ

/-- `scalarSections` read on the homotopy category, followed by the localization to `D(A)`. -/
abbrev homotopyScalarSections :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (scalarSections Z σ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **`A`-linear unbounded derived global sections** `RΓ(Z, -) : D(𝒪_Z) ⥤ D(A)`, the total right
derived functor of global sections with scalars restricted along `σ : A ⟶ Γ(Z, 𝒪_Z)`. -/
def derivedScalarSections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (homotopyScalarSections Z σ).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))

/-- The comparison exhibiting `derivedScalarSections` as a right derived functor. -/
def derivedScalarSectionsUnit :
    homotopyScalarSections Z σ ⟶ DerivedCategory.Qh ⋙ derivedScalarSections Z σ :=
  (homotopyScalarSections Z σ).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))

/-- `derivedScalarSections` is a right derived functor via `derivedScalarSectionsUnit`. -/
instance isRightDerivedFunctor_derivedScalarSectionsUnit :
    (derivedScalarSections Z σ).IsRightDerivedFunctor (derivedScalarSectionsUnit Z σ)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ)) := by
  dsimp only [derivedScalarSections, derivedScalarSectionsUnit]
  infer_instance

/-- A K-injective complex computes `A`-linear derived global sections. -/
theorem isIso_derivedScalarSectionsUnit_app
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedScalarSectionsUnit Z σ).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  isIso_app_of_isKInjective _ _ (derivedScalarSectionsUnit Z σ) hI

/-- `A`-linear derived global sections are derived global sections followed by restriction of
scalars along `σ`. -/
def derivedScalarSectionsIso :
    derivedScalarSections Z σ ≅ derivedSectionsOverOpen Z ⊤ ⋙ derivedRestrict Z ⊤ σ :=
  Functor.rightDerivedUnique (derivedScalarSections Z σ)
    (derivedSectionsOverOpen Z ⊤ ⋙ derivedRestrict Z ⊤ σ) (derivedScalarSectionsUnit Z σ)
    (restrictComparison Z ⊤ σ)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))

/-- The unit of `derivedScalarSections` followed by `derivedScalarSectionsIso` is
`restrictComparison`. -/
theorem derivedScalarSectionsUnit_comp_iso_hom :
    derivedScalarSectionsUnit Z σ ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedScalarSectionsIso Z σ).hom =
      restrictComparison Z ⊤ σ := by
  simp [derivedScalarSectionsIso]

/-- **A K-injective complex is acyclic for `A`-linear derived global sections after
pushforward.** -/
theorem isIso_derivedScalarSectionsUnit_app_pushforward {Y : RingedSpace.{u, u}} (h : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedScalarSectionsUnit Z σ).app
      (((modulePushforward h).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have h₁ := isIso_restrictComparison_app Z ⊤ σ _
    (isIso_derivedSectionsOverOpenUnit_app_pushforward h ⊤ I hI)
  have h₂ := congrArg (fun τ => τ.app
      (((modulePushforward h).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))
    (derivedScalarSectionsUnit_comp_iso_hom Z σ)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂
  rw [← h₂] at h₁
  exact IsIso.of_isIso_comp_right _ ((derivedScalarSectionsIso Z σ).hom.app _)

end Scalar

/-! ### Derived global sections of a derived pushforward, and the map along a morphism -/

section Pushforward

variable {X Y : RingedSpace.{u, u}} (h : Y ⟶ X) {A : Type u} [Ring A]
  (σ : A →+* (structureSheafRing X).obj.obj (op ⊤))

/-- The ring map `h^♯ : Γ(X, 𝒪_X) ⟶ Γ(Y, 𝒪_Y)`. -/
abbrev globalRingHom :
    (structureSheafRing X).obj.obj (op ⊤) →+* (structureSheafRing Y).obj.obj (op ⊤) :=
  ((structureSheafHom h).hom.app (op ⊤)).hom

/-- Termwise, `Γ(X, h_* -) = Γ(Y, -)` as `A`-modules: the two functors are equal. -/
def pushforwardSectionsTermIso :
    modulePushforward h ⋙ scalarSections X σ ≅ scalarSections Y ((globalRingHom h).comp σ) :=
  Iso.refl _

/-- The comparison from termwise `A`-linear global sections on `Y`, with `A` acting through
`h^♯ ∘ σ`, to `RΓ(X, Rh_* -)`: the identification `Γ(X, h_* -) = Γ(Y, -)`, the unit of
`RΓ(X, -)` at a pushforward, and the unit of `Rh_*`. -/
def pushforwardScalarUnit :
    homotopyScalarSections Y ((globalRingHom h).comp σ) ⟶
      DerivedCategory.Qh ⋙ (derivedPushforward h ⋙ derivedScalarSections X σ) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (pushforwardSectionsTermIso h σ) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft ((modulePushforward h).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedScalarSectionsUnit X σ) ≫
    Functor.whiskerRight (derivedPushforwardUnit h) (derivedScalarSections X σ)

/-- The component of `pushforwardScalarUnit` at a complex `K`. -/
theorem pushforwardScalarUnit_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (pushforwardScalarUnit h σ).app K =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (pushforwardSectionsTermIso h σ) (ComplexShape.up ℤ)).inv.app K) ≫
      (derivedScalarSectionsUnit X σ).app
        (((modulePushforward h).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (derivedScalarSections X σ).map ((derivedPushforwardUnit h).app K) :=
  rfl

/-- `Rh_* ⋙ RΓ_A(X, -)` is a right derived functor of `A`-linear global sections on `Y` via
`pushforwardScalarUnit`. -/
instance isRightDerivedFunctor_pushforwardScalarUnit :
    (derivedPushforward h ⋙ derivedScalarSections X σ).IsRightDerivedFunctor
      (pushforwardScalarUnit h σ)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)) := by
  apply isRightDerivedFunctor_of_isIso_app_isKInjective _ (exists_quasiIso_isKInjective Y)
  intro I hI
  have h₁ := isIso_derivedScalarSectionsUnit_app_pushforward X σ h I hI
  have h₂ : IsIso ((derivedScalarSections X σ).map ((derivedPushforwardUnit h).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
    have := isIso_derivedPushforwardUnit_app_of_isKInjective h I hI
    infer_instance
  have h₃ : IsIso (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (pushforwardSectionsTermIso h σ) (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := inferInstance
  rw [pushforwardScalarUnit_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₃ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂)

/-- **Derived global sections of a derived pushforward** (Stacks 0D5W):
`RΓ(X, Rh_* E) ≅ RΓ(Y, E)` in `D(A)`, where `A` acts on the right hand side through
`h^♯ ∘ σ`. -/
def pushforwardScalarSectionsIso :
    derivedPushforward h ⋙ derivedScalarSections X σ ≅
      derivedScalarSections Y ((globalRingHom h).comp σ) :=
  Functor.rightDerivedUnique (derivedPushforward h ⋙ derivedScalarSections X σ)
    (derivedScalarSections Y ((globalRingHom h).comp σ)) (pushforwardScalarUnit h σ)
    (derivedScalarSectionsUnit Y ((globalRingHom h).comp σ))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))

/-- `pushforwardScalarUnit` followed by `pushforwardScalarSectionsIso` is the unit of
`derivedScalarSections` on `Y`. -/
@[reassoc]
theorem pushforwardScalarUnit_comp_iso_hom_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (pushforwardScalarUnit h σ).app K ≫
        (pushforwardScalarSectionsIso h σ).hom.app (DerivedCategory.Qh.obj K) =
      (derivedScalarSectionsUnit Y ((globalRingHom h).comp σ)).app K := by
  simp [pushforwardScalarSectionsIso]

/-- The unit of `derivedScalarSections` on `Y` followed by the inverse of
`pushforwardScalarSectionsIso` is `pushforwardScalarUnit`. -/
@[reassoc]
theorem derivedScalarSectionsUnit_comp_iso_inv_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (derivedScalarSectionsUnit Y ((globalRingHom h).comp σ)).app K ≫
        (pushforwardScalarSectionsIso h σ).inv.app (DerivedCategory.Qh.obj K) =
      (pushforwardScalarUnit h σ).app K := by
  rw [← pushforwardScalarUnit_comp_iso_hom_app, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- **The canonical map `RΓ(X, N) ⟶ RΓ(Y, Lh^*N)`** of `D(A)`: `RΓ(X, -)` of the unit
`N ⟶ Rh_* Lh^* N` of the derived adjunction of Stacks 079W, followed by the identification
`RΓ(X, Rh_* -) = RΓ(Y, -)`.  This is the map along which the canonical map of global hom complexes
of Cohomology, Section 0B6A, is defined. -/
def sectionsPullback (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedScalarSections X σ).obj N ⟶
      (derivedScalarSections Y ((globalRingHom h).comp σ)).obj ((derivedPullback h).obj N) :=
  (derivedScalarSections X σ).map ((derivedAdjunction h).unit.app N) ≫
    (pushforwardScalarSectionsIso h σ).hom.app ((derivedPullback h).obj N)

end Pushforward

/-! ### An abstract composition lemma for comparisons of right derived functors -/

section Abstract

variable {KW KY KX DW DY DX H : Type*} [Category KW] [Category KY] [Category KX] [Category DW]
  [Category DY] [Category DX] [Category H]

/-- **Composition of identifications of derived global sections of pushforwards, abstractly.**
Three right-derived-functor comparisons `lh`, `lk`, `lkh` — each characterized by its value on the
units — and the composition isomorphism `e` of the pushforwards, itself characterized on the
units, satisfy the composition law as soon as the termwise identifications do. -/
theorem comp_of_units (Qw : KW ⥤ DW) (Qy : KY ⥤ DY) (Qx : KX ⥤ DX)
    (Pk : KW ⥤ KY) (Ph : KY ⥤ KX) (Pkh : KW ⥤ KX)
    (Rk : DW ⥤ DY) (Rh : DY ⥤ DX) (Rkh : DW ⥤ DX)
    (FX : KX ⥤ H) (FY : KY ⥤ H) (FW : KW ⥤ H) (GX : DX ⥤ H) (GY : DY ⥤ H) (GW : DW ⥤ H)
    (uX : FX ⟶ Qx ⋙ GX) (uY : FY ⟶ Qy ⋙ GY) (uW : FW ⟶ Qw ⋙ GW)
    (ηk : Pk ⋙ Qy ⟶ Qw ⋙ Rk) (ηh : Ph ⋙ Qx ⟶ Qy ⋙ Rh) (ηkh : Pkh ⋙ Qx ⟶ Qw ⋙ Rkh)
    (c₁ : FW ⟶ Pk ⋙ FY) (c₂ : FY ⟶ Ph ⋙ FX) (c₃ : FW ⟶ Pkh ⋙ FX) (m : Pkh ⟶ Pk ⋙ Ph)
    (e : Rk ⋙ Rh ≅ Rkh) (lh : Rh ⋙ GX ≅ GY) (lk : Rk ⋙ GY ≅ GW) (lkh : Rkh ⋙ GX ≅ GW)
    (W : MorphismProperty KW) [Qw.IsLocalization W] [GW.IsRightDerivedFunctor uW W]
    (hlh : ∀ K, c₂.app K ≫ uX.app (Ph.obj K) ≫ GX.map (ηh.app K) =
      uY.app K ≫ lh.inv.app (Qy.obj K))
    (hlk : ∀ K, c₁.app K ≫ uY.app (Pk.obj K) ≫ GY.map (ηk.app K) =
      uW.app K ≫ lk.inv.app (Qw.obj K))
    (hlkh : ∀ K, c₃.app K ≫ uX.app (Pkh.obj K) ≫ GX.map (ηkh.app K) =
      uW.app K ≫ lkh.inv.app (Qw.obj K))
    (he : ∀ K, ηkh.app K ≫ e.inv.app (Qw.obj K) =
      Qx.map (m.app K) ≫ ηh.app (Pk.obj K) ≫ Rh.map (ηk.app K))
    (hc : ∀ K, c₁.app K ≫ c₂.app (Pk.obj K) = c₃.app K ≫ FX.map (m.app K)) (E : DW) :
    lh.hom.app (Rk.obj E) ≫ lk.hom.app E = GX.map (e.hom.app E) ≫ lkh.hom.app E := by
  have key : lk.inv ≫ Functor.whiskerLeft Rk lh.inv =
      lkh.inv ≫ Functor.whiskerRight e.inv GX := by
    refine Functor.rightDerived_ext GW uW W _ _ _ ?_
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj]
    rw [← reassoc_of% (hlk K), ← reassoc_of% (hlkh K), lh.inv.naturality,
      Functor.comp_map, ← reassoc_of% (hlh (Pk.obj K)),
      ← GX.map_comp (ηkh.app K), he, Functor.map_comp, Functor.map_comp]
    have hn : uX.app (Pkh.obj K) ≫ GX.map (Qx.map (m.app K)) =
        FX.map (m.app K) ≫ uX.app (Ph.obj (Pk.obj K)) := (uX.naturality (m.app K)).symm
    rw [reassoc_of% hn, reassoc_of% (hc K)]
  have := congrArg (fun τ => τ.app E) key
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at this
  rw [← IsIso.inv_eq_inv]
  simpa [← Functor.map_inv] using this

end Abstract

/-! ### Along a morphism to a fixed base

Fix a ringed space `X` and a ring map `σ : A ⟶ Γ(X, 𝒪_X)`.  For a morphism `p : Y ⟶ X` the
derived global sections on `Y` are `A`-linear through `p^♯ ∘ σ`; for `k : W ⟶ Y` the identification
of derived global sections of a derived pushforward along `k` then lands in the `A`-linear derived
global sections attached to `k ≫ p`. -/

section Relative

variable {X Y W : RingedSpace.{u, u}} {A : Type u} [Ring A]
  (σ : A →+* (structureSheafRing X).obj.obj (op ⊤))

/-- Termwise, `Γ(Y, k_* -) = Γ(W, -)` as `A`-modules, the scalars acting through `p^♯ ∘ σ` and
`(k ≫ p)^♯ ∘ σ`: the two functors are equal. -/
def relSectionsTermIso (k : W ⟶ Y) (p : Y ⟶ X) :
    modulePushforward k ⋙ scalarSections Y ((globalRingHom p).comp σ) ≅
      scalarSections W ((globalRingHom (k ≫ p)).comp σ) :=
  Iso.refl _

/-- The comparison exhibiting `RΓ(Y, Rk_* -)` as a right derived functor of `A`-linear global
sections on `W`, where `A` acts through `(k ≫ p)^♯ ∘ σ`. -/
def relPushforwardUnit (k : W ⟶ Y) (p : Y ⟶ X) :
    homotopyScalarSections W ((globalRingHom (k ≫ p)).comp σ) ⟶
      DerivedCategory.Qh ⋙
        (derivedPushforward k ⋙ derivedScalarSections Y ((globalRingHom p).comp σ)) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (relSectionsTermIso σ k p) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((modulePushforward k).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedScalarSectionsUnit Y ((globalRingHom p).comp σ)) ≫
    Functor.whiskerRight (derivedPushforwardUnit k)
      (derivedScalarSections Y ((globalRingHom p).comp σ))

/-- The component of `relPushforwardUnit` at a complex `K`. -/
theorem relPushforwardUnit_app (k : W ⟶ Y) (p : Y ⟶ X)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ)) :
    (relPushforwardUnit σ k p).app K =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (relSectionsTermIso σ k p) (ComplexShape.up ℤ)).inv.app K) ≫
      (derivedScalarSectionsUnit Y ((globalRingHom p).comp σ)).app
        (((modulePushforward k).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (derivedScalarSections Y ((globalRingHom p).comp σ)).map
        ((derivedPushforwardUnit k).app K) :=
  rfl

/-- `Rk_* ⋙ RΓ_A(Y, -)` is a right derived functor of `A`-linear global sections on `W` via
`relPushforwardUnit`. -/
instance isRightDerivedFunctor_relPushforwardUnit (k : W ⟶ Y) (p : Y ⟶ X) :
    (derivedPushforward k ⋙
      derivedScalarSections Y ((globalRingHom p).comp σ)).IsRightDerivedFunctor
      (relPushforwardUnit σ k p)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing W))
        (ComplexShape.up ℤ)) := by
  apply isRightDerivedFunctor_of_isIso_app_isKInjective _ (exists_quasiIso_isKInjective W)
  intro I hI
  have h₁ := isIso_derivedScalarSectionsUnit_app_pushforward Y ((globalRingHom p).comp σ) k I hI
  have h₂ : IsIso ((derivedScalarSections Y ((globalRingHom p).comp σ)).map
      ((derivedPushforwardUnit k).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
    have := isIso_derivedPushforwardUnit_app_of_isKInjective k I hI
    infer_instance
  have h₃ : IsIso (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (relSectionsTermIso σ k p) (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := inferInstance
  rw [relPushforwardUnit_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₃ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂)

/-- **Derived global sections of a derived pushforward, along a morphism to the base**:
`RΓ(Y, Rk_* E) ≅ RΓ(W, E)` in `D(A)`, the scalars acting through `p^♯ ∘ σ` and
`(k ≫ p)^♯ ∘ σ`. -/
def relPushforwardIso (k : W ⟶ Y) (p : Y ⟶ X) :
    derivedPushforward k ⋙ derivedScalarSections Y ((globalRingHom p).comp σ) ≅
      derivedScalarSections W ((globalRingHom (k ≫ p)).comp σ) :=
  Functor.rightDerivedUnique
    (derivedPushforward k ⋙ derivedScalarSections Y ((globalRingHom p).comp σ))
    (derivedScalarSections W ((globalRingHom (k ≫ p)).comp σ)) (relPushforwardUnit σ k p)
    (derivedScalarSectionsUnit W ((globalRingHom (k ≫ p)).comp σ))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ))

/-- `relPushforwardUnit` followed by `relPushforwardIso` is the unit of `derivedScalarSections`
on `W`. -/
@[reassoc]
theorem relPushforwardUnit_comp_iso_hom_app (k : W ⟶ Y) (p : Y ⟶ X)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ)) :
    (relPushforwardUnit σ k p).app K ≫
        (relPushforwardIso σ k p).hom.app (DerivedCategory.Qh.obj K) =
      (derivedScalarSectionsUnit W ((globalRingHom (k ≫ p)).comp σ)).app K := by
  simp [relPushforwardIso]

/-- The unit of `derivedScalarSections` on `W` followed by the inverse of `relPushforwardIso` is
`relPushforwardUnit`. -/
@[reassoc]
theorem derivedScalarSectionsUnit_comp_relPushforwardIso_inv_app (k : W ⟶ Y) (p : Y ⟶ X)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ)) :
    (derivedScalarSectionsUnit W ((globalRingHom (k ≫ p)).comp σ)).app K ≫
        (relPushforwardIso σ k p).inv.app (DerivedCategory.Qh.obj K) =
      (relPushforwardUnit σ k p).app K := by
  rw [← relPushforwardUnit_comp_iso_hom_app, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- **The canonical map `RΓ(Y, N) ⟶ RΓ(W, Lk^*N)` along a morphism to the base**, in `D(A)`:
`RΓ(Y, -)` of the unit `N ⟶ Rk_* Lk^* N` of the derived adjunction of Stacks 079W, followed by
the identification `RΓ(Y, Rk_* -) = RΓ(W, -)`. -/
def relSectionsPullback (k : W ⟶ Y) (p : Y ⟶ X)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedScalarSections Y ((globalRingHom p).comp σ)).obj N ⟶
      (derivedScalarSections W ((globalRingHom (k ≫ p)).comp σ)).obj ((derivedPullback k).obj N) :=
  (derivedScalarSections Y ((globalRingHom p).comp σ)).map ((derivedAdjunction k).unit.app N) ≫
    (relPushforwardIso σ k p).hom.app ((derivedPullback k).obj N)

/-- Termwise, the identifications `Γ(W, -) = Γ(Y, k_* -)` and `Γ(Y, -) = Γ(X, h_* -)` compose to
`Γ(W, -) = Γ(X, (k ≫ h)_* -)`. -/
theorem termwise_comp (k : W ⟶ Y) (h : Y ⟶ X)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso (relSectionsTermIso σ k h)
        (ComplexShape.up ℤ)).inv.app K) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (pushforwardSectionsTermIso h σ) (ComplexShape.up ℤ)).inv.app
          (((modulePushforward k).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) =
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (pushforwardSectionsTermIso (k ≫ h) σ) (ComplexShape.up ℤ)).inv.app K) ≫
      DerivedCategory.Qh.map (((scalarSections X σ).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (modulePushforwardComp k h)
          (ComplexShape.up ℤ)).inv.app K)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- **The identification of derived global sections of a derived pushforward is compatible with
composition**: for `k : W ⟶ Y` and `h : Y ⟶ X`, identifying `RΓ(X, Rh_* Rk_* E)` with `RΓ(W, E)`
in two steps agrees with doing it in one step along `k ≫ h`, after the composition isomorphism
`Rk_* ⋙ Rh_* ≅ R(k ≫ h)_*` of Stacks 079W. -/
theorem pushforwardScalarSectionsIso_hom_comp (k : W ⟶ Y) (h : Y ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    (pushforwardScalarSectionsIso h σ).hom.app ((derivedPushforward k).obj E) ≫
        (relPushforwardIso σ k h).hom.app E =
      (derivedScalarSections X σ).map ((derivedPushforwardCompIso k h).hom.app E) ≫
        (pushforwardScalarSectionsIso (k ≫ h) σ).hom.app E :=
  comp_of_units DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh
    ((modulePushforward k).mapHomotopyCategory (ComplexShape.up ℤ))
    ((modulePushforward h).mapHomotopyCategory (ComplexShape.up ℤ))
    ((modulePushforward (k ≫ h)).mapHomotopyCategory (ComplexShape.up ℤ))
    (derivedPushforward k) (derivedPushforward h) (derivedPushforward (k ≫ h))
    (homotopyScalarSections X σ) (homotopyScalarSections Y ((globalRingHom h).comp σ))
    (homotopyScalarSections W ((globalRingHom (k ≫ h)).comp σ))
    (derivedScalarSections X σ) (derivedScalarSections Y ((globalRingHom h).comp σ))
    (derivedScalarSections W ((globalRingHom (k ≫ h)).comp σ))
    (derivedScalarSectionsUnit X σ) (derivedScalarSectionsUnit Y ((globalRingHom h).comp σ))
    (derivedScalarSectionsUnit W ((globalRingHom (k ≫ h)).comp σ))
    (derivedPushforwardUnit k) (derivedPushforwardUnit h) (derivedPushforwardUnit (k ≫ h))
    (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (relSectionsTermIso σ k h)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
    (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsTermIso h σ)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
    (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (pushforwardSectionsTermIso (k ≫ h) σ) (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
    (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp k h) (ComplexShape.up ℤ)).inv
    (derivedPushforwardCompIso k h) (pushforwardScalarSectionsIso h σ) (relPushforwardIso σ k h)
    (pushforwardScalarSectionsIso (k ≫ h) σ)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing W)) (ComplexShape.up ℤ))
    (fun K => (pushforwardScalarUnit_app h σ K).symm.trans
      (derivedScalarSectionsUnit_comp_iso_inv_app h σ K).symm)
    (fun K => (relPushforwardUnit_app σ k h K).symm.trans
      (derivedScalarSectionsUnit_comp_relPushforwardIso_inv_app σ k h K).symm)
    (fun K => (pushforwardScalarUnit_app (k ≫ h) σ K).symm.trans
      (derivedScalarSectionsUnit_comp_iso_inv_app (k ≫ h) σ K).symm)
    (fun K => by
      rw [← DerivedPushforwardComposition.derivedPushforwardCompUnit_comp_derivedPushforwardCompIso
        k h K]
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).trans
        (Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit_app k h
          (derivedPushforward k) (derivedPushforward h) (derivedPushforwardUnit k)
          (derivedPushforwardUnit h) K))
    (fun K => termwise_comp σ k h K) E

end Relative

/-! ### The unit and the base change map -/

section AbstractBaseChange

variable {DS DS' DX DX' : Type*} [Category DS] [Category DS'] [Category DX] [Category DX']

/-- **The unit and a base change map, abstractly.**  For a commutative square of adjunctions
`Lf ⊣ Rf`, `Lg ⊣ Rg`, `Lf' ⊣ Rf'`, `Lg' ⊣ Rg'`, with adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` along the
two composites and composition isomorphisms compatible with transposition, the unit of `Lg ⊣ Rg`
followed by `Rg` of the base change map is `Rf` of the unit of `Lg' ⊣ Rg'` followed by the
identification `Rf ∘ Rg' ≅ R₁ ≅ R₂ ≅ Rg ∘ Rf'`. -/
theorem unit_comp_baseChange_of_adjunctions {Lf : DS ⥤ DX} {Rf : DX ⥤ DS} (af : Lf ⊣ Rf)
    {Lg : DS ⥤ DS'} {Rg : DS' ⥤ DS} (ag : Lg ⊣ Rg) {Lf' : DS' ⥤ DX'} {Rf' : DX' ⥤ DS'}
    (af' : Lf' ⊣ Rf') {Lg' : DX ⥤ DX'} {Rg' : DX' ⥤ DX} (ag' : Lg' ⊣ Rg')
    {L₁ : DS ⥤ DX'} {R₁ : DX' ⥤ DS} (a₁ : L₁ ⊣ R₁) {L₂ : DS ⥤ DX'} {R₂ : DX' ⥤ DS} (a₂ : L₂ ⊣ R₂)
    (c₁ : Lf ⋙ Lg' ≅ L₁) (c₂ : Lg ⋙ Lf' ≅ L₂) (d₁ : Rg' ⋙ Rf ≅ R₁) (d₂ : Rf' ⋙ Rg ≅ R₂)
    (τ : L₂ ≅ L₁) (ρ : R₁ ≅ R₂)
    (hd₁ : ∀ M N (φ : L₁.obj M ⟶ N),
      af.homEquiv _ _ (ag'.homEquiv _ _ (c₁.hom.app M ≫ φ)) ≫ d₁.hom.app N = a₁.homEquiv M N φ)
    (hd₂ : ∀ M N (φ : L₂.obj M ⟶ N),
      ag.homEquiv _ _ (af'.homEquiv _ _ (c₂.hom.app M ≫ φ)) ≫ d₂.hom.app N = a₂.homEquiv M N φ)
    (ht : ∀ M N (φ : L₁.obj M ⟶ N),
      a₂.homEquiv M N (τ.hom.app M ≫ φ) = a₁.homEquiv M N φ ≫ ρ.hom.app N)
    (eg : Lg ⋙ Lf' ≅ L₁) (heg : ∀ M, eg.hom.app M = c₂.hom.app M ≫ τ.hom.app M)
    (E : DX) (bc : Lf'.obj (Lg.obj (Rf.obj E)) ⟶ Lg'.obj E)
    (hbc : bc = eg.hom.app (Rf.obj E) ≫ c₁.inv.app (Rf.obj E) ≫ Lg'.map (af.counit.app E)) :
    ag.unit.app (Rf.obj E) ≫ Rg.map (af'.homEquiv _ _ bc) =
      Rf.map (ag'.unit.app E) ≫ d₁.hom.app (Lg'.obj E) ≫ ρ.hom.app (Lg'.obj E) ≫
        d₂.inv.app (Lg'.obj E) := by
  have h0 : ag.unit.app (Rf.obj E) ≫ Rg.map (af'.homEquiv _ _ bc) =
      ag.homEquiv _ _ (af'.homEquiv _ _ bc) := rfl
  rw [h0, ← cancel_mono (d₂.hom.app (Lg'.obj E))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hbc, heg, Category.assoc, hd₂, ht, ← hd₁, Iso.hom_inv_id_app_assoc]
  have hn : ag'.unit.app (Lf.obj (Rf.obj E)) ≫ Rg'.map (Lg'.map (af.counit.app E)) =
      af.counit.app E ≫ ag'.unit.app E := (ag'.unit.naturality (af.counit.app E)).symm
  have hv : af.homEquiv (Rf.obj E) (Rg'.obj (Lg'.obj E)) (af.counit.app E ≫ ag'.unit.app E) =
      Rf.map (ag'.unit.app E) := by
    rw [Adjunction.homEquiv_naturality_right]
    show (af.unit.app (Rf.obj E) ≫ Rf.map (af.counit.app E)) ≫ _ = _
    simp
  rw [show ag'.homEquiv (Lf.obj (Rf.obj E)) (Lg'.obj E) (Lg'.map (af.counit.app E)) =
      ag'.unit.app (Lf.obj (Rf.obj E)) ≫ Rg'.map (Lg'.map (af.counit.app E)) from rfl, hn, hv]
  simp

end AbstractBaseChange

section BaseChange

/-- Transposition along equal morphisms. -/
theorem derivedAdjunction_homEquiv_eqToHom {X' S : RingedSpace.{u, u}} {p q : CHom X' S}
    (e : p = q) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (φ : (derivedPullback p).obj M ⟶ N) :
    (derivedAdjunction q).homEquiv M N
        ((eqToIso (congrArg (fun r : X' ⟶ S => derivedPullback r) e.symm)).hom.app M ≫ φ) =
      (derivedAdjunction p).homEquiv M N φ ≫
        (eqToIso (congrArg (fun r : X' ⟶ S => derivedPushforward r) e)).hom.app N := by
  subst e
  simp

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (sq : g' ≫ f = f' ≫ g)

/-- **The unit of `Lg^* ⊣ Rg_*` followed by `Rg_*` of the base change map** of Stacks 08HY is the
direct image along `f` of the unit of `L(g')^* ⊣ Rg'_*`, followed by the identification
`Rf_* Rg'_* ≅ R(g' ≫ f)_* = R(f' ≫ g)_* ≅ Rg_* Rf'_*` of Stacks 079W. -/
theorem unit_comp_derivedBaseChangeMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedAdjunction g).unit.app ((derivedPushforward f).obj E) ≫
        (derivedPushforward g).map
          (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq E) =
      (derivedPushforward f).map ((derivedAdjunction g').unit.app E) ≫
        (derivedPushforwardCompIso g' f).hom.app ((derivedPullback g').obj E) ≫
        (eqToIso (congrArg (fun r : X' ⟶ S => derivedPushforward r) sq)).hom.app
          ((derivedPullback g').obj E) ≫
        (derivedPushforwardCompIso f' g).inv.app ((derivedPullback g').obj E) := by
  rw [Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq]
  exact unit_comp_baseChange_of_adjunctions (derivedAdjunction f) (derivedAdjunction g)
    (derivedAdjunction f') (derivedAdjunction g') (derivedAdjunction (g' ≫ f))
    (derivedAdjunction (f' ≫ g))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f' g)
    (derivedPushforwardCompIso g' f) (derivedPushforwardCompIso f' g)
    (eqToIso (congrArg (fun r : X' ⟶ S => derivedPullback r) sq.symm))
    (eqToIso (congrArg (fun r : X' ⟶ S => derivedPushforward r) sq))
    (derivedAdjunction_comp_homEquiv g' f) (derivedAdjunction_comp_homEquiv f' g)
    (derivedAdjunction_homEquiv_eqToHom sq)
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq)
    (StacksDraft.UnitPullbackComposition.derivedPullbackCompIsoLeft_hom_app g f f' g' sq)
    E _ rfl

end BaseChange

/-! ### The map on derived global sections and the base change map, abstractly -/

section AbstractSquare

variable {DS DX DS' DX' H : Type*} [Category DS] [Category DX] [Category DS'] [Category DX']
  [Category H]

/-- **The canonical map on derived global sections along the top of a square is the one along
the bottom followed by the base change map, abstractly.**  Here `ΓS ∘ Rf ≅ ΓX` and the other
identifications are those of derived global sections of pushforwards, the compatibilities `hLC₁`,
`hLC₂` say that they compose with the composition isomorphisms of the pushforwards, `hT` that
they are compatible with the identification of the two composites, and `hBC` is the identity
`unit_comp_derivedBaseChangeMap`. -/
theorem sectionsPullback_square_of_facts {Rf : DX ⥤ DS} {Rg' : DX' ⥤ DX} {Rg : DS' ⥤ DS}
    {Rf' : DX' ⥤ DS'} {R₁ R₂ : DX' ⥤ DS} {Lg' : DX ⥤ DX'} {Lg : DS ⥤ DS'}
    (ηg' : 𝟭 DX ⟶ Lg' ⋙ Rg') (ηg : 𝟭 DS ⟶ Lg ⋙ Rg)
    {ΓS : DS ⥤ H} {ΓX : DX ⥤ H} {ΓS' : DS' ⥤ H} {Γ₁ Γ₂ : DX' ⥤ H}
    (ℓf : Rf ⋙ ΓS ≅ ΓX) (ℓg' : Rg' ⋙ ΓX ≅ Γ₁) (ℓg : Rg ⋙ ΓS ≅ ΓS') (ℓf' : Rf' ⋙ ΓS' ≅ Γ₂)
    (μ₁ : R₁ ⋙ ΓS ≅ Γ₁) (μ₂ : R₂ ⋙ ΓS ≅ Γ₂) (d₁ : Rg' ⋙ Rf ≅ R₁) (d₂ : Rf' ⋙ Rg ≅ R₂)
    (ρ : R₁ ≅ R₂) (κ : Γ₁ ≅ Γ₂)
    (hLC₁ : ∀ F, ℓf.hom.app (Rg'.obj F) ≫ ℓg'.hom.app F = ΓS.map (d₁.hom.app F) ≫ μ₁.hom.app F)
    (hLC₂ : ∀ F, ℓg.hom.app (Rf'.obj F) ≫ ℓf'.hom.app F = ΓS.map (d₂.hom.app F) ≫ μ₂.hom.app F)
    (hT : ∀ F, ΓS.map (ρ.hom.app F) ≫ μ₂.hom.app F = μ₁.hom.app F ≫ κ.hom.app F)
    (E : DX) (bc : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E))
    (hBC : ηg.app (Rf.obj E) ≫ Rg.map bc =
      Rf.map (ηg'.app E) ≫ d₁.hom.app (Lg'.obj E) ≫ ρ.hom.app (Lg'.obj E) ≫
        d₂.inv.app (Lg'.obj E)) :
    ℓf.hom.app E ≫ ΓX.map (ηg'.app E) ≫ ℓg'.hom.app (Lg'.obj E) ≫ κ.hom.app (Lg'.obj E) =
      ΓS.map (ηg.app (Rf.obj E)) ≫ ℓg.hom.app (Lg.obj (Rf.obj E)) ≫ ΓS'.map bc ≫
        ℓf'.hom.app (Lg'.obj E) := by
  have n₁ : ℓf.hom.app E ≫ ΓX.map (ηg'.app E) =
      ΓS.map (Rf.map (ηg'.app E)) ≫ ℓf.hom.app ((Lg' ⋙ Rg').obj E) :=
    (ℓf.hom.naturality (ηg'.app E)).symm
  have n₂ : ℓg.hom.app (Lg.obj (Rf.obj E)) ≫ ΓS'.map bc =
      ΓS.map (Rg.map bc) ≫ ℓg.hom.app (Rf'.obj (Lg'.obj E)) :=
    (ℓg.hom.naturality bc).symm
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% (hLC₁ (Lg'.obj E)), ← hT, hLC₂,
    ← ΓS.map_comp_assoc, ← ΓS.map_comp_assoc, ← ΓS.map_comp_assoc, ← ΓS.map_comp_assoc, hBC]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end AbstractSquare

/-! ### The square, for ringed spaces -/

section Square

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (sq : g' ≫ f = f' ≫ g) {A : Type u} [Ring A] (σ : A →+* (structureSheafRing S).obj.obj (op ⊤))

/-- Identifying derived global sections of a pushforward along equal morphisms. -/
theorem pushforwardScalarSectionsIso_eqToHom {p q : CHom X' S} (e : p = q)
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) :
    (derivedScalarSections S σ).map
        ((eqToIso (congrArg (fun r : X' ⟶ S => derivedPushforward r) e)).hom.app F) ≫
      (pushforwardScalarSectionsIso q σ).hom.app F =
    (pushforwardScalarSectionsIso p σ).hom.app F ≫
      (eqToIso (congrArg (fun r : X' ⟶ S => derivedScalarSections X' ((globalRingHom r).comp σ))
        e)).hom.app F := by
  subst e
  simp

/-- **The canonical map on derived global sections along the top of a commutative square**,
`RΓ(X, E) ⟶ RΓ(X', L(g')^*E)` in `D(A)`, the scalars on `X'` acting through `(f' ≫ g)^♯ ∘ σ`. -/
def squareSectionsPullback (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedScalarSections X ((globalRingHom f).comp σ)).obj E ⟶
      (derivedScalarSections X' ((globalRingHom (f' ≫ g)).comp σ)).obj
        ((derivedPullback g').obj E) :=
  relSectionsPullback σ g' f E ≫
    (eqToIso (congrArg (fun r : X' ⟶ S => derivedScalarSections X' ((globalRingHom r).comp σ))
      sq)).hom.app ((derivedPullback g').obj E)

/-- **The canonical map on derived global sections along the top of a commutative square is the
one along the bottom followed by the base change map** of Stacks 08HY:
`RΓ(X, E) ⟶ RΓ(X', L(g')^*E)` is `RΓ(S, Rf_* E) ⟶ RΓ(S', Lg^*Rf_* E) ⟶ RΓ(S', Rf'_* L(g')^*E)`
read through the identifications of derived global sections of pushforwards. -/
theorem relSectionsPullback_square
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (pushforwardScalarSectionsIso f σ).hom.app E ≫ squareSectionsPullback g' f' f g sq σ E =
      sectionsPullback g σ ((derivedPushforward f).obj E) ≫
        (derivedScalarSections S' ((globalRingHom g).comp σ)).map
          (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq E) ≫
        (relPushforwardIso σ f' g).hom.app ((derivedPullback g').obj E) := by
  simpa only [squareSectionsPullback, relSectionsPullback, sectionsPullback, Category.assoc] using
    sectionsPullback_square_of_facts (derivedAdjunction g').unit (derivedAdjunction g).unit
    (pushforwardScalarSectionsIso f σ) (relPushforwardIso σ g' f)
    (pushforwardScalarSectionsIso g σ) (relPushforwardIso σ f' g)
    (pushforwardScalarSectionsIso (g' ≫ f) σ) (pushforwardScalarSectionsIso (f' ≫ g) σ)
    (derivedPushforwardCompIso g' f) (derivedPushforwardCompIso f' g)
    (eqToIso (congrArg (fun r : X' ⟶ S => derivedPushforward r) sq))
    (eqToIso (congrArg (fun r : X' ⟶ S => derivedScalarSections X' ((globalRingHom r).comp σ)) sq))
    (pushforwardScalarSectionsIso_hom_comp σ g' f) (pushforwardScalarSectionsIso_hom_comp σ f' g)
    (pushforwardScalarSectionsIso_eqToHom σ sq) E
    (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq E)
    (unit_comp_derivedBaseChangeMap g' f' f g sq E)

end Square

/-! ### Changing the ring of scalars -/

section ChangeScalars

variable (Z : RingedSpace.{u, u}) {A B : Type u} [Ring A] [Ring B] (φ : A →+* B)
  (σ : B →+* (structureSheafRing Z).obj.obj (op ⊤))

/-- Restriction of scalars along `φ`, on derived categories of modules. -/
abbrev derivedRestrictScalars :
    DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory

/-- Termwise, `A`-linear global sections through `σ ∘ φ` are `B`-linear global sections followed
by restriction of scalars along `φ`. -/
def homotopyScalarsIso :
    homotopyScalarSections Z (σ.comp φ) ≅
      (scalarSections Z σ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
        derivedRestrictScalars φ :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (scalarSections Z σ ⋙ ModuleCat.restrictScalars.{u} φ))
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((scalarSections Z σ).mapHomotopyCategory (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactorsh.symm

variable {σ} {τ : A →+* (structureSheafRing Z).obj.obj (op ⊤)} (h : τ = σ.comp φ)

/-- Termwise, `A`-linear global sections through `τ = σ ∘ φ` are `B`-linear global sections
followed by restriction of scalars along `φ`. -/
def homotopyScalarsIsoOfEq :
    homotopyScalarSections Z τ ≅
      (scalarSections Z σ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
        derivedRestrictScalars φ :=
  eqToIso (congrArg (homotopyScalarSections Z) h) ≪≫ homotopyScalarsIso Z φ σ

/-- The comparison exhibiting `RΓ(Z, -) ⋙ res_φ` as a right derived functor of `A`-linear global
sections through `τ = σ ∘ φ`. -/
def changeScalarsUnit :
    homotopyScalarSections Z τ ⟶
      DerivedCategory.Qh ⋙ (derivedScalarSections Z σ ⋙ derivedRestrictScalars φ) :=
  (homotopyScalarsIsoOfEq Z φ h).hom ≫
    Functor.whiskerRight (derivedScalarSectionsUnit Z σ) (derivedRestrictScalars φ)

/-- `RΓ(Z, -) ⋙ res_φ` is a right derived functor of `A`-linear global sections through `τ` via
`changeScalarsUnit`. -/
instance isRightDerivedFunctor_changeScalarsUnit :
    (derivedScalarSections Z σ ⋙ derivedRestrictScalars φ).IsRightDerivedFunctor
      (changeScalarsUnit Z φ h)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z))
        (ComplexShape.up ℤ)) := by
  apply isRightDerivedFunctor_of_isIso_app_isKInjective _ (exists_quasiIso_isKInjective Z)
  intro I hI
  have := isIso_derivedScalarSectionsUnit_app Z σ I hI
  dsimp only [changeScalarsUnit, NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

/-- **Changing the ring of scalars**: `A`-linear derived global sections through `τ = σ ∘ φ` are
the `B`-linear ones followed by restriction of scalars along `φ`. -/
def changeScalarsIso :
    derivedScalarSections Z τ ≅ derivedScalarSections Z σ ⋙ derivedRestrictScalars φ :=
  Functor.rightDerivedUnique (derivedScalarSections Z τ)
    (derivedScalarSections Z σ ⋙ derivedRestrictScalars φ) (derivedScalarSectionsUnit Z τ)
    (changeScalarsUnit Z φ h)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))

/-- The unit of `derivedScalarSections` through `τ` followed by `changeScalarsIso` is
`changeScalarsUnit`. -/
@[reassoc]
theorem derivedScalarSectionsUnit_comp_changeScalarsIso_hom_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (derivedScalarSectionsUnit Z τ).app K ≫
        (changeScalarsIso Z φ h).hom.app (DerivedCategory.Qh.obj K) =
      (changeScalarsUnit Z φ h).app K := by
  simp [changeScalarsIso]

end ChangeScalars

/-! ### Changing the ring of scalars is compatible with pushforward -/

section AbstractChangeScalars

variable {KY KX DY DX HA HB : Type*} [Category KY] [Category KX] [Category DY] [Category DX]
  [Category HA] [Category HB]

/-- **The identification of derived global sections of a pushforward commutes with changing the
ring of scalars, abstractly.** -/
theorem changeScalars_of_units {Qy : KY ⥤ DY} {Qx : KX ⥤ DX} {P : KY ⥤ KX} {Rp : DY ⥤ DX}
    (ηp : P ⋙ Qx ⟶ Qy ⋙ Rp) (res : HB ⥤ HA)
    {FXA : KX ⥤ HA} {FXB : KX ⥤ HB} {FYA : KY ⥤ HA} {FYB : KY ⥤ HB}
    {GXA : DX ⥤ HA} {GXB : DX ⥤ HB} {GYA : DY ⥤ HA} {GYB : DY ⥤ HB}
    (uXA : FXA ⟶ Qx ⋙ GXA) (uXB : FXB ⟶ Qx ⋙ GXB) (uYA : FYA ⟶ Qy ⋙ GYA)
    (uYB : FYB ⟶ Qy ⋙ GYB)
    (cA : FYA ⟶ P ⋙ FXA) (cB : FYB ⟶ P ⋙ FXB) (dX : FXA ⟶ FXB ⋙ res) (dY : FYA ⟶ FYB ⋙ res)
    (ℓA : Rp ⋙ GXA ≅ GYA) (ℓB : Rp ⋙ GXB ≅ GYB) (μX : GXA ≅ GXB ⋙ res) (μY : GYA ≅ GYB ⋙ res)
    (W : MorphismProperty KY) [Qy.IsLocalization W] [GYA.IsRightDerivedFunctor uYA W]
    (hℓA : ∀ K, cA.app K ≫ uXA.app (P.obj K) ≫ GXA.map (ηp.app K) =
      uYA.app K ≫ ℓA.inv.app (Qy.obj K))
    (hℓB : ∀ K, cB.app K ≫ uXB.app (P.obj K) ≫ GXB.map (ηp.app K) =
      uYB.app K ≫ ℓB.inv.app (Qy.obj K))
    (hμX : ∀ K, uXA.app K ≫ μX.hom.app (Qx.obj K) = dX.app K ≫ res.map (uXB.app K))
    (hμY : ∀ K, uYA.app K ≫ μY.hom.app (Qy.obj K) = dY.app K ≫ res.map (uYB.app K))
    [∀ K, IsIso (cB.app K)]
    (hc : ∀ K, cA.app K ≫ dX.app (P.obj K) = dY.app K ≫ res.map (cB.app K)) (F : DY) :
    ℓA.hom.app F ≫ μY.hom.app F = μX.hom.app (Rp.obj F) ≫ res.map (ℓB.hom.app F) := by
  have key : μY.hom = ℓA.inv ≫ Functor.whiskerLeft Rp μX.hom ≫
      Functor.whiskerRight ℓB.hom res := by
    refine Functor.rightDerived_ext GYA uYA W _ _ _ ?_
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj]
    rw [hμY, ← reassoc_of% (hℓA K)]
    have n₁ : GXA.map (ηp.app K) ≫ μX.hom.app (Rp.obj (Qy.obj K)) =
        μX.hom.app (Qx.obj (P.obj K)) ≫ res.map (GXB.map (ηp.app K)) :=
      μX.hom.naturality (ηp.app K)
    have n₂ : uXB.app (P.obj K) ≫ GXB.map (ηp.app K) ≫ ℓB.hom.app (Qy.obj K) =
        inv (cB.app K) ≫ uYB.app K := by
      rw [← cancel_epi (cB.app K), IsIso.hom_inv_id_assoc]
      simpa using congrArg (· ≫ ℓB.hom.app (Qy.obj K)) (hℓB K)
    rw [reassoc_of% n₁, reassoc_of% (hμX (P.obj K)), ← res.map_comp, ← res.map_comp, n₂,
      reassoc_of% (hc K), res.map_comp, ← res.map_comp_assoc, IsIso.hom_inv_id, res.map_id,
      Category.id_comp]
  rw [key]
  simp

end AbstractChangeScalars

section ChangeScalarsPushforward

variable {X Y : RingedSpace.{u, u}} (p : Y ⟶ X) {A B : Type u} [Ring A] [Ring B] (φ : A →+* B)
  {σ : B →+* (structureSheafRing X).obj.obj (op ⊤)}
  {τ : A →+* (structureSheafRing X).obj.obj (op ⊤)}
  (hX : τ = σ.comp φ) (hY : (globalRingHom p).comp τ = ((globalRingHom p).comp σ).comp φ)

/-- The termwise change of scalars at `τ = σ ∘ φ`, read on the image of a complex. -/
theorem homotopyScalarsIsoOfEq_hom_app_rfl (Z : RingedSpace.{u, u})
    (σ' : B →+* (structureSheafRing Z).obj.obj (op ⊤))
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (homotopyScalarsIsoOfEq Z φ (rfl : σ'.comp φ = σ'.comp φ)).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) =
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactorsh.inv.app
        (((scalarSections Z σ').mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) := by
  have h₀ : (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (scalarSections Z σ' ⋙ ModuleCat.restrictScalars.{u} φ))
        (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) =
      𝟙 _ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_id _
  show 𝟙 _ ≫ (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (scalarSections Z σ' ⋙ ModuleCat.restrictScalars.{u} φ))
        (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ≫
      𝟙 _ ≫ (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactorsh.inv.app
        (((scalarSections Z σ').mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M))) = _
  rw [h₀]
  exact (Category.id_comp _).trans ((congrArg (· ≫ _) (DerivedCategory.Qh.map_id _)).trans
    ((Category.id_comp _).trans (Category.id_comp _)))

/-- Termwise, changing the ring of scalars commutes with the identification of sections of a
pushforward. -/
theorem termwise_changeScalars
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (pushforwardSectionsTermIso p τ) (ComplexShape.up ℤ)).inv.app K) ≫
      (homotopyScalarsIsoOfEq X φ hX).hom.app
        (((modulePushforward p).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
    (homotopyScalarsIsoOfEq Y φ hY).hom.app K ≫
      (derivedRestrictScalars φ).map (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (pushforwardSectionsTermIso p σ) (ComplexShape.up ℤ)).inv.app K)) := by
  subst hX
  cases hY
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have e₁ : (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsTermIso p (σ.comp φ))
      (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
        𝟙 _ :=
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_id _
  have e₂ : (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsTermIso p σ)
      (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
        𝟙 _ :=
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_id _
  rw [e₁, e₂]
  refine ((congrArg (· ≫ _) (DerivedCategory.Qh.map_id _)).trans (Category.id_comp _)).trans ?_
  refine Eq.trans ?_ ((congrArg (_ ≫ ·) ((congrArg (derivedRestrictScalars φ).map
    (DerivedCategory.Qh.map_id _)).trans ((derivedRestrictScalars φ).map_id _))).trans
    (Category.comp_id _)).symm
  exact (homotopyScalarsIsoOfEq_hom_app_rfl φ X σ _).trans
    (homotopyScalarsIsoOfEq_hom_app_rfl φ Y ((globalRingHom p).comp σ) L).symm

/-- **Changing the ring of scalars commutes with the identification of derived global sections of
a pushforward.** -/
theorem pushforwardScalarSectionsIso_changeScalars
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (pushforwardScalarSectionsIso p τ).hom.app F ≫ (changeScalarsIso Y φ hY).hom.app F =
      (changeScalarsIso X φ hX).hom.app ((derivedPushforward p).obj F) ≫
        (derivedRestrictScalars φ).map ((pushforwardScalarSectionsIso p σ).hom.app F) :=
  changeScalars_of_units (derivedPushforwardUnit p) (derivedRestrictScalars φ)
    (derivedScalarSectionsUnit X τ) (derivedScalarSectionsUnit X σ)
    (derivedScalarSectionsUnit Y ((globalRingHom p).comp τ))
    (derivedScalarSectionsUnit Y ((globalRingHom p).comp σ))
    (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsTermIso p τ)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
    (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsTermIso p σ)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
    (homotopyScalarsIsoOfEq X φ hX).hom (homotopyScalarsIsoOfEq Y φ hY).hom
    (pushforwardScalarSectionsIso p τ) (pushforwardScalarSectionsIso p σ)
    (changeScalarsIso X φ hX) (changeScalarsIso Y φ hY)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (fun K => (pushforwardScalarUnit_app p τ K).symm.trans
      (derivedScalarSectionsUnit_comp_iso_inv_app p τ K).symm)
    (fun K => (pushforwardScalarUnit_app p σ K).symm.trans
      (derivedScalarSectionsUnit_comp_iso_inv_app p σ K).symm)
    (fun K => derivedScalarSectionsUnit_comp_changeScalarsIso_hom_app X φ hX K)
    (fun K => derivedScalarSectionsUnit_comp_changeScalarsIso_hom_app Y φ hY K)
    (termwise_changeScalars p φ hX hY) F

end ChangeScalarsPushforward

end Stacks.Cohomology.DerivedSectionsPullback

end
