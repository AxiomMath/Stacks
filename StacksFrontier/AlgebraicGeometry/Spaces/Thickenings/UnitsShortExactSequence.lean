module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.DenseSubsiteRingedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The units sequence of a first-order thickening of algebraic spaces

Let `G ⊂ X` be a first-order thickening of algebraic spaces over a scheme `S`, with defining
ideal sheaf `𝓘`.  On the small étale site of the ambient space `X` the sequence of sheaves of
abelian groups

`0 ⟶ 𝓘 ⟶ 𝒪_X^* ⟶ i_* 𝒪_G^* ⟶ 0`,

whose left map is `f ↦ 1 + f` and whose right map is restriction of units along the
thickening, is short exact.

## Main definitions

* `AlgebraicGeometry.Space.firstOrderThickeningSubspace`: the closed subspace underlying a
  first-order thickening, bundled.
* `AlgebraicGeometry.Space.thickeningIdealAddSheaf`: the defining ideal sheaf, read as a sheaf
  of abelian groups.
* `AlgebraicGeometry.Space.thickeningRestrictRingedSite`: the small étale site of the ambient
  space, ringed by `i_* 𝒪_G`; its sheaf of units is the third term of the sequence.
* `AlgebraicGeometry.Space.thickeningStructureSharp`: the structure map `𝒪_X ⟶ i_* 𝒪_G`.
* `AlgebraicGeometry.Space.thickeningIdealToUnits`: the map `f ↦ 1 + f`.
* `AlgebraicGeometry.Space.thickeningUnitsRestriction`: restriction of units along the
  thickening.
* `AlgebraicGeometry.Space.thickeningUnitsShortComplex`: the sequence itself.

## Main results

* `AlgebraicGeometry.Space.thickeningUnitsShortComplex_shortExact`: the sequence is short
  exact.
* `AlgebraicGeometry.Space.thickeningIdealToUnits_app_val`: on sections the left map is
  `f ↦ 1 + f`.
* `AlgebraicGeometry.Space.thickeningUnitsRestriction_app`: on sections the right map is
  restriction of units.
* `AlgebraicGeometry.Space.ker_thickeningStructureSharp_app`: the kernel of the structure map on
  the sections over an étale chart is the defining ideal there.
* `AlgebraicGeometry.Space.thickeningIdealToUnits_mono` and
  `AlgebraicGeometry.Space.thickeningUnitsRestriction_isLocallySurjective`: the left map is a
  monomorphism and the right map is locally surjective.

## Implementation notes

The model of `i_* 𝒪_G` is the structure sheaf of the closed subspace restricted along the dense
subsite inclusion `AlgebraicGeometry.Space.thickeningChartBaseChange`, that is
`AlgebraicGeometry.RingedSite.denseRestrict` of the small étale ringed site of the closed
subspace. Its sections over an étale chart `U` of `X` are the regular functions on `G ×_X U`, and
the structure map is `AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat`, pullback of
regular functions along the cartesian projection `G ×_X U ⟶ U`.

Sections of the ideal sheaf are sections of the underlying sheaf of modules of
`AlgebraicGeometry.Space.definingIdealSheaf`, which are the elements of
`AlgebraicGeometry.Space.definingIdealAt`.

## References

* [Stacks Project, Tag 0DNM](https://stacks.math.columbia.edu/tag/0DNM)
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings (onePlusHomOfSqZero onePlusHomOfSqZero_exact_for
  onePlusHomOfSqZero_injective onePlusHomOfSqZero_map unitsMap_surjective_of_sqZero_ker)

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-! ### Commutativity of the rings of sections -/

/-- The sections of the structure sheaf of an algebraic space over an étale chart form a
commutative ring. -/
local instance commRing_structureRingSheaf_obj (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    CommRing (ToType ((structureRingSheaf B S hS X).obj.obj U)) :=
  inferInstanceAs (CommRing (ToType ((smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj U)))

/-! ### The data attached to a first-order thickening -/

/-- The closed subspace underlying a first-order thickening `G ⊂ X`, bundled as a closed
subspace of `X`.  Its defining ideal is the one whose square vanishes. -/
abbrev firstOrderThickeningSubspace (hG : IsFirstOrderThickening B S hS X G) :
    ClosedSubspaces B S hS X.1 :=
  ⟨G, hG.1.1⟩

/-- The defining ideal of a first-order thickening has zero multiplication on every chart. -/
theorem definingIdealAt_mul_self_eq_bot (hG : IsFirstOrderThickening B S hS X G)
    (U : SmallEtale B S hS X.1) :
    definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op U) *
        definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op U) = ⊥ := by
  have h := hG.2 U
  rwa [Submodule.pow_succ, Submodule.pow_one] at h

/-- The defining ideal sheaf of a first-order thickening `G ⊂ X`, read as a sheaf of abelian
groups on the small étale site of the ambient space. -/
abbrev thickeningIdealAddSheaf (hG : IsFirstOrderThickening B S hS X G) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj
    (definingIdealSheaf B S hS X (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules

/-- The sections of the ideal sheaf of a first-order thickening over an étale chart are the
elements of the defining ideal there. -/
theorem thickeningIdealAddSheaf_obj_obj (hG : IsFirstOrderThickening B S hS X G)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    ToType ((thickeningIdealAddSheaf B S hS hG).obj.obj U) =
      ↥(definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) U) :=
  rfl

/-! ### The map `f ↦ 1 + f` -/

/-- On an étale chart of the ambient space, `f ↦ 1 + f` from the sections of the defining ideal
of a first-order thickening to the units of the structure sheaf, written additively. -/
@[ega "IV 21.13.9" "more general"]
def thickeningIdealOnePlusHom (hG : IsFirstOrderThickening B S hS X G)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    ↥(definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) U) →+
      ToType ((Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (smallEtaleRingedSite B S hS X.1 X.2)).obj.obj U) :=
  onePlusHomOfSqZero _ (definingIdealAt_mul_self_eq_bot B S hS hG U.unop)

/-- On sections, `AlgebraicGeometry.Space.thickeningIdealOnePlusHom` is `f ↦ 1 + f`. -/
theorem thickeningIdealOnePlusHom_val (hG : IsFirstOrderThickening B S hS X G)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (f : ↥(definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) U)) :
    Units.val (Additive.toMul (thickeningIdealOnePlusHom B S hS hG U f)) = 1 + f.1 :=
  rfl

/-- The map `f ↦ 1 + f` commutes with étale restriction. -/
theorem thickeningIdealOnePlusHom_naturality (hG : IsFirstOrderThickening B S hS X G)
    {U V : (SmallEtale B S hS X.1)ᵒᵖ} (m : U ⟶ V)
    (f : ↥(definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) U)) :
    thickeningIdealOnePlusHom B S hS hG V
        (ConcreteCategory.hom ((thickeningIdealAddSheaf B S hS hG).obj.map m) f) =
      ConcreteCategory.hom ((Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
          (smallEtaleRingedSite B S hS X.1 X.2)).obj.map m)
        (thickeningIdealOnePlusHom B S hS hG U f) := by
  exact Additive.toMul.injective (onePlusHomOfSqZero_map _
    (definingIdealAt_mul_self_eq_bot B S hS hG U.unop) _
    (definingIdealAt_mul_self_eq_bot B S hS hG V.unop)
    (ConcreteCategory.hom ((structureRingSheaf B S hS X).obj.map m)) f
    (definingIdealAt_map B S hS X (firstOrderThickeningSubspace B S hS hG) m f.1 f.2)).symm

/-- The map `f ↦ 1 + f` of a first-order thickening, as a morphism of sheaves of abelian groups
from the defining ideal sheaf to the sheaf of units of the ambient space. -/
def thickeningIdealToUnits (hG : IsFirstOrderThickening B S hS X G) :
    thickeningIdealAddSheaf B S hS hG ⟶
      (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (smallEtaleRingedSite B S hS X.1 X.2) :
          Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (thickeningIdealOnePlusHom B S hS hG U)
      naturality := fun U V m ↦ by
        ext f
        exact thickeningIdealOnePlusHom_naturality B S hS hG m f }

/-- On sections the left map of the sequence is `f ↦ 1 + f`. -/
theorem thickeningIdealToUnits_app_val (hG : IsFirstOrderThickening B S hS X G)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (f : ↥(definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) U)) :
    Units.val (Additive.toMul ((thickeningIdealToUnits B S hS hG).hom.app U f)) = 1 + f.1 :=
  rfl

/-! ### The sheaf of units of the closed subspace, pushed forward -/

/-- The small étale site of the ambient space, ringed by `i_* 𝒪_G`: the structure sheaf of the
closed subspace underlying a first-order thickening, restricted along base change of étale scheme
charts. Its sections over an étale chart `U` of `X` are the regular functions on `G ×_X U`. -/
def thickeningRestrictRingedSite (hG : IsFirstOrderThickening B S hS X G) :
    RingedSite.{u + 1, u, u} :=
  @RingedSite.denseRestrict (SmallEtale B S hS X.1) _ (SmallEtale.topology B S hS X.1)
    (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
      (IsThickening.space B S hS hG.1).2)
    (thickeningChartBaseChange B S hS hG.1)
    (thickeningChartBaseChange_isDenseSubsite B S hS hG.1)

/-- The sections of `i_* 𝒪_G` over an étale chart `U` of `X` are the regular functions on the
base-changed chart `G ×_X U`. -/
theorem thickeningRestrictRingedSite_O_obj_obj (hG : IsFirstOrderThickening B S hS X G)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (thickeningRestrictRingedSite B S hS hG).O.obj.obj U =
      (smallEtaleRingedSite B S hS (IsThickening.space B S hS hG.1).1
          (IsThickening.space B S hS hG.1).2).O.obj.obj
        (op ((thickeningChartBaseChange B S hS hG.1).obj U.unop)) :=
  rfl

/-- The structure map `i^♯ : 𝒪_X ⟶ i_* 𝒪_G` of a first-order thickening, as a homomorphism of
sheaves of commutative rings on the small étale site of the ambient space. On an étale chart `U`
it is pullback of regular functions along the cartesian projection `G ×_X U ⟶ U`. -/
abbrev thickeningStructureSharp (hG : IsFirstOrderThickening B S hS X G) :
    (smallEtaleRingedSite B S hS X.1 X.2).O ⟶ (thickeningRestrictRingedSite B S hS hG).O :=
  smallBaseChangeSharpCommRingCat B S hS (IsThickening.inclusion B S hS hG.1)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG.1).rep

/-- On sections the structure map of a first-order thickening is pullback of regular functions
along the cartesian projection. -/
theorem thickeningStructureSharp_app_hom (hG : IsFirstOrderThickening B S hS X G)
    (U : SmallEtale B S hS X.1) :
    ((thickeningStructureSharp B S hS hG).hom.app (op U)).hom =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((isClosedImmersion_inclusion_of_isThickening B S hS hG.1).rep.snd U.1.hom)).op).hom :=
  rfl

/-- The kernel of the structure map of a first-order thickening on the sections over an étale
chart is its defining ideal there. -/
theorem ker_thickeningStructureSharp_app (hG : IsFirstOrderThickening B S hS X G)
    (U : SmallEtale B S hS X.1) :
    RingHom.ker ((thickeningStructureSharp B S hS hG).hom.app (op U)).hom =
      definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op U) := by
  rw [definingIdealAt_eq_ker]
  rfl

/-- The structure map of a first-order thickening is surjective on the sections over an affine
étale chart. -/
theorem surjective_thickeningStructureSharp_app_of_isAffine
    (hG : IsFirstOrderThickening B S hS X G) (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)) :
    Function.Surjective ((thickeningStructureSharp B S hS hG).hom.app (op U)).hom := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((isClosedImmersion_inclusion_of_isThickening B S hS hG.1).rep.snd U.1.hom)) :=
    hG.1.1.2.property U.1.hom _ _
      ((isClosedImmersion_inclusion_of_isThickening B S hS hG.1).rep.isPullback U.1.hom)
  exact Scheme.Hom.app_surjective ((BigFppfOver.toScheme B S hS).map
    ((isClosedImmersion_inclusion_of_isThickening B S hS hG.1).rep.snd U.1.hom)) ⊤
    (isAffineOpen_top _)

/-- Restriction of units along a first-order thickening, as a morphism of sheaves of abelian
groups from the sheaf of units of the ambient space to the sheaf of units of `i_* 𝒪_G`. -/
def thickeningUnitsRestriction (hG : IsFirstOrderThickening B S hS X G) :
    (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (smallEtaleRingedSite B S hS X.1 X.2) :
          Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) ⟶
      (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (thickeningRestrictRingedSite B S hS hG) :
          Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  letI : Limits.PreservesLimitsOfSize.{u + 1, u + 1} CommGrpCat.toAddCommGrp.{u} :=
    commGroupAddCommGroupEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  (sheafCompose (SmallEtale.topology B S hS X.1) CommGrpCat.toAddCommGrp.{u}).map
    ((sheafCompose (SmallEtale.topology B S hS X.1) CommMonCat.units.{u}).map
      ((sheafCompose (SmallEtale.topology B S hS X.1)
        (forget₂ CommRingCat.{u} CommMonCat.{u})).map (thickeningStructureSharp B S hS hG)))

/-- On sections, restriction of units is the map of units induced by the structure map. -/
theorem thickeningUnitsRestriction_app (hG : IsFirstOrderThickening B S hS X G)
    (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (v : (ToType ((smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj U))ˣ) :
    Additive.toMul ((thickeningUnitsRestriction B S hS hG).hom.app U (Additive.ofMul v)) =
      Units.map ((thickeningStructureSharp B S hS hG).hom.app U).hom.toMonoidHom v :=
  rfl

/-! ### The sections of `i_* 𝒪_G` form a commutative ring -/

/-- The sections of `i_* 𝒪_G` over an étale chart of the ambient space form a commutative
ring. -/
local instance commRing_thickeningRestrictRingedSite_O_obj
    (hG : IsFirstOrderThickening B S hS X G) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    CommRing (ToType ((thickeningRestrictRingedSite B S hS hG).O.obj.obj U)) :=
  inferInstanceAs (CommRing (ToType ((smallEtaleRingedSite B S hS
    (IsThickening.space B S hS hG.1).1 (IsThickening.space B S hS hG.1).2).O.obj.obj
      (op ((thickeningChartBaseChange B S hS hG.1).obj U.unop)))))

/-! ### The composite of the two maps vanishes -/

/-- A section of the units of the ambient space restricts to the identity on the closed subspace
exactly when it is of the form `1 + f` with `f` a section of the defining ideal. -/
private theorem thickeningUnitsRestriction_app_eq_zero_iff
    (hG : IsFirstOrderThickening B S hS X G) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : ToType ((Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
      (smallEtaleRingedSite B S hS X.1 X.2)).obj.obj U)) :
    (thickeningUnitsRestriction B S hS hG).hom.app U t = 0 ↔
      ∃ f, (thickeningIdealToUnits B S hS hG).hom.app U f = t := by
  have h := onePlusHomOfSqZero_exact_for _ (definingIdealAt_mul_self_eq_bot B S hS hG U.unop)
    ((thickeningStructureSharp B S hS hG).hom.app U).hom
    (ker_thickeningStructureSharp_app B S hS hG U.unop) (Additive.toMul t)
  exact ⟨fun ht ↦ (h.1 (congrArg Additive.toMul ht)).imp fun f hf ↦ congrArg Additive.ofMul hf,
    fun ⟨f, hf⟩ ↦ Additive.toMul.injective (h.2 ⟨f, congrArg Additive.toMul hf⟩)⟩

/-- A unit of the form `1 + f`, with `f` a section of the defining ideal, restricts to the
identity on the closed subspace. -/
theorem thickeningUnitsRestriction_app_onePlus (hG : IsFirstOrderThickening B S hS X G)
    (U : SmallEtale B S hS X.1)
    (f : ↥(definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op U))) :
    (thickeningUnitsRestriction B S hS hG).hom.app (op U)
        ((thickeningIdealToUnits B S hS hG).hom.app (op U) f) = 0 :=
  (thickeningUnitsRestriction_app_eq_zero_iff B S hS hG (op U) _).2 ⟨f, rfl⟩

/-! ### The sequence and its exactness -/

/-- The sequence of sheaves of abelian groups `0 ⟶ 𝓘 ⟶ 𝒪_X^* ⟶ i_* 𝒪_G^* ⟶ 0` of a first-order
thickening, on the small étale site of the ambient space. -/
def thickeningUnitsShortComplex (hG : IsFirstOrderThickening B S hS X G) :
    ShortComplex (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  ShortComplex.mk (thickeningIdealToUnits B S hS hG) (thickeningUnitsRestriction B S hS hG) <| by
    refine ObjectProperty.hom_ext _ ?_
    ext U f
    exact thickeningUnitsRestriction_app_onePlus B S hS hG U.unop f

/-- The composite of `f ↦ 1 + f` with restriction of units vanishes. -/
theorem thickeningIdealToUnits_comp_unitsRestriction
    (hG : IsFirstOrderThickening B S hS X G) :
    (thickeningUnitsShortComplex B S hS hG).f ≫ (thickeningUnitsShortComplex B S hS hG).g = 0 :=
  (thickeningUnitsShortComplex B S hS hG).zero

/-- The map `f ↦ 1 + f` is a monomorphism. -/
theorem thickeningIdealToUnits_mono (hG : IsFirstOrderThickening B S hS X G) :
    Mono (thickeningIdealToUnits B S hS hG) :=
  Sheaf.mono_of_injective _ fun U ↦
    onePlusHomOfSqZero_injective _ (definingIdealAt_mul_self_eq_bot B S hS hG U.unop)

/-- Restriction of units along a first-order thickening is locally surjective. -/
theorem thickeningUnitsRestriction_isLocallySurjective
    (hG : IsFirstOrderThickening B S hS X G) :
    Sheaf.IsLocallySurjective (thickeningUnitsRestriction B S hS hG) := by
  refine ⟨fun {U} t ↦ ?_⟩
  obtain ⟨_, Y, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X.1 U
  have key : ∀ j,
      (Presheaf.imageSieve (thickeningUnitsRestriction B S hS hG).hom t).arrows (a j) := by
    intro j
    obtain ⟨v, hv⟩ := unitsMap_surjective_of_sqZero_ker
      (definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op (Y j)))
      ((thickeningStructureSharp B S hS hG).hom.app (op (Y j))).hom
      (surjective_thickeningStructureSharp_app_of_isAffine B S hS hG (Y j) (haff j))
      (ker_thickeningStructureSharp_app B S hS hG (Y j))
      (definingIdealAt_mul_self_eq_bot B S hS hG (Y j))
      (Additive.toMul (ConcreteCategory.hom
        ((Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
          (thickeningRestrictRingedSite B S hS hG)).obj.map (a j).op) t))
    exact ⟨Additive.ofMul v, congrArg Additive.ofMul hv⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hcov
  rintro V f ⟨_, h, _, ⟨j⟩, rfl⟩
  exact (Presheaf.imageSieve (thickeningUnitsRestriction B S hS hG).hom t).downward_closed
    (key j) h

/-- Sections of the kernel of a morphism of sheaves of abelian groups on the small étale site
inject into the sections of the source. -/
theorem injective_kernel_ι_app
    {F₁ F₂ : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}} (g : F₁ ⟶ F₂)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective ((kernel.ι g).hom.app U) := by
  have : Limits.PreservesFiniteLimits
      ((sheafSections (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}).obj U) :=
    inferInstanceAs (Limits.PreservesFiniteLimits
      (sheafToPresheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} ⋙
        (evaluation ((SmallEtale B S hS X.1)ᵒᵖ) AddCommGrpCat.{u}).obj U))
  exact (AddCommGrpCat.mono_iff_injective _).1
    (Functor.map_mono ((sheafSections (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.{u}).obj U) (kernel.ι g))

/-- The canonical map from the defining ideal sheaf to the kernel of restriction of units is
surjective on the sections over every étale chart. -/
@[ega "IV 21.13.9" "partial"]
theorem surjective_kernelLift_thickeningUnitsShortComplex_app
    (hG : IsFirstOrderThickening B S hS X G) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Surjective ((kernel.lift (thickeningUnitsShortComplex B S hS hG).g
      (thickeningUnitsShortComplex B S hS hG).f
      (thickeningUnitsShortComplex B S hS hG).zero).hom.app U) := by
  intro w
  have hzero : (thickeningUnitsRestriction B S hS hG).hom.app U
      ((kernel.ι (thickeningUnitsShortComplex B S hS hG).g).hom.app U w) = 0 :=
    congrArg (fun k : kernel (thickeningUnitsShortComplex B S hS hG).g ⟶
        (thickeningUnitsShortComplex B S hS hG).X₃ ↦ k.hom.app U w)
      (kernel.condition (thickeningUnitsShortComplex B S hS hG).g)
  obtain ⟨x, hx⟩ := (thickeningUnitsRestriction_app_eq_zero_iff B S hS hG U _).1 hzero
  refine ⟨x, injective_kernel_ι_app B S hS _ U ?_⟩
  refine Eq.trans (congrArg (fun k : (thickeningUnitsShortComplex B S hS hG).X₁ ⟶
      (thickeningUnitsShortComplex B S hS hG).X₂ ↦ k.hom.app U x)
    (kernel.lift_ι (thickeningUnitsShortComplex B S hS hG).g
      (thickeningUnitsShortComplex B S hS hG).f
      (thickeningUnitsShortComplex B S hS hG).zero)) ?_
  exact hx

/-- The sequence `0 ⟶ 𝓘 ⟶ 𝒪_X^* ⟶ i_* 𝒪_G^* ⟶ 0` of a first-order thickening of algebraic
spaces is short exact. -/
theorem thickeningUnitsShortComplex_shortExact (hG : IsFirstOrderThickening B S hS X G) :
    (thickeningUnitsShortComplex B S hS hG).ShortExact := by
  have : Mono (thickeningUnitsShortComplex B S hS hG).f :=
    thickeningIdealToUnits_mono B S hS hG
  have : Sheaf.IsLocallySurjective (thickeningUnitsShortComplex B S hS hG).g :=
    thickeningUnitsRestriction_isLocallySurjective B S hS hG
  have : Epi (thickeningUnitsShortComplex B S hS hG).g :=
    Sheaf.epi_of_isLocallySurjective _
  refine { exact := ?_ }
  refine (thickeningUnitsShortComplex B S hS hG).exact_iff_epi_kernel_lift.mpr ?_
  have : Sheaf.IsLocallySurjective (kernel.lift (thickeningUnitsShortComplex B S hS hG).g
      (thickeningUnitsShortComplex B S hS hG).f
      (thickeningUnitsShortComplex B S hS hG).zero) :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (surjective_kernelLift_thickeningUnitsShortComplex_app B S hS hG)
  exact Sheaf.epi_of_isLocallySurjective _

end AlgebraicGeometry.Space

end
