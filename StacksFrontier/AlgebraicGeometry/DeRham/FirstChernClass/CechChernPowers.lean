module

public import StacksFrontier.AlgebraicGeometry.DeRham.CechCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.RealizationChernClass
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyTruncationPairing

/-!
# Powers of the de Rham first Chern class along the brutal filtration

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` with local
stalks, let `Ω^•` be the relative de Rham complex and suppose Čech cohomology computes the
cohomology of each of its terms. For an invertible module `L` the de Rham first Chern class
`c₁^{dR}(L) ∈ H²_{dR}` ([Stacks, Section 0FLE]) has cup powers `c₁^{dR}(L)^i ∈ H^{2i}_{dR}`.
Following [Stacks, Remark 0FME] they are computed along the brutal filtration: the class
`γ₁(L) ∈ H²(X, σ^{≥1}Ω^•)` has powers `γ₁(L)^i ∈ H^{2i}(X, σ^{≥i}Ω^•)` for the pairing
`σ^{≥a} ⊗ σ^{≥b} ⟶ σ^{≥a+b}` of the brutal truncations, these map to `c₁^{dR}(L)^i` under the
inclusion `σ^{≥i}Ω^• ⟶ Ω^•`, and their images under the projection `σ^{≥i}Ω^• ⟶ Ωⁱ[-i]` are the
cup powers of the image of `γ₁(L)` in `H²(X, Ω¹[-1])`, which is the Hodge first Chern class.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassModule`: `c₁^{dR}(L)`, in the
  sheaf-of-modules realization of `H²_{dR}` over which the cup product is taken.
* `AlgebraicGeometry.SheafOfModules.deRhamChernPowCech`: the cup powers `c₁^{dR}(L)^i`.
* `AlgebraicGeometry.SheafOfModules.filteredChernPow`: the powers `γ₁(L)^i ∈ H^{2i}(X, σ^{≥i}Ω^•)`.

## Main results

* `AlgebraicGeometry.SheafOfModules.hypercohomologyMap_ιTruncPlus_filteredChernPow`: the
  inclusion `σ^{≥i}Ω^• ⟶ Ω^•` carries `γ₁(L)^i` to `c₁^{dR}(L)^i`.
* `AlgebraicGeometry.SheafOfModules.hypercohomologyMap_truncPlusπ_filteredChernPow_succ`: the
  projection to the graded piece is multiplicative.

## References

* [Stacks Project, Remark 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Section 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.Hypercohomology

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

/-- The commutative ring structure on the sections of the base ring sheaf, at the spelling
`TopCat.Sheaf` in which the base ring sheaf of the de Rham complex is given; it is
`Stacks.Cech.Refinement.sectionCommRing`. -/
@[reducible]
def sectionCommRingTopCat {Y : TopCat.{u}} (A : TopCat.Sheaf CommRingCat.{u} Y) (W : Opens Y) :
    CommRing (Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf A) W) :=
  Stacks.Cech.Refinement.sectionCommRing (O := A) W

attribute [local instance high] sectionCommRingTopCat

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)
  (hT : ∀ q, CechComputesSheaf A ((deRhamComplexInt B D).X q))

/-! ### Čech cohomology computes the cohomology of the truncations -/

include hT in
/-- Čech cohomology computes the hypercohomology of the de Rham complex. -/
theorem cechComputes_deRhamComplexPlus_of_terms : CechComputes A (deRhamComplexPlus B D) :=
  cechComputes_of_terms _ _ hT

include hT in
/-- Čech cohomology computes the hypercohomology of the brutal truncations of the de Rham
complex. -/
theorem cechComputes_truncPlus_deRhamComplexInt (a : ℤ) :
    CechComputes A (truncPlus A (deRhamComplexInt B D) a) :=
  cechComputes_of_terms _ _ fun q => by
    by_cases hq : a ≤ q
    · have e := StacksDraft.StupidTruncation.stupidTruncGEXIso (deRhamComplexInt B D) a q hq
      exact fun n => cechSurjAt_cechInjAt_of_iso A
        (ObjectProperty.isoMk _ ((HomologicalComplex.single _ (up ℤ) 0).mapIso e.symm) :
          singlePlus A ((deRhamComplexInt B D).X q) 0 ≅ singlePlus A _ 0) n (hT q n)
    · exact cechComputes_of_isZero_X _ _ fun k => by
        change IsZero (((HomologicalComplex.single _ (up ℤ) 0).obj _).X k)
        by_cases hk : k = 0
        · subst hk
          exact (CochainComplex.isZero_of_isStrictlyGE
            ((deRhamComplexInt B D).stupidTrunc (ComplexShape.embeddingUpIntGE a)) a q
              (by omega)).of_iso (HomologicalComplex.singleObjXSelf (up ℤ) 0 _)
        · exact HomologicalComplex.isZero_single_obj_X (up ℤ) 0 _ k hk

/-! ### The powers -/

section Powers

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

variable (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
  (structureSheaf X.sheaf).property)

/-- **The de Rham first Chern class `c₁^{dR}(L) ∈ H²_{dR}`** ([Stacks, Section 0FLE]), carried
from the abelian-sheaf realization, in which logarithmic differentiation forms it, to the
hypercohomology of the de Rham complex of sheaves of `A`-modules, over which the cup product is
taken. -/
def deRhamFirstChernClassModule : hypercohomology A (deRhamComplexPlus B D) 2 :=
  (deRhamCohomologyAbelianIso B D 2).hom.hom (deRhamFirstChernClassAbelian B D c)

/-- **The cup powers `c₁^{dR}(L)^i ∈ H^{2i}_{dR}`** of the de Rham first Chern class, for the cup
product of Section 0FM3: `c₁^{dR}(L)⁰ = 1` and `c₁^{dR}(L)^{i+1} = c₁^{dR}(L)^i ∪ c₁^{dR}(L)`. -/
def deRhamChernPowCech : (i : ℕ) → hypercohomology A (deRhamComplexPlus B D) (2 * (i : ℤ))
  | 0 => differentialGradedUnitClass (deRhamDifferentialGradedAlgebra B D) 0
  | k + 1 => cup A (cechComputes_deRhamComplexPlus_of_terms B D hT)
      (cechComputes_deRhamComplexPlus_of_terms B D hT) (deRhamCechPairing B D) (2 * (k : ℤ)) 2
      (2 * ((k + 1 : ℕ) : ℤ)) (by push_cast; ring) (deRhamChernPowCech k)
      (deRhamFirstChernClassModule B D c)

/-- The unit of the de Rham complex read in its brutal truncation `σ^{≥0}`, which is the de Rham
complex itself. -/
def truncatedUnitClass : hypercohomology A (truncPlus A (deRhamComplexInt B D) (0 : ℕ)) 0 :=
  hypercohomologyMap A (truncPlusIso A (deRhamComplexPlus B D) 0).inv 0
    (differentialGradedUnitClass (deRhamDifferentialGradedAlgebra B D) 0)

/-- **The powers `γ₁(L)^i ∈ H^{2i}(X, σ^{≥i}Ω^•)`** of the Hodge-filtered first Chern class, for
the pairing of the brutal truncations induced by the wedge product ([Stacks, Remark 0FME]). -/
def filteredChernPow :
    (i : ℕ) → hypercohomology A (truncPlus A (deRhamComplexInt B D) (i : ℤ)) (2 * (i : ℤ))
  | 0 => truncatedUnitClass B D
  | k + 1 => cup A (cechComputes_truncPlus_deRhamComplexInt B D hT k)
      (cechComputes_truncPlus_deRhamComplexInt B D hT 1)
      (truncPairing (deRhamCechPairing B D) (k : ℤ) 1) (2 * (k : ℤ)) 2 (2 * ((k + 1 : ℕ) : ℤ))
      (by push_cast; ring) (filteredChernPow k) (filteredFirstChernClassModule B D c)

/-- **The inclusion `σ^{≥i}Ω^• ⟶ Ω^•` carries `γ₁(L)^i` to `c₁^{dR}(L)^i`** ([Stacks,
Remark 0FME]): the inclusions of the brutal truncations are multiplicative, and the inclusion
carries `γ₁(L)` to `c₁^{dR}(L)`. -/
theorem hypercohomologyMap_ιTruncPlus_filteredChernPow (i : ℕ) :
    hypercohomologyMap A (ιTruncPlus A (deRhamComplexPlus B D) (i : ℤ)) (2 * (i : ℤ))
        (filteredChernPow B D hT c i) = deRhamChernPowCech B D hT c i := by
  induction i with
  | zero =>
    exact (hypercohomologyMapIso A (truncPlusIso A (deRhamComplexPlus B D) 0) 0).inv_hom_id_apply
      (differentialGradedUnitClass (deRhamDifferentialGradedAlgebra B D) 0)
  | succ k ih =>
    rw [filteredChernPow, deRhamChernPowCech, ← ih, deRhamFirstChernClassModule,
      deRhamCohomologyAbelianIso_deRhamFirstChernClassAbelian]
    exact cup_natural A _ _ _ _ _ _ _ _ _
      (pairingHom_ιTruncPlus (deRhamCechPairing B D) (k : ℤ) 1) _ _ _ _ _ _

omit [∀ x : X, IsLocalRing (X.presheaf.stalk x)] in
include hT in
/-- Čech cohomology computes the cohomology of a term of the de Rham complex placed in any
degree. -/
theorem cechComputes_singlePlus_deRhamComplexInt (a q : ℤ) :
    CechComputes A (singlePlus A ((deRhamComplexInt B D).X a) q) :=
  (hT a).singlePlus A q

/-- **The projection to the graded pieces is multiplicative on the powers of `γ₁(L)`**: the image
of `γ₁(L)^{i+1}` in `H^{2i+2}(X, Ω^{i+1}[-i-1])` is the cup product, for the wedge product
`Ωⁱ ⊗ Ω¹ ⟶ Ω^{i+1}`, of the image of `γ₁(L)^i` in `H^{2i}(X, Ωⁱ[-i])` with the image of
`γ₁(L)` in `H²(X, Ω¹[-1])`. -/
theorem hypercohomologyMap_truncPlusπ_filteredChernPow_succ (k : ℕ) :
    hypercohomologyMap A (truncPlusπ (deRhamComplexInt B D) ((k : ℤ) + 1)) (2 * ((k + 1 : ℕ) : ℤ))
        (filteredChernPow B D hT c (k + 1)) =
      cup A (cechComputes_singlePlus_deRhamComplexInt B D hT _ _)
        (cechComputes_singlePlus_deRhamComplexInt B D hT _ _)
        (singlePairingAt (k : ℤ) 1 ((deRhamCechPairing B D).μ (k : ℤ) 1 ((k : ℤ) + 1) rfl))
        (2 * (k : ℤ)) 2 (2 * ((k + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (hypercohomologyMap A (truncPlusπ (deRhamComplexInt B D) (k : ℤ)) (2 * (k : ℤ))
          (filteredChernPow B D hT c k))
        (hypercohomologyMap A (truncPlusπ (deRhamComplexInt B D) 1) 2
          (filteredFirstChernClassModule B D c)) :=
  cup_natural A _ _ _ _ _ _ _ _ _ (pairingHom_truncSC_g (deRhamCechPairing B D) (k : ℤ) 1) _ _ _
    _ _ _

end Powers

end AlgebraicGeometry.SheafOfModules


/-! ### Morphisms of schemes -/

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (p : X ⟶ S) [IsAffineHom (pullback.diagonal (terminal.from X))]
  (L : SheafOfModules.{u} (_root_.structureSheaf X.toRingedSpace.sheaf))
  (hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.sheaf.obj
    (_root_.structureSheaf X.toRingedSpace.sheaf).property L)

/-- **The de Rham first Chern class `c₁^{dR}(L) ∈ H²_{dR}(X/S)`** of an invertible module
([Stacks, Section 0FLE]), as an element of the `H⁰(S, 𝒪_S)`-module `H²_{dR}(X/S)`: the class
`AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelianOf` formed by logarithmic
differentiation, carried by the comparison of Tag 01F1 to the realization of de Rham cohomology
over `p⁻¹𝒪_S`. -/
def deRhamFirstChernClass : deRhamCohomologyBaseModule p 2 :=
  (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 2).hom
    (SheafOfModules.deRhamFirstChernClassModule (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p))
      (Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
        (_root_.structureSheaf X.toRingedSpace.sheaf).property L hL))

/-- **The cup powers `c₁^{dR}(L)^i ∈ H^{2i}_{dR}(X/S)`** of the de Rham first Chern class, for the
cup product `AlgebraicGeometry.Scheme.Hom.deRhamCup`; see `deRhamChernPow_zero` and
`deRhamChernPow_succ`. -/
def deRhamChernPow (i : ℕ) : deRhamCohomologyBaseModule p (2 * (i : ℤ)) :=
  (SheafOfModules.hypercohomologyIsoDeRhamCohomology (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) (2 * (i : ℤ))).hom
    (SheafOfModules.deRhamChernPowCech (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p))
      (cechComputesSheaf_deRhamComplexInt_X p)
      (Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
        (_root_.structureSheaf X.toRingedSpace.sheaf).property L hL) i)

/-- The zeroth power of the de Rham first Chern class is the unit `1 ∈ H⁰_{dR}(X/S)`. -/
theorem deRhamChernPow_zero : deRhamChernPow p L hL 0 = deRhamUnit p :=
  rfl

/-- **`c₁^{dR}(L)^{i+1} = c₁^{dR}(L)^i ∪ c₁^{dR}(L)`.** -/
theorem deRhamChernPow_succ (i : ℕ) :
    deRhamChernPow p L hL (i + 1) =
      deRhamCup p (2 * (i : ℤ)) 2 (2 * ((i + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (deRhamChernPow p L hL i) (deRhamFirstChernClass p L hL) := by
  simp only [deRhamChernPow, deRhamCup, deRhamFirstChernClass, SheafOfModules.deRhamCechCup]
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply,
    ← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
  rfl

end AlgebraicGeometry.Scheme.Hom

end
