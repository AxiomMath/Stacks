module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologySinglePairing

/-!
# The pairing of a sheaf of differential graded algebras

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings and let `𝒜` be a sheaf of
differential graded `𝒪_X`-algebras whose underlying complex is bounded below. Multiplication
`𝒜ᵖ × 𝒜^q ⟶ 𝒜^{p+q}` is bilinear over `𝒪_X` and satisfies the graded Leibniz rule, which is
exactly the data of a pairing of the complex `𝒜` with itself into itself in the sense of
`Stacks.Cech.Hypercohomology.Pairing`, to which the cup product of Cohomology, Section 01FP
applies. The global unit section of `𝒜⁰` is closed and defines the class `1 ∈ H⁰(X, 𝒜)`.

## Main definitions

* `Stacks.Cech.Hypercohomology.differentialGradedComplexPlus`: the complex underlying `𝒜`, as a
  bounded below complex.
* `Stacks.Cech.Hypercohomology.differentialGradedPairing`: **the pairing of `𝒜` with itself given
  by multiplication.**
* `Stacks.Cech.Hypercohomology.globalCocycleClass`: the class in `H⁰(X, K)` of a global section of
  `K⁰` killed by the differential.
* `Stacks.Cech.Hypercohomology.differentialGradedUnitClass`: **the unit `1 ∈ H⁰(X, 𝒜)`**, the
  class of the global unit section of `𝒜⁰`.

## Main results

* `Stacks.Cech.Hypercohomology.differentialGradedPairing_app_tmul`: the pairing is multiplication
  on homogeneous local sections.
* `Stacks.Cech.Hypercohomology.unitHom_comp_d_eq_zero`: the unit of `𝒜` is closed.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
* [Stacks Project, Definition 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor)
open Stacks.Cech.LinearCupProduct (tensorPresheafModules)
open scoped TensorProduct

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf O))
  (N : ℤ) [𝒜.complex.IsStrictlyGE N]

/-- The complex underlying a sheaf of differential graded algebras concentrated in degrees
`≥ N`, as a bounded below complex. -/
def differentialGradedComplexPlus :
    CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf O)) :=
  ⟨𝒜.complex, N, inferInstance⟩

/-- The components of the multiplication pairing: multiplication of homogeneous sections,
followed by the identification of the degree `p + q` with `n`. -/
def differentialGradedPairingμ (p q n : ℤ) (h : p + q = n) :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
        (sectionsP O (𝒜.complex.X p))).obj (sectionsP O (𝒜.complex.X q)) ⟶
      sectionsP O (𝒜.complex.X n) :=
  bilinearPairing (𝒜.mul p q) ≫
    (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map (𝒜.complex.XIsoOfEq h).hom

/-- The multiplication pairing on a pure tensor of homogeneous local sections. -/
theorem differentialGradedPairingμ_app_tmul (p q n : ℤ) (h : p + q = n)
    (Z : (Over (⊤ : Opens X))ᵒᵖ) (x : (𝒜.complex.X p).val.obj (op (unop Z).left))
    (y : (𝒜.complex.X q).val.obj (op (unop Z).left)) :
    ((differentialGradedPairingμ 𝒜 p q n h).app Z).hom (x ⊗ₜ y) =
      SheafOfModules.gradedCast (fun k => (𝒜.complex.X k).val.obj (op (unop Z).left)) h
        ((𝒜.mul p q).app (op (unop Z).left) x y) := by
  subst h
  rfl

/-- In degree `p + q` itself the multiplication pairing is multiplication of homogeneous
sections. -/
theorem differentialGradedPairingμ_rfl (p q : ℤ) :
    differentialGradedPairingμ 𝒜 p q (p + q) rfl = bilinearPairing (𝒜.mul p q) := by
  rw [differentialGradedPairingμ, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The pairing of a sheaf of differential graded algebras with itself given by
multiplication.** Its Leibniz rule is the graded Leibniz rule of `𝒜`. -/
def differentialGradedPairing :
    Pairing O (differentialGradedComplexPlus 𝒜 N) (differentialGradedComplexPlus 𝒜 N)
      (differentialGradedComplexPlus 𝒜 N) where
  μ := differentialGradedPairingμ 𝒜
  μ_d p q n h := by
    subst h
    refine NatTrans.ext (funext fun Z => ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_))
    have hl := 𝒜.leibniz p q (op (unop Z).left) x y
    change ((𝒜.complex.d (p + q) (p + q + 1)).val.app (op (unop Z).left))
        (((differentialGradedPairingμ 𝒜 p q (p + q) rfl).app Z).hom (x ⊗ₜ y)) =
      ((differentialGradedPairingμ 𝒜 (p + 1) q (p + q + 1) (by omega)).app Z).hom
          (((𝒜.complex.d p (p + 1)).val.app (op (unop Z).left) x) ⊗ₜ y) +
        p.negOnePow • ((differentialGradedPairingμ 𝒜 p (q + 1) (p + q + 1) (by omega)).app
          Z).hom (x ⊗ₜ ((𝒜.complex.d q (q + 1)).val.app (op (unop Z).left) y))
    refine (congrArg _ (differentialGradedPairingμ_app_tmul 𝒜 p q (p + q) rfl Z x y)).trans
      (hl.trans ?_)
    exact (congrArg₂ (· + ·)
      (differentialGradedPairingμ_app_tmul 𝒜 (p + 1) q (p + q + 1) (by omega) Z _ y).symm
      (congrArg (p.negOnePow • ·)
        (differentialGradedPairingμ_app_tmul 𝒜 p (q + 1) (p + q + 1) (by omega) Z x _).symm))

/-- The multiplication pairing on a pure tensor of homogeneous local sections, as a pairing of
complexes. -/
theorem differentialGradedPairing_app_tmul (p q n : ℤ) (h : p + q = n)
    (Z : (Over (⊤ : Opens X))ᵒᵖ) (x : (𝒜.complex.X p).val.obj (op (unop Z).left))
    (y : (𝒜.complex.X q).val.obj (op (unop Z).left)) :
    (((differentialGradedPairing 𝒜 N).μ p q n h).app Z).hom (x ⊗ₜ y) =
      SheafOfModules.gradedCast (fun k => (𝒜.complex.X k).val.obj (op (unop Z).left)) h
        ((𝒜.mul p q).app (op (unop Z).left) x y) :=
  differentialGradedPairingμ_app_tmul 𝒜 p q n h Z x y

/-! ### Classes of closed global sections -/

variable {𝒜 N}

/-- A global section of `K⁰` killed by the differential `K⁰ ⟶ K¹` is killed by every
differential out of degree zero. -/
theorem globalCocycle_d (K : CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf O)))
    (s : (K.obj.X 0).sections) (hs : (K.obj.X 0).unitHomEquiv.symm s ≫ K.obj.d 0 1 = 0)
    (k : ℤ) (hk : (ComplexShape.up ℤ).Rel 0 k) :
    (K.obj.X 0).unitHomEquiv.symm s ≫ K.obj.d 0 k = 0 := by
  obtain rfl : 1 = k := hk
  exact hs

/-- The morphism of complexes `𝒪_X[0] ⟶ K` attached to a global section `s` of `K⁰` killed by the
differential: `1 ↦ s` in degree zero. -/
def globalCocycleHom (K : CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf O)))
    (s : (K.obj.X 0).sections) (hs : (K.obj.X 0).unitHomEquiv.symm s ≫ K.obj.d 0 1 = 0) :
    singlePlus O (unitSheaf O) 0 ⟶ K :=
  ObjectProperty.homMk (HomologicalComplex.mkHomFromSingle ((K.obj.X 0).unitHomEquiv.symm s)
    (globalCocycle_d K s hs))

/-- **The class in `H⁰(X, K)` of a global section of `K⁰` killed by the differential**: the image
of the class of the unit section of `𝒪_X` under the morphism `𝒪_X[0] ⟶ K` it defines. -/
def globalCocycleClass (K : CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf O)))
    (s : (K.obj.X 0).sections) (hs : (K.obj.X 0).unitHomEquiv.symm s ≫ K.obj.d 0 1 = 0) :
    hypercohomology O K 0 :=
  hypercohomologyMap O (globalCocycleHom K s hs) 0 (sectionClass (unitSheaf O) (oneSection O))

/-- On the term in a retained degree, the inverse of the identification `σ^{≥a}K = K` of a
complex in degrees `≥ a` is the inverse of the identification of terms. -/
@[reassoc]
theorem truncPlusIso_inv_f_comp (K : CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf O)))
    (a n : ℤ) [K.obj.IsStrictlyGE a] (h : a ≤ n) :
    (truncPlusIso O K a).inv.hom.f n ≫
        (StacksDraft.StupidTruncation.stupidTruncGEXIso K.obj a n h).hom = 𝟙 _ := by
  rw [← StacksDraft.StupidTruncation.ιStupidTruncGE_f K.obj a n h]
  exact congrArg (fun φ => φ.hom.f n) (truncPlusIso O K a).inv_hom_id

/-- **The class of a closed global section, lifted to `σ^{≥0}K = K` and projected onto the bottom
term, is the class of that section**: on complexes, the morphism `𝒪_X[0] ⟶ K` attached to `s`,
read into `σ^{≥0}K` and projected onto `K⁰[0]`, is the morphism `𝒪_X[0] ⟶ K⁰[0]` attached to
`s`. -/
theorem globalCocycleHom_comp_truncPlusπ
    (K : CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf O))) [K.obj.IsStrictlyGE 0]
    (s : (K.obj.X 0).sections) (hs : (K.obj.X 0).unitHomEquiv.symm s ≫ K.obj.d 0 1 = 0) :
    globalCocycleHom K s hs ≫ (truncPlusIso O K 0).inv ≫ truncPlusπ K.obj 0 =
      singlePlusMap O ((K.obj.X 0).unitHomEquiv.symm s) := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.from_single_hom_ext ?_)
  have e₁ : (globalCocycleHom K s hs).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫
        (K.obj.X 0).unitHomEquiv.symm s :=
    HomologicalComplex.mkHomFromSingle_f _ (globalCocycle_d K s hs)
  have e₂ : (truncPlusπ K.obj 0).hom.f 0 =
      (StacksDraft.StupidTruncation.stupidTruncGEXIso K.obj 0 0 le_rfl).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.obj.X 0)).inv :=
    StacksDraft.StupidTruncation.stupidTruncGEπ_f K.obj 0
  have e₃ : (singlePlusMap O ((K.obj.X 0).unitHomEquiv.symm s)).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫
        (K.obj.X 0).unitHomEquiv.symm s ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv :=
    HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 _
  refine (HomologicalComplex.comp_f _ _ 0).trans ?_
  refine (congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ 0)).trans ?_
  rw [e₁, e₂, e₃, Category.assoc]
  exact congrArg (fun φ => _ ≫ _ ≫ φ)
    ((Category.assoc _ _ _).symm.trans (truncPlusIso_inv_f_comp_assoc K 0 0 le_rfl _))

variable (𝒜 N)

/-- **The unit of a sheaf of differential graded algebras is closed**: `d 1 = 0`. -/
theorem unitHom_comp_d_eq_zero :
    (𝒜.complex.X 0).unitHomEquiv.symm 𝒜.one ≫ 𝒜.complex.d 0 1 = 0 := by
  apply (_root_.SheafOfModules.unitHomEquiv _).injective
  refine Subtype.ext (funext fun U => ?_)
  rw [_root_.SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply,
    _root_.SheafOfModules.unitHomEquiv_apply_coe]
  have h := 𝒜.leibniz 0 0 U (𝒜.one.eval U) (𝒜.one.eval U)
  simp only [SheafOfModules.gradedCast, Int.reduceAdd, Int.negOnePow_zero, id, Units.val_one,
    one_smul, eq_of_heq (𝒜.mul_one 0 U (𝒜.one.eval U)), eq_of_heq (𝒜.mul_one 1 U _),
    eq_of_heq (𝒜.one_mul 1 U _)] at h
  exact add_eq_left.mp h.symm

/-- **The unit `1 ∈ H⁰(X, 𝒜)` of the hypercohomology of a sheaf of differential graded
algebras**: the class of the global unit section of `𝒜⁰`, which is closed. -/
def differentialGradedUnitClass :
    hypercohomology O (differentialGradedComplexPlus 𝒜 N) 0 :=
  globalCocycleClass (differentialGradedComplexPlus 𝒜 N) 𝒜.one (unitHom_comp_d_eq_zero 𝒜)

end Stacks.Cech.Hypercohomology

end
