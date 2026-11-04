module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupWithUniversalClass
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityPairingCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# The cup product against a dual, contracted

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)`, `E` a perfect object of `D(𝒪_S)` with derived
dual `E^∨ = R𝓗om(E, 𝒪_S)` and evaluation `ε : E^∨ ⊗^𝐋 E ⟶ 𝒪_S` (Stacks 0FPC), and `W` an object
of `D(𝒪_S)`. For every `i` there is the map

`Hⁱ(S, W ⊗^𝐋 E^∨) ⊗_A H⁻ⁱ(S, E) ⟶ H⁰(S, W)`, `ξ ⊗ η ↦ (1 ⊗ ε)(ξ ∪ η)`,

with `∪` the cup product of Section 0FKU. This file shows that it is *represented* by a single
object: with `Z₀ = L(A[-i])` the universal object of degree `i` and `Y = Z₀ ⊗^𝐋 E`, there are
bijections `H⁻ⁱ(S, E) ≃ H⁰(S, Y)` (cup product with the universal class) and
`Hom(Y, W) ≃ Hⁱ(S, W ⊗^𝐋 E^∨)` such that the map sends `ξ ⊗ η` to `H⁰(β)(m η)` for `β` the
morphism attached to `ξ` and `m η` the class attached to `η`. This turns the cup-product pairing
into the evaluation pairing `Hom(Y, W) × H⁰(S, Y) ⟶ H⁰(S, W)`.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.dualContraction` — `1 ⊗ ε : (W ⊗^𝐋 E^∨) ⊗^𝐋 E ⟶ W`,
  read on the derived tensor product of Tag 06YU.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupDualContraction` — the map above.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupTestObject` — `Y = Z₀ ⊗^𝐋 E`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupUniversalEquiv` — `H⁻ⁱ(S, E) ≃ H⁰(S, Y)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupTestClassEquiv` — `Hom(Y, W) ≃ Hⁱ(S, W ⊗^𝐋 E^∨)`.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.bijective_map_comp_dualContraction` — morphisms
  into `W ⊗^𝐋 E^∨` are morphisms out of `- ⊗^𝐋 E` into `W` (Stacks 0FPC).
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupDualContraction_cupTestClassEquiv` — the
  representation of the cup-product pairing.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isPerfect_cupTestObject` — `Y` is perfect.
-/

@[expose] public noncomputable section


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

open Stacks.Cohomology.GlobalKunneth

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
  Stacks.Topology.RingedSpaceSheafifyOpens.hasSheafifyOverOpen
  Stacks.Topology.RingedSpaceSheafifyOpens.wEqualsLocallyBijectiveOverOpen
attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable (S : RingedSpace.{u, u})

/-! ### Pulling the string on the right -/

/-- Pulling the string on the right for the left dual `E^∨` of a perfect `E` (Stacks 0FPC) is
`g ↦ (1 ⊗ ε) ∘ (g ⊗ 1)`, the contraction of `Stacks.SheafOfModules.derivedDualContraction`. -/
theorem tensorRightHomEquiv_derivedDual_symm_apply
    (E : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules S.sheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E)
    (T W : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules S.sheaf))
    (g : T ⟶ ((Stacks.SheafOfModules.derivedTensor S.sheaf).obj W).obj
        (Stacks.SheafOfModules.derivedDual S.sheaf E)) :
    letI := Stacks.SheafOfModules.derivedMonoidalStructure S.sheaf
    (@tensorRightHomEquiv (DerivedCategory
          (Stacks.SheafOfModules.StructureSheafModules S.sheaf)) _
          (Stacks.SheafOfModules.derivedMonoidalStructure S.sheaf) T E
          (Stacks.SheafOfModules.derivedDual S.sheaf E) W
          (Stacks.SheafOfModules.exactPairingDerivedDual S.sheaf E
            (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect _ E hE))).symm g =
      g ▷ E ≫ Stacks.SheafOfModules.derivedDualContraction S.sheaf W E := by
  let := Stacks.SheafOfModules.derivedMonoidalStructure S.sheaf
  let := Stacks.SheafOfModules.exactPairingDerivedDual S.sheaf E
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect _ E hE)
  simp only [tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
  rw [show ε_ E (Stacks.SheafOfModules.derivedDual S.sheaf E) =
    Stacks.SheafOfModules.derivedDualEvaluation S.sheaf E from
    Stacks.SheafOfModules.exactPairingDerivedDual_evaluation' S.sheaf E _]
  rfl

/-- **Morphisms into `W ⊗^𝐋 E^∨` are morphisms out of `- ⊗^𝐋 E` into `W`**, for `E` perfect:
`g ↦ (1 ⊗ ε) ∘ (g ⊗ 1)` is a bijection `Hom(T, W ⊗^𝐋 E^∨) ≃ Hom(T ⊗^𝐋 E, W)`, `E^∨` being a left
dual of `E` (Stacks 0FPC). -/
theorem bijective_whiskerRight_comp_derivedDualContraction
    (E : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules S.sheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E)
    (T W : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules S.sheaf)) :
    letI := Stacks.SheafOfModules.derivedMonoidalStructure S.sheaf
    Function.Bijective (fun g : T ⟶ ((Stacks.SheafOfModules.derivedTensor S.sheaf).obj
        W).obj (Stacks.SheafOfModules.derivedDual S.sheaf E) ↦
      g ▷ E ≫ Stacks.SheafOfModules.derivedDualContraction S.sheaf W E) := by
  let := Stacks.SheafOfModules.derivedMonoidalStructure S.sheaf
  have h := (@tensorRightHomEquiv (DerivedCategory
          (Stacks.SheafOfModules.StructureSheafModules S.sheaf)) _
          (Stacks.SheafOfModules.derivedMonoidalStructure S.sheaf) T E
          (Stacks.SheafOfModules.derivedDual S.sheaf E) W
          (Stacks.SheafOfModules.exactPairingDerivedDual S.sheaf E
            (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect _ E
              hE))).symm.bijective
  rwa [funext (tensorRightHomEquiv_derivedDual_symm_apply S E hE T W)] at h

/-! ### The contraction on the derived tensor product of Tag 06YU -/

variable (W E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))

/-- `W ⊗^𝐋_{𝒪_S} E^∨`, for the derived tensor product of [Stacks, Tag 0FPT] and the derived dual
`E^∨ = R𝓗om(E, 𝒪_S)`. -/
def tensorDual : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) :=
  ((Stacks.SheafOfModules.derivedTensor S.sheaf).obj W).obj
    (Stacks.SheafOfModules.derivedDual S.sheaf E)

/-- **The contraction `1 ⊗ ε : (W ⊗^𝐋 E^∨) ⊗^𝐋 E ⟶ W`**, on the outer derived tensor product of
Tag 06YU in which the cup product of Section 0FKU takes its values: the identification with the
derived tensor product of Tag 0FPT, followed by the re-bracketing, the evaluation
`ε : E^∨ ⊗^𝐋 E ⟶ 𝒪_S` of Stacks 0FPC on the last two factors and the unit constraint. -/
def dualContraction :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).obj
      (tensorDual S W E)).obj E ⟶ W :=
  ((Stacks.SheafOfModules.derivedTensorCanonicalIso S).inv.app (tensorDual S W E)).app E ≫
    Stacks.SheafOfModules.derivedDualContraction S.sheaf W E

/-- The contraction after a morphism `g : T ⟶ W ⊗^𝐋 E^∨` tensored with `E`: the identification
of the two derived tensor products at `(T, E)`, then `g ⊗ 1` on the derived tensor product of
Tag 0FPT and the contraction there. -/
theorem map_app_comp_dualContraction
    (T : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (g : T ⟶ tensorDual S W E) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).map g).app E ≫
        dualContraction S W E =
      ((Stacks.SheafOfModules.derivedTensorCanonicalIso S).inv.app T).app E ≫
        (((Stacks.SheafOfModules.derivedTensor S.sheaf).map g).app E ≫
          Stacks.SheafOfModules.derivedDualContraction S.sheaf W E) := by
  have hn : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).map g).app E ≫
      ((Stacks.SheafOfModules.derivedTensorCanonicalIso S).inv.app (tensorDual S W E)).app E =
      ((Stacks.SheafOfModules.derivedTensorCanonicalIso S).inv.app T).app E ≫
        ((Stacks.SheafOfModules.derivedTensor S.sheaf).map g).app E :=
    NatTrans.congr_app ((Stacks.SheafOfModules.derivedTensorCanonicalIso S).inv.naturality g) E
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Stacks.SheafOfModules.derivedDualContraction S.sheaf W E) hn).trans
      (Category.assoc _ _ _))

/-- The contraction of Tag 0FPT after `g ⊗ 1` is bijective in `g`, for `E` perfect. -/
theorem bijective_derivedTensor_map_comp_derivedDualContraction
    (E : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules S.sheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E)
    (T W : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules S.sheaf)) :
    Function.Bijective (fun g : T ⟶ ((Stacks.SheafOfModules.derivedTensor S.sheaf).obj
        W).obj (Stacks.SheafOfModules.derivedDual S.sheaf E) ↦
      ((Stacks.SheafOfModules.derivedTensor S.sheaf).map g).app E ≫
        Stacks.SheafOfModules.derivedDualContraction S.sheaf W E) :=
  bijective_whiskerRight_comp_derivedDualContraction S E hE T W

/-- **Morphisms into `W ⊗^𝐋 E^∨` are morphisms out of `- ⊗^𝐋 E` into `W`**, on the derived
tensor product of Tag 06YU, for `E` perfect. -/
theorem bijective_map_comp_dualContraction
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E)
    (T : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    Function.Bijective (fun g : T ⟶ tensorDual S W E ↦
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).map g).app E ≫
        dualContraction S W E) := by
  rw [show (fun g : T ⟶ tensorDual S W E ↦
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).map g).app E ≫
        dualContraction S W E) =
      (((Stacks.SheafOfModules.derivedTensorCanonicalIso S).app T).app E).homFromEquiv ∘
        (fun g : T ⟶ tensorDual S W E ↦
          ((Stacks.SheafOfModules.derivedTensor S.sheaf).map g).app E ≫
            Stacks.SheafOfModules.derivedDualContraction S.sheaf W E)
    from funext (map_app_comp_dualContraction S W E T)]
  exact (Equiv.bijective _).comp
    (bijective_derivedTensor_map_comp_derivedDualContraction S E hE T W)

/-! ### The pairing -/

/-- Moving a degree along an equality of degrees commutes with the cohomology of a morphism. -/
theorem homologyFunctor_map_comp_eqToHom {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {n n' : ℤ} (h : n = n') {K L : DerivedCategory C} (φ : K ⟶ L) :
    (DerivedCategory.homologyFunctor C n).map φ ≫
        eqToHom (congrArg (fun m ↦ (DerivedCategory.homologyFunctor C m).obj L) h) =
      eqToHom (congrArg (fun m ↦ (DerivedCategory.homologyFunctor C m).obj K) h) ≫
        (DerivedCategory.homologyFunctor C n').map φ := by
  subst h
  simp

/-- **The map `Hⁱ(S, W ⊗^𝐋 E^∨) ⊗_A H⁻ⁱ(S, E) ⟶ H⁰(S, W)`, `ξ ⊗ η ↦ (1 ⊗ ε)(ξ ∪ η)`**: the
cup product of Section 0FKU at the canonical global cup product, followed by the map induced by
`dualContraction` on cohomology in degree `i + (-i) = 0`. -/
def cupDualContraction (i : ℤ) :
    cohomologyModule (tensorDual S W E) i ⊗ cohomologyModule E (-i) ⟶ cohomologyModule W 0 :=
  cupPairing (globalCupProductCanonical S) (tensorDual S W E) E i (-i) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + -i)).map
      ((baseSections S).map (dualContraction S W E)) ≫
    eqToHom (congrArg (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).obj
      ((baseSections S).obj W)) (add_neg_cancel i))

/-! ### The representing object -/

/-- A morphism out of the free module of rank one is its value at `1`. -/
def homFromFreeRankOneEquiv {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (ModuleCat.of R R ⟶ M) ≃ M where
  toFun φ := φ.hom 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
  left_inv φ := by
    ext
    simp
  right_inv x := by simp

/-- The value at `1` of a composite out of `R ⊗ R`. -/
theorem leftUnitor_inv_tensorHom_comp_hom_one {R : CommRingCat.{u}} {P Q T : ModuleCat.{u} R}
    (φ : ModuleCat.of R R ⟶ P) (ψ : ModuleCat.of R R ⟶ Q) (h : P ⊗ Q ⟶ T) :
    ((λ_ (ModuleCat.of R R)).inv ≫ (φ ⊗ₘ ψ) ≫ h).hom 1 = h.hom (φ.hom 1 ⊗ₜ ψ.hom 1) := by
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply, ModuleCat.MonoidalCategory.tensorHom_tmul]

/-- **The representing object** `Y = Z₀ ⊗^𝐋 E` of degree `i`, for `Z₀ = L(A[-i])` the universal
object of degree `i`. -/
def cupTestObject (i : ℤ) : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).obj
    (cupUniversalObject S i)).obj E

/-- The cup product with the universal class, `η ↦ z₀ ∪ η : H⁻ⁱ(S, E) ⟶ H⁰(S, Y)`, as a map of
`A`-modules. -/
def cupUniversalLinearMap (i : ℤ) :
    cohomologyModule E (-i) →ₗ[baseRing S] cohomologyModule (cupTestObject S E i) 0 :=
  (eqToHom (congrArg (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).obj
      ((baseSections S).obj (cupTestObject S E i))) (add_neg_cancel i))).hom ∘ₗ
    (cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i (-i)).hom ∘ₗ
      TensorProduct.mk (baseRing S) _ _ ((cupUniversalClass S i).hom 1)

/-- The cup product with the universal class is bijective on elements. -/
theorem bijective_cupUniversalLinearMap (i : ℤ) :
    Function.Bijective (cupUniversalLinearMap S E i) := by
  have hcast : Function.Bijective (eqToHom (congrArg (fun n ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).obj
        ((baseSections S).obj (cupTestObject S E i))) (add_neg_cancel i))).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hmid : (fun η : cohomologyModule E (-i) ↦
      (cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i (-i)).hom
        ((cupUniversalClass S i).hom 1 ⊗ₜ η)) =
      (homFromFreeRankOneEquiv _) ∘ (fun η' ↦ (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (cupUniversalClass S i ⊗ₘ η') ≫
          cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i (-i)) ∘
        (homFromFreeRankOneEquiv _).symm := by
    funext η
    simp only [Function.comp_apply, homFromFreeRankOneEquiv, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk]
    rw [leftUnitor_inv_tensorHom_comp_hom_one]
    simp
  have h₁ : Function.Bijective (fun η : cohomologyModule E (-i) ↦
      (cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i (-i)).hom
        ((cupUniversalClass S i).hom 1 ⊗ₜ η)) := by
    rw [hmid]
    exact (Equiv.bijective _).comp
      ((bijective_cupUniversalClass_cupPairing_canonical S E i (-i)).comp (Equiv.bijective _))
  exact hcast.comp h₁

/-- **`H⁻ⁱ(S, E) ≃ H⁰(S, Y)`**, the cup product with the universal class of degree `i`. -/
def cupUniversalEquiv (i : ℤ) :
    cohomologyModule E (-i) ≃ₗ[baseRing S] cohomologyModule (cupTestObject S E i) 0 :=
  LinearEquiv.ofBijective (cupUniversalLinearMap S E i) (bijective_cupUniversalLinearMap S E i)

/-- **`Hom(Y, W) ≃ Hⁱ(S, W ⊗^𝐋 E^∨)`**, for `E` perfect: a morphism `β : Y = Z₀ ⊗^𝐋 E ⟶ W` is
`(1 ⊗ ε) ∘ (g ⊗ 1)` for exactly one `g : Z₀ ⟶ W ⊗^𝐋 E^∨` (Stacks 0FPC), and `g` is attached to
exactly one class `Hⁱ(g)(z₀)` (the universal property of `z₀`). -/
def cupTestClassEquiv (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E) (i : ℤ) :
    (cupTestObject S E i ⟶ W) ≃ cohomologyModule (tensorDual S W E) i :=
  (Equiv.ofBijective _
      (bijective_map_comp_dualContraction S W E hE (cupUniversalObject S i))).symm.trans
    ((Equiv.ofBijective _ (bijective_cupUniversalClass_comp S i (tensorDual S W E))).trans
      (homFromFreeRankOneEquiv _))

/-- The class attached to `β`, written out: `Hⁱ(g)(z₀)` for the `g` with
`(1 ⊗ ε) ∘ (g ⊗ 1) = β`. -/
theorem cupTestClassEquiv_apply (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E)
    (i : ℤ) (β : cupTestObject S E i ⟶ W) :
    cupTestClassEquiv S W E hE i β =
      (cupUniversalClass S i ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
        ((baseSections S).map ((Equiv.ofBijective _ (bijective_map_comp_dualContraction S W E hE
          (cupUniversalObject S i))).symm β))).hom 1 :=
  rfl

/-- The morphism form of `cupDualContraction_cupTestClassEquiv`. -/
theorem cupDualContraction_comp_eq (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E)
    (i : ℤ) (β : cupTestObject S E i ⟶ W)
    (ηm : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule E (-i)) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((cupUniversalClass S i ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
          ((baseSections S).map ((Equiv.ofBijective _ (bijective_map_comp_dualContraction S W E hE
            (cupUniversalObject S i))).symm β))) ⊗ₘ
          (ηm ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (-i)).map
            ((baseSections S).map (𝟙 E)))) ≫ cupDualContraction S W E i =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (cupUniversalClass S i ⊗ₘ ηm) ≫
        cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i (-i) ≫
          eqToHom (congrArg (fun n ↦ (DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing S)) n).obj ((baseSections S).obj (cupTestObject S E i)))
            (add_neg_cancel i)) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) 0).map
            ((baseSections S).map β) := by
  set g := (Equiv.ofBijective _ (bijective_map_comp_dualContraction S W E hE
    (cupUniversalObject S i))).symm β
  have hg : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).map g).app E ≫
      dualContraction S W E = β :=
    (Equiv.ofBijective _ (bijective_map_comp_dualContraction S W E hE
      (cupUniversalObject S i))).apply_symm_apply β
  have nat := cupPairing_naturality (globalCupProductCanonical S) g (𝟙 E) i (-i)
    (cupUniversalClass S i) ηm
  have hu : (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map (g ×ₘ 𝟙 E) ≫
        dualContraction S W E = β :=
    (congrArg (· ≫ dualContraction S W E)
      (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right _ g E)).trans hg
  have e₁ := ((baseSections S).map_comp _ _).symm.trans (congrArg (baseSections S).map hu)
  have e₂ := ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + -i)).map_comp
    _ _).symm.trans (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S))
      (i + -i)).map e₁)
  have htail := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eqToHom (congrArg
    (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).obj
      ((baseSections S).obj W)) (add_neg_cancel i))) e₂).trans
    (homologyFunctor_map_comp_eqToHom (add_neg_cancel i) ((baseSections S).map β)))
  have h₂ := nat =≫ ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + -i)).map
        ((baseSections S).map (dualContraction S W E)) ≫
      eqToHom (congrArg (fun n ↦
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).obj
          ((baseSections S).obj W)) (add_neg_cancel i)))
  simp only [Category.assoc] at h₂
  exact h₂.trans (congrArg (fun t ↦ (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
    (cupUniversalClass S i ⊗ₘ ηm) ≫
      cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i (-i) ≫ t) htail)

/-- **The representation of the cup-product pairing.** For `E` perfect, `β : Y ⟶ W` and
`η ∈ H⁻ⁱ(S, E)`, the contraction of the cup product of the class attached to `β` with `η` is the
image under `H⁰(β)` of the class attached to `η`:

`(1 ⊗ ε)(ξ_β ∪ η) = H⁰(β)(z₀ ∪ η)`. -/
theorem cupDualContraction_cupTestClassEquiv
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E) (i : ℤ)
    (β : cupTestObject S E i ⟶ W) (η : cohomologyModule E (-i)) :
    (cupDualContraction S W E i).hom (cupTestClassEquiv S W E hE i β ⊗ₜ η) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) 0).map
        ((baseSections S).map β)).hom (cupUniversalEquiv S E i η) := by
  have h := congrArg (fun φ ↦ φ.hom (1 : baseRing S))
    (cupDualContraction_comp_eq S W E hE i β ((homFromFreeRankOneEquiv _).symm η))
  dsimp only at h
  rw [leftUnitor_inv_tensorHom_comp_hom_one, leftUnitor_inv_tensorHom_comp_hom_one] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rw [cupTestClassEquiv_apply]
    congr 2
    simp [homFromFreeRankOneEquiv]
  · simp [homFromFreeRankOneEquiv, cupUniversalEquiv, cupUniversalLinearMap]
    rfl

/-- **The representing object `Y = Z₀ ⊗^𝐋 E` is perfect**, for `E` perfect. -/
theorem isPerfect_cupTestObject (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) E)
    (i : ℤ) : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) (cupTestObject S E i) := by
  have h₀ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S)
      (Stacks.Cohomology.DerivedProjectionFormula.singleUnit S) :=
    Stacks.SheafOfModules.isPerfect_derivedStructureSheaf_space S
  have h₁ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S) (cupUniversalObject S i) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
      ((((DerivedCategory.singleFunctors (SheafOfModules.{u} (structureSheafRing S))).shiftIso
          (-i) i 0 (by omega)).app (SheafOfModules.unit (structureSheafRing S))) ≪≫
        (pullbackBaseShiftIso S i).symm)
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift.{u, u + 1} h₀ (-i))
  exact AlgebraicGeometry.RingedSpace.isPerfect_canonicalDerivedTensorProduct S _ _ h₁ hE

end Stacks.Cohomology.DerivedGlobalCupProduct

end
