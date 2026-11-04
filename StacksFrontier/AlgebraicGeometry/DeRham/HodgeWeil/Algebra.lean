module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CupProductLaws
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupRightUnit
public import StacksFrontier.Algebra.DirectSum.RangeGrading

/-!
# Hodge cohomology as a graded commutative algebra

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^p` be the exterior powers of its sheaf of relative differentials. The Hodge cohomology

`H^*_{Hodge}(X/S) = ⨁_{n ∈ 𝐙} H^n_{Hodge}(X/S)`, `H^n_{Hodge}(X/S) = ⨁_{p + q = n} H^q(X, Ω^p)`,

with the cup product of Section 50.5 (Tag 0FM4), is a `𝐙`-graded ring, graded commutative by
Tag 0FM5: `a ∪ b = (-1)^{ij} b ∪ a` for `a` of degree `i` and `b` of degree `j`. Its unit is the
class of the global function `1 ∈ Γ(X, Ω^0)`. Over a commutative ring `k` mapping to the ring
`R = Γ(X, A)` of global sections of the base ring sheaf, over which the groups `H^q(X, Ω^p)` are
modules, it is a graded `k`-algebra. This is the datum (D1) of Weil Cohomology Theories,
Section 0FID, that Remark 0FWE attaches to Hodge cohomology.

## Main definitions

* `Stacks.HodgeWeil.hodgeOne`: the unit class `1 ∈ H^0(X, Ω^0)`.
* `Stacks.HodgeWeil.hodgePiece`: `H^n_{Hodge}(X/S)` for `n ∈ 𝐙`.
* `Stacks.HodgeWeil.hodgePieceMul`: the cup product
  `H^n_{Hodge}(X/S) × H^m_{Hodge}(X/S) ⟶ H^{n + m}_{Hodge}(X/S)`.
* `Stacks.HodgeWeil.hodgeGRing`: the graded ring structure on `n ↦ H^n_{Hodge}(X/S)`.
* `Stacks.HodgeWeil.hodgeAlgebra`: **the ring `H^*_{Hodge}(X/S)`**.
* `Stacks.HodgeWeil.hodgeGAlgebra`, `Stacks.HodgeWeil.hodgeAlgebraAlgebra`: the graded
  `k`-algebra structure, for a ring map `σ : k →+* R`.
* `Stacks.HodgeWeil.hodgeGrade`, `Stacks.HodgeWeil.hodgeGradedAlgebra`: the grading of
  `H^*_{Hodge}(X/S)` by the `k`-submodules `H^n_{Hodge}(X/S)`.

## Main results

* `Stacks.HodgeWeil.hodgeOne_hodgeCohomologyCup` and
  `Stacks.HodgeWeil.hodgeCohomologyCup_hodgeOne`: **`1` is a two-sided unit** for the cup product
  on Hodge cohomology.
* `Stacks.HodgeWeil.hodgePieceMul_assoc`: the cup product is associative (Tag 0FM5).
* `Stacks.HodgeWeil.hodgePieceMul_comm`: the cup product is graded commutative (Tag 0FM5).
* `Stacks.HodgeWeil.hodgeAlgebra_graded_comm`: **the Koszul sign rule** on `H^*_{Hodge}(X/S)`.
* `Stacks.HodgeWeil.hodgePieceEquiv`: in degree `n ≥ 0` the piece is the base's
  `AlgebraicGeometry.SheafOfModules.hodgeCohomology`; `Stacks.HodgeWeil.subsingleton_hodgePiece`:
  it vanishes in negative degrees.

## Implementation notes

The summands of `H^n_{Hodge}(X/S)` are indexed by pairs `(p, q)` of natural numbers with
`p + q = n` in `𝐙`, so the negative pieces are zero because their index set is empty. The
product is the biadditive extension of the cup product of pure bidegrees
`AlgebraicGeometry.SheafOfModules.hodgeCohomologyCup`, and the two laws are those of the base,
`AlgebraicGeometry.SheafOfModules.hodgeCupProduct_assoc` and
`AlgebraicGeometry.SheafOfModules.hodgeCupProduct_comm`.

The unit laws are proved for the right unit: the cup product of Section 0FKU with the class of a
global section `u` of `Ω^0` is right multiplication by `u`
(`Stacks.DeRham.GysinCupHodge.canonicalPairingModule_unitComplexSectionMap`, for the ringed space
`(X, A)`), and `ω ∧ 1 = ω`. The left unit law follows from graded commutativity, the sign being
`(-1)^{0 · n} = 1`.

The ring `R` is the section ring of a sheaf of rings, which instance search does not see as
commutative, and the field of the source acts through a ring map to it which is not canonical
in this generality. The scalars therefore act through an explicit ring map `σ : k →+* R`; the
module, algebra and grading structures it defines are definitions, not instances. The case of
`R` itself is `σ = Stacks.HodgeWeil.globalSectionsRingHom`.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FM5](https://stacks.math.columbia.edu/tag/0FM5)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.SheafOfModules
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyMap cohomologyCast
  globalCycleClass unitCycleHom)
open scoped TensorProduct DirectSum

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### The unit class -/

/-- The global function `1`, the unit of the exterior algebra, as a global section of `Ω^0`. -/
def formsOne : (deRhamTerm B 0).val.sections :=
  B.exterior.one

/-- **The unit class** `1 ∈ H^0(X, Ω^0)`: the class of the global function `1`. -/
def hodgeOne : hodgeCohomologyComponent B 0 0 :=
  ofHodgeComponentBase B ((hodgeComponentIso B 0 0).hom.hom
    ((cohomologyMap (S := baseRingedSpace A)
      (Stacks.DeRham.GysinCupHodge.unitComplexSectionMap (X := baseRingedSpace A)
        (@deRhamTerm X A φ B 0) (formsOne B)) 0).hom
      ((globalCycleClass (S := baseRingedSpace A) (unitCycleHom (baseRingedSpace A))).hom 1)))

/-! ### The unit laws -/

/-- The multiplication of complexes concentrated in degree `0` induced by a morphism
`F ⊗_A G ⟶ H` is the multiplication `Stacks.DeRham.GysinCupHodge.singleTensorMult` of the ringed
space `(X, A)` in degrees `0`, `0`. -/
theorem singleMultiplication_eq_singleTensorMult
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (μ : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) :
    singleMultiplication μ =
      Stacks.DeRham.GysinCupHodge.singleTensorMult (X := baseRingedSpace A) μ 0 0 0 rfl := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    change (HomologicalComplex.mkHomToSingle (K := HomologicalComplex.mapBifunctor
        (singleNat F) (singleNat G) (sheafTensor.{u, u, u, u, u} A) (up ℕ))
        (singleMultiplicationX μ) (fun i hi => by change i + 1 = 0 at hi; omega)).f 0 =
      (HomologicalComplex.mkHomToSingle (K := HomologicalComplex.mapBifunctor
        (singleNat F) (singleNat G) (sheafTensor.{u, u, u, u, u} A) (up ℕ))
        (HomologicalComplex.mapBifunctorDesc fun a b _ =>
          Stacks.DeRham.GysinCupHodge.singleTensorMultSummand (X := baseRingedSpace A) μ 0 0 a b)
        (fun i hi => by change i + 1 = 0 at hi; omega)).f 0
    rw [HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomToSingle_f]
    refine congrArg (· ≫ _) (HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_)
    rw [singleMultiplicationX, HomologicalComplex.ι_mapBifunctorDesc]
    refine Eq.trans ?_ (HomologicalComplex.ι_mapBifunctorDesc
      (fun a b _ => Stacks.DeRham.GysinCupHodge.singleTensorMultSummand (X := baseRingedSpace A)
        μ 0 0 a b) i₁ i₂ h).symm
    change i₁ + i₂ = 0 at h
    obtain rfl : i₁ = 0 := by omega
    obtain rfl : i₂ = 0 := by omega
    dsimp only [Stacks.DeRham.GysinCupHodge.singleTensorMultSummand]
    rw [dite_eq_left ⟨rfl, rfl⟩]
    exact (NatTrans.naturality_assoc _ _ _).symm
  · exact (HomologicalComplex.isZero_single_obj_X (up ℕ) 0 H n hn).eq_of_tgt _ _

/-- **Right multiplication by the global function `1` is the identity**: `ω ∧ 1 = ω`, the degree
`p + 0` being `p` definitionally. -/
theorem rightMulTensor_exteriorProductComponent_formsOne (p : ℕ) :
    Stacks.DeRham.GysinCupHodge.rightMulTensor (X := baseRingedSpace A)
      (exteriorProductComponent B p 0) (formsOne B) = 𝟙 (deRhamTerm B p) := by
  refine _root_.SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U => ?_)
  ext ω
  show multValue B (exteriorProductComponent B p 0) U ω ((formsOne B).eval U) = ω
  rw [multValue_exteriorProductComponent]
  exact eq_of_heq (B.exterior.mul_one (p : ℤ) U ω)

/-- **The cup product with the class of a global section is right multiplication by it**, for the
cup product of Section 0FKU of the ringed space `(X, A)` along a multiplication `μ` of sheaves
concentrated in degree `0`. -/
theorem canonicalPairingModule_singleMultiplication_unitComplexSectionMap
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (μ : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) (s : G.val.sections) (i : ℤ)
    (x : cohomologyModule (moduleDerived (singleNat F)) i) :
    (canonicalPairingModule (singleMultiplication μ) i 0).hom
        (x ⊗ₜ (cohomologyMap (S := baseRingedSpace A)
          (Stacks.DeRham.GysinCupHodge.unitComplexSectionMap (X := baseRingedSpace A) G s) 0).hom
          ((globalCycleClass (S := baseRingedSpace A) (unitCycleHom (baseRingedSpace A))).hom 1)) =
      (cohomologyCast (moduleDerived (singleNat H)) (add_zero i).symm).hom
        ((cohomologyMap (S := baseRingedSpace A) (HomologicalComplex.extendMap
          ((HomologicalComplex.single _ (up ℕ) 0).map
            (Stacks.DeRham.GysinCupHodge.rightMulTensor (X := baseRingedSpace A) μ s))
          embeddingUpNat) i).hom x) := by
  rw [singleMultiplication_eq_singleTensorMult]
  exact Stacks.DeRham.GysinCupHodge.canonicalPairingModule_unitComplexSectionMap
    (X := baseRingedSpace A) μ s i x

/-- Right multiplication by the global function `1`, placed in degree `0`, induces the identity
on cohomology. -/
theorem cohomologyMap_rightMulTensor_formsOne (p : ℕ) (i : ℤ)
    (x : cohomologyModule (moduleDerived (singleNat (deRhamTerm B p))) i) :
    (cohomologyMap (S := baseRingedSpace A) (HomologicalComplex.extendMap
        ((HomologicalComplex.single
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
          (up ℕ) 0).map
          (Stacks.DeRham.GysinCupHodge.rightMulTensor (X := baseRingedSpace A)
            (exteriorProductComponent B p 0) (formsOne B))) embeddingUpNat) i).hom x = x := by
  rw [rightMulTensor_exteriorProductComponent_formsOne, CategoryTheory.Functor.map_id,
    HomologicalComplex.extendMap_id]
  exact Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_id_apply _ i x

/-- **The unit class is a right unit for the cup product of Section 0FKU along the wedge
product**: `ξ ∪ 1 = ξ` for `ξ ∈ H^q(X, Ω^p)`, the product read in degree `q`. -/
theorem hodgeComponentCup_hodgeOne (p : ℕ) (q : ℤ) (ξ : hodgeCohomologyComponent B p q) :
    hodgeComponentCup B (exteriorProductComponent B p 0) q 0 ξ (hodgeOne B) =
      reindexHodgeDeg B (add_zero q).symm ξ := by
  have hone : (hodgeComponentIso B 0 0).inv.hom (toHodgeComponentBase B (hodgeOne B)) =
      (cohomologyMap (S := baseRingedSpace A)
        (Stacks.DeRham.GysinCupHodge.unitComplexSectionMap (X := baseRingedSpace A)
          (@deRhamTerm X A φ B 0) (formsOne B)) 0).hom
        ((globalCycleClass (S := baseRingedSpace A) (unitCycleHom (baseRingedSpace A))).hom 1) :=
    hodgeComponentIso_inv_hom_apply B _
  have hc := canonicalPairingModule_singleMultiplication_unitComplexSectionMap
    (exteriorProductComponent B p 0) (formsOne B) q
    ((hodgeComponentIso B p q).inv.hom (toHodgeComponentBase B ξ))
  have hid := cohomologyMap_rightMulTensor_formsOne B p q
    ((hodgeComponentIso B p q).inv.hom (toHodgeComponentBase B ξ))
  refine (congrArg (fun t => ofHodgeComponentBase B ((hodgeComponentIso B p (q + 0)).hom.hom
    ((canonicalPairingModule (singleMultiplication (exteriorProductComponent B p 0)) q 0).hom
      ((hodgeComponentIso B p q).inv.hom (toHodgeComponentBase B ξ) ⊗ₜ t)))) hone).trans ?_
  refine (congrArg (fun t => ofHodgeComponentBase B ((hodgeComponentIso B p (q + 0)).hom.hom t))
    hc).trans ?_
  refine (congrArg (fun t => ofHodgeComponentBase B ((hodgeComponentIso B p (q + 0)).hom.hom
    ((cohomologyCast (moduleDerived (singleNat (deRhamTerm B p))) (add_zero q).symm).hom t)))
    hid).trans ?_
  refine (hodgeComponentIso_eqToHom B (add_zero q).symm _).trans ?_
  exact congrArg (reindexHodgeDeg B (add_zero q).symm)
    (ModuleCat.hom_inv_apply (hodgeComponentIso B p q) ξ)

/-- **The unit class is a right unit for the cup product on Hodge cohomology**: `ξ ∪ 1 = ξ` for
`ξ ∈ H^q(X, Ω^p)`, the product read in bidegree `(p, q)`. -/
theorem hodgeCohomologyCup_hodgeOne (p : ℕ) (q : ℤ) (ξ : hodgeCohomologyComponent B p q) :
    reindexHodgeDeg B (add_zero q) (hodgeCohomologyCup B p 0 q 0 ξ (hodgeOne B)) = ξ := by
  have h : hodgeCohomologyCup B p 0 q 0 ξ (hodgeOne B) =
      hodgeComponentCup B (exteriorProductComponent B p 0) q 0 ξ (hodgeOne B) := by
    rw [hodgeCohomologyCup, hodgeCupProduct, Nat.cast_zero, mul_zero, Int.negOnePow_zero,
      Units.val_one, one_smul]
    rfl
  rw [h, hodgeComponentCup_hodgeOne]
  exact eq_of_heq ((reindexHodgeDeg_heq B _ _).trans (reindexHodgeDeg_heq B _ _))

/-- **The unit class is a left unit for the cup product on Hodge cohomology**: `1 ∪ ξ = ξ` for
`ξ ∈ H^q(X, Ω^p)`, the product read in bidegree `(p, q)`. By graded commutativity, the sign
being `(-1)^{0 · (p + q)} = 1`. -/
theorem hodgeOne_hodgeCohomologyCup (p : ℕ) (q : ℤ) (ξ : hodgeCohomologyComponent B p q) :
    reindexHodge B (zero_add p) (zero_add q) (hodgeCohomologyCup B 0 p 0 q (hodgeOne B) ξ) = ξ := by
  rw [hodgeCohomologyCup, hodgeCupProduct_comm B (hodgeCohomologyCupProduct B)]
  have hs : (((((0 : ℕ) : ℤ) + (0 : ℤ)) * ((p : ℤ) + q)).negOnePow : ℤ) = 1 := by simp
  rw [hs, one_smul]
  refine eq_of_heq ((reindexHodge_heq B _ _ _).trans ((reindexHodge_heq B _ _ _).trans ?_))
  exact (reindexHodgeDeg_heq B (add_zero q) _).symm.trans
    (heq_of_eq (hodgeCohomologyCup_hodgeOne B p q ξ))

/-- The unit class is a left unit, up to heterogeneous equality. -/
theorem hodgeOne_hodgeCohomologyCup_heq (p : ℕ) (q : ℤ) (ξ : hodgeCohomologyComponent B p q) :
    HEq (hodgeCohomologyCup B 0 p 0 q (hodgeOne B) ξ) ξ :=
  (reindexHodge_heq B (zero_add p) (zero_add q) _).symm.trans
    (heq_of_eq (hodgeOne_hodgeCohomologyCup B p q ξ))

/-- The unit class is a right unit, up to heterogeneous equality. -/
theorem hodgeCohomologyCup_hodgeOne_heq (p : ℕ) (q : ℤ) (ξ : hodgeCohomologyComponent B p q) :
    HEq (hodgeCohomologyCup B p 0 q 0 ξ (hodgeOne B)) ξ :=
  (reindexHodgeDeg_heq B (add_zero q) _).symm.trans
    (heq_of_eq (hodgeCohomologyCup_hodgeOne B p q ξ))

/-- Reindexing the cohomological degree commutes with the action of the global sections of the
base ring sheaf. -/
theorem reindexHodgeDeg_smul {p : ℕ} {q q' : ℤ} (hq : q = q')
    (a : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))
    (x : hodgeCohomologyComponent B p q) :
    reindexHodgeDeg B hq (a • x) = a • reindexHodgeDeg B hq x := by
  subst hq; rfl

/-- The cup product on Hodge cohomology is linear over the global sections of the base ring sheaf
in its first variable. -/
theorem hodgeCohomologyCup_smul_left (p p' : ℕ) (q q' : ℤ)
    (a : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))
    (ξ : hodgeCohomologyComponent B p q)
    (ζ : hodgeCohomologyComponent B p' q') :
    hodgeCohomologyCup B p p' q q' (a • ξ) ζ = a • hodgeCohomologyCup B p p' q q' ξ ζ := by
  rw [hodgeCohomologyCup, hodgeCohomologyCup, hodgeCupProduct, hodgeCupProduct,
    (hodgeCohomologyCupProduct B).cup_smul_left, smul_comm]

/-- The cup product on Hodge cohomology is linear over the global sections of the base ring sheaf
in its second variable. -/
theorem hodgeCohomologyCup_smul_right (p p' : ℕ) (q q' : ℤ)
    (a : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))
    (ξ : hodgeCohomologyComponent B p q)
    (ζ : hodgeCohomologyComponent B p' q') :
    hodgeCohomologyCup B p p' q q' ξ (a • ζ) = a • hodgeCohomologyCup B p p' q q' ξ ζ := by
  rw [hodgeCohomologyCup, hodgeCohomologyCup, hodgeCupProduct, hodgeCupProduct,
    (hodgeCohomologyCupProduct B).cup_smul_right, smul_comm]

/-! ### Hodge cohomology in every integer degree -/

/-- The bidegrees `(p, q)` of total degree `n ∈ ℤ`, the index set of the summands of `H^n_{Hodge}`;
it is empty for `n < 0`. -/
abbrev HodgeBidegreeInt (n : ℤ) :=
  {i : ℕ × ℕ // ((i.1 + i.2 : ℕ) : ℤ) = n}

/-- **Hodge cohomology in degree `n ∈ ℤ`**,
`H^n_{Hodge}(X/S) = ⨁_{p + q = n} H^q(X, Ω^p)`, as a module over the global sections of the base
ring sheaf. -/
abbrev hodgePiece (n : ℤ) : Type u :=
  DirectSum (HodgeBidegreeInt n) fun i =>
    (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)

/-- `H^n_{Hodge}(X/S)` vanishes in negative degrees. -/
theorem subsingleton_hodgePiece {n : ℤ} (hn : n < 0) : Subsingleton (hodgePiece B n) := by
  have : IsEmpty (HodgeBidegreeInt n) := ⟨fun i => by have := i.2; omega⟩
  exact inferInstanceAs (Subsingleton (Π₀ i : HodgeBidegreeInt n, _))

/-- The bidegrees of total degree `n` as an integer are those of total degree `n`. -/
def hodgeBidegreeIntEquiv (n : ℕ) : HodgeBidegreeInt (n : ℤ) ≃ HodgeBidegree n :=
  Equiv.subtypeEquivRight fun _ => Nat.cast_inj

/-- **In nonnegative degrees `H^n_{Hodge}(X/S)` is the base's `hodgeCohomology`.** -/
def hodgePieceEquiv (n : ℕ) :
    hodgePiece B (n : ℤ) ≃ₗ[(AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤)]
      hodgeCohomology B n :=
  DirectSum.lequivCongrLeft _ (hodgeBidegreeIntEquiv n)

/-- `hodgePieceEquiv` on a class of pure bidegree. -/
theorem hodgePieceEquiv_of (n : ℕ) (i : HodgeBidegreeInt (n : ℤ))
    (x : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ)) :
    hodgePieceEquiv B n (DirectSum.of _ i x) =
      DirectSum.of (fun i : HodgeBidegree n =>
        (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) (hodgeBidegreeIntEquiv n i) x :=
  DirectSum.lequivCongrLeft_lof
    ((AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))
    (M := fun i : HodgeBidegreeInt (n : ℤ) =>
      (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u))
    (e := hodgeBidegreeIntEquiv n) (i := i) (k := hodgeBidegreeIntEquiv n i) rfl x x rfl

/-- A class of `H^n_{Hodge}` read in another, equal, degree. -/
def castHodgePiece {n n' : ℤ} (h : n = n') : hodgePiece B n →+ hodgePiece B n' := by
  subst h
  exact AddMonoidHom.id _

/-- Reading a class of pure bidegree in an equal degree. -/
theorem castHodgePiece_of {n n' : ℤ} (h : n = n') (i : HodgeBidegreeInt n)
    (x : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ)) :
    castHodgePiece B h (DirectSum.of _ i x) = DirectSum.of _ ⟨i.1, i.2.trans h⟩ x := by
  subst h
  rfl

/-- Reading a class in an equal degree does not change it up to heterogeneous equality. -/
theorem castHodgePiece_heq {n n' : ℤ} (h : n = n') (x : hodgePiece B n) :
    HEq (castHodgePiece B h x) x := by
  subst h
  rfl

/-- Reading a class in an equal degree commutes with the action of the global sections of the
base ring sheaf. -/
theorem castHodgePiece_smul {n n' : ℤ} (h : n = n')
    (a : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))
    (x : hodgePiece B n) : castHodgePiece B h (a • x) = a • castHodgePiece B h x := by
  subst h
  rfl

/-- A pair of a degree and a class in that degree is determined by the class read in any equal
degree. -/
theorem gradedMonoid_mk_castHodgePiece {n n' : ℤ} (h : n = n') (x : hodgePiece B n) :
    (GradedMonoid.mk n x : GradedMonoid (hodgePiece B)) =
      GradedMonoid.mk n' (castHodgePiece B h x) := by
  subst h
  rfl

/-- The bidegree of a product. -/
theorem hodgeBidegreeInt_add {n m : ℤ} (i : HodgeBidegreeInt n) (j : HodgeBidegreeInt m) :
    (((i.1.1 + j.1.1, i.1.2 + j.1.2).1 + (i.1.1 + j.1.1, i.1.2 + j.1.2).2 : ℕ) : ℤ) = n + m := by
  have hi := i.2
  have hj := j.2
  dsimp only at hi hj ⊢
  omega

/-- The summand of the cup product `H^n_{Hodge} × H^m_{Hodge} ⟶ H^{n + m}_{Hodge}` at a pair of
bidegrees: the cup product of pure bidegrees `hodgeCohomologyCup`. -/
def hodgePieceSummand {n m : ℤ} (i : HodgeBidegreeInt n) (j : HodgeBidegreeInt m) :
    (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u) →+
      (hodgeCohomologyComponent B j.1.1 (j.1.2 : ℤ) : Type u) →+ hodgePiece B (n + m) :=
  AddMonoidHom.mk' (fun ξ => AddMonoidHom.mk' (fun ζ =>
      DirectSum.of (fun k : HodgeBidegreeInt (n + m) =>
          (hodgeCohomologyComponent B k.1.1 (k.1.2 : ℤ) : Type u))
        ⟨(i.1.1 + j.1.1, i.1.2 + j.1.2), hodgeBidegreeInt_add i j⟩
        (reindexHodgeDeg B (Nat.cast_add i.1.2 j.1.2).symm
          (hodgeCohomologyCup B i.1.1 j.1.1 (i.1.2 : ℤ) (j.1.2 : ℤ) ξ ζ)))
      (fun ζ ζ' => by
        rw [hodgeCupProduct_add_right, reindexHodgeDeg_add, map_add]))
    (fun ξ ξ' => by
      ext ζ
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [hodgeCupProduct_add_left, reindexHodgeDeg_add, map_add])

/-- **The cup product** `∪ : H^n_{Hodge}(X/S) × H^m_{Hodge}(X/S) ⟶ H^{n + m}_{Hodge}(X/S)` for
`n, m ∈ ℤ`: the biadditive extension of the cup product of pure bidegrees
`AlgebraicGeometry.SheafOfModules.hodgeCohomologyCup`. -/
def hodgePieceMul (n m : ℤ) : hodgePiece B n →+ hodgePiece B m →+ hodgePiece B (n + m) :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.toAddMonoid fun j => (hodgePieceSummand B i j).flip).flip

/-- On classes of pure bidegree the cup product is the cup product of pure bidegrees. -/
theorem hodgePieceMul_of {n m : ℤ} (i : HodgeBidegreeInt n) (j : HodgeBidegreeInt m)
    (ξ : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ))
    (ζ : hodgeCohomologyComponent B j.1.1 (j.1.2 : ℤ)) :
    hodgePieceMul B n m (DirectSum.of _ i ξ) (DirectSum.of _ j ζ) =
      DirectSum.of (fun k : HodgeBidegreeInt (n + m) =>
          (hodgeCohomologyComponent B k.1.1 (k.1.2 : ℤ) : Type u))
        ⟨(i.1.1 + j.1.1, i.1.2 + j.1.2), hodgeBidegreeInt_add i j⟩
        (reindexHodgeDeg B (Nat.cast_add i.1.2 j.1.2).symm
          (hodgeCohomologyCup B i.1.1 j.1.1 (i.1.2 : ℤ) (j.1.2 : ℤ) ξ ζ)) := by
  simp only [hodgePieceMul, DirectSum.toAddMonoid_of, AddMonoidHom.flip_apply]
  rfl

/-- **The cup product on `H^*_{Hodge}(X/S)` is associative**, the two sides read in the same
degree. -/
theorem hodgePieceMul_assoc (n m l : ℤ) (x : hodgePiece B n) (y : hodgePiece B m)
    (z : hodgePiece B l) :
    castHodgePiece B (add_assoc n m l) (hodgePieceMul B (n + m) l (hodgePieceMul B n m x y) z) =
      hodgePieceMul B n (m + l) x (hodgePieceMul B m l y z) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx']
  | of i ξ =>
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp [hy, hy']
  | of j ζ =>
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z z' hz hz' => simp [hz, hz']
  | of k θ =>
  rw [hodgePieceMul_of, hodgePieceMul_of, hodgePieceMul_of, hodgePieceMul_of, castHodgePiece_of]
  refine DirectSum.of_eq_of_heq
    (Subtype.ext (Prod.ext (add_assoc _ _ _) (add_assoc _ _ _))) ?_
  refine (reindexHodgeDeg_heq B _ _).trans (HEq.trans ?_ (reindexHodgeDeg_heq B _ _).symm)
  refine (hodgeCupProduct_heq B (Nat.cast_add i.1.2 j.1.2) rfl
    (reindexHodgeDeg_heq B _ _) HEq.rfl).trans (HEq.trans ?_
      (hodgeCupProduct_heq B rfl (Nat.cast_add j.1.2 k.1.2) HEq.rfl
        (reindexHodgeDeg_heq B _ _)).symm)
  exact (reindexHodge_heq B _ _ _).symm.trans
    (heq_of_eq (hodgeCupProduct_assoc B (hodgeCohomologyCupProduct B) _ _ _ _ _ _ ξ ζ θ))

/-- **The cup product on `H^*_{Hodge}(X/S)` is graded commutative**: `x ∪ y = (-1)^{nm} y ∪ x`
for `x` of degree `n` and `y` of degree `m`. -/
theorem hodgePieceMul_comm (n m : ℤ) (x : hodgePiece B n) (y : hodgePiece B m) :
    hodgePieceMul B n m x y =
      ((n * m).negOnePow : ℤ) • castHodgePiece B (add_comm m n) (hodgePieceMul B m n y x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx', smul_add]
  | of i ξ =>
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp [hy, hy', smul_add]
  | of j ζ =>
  rw [hodgePieceMul_of, hodgePieceMul_of, castHodgePiece_of, ← map_zsmul]
  refine DirectSum.of_eq_of_heq (Subtype.ext (Prod.ext (add_comm _ _) (add_comm _ _))) ?_
  have hs : ((((i.1.1 : ℤ) + (i.1.2 : ℤ)) * ((j.1.1 : ℤ) + (j.1.2 : ℤ))).negOnePow : ℤ) =
      ((n * m).negOnePow : ℤ) := by
    have hi : ((i.1.1 : ℤ) + (i.1.2 : ℤ)) = n := by have := i.2; push_cast at this; exact this
    have hj : ((j.1.1 : ℤ) + (j.1.2 : ℤ)) = m := by have := j.2; push_cast at this; exact this
    rw [hi, hj]
  refine (reindexHodgeDeg_heq B _ _).trans ?_
  rw [hodgeCohomologyCup, hodgeCupProduct_comm B (hodgeCohomologyCupProduct B), hs]
  refine (zsmul_hodge_heq B (Nat.add_comm _ _) (add_comm _ _) _
    (reindexHodge_heq B _ _ _)).trans ?_
  exact zsmul_hodge_heq B rfl (Nat.cast_add _ _).symm _ (reindexHodgeDeg_heq B _ _).symm

/-- The unit `1 ∈ H^0_{Hodge}(X/S)`: the unit class `hodgeOne` in bidegree `(0, 0)`. -/
def hodgePieceOne : hodgePiece B 0 :=
  DirectSum.of (fun k : HodgeBidegreeInt 0 =>
    (hodgeCohomologyComponent B k.1.1 (k.1.2 : ℤ) : Type u)) ⟨(0, 0), rfl⟩ (hodgeOne B)

/-- `1 ∪ x = x` in `H^*_{Hodge}(X/S)`. -/
theorem hodgePieceMul_one_left (n : ℤ) (x : hodgePiece B n) :
    castHodgePiece B (zero_add n) (hodgePieceMul B 0 n (hodgePieceOne B) x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx']
  | of i ξ =>
  rw [hodgePieceOne, hodgePieceMul_of, castHodgePiece_of]
  refine DirectSum.of_eq_of_heq (Subtype.ext (Prod.ext (zero_add _) (zero_add _))) ?_
  exact (reindexHodgeDeg_heq B _ _).trans (hodgeOne_hodgeCohomologyCup_heq B _ _ ξ)

/-- `x ∪ 1 = x` in `H^*_{Hodge}(X/S)`. -/
theorem hodgePieceMul_one_right (n : ℤ) (x : hodgePiece B n) :
    castHodgePiece B (add_zero n) (hodgePieceMul B n 0 x (hodgePieceOne B)) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx']
  | of i ξ =>
  rw [hodgePieceOne, hodgePieceMul_of, castHodgePiece_of]
  refine DirectSum.of_eq_of_heq (Subtype.ext (Prod.ext (add_zero _) (add_zero _))) ?_
  exact (reindexHodgeDeg_heq B _ _).trans (hodgeCohomologyCup_hodgeOne_heq B _ _ ξ)

/-- The cup product on `H^*_{Hodge}(X/S)` is linear over the global sections of the base ring sheaf
in each variable. -/
private theorem hodgePieceMul_smul_left_and_right (n m : ℤ)
    (a : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))
    (x : hodgePiece B n) (y : hodgePiece B m) :
    hodgePieceMul B n m (a • x) y = a • hodgePieceMul B n m x y ∧
      hodgePieceMul B n m x (a • y) = a • hodgePieceMul B n m x y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp_all [smul_add]
  | of i ξ =>
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp_all [smul_add]
  | of j ζ =>
  constructor
  · rw [← DirectSum.of_smul, hodgePieceMul_of, hodgePieceMul_of, hodgeCohomologyCup_smul_left,
      reindexHodgeDeg_smul, DirectSum.of_smul]
  · rw [← DirectSum.of_smul, hodgePieceMul_of, hodgePieceMul_of, hodgeCohomologyCup_smul_right,
      reindexHodgeDeg_smul, DirectSum.of_smul]

/-- The cup product on `H^*_{Hodge}(X/S)` is linear over the global sections of the base ring
sheaf in its first variable. -/
theorem hodgePieceMul_smul_left (n m : ℤ)
    (a : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))
    (x : hodgePiece B n) (y : hodgePiece B m) :
    hodgePieceMul B n m (a • x) y = a • hodgePieceMul B n m x y :=
  (hodgePieceMul_smul_left_and_right B n m a x y).1

/-- The cup product on `H^*_{Hodge}(X/S)` is linear over the global sections of the base ring
sheaf in its second variable. -/
theorem hodgePieceMul_smul_right (n m : ℤ)
    (a : (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))
    (x : hodgePiece B n) (y : hodgePiece B m) :
    hodgePieceMul B n m x (a • y) = a • hodgePieceMul B n m x y :=
  (hodgePieceMul_smul_left_and_right B n m a x y).2

/-! ### The graded ring -/

/-- The graded unit: the class of the global function `1`. -/
instance hodgeGOne : GradedMonoid.GOne (hodgePiece B) where
  one := hodgePieceOne B

/-- The graded multiplication: the cup product. -/
instance hodgeGMul : GradedMonoid.GMul (hodgePiece B) where
  mul {i j} x y := hodgePieceMul B i j x y

/-- The graded multiplication is the cup product. -/
theorem hodge_gMul_eq {i j : ℤ} (x : hodgePiece B i) (y : hodgePiece B j) :
    GradedMonoid.GMul.mul x y = hodgePieceMul B i j x y :=
  rfl

/-- The graded unit is the unit class. -/
theorem hodge_gOne_eq : (GradedMonoid.GOne.one : hodgePiece B 0) = hodgePieceOne B :=
  rfl

/-- **The graded ring `n ↦ H^n_{Hodge}(X/S)`**: the product is the cup product of Section 50.5,
the unit the class of the global function `1`; it is associative by Tag 0FM5. -/
instance hodgeGRing : DirectSum.GRing (hodgePiece B) where
  mul_zero {i j} x := (hodgePieceMul B i j x).map_zero
  zero_mul {i j} y := by
    change hodgePieceMul B i j 0 y = 0
    rw [map_zero, AddMonoidHom.zero_apply]
  mul_add {i j} x y y' := (hodgePieceMul B i j x).map_add y y'
  add_mul {i j} x x' y := by
    change hodgePieceMul B i j (x + x') y = hodgePieceMul B i j x y + hodgePieceMul B i j x' y
    rw [map_add, AddMonoidHom.add_apply]
  one_mul a := by
    obtain ⟨i, x⟩ := a
    exact (gradedMonoid_mk_castHodgePiece B (zero_add i) _).trans
      (congrArg (GradedMonoid.mk i) (hodgePieceMul_one_left B i x))
  mul_one a := by
    obtain ⟨i, x⟩ := a
    exact (gradedMonoid_mk_castHodgePiece B (add_zero i) _).trans
      (congrArg (GradedMonoid.mk i) (hodgePieceMul_one_right B i x))
  mul_assoc a b c := by
    obtain ⟨i, x⟩ := a
    obtain ⟨j, y⟩ := b
    obtain ⟨k, z⟩ := c
    exact (gradedMonoid_mk_castHodgePiece B (add_assoc i j k) _).trans
      (congrArg (GradedMonoid.mk (i + (j + k))) (hodgePieceMul_assoc B i j k x y z))
  natCast n := (n : ℤ) • hodgePieceOne B
  natCast_zero := by simp
  natCast_succ n := by
    change ((n + 1 : ℕ) : ℤ) • hodgePieceOne B = (n : ℤ) • hodgePieceOne B + _
    rw [Nat.cast_succ, add_smul, one_smul]
    rfl
  intCast z := z • hodgePieceOne B
  intCast_ofNat _ := rfl
  intCast_negSucc_ofNat n := by
    change Int.negSucc n • hodgePieceOne B = -(((n + 1 : ℕ) : ℤ) • hodgePieceOne B)
    rw [Int.negSucc_eq, neg_smul]
    push_cast
    rfl

/-- **The Hodge cohomology ring** `H^*_{Hodge}(X/S) = ⨁_{n ∈ 𝐙} H^n_{Hodge}(X/S)`, with the cup
product. -/
abbrev hodgeAlgebra : Type u :=
  DirectSum ℤ (hodgePiece B)

/-- The product of two homogeneous classes is their cup product. -/
theorem hodgeAlgebra_of_mul_of {i j : ℤ} (x : hodgePiece B i) (y : hodgePiece B j) :
    (DirectSum.of (hodgePiece B) i x * DirectSum.of (hodgePiece B) j y : hodgeAlgebra B) =
      DirectSum.of (hodgePiece B) (i + j) (hodgePieceMul B i j x y) :=
  DirectSum.of_mul_of (A := hodgePiece B) x y

/-- The unit of `H^*_{Hodge}(X/S)` is the class of the global function `1` in degree `0`. -/
theorem hodgeAlgebra_one :
    (1 : hodgeAlgebra B) = DirectSum.of (hodgePiece B) 0 (hodgePieceOne B) :=
  rfl

/-- Inclusions of a class read in equal degrees agree. -/
theorem of_castHodgePiece {n n' : ℤ} (h : n = n') (x : hodgePiece B n) :
    DirectSum.of (hodgePiece B) n' (castHodgePiece B h x) = DirectSum.of (hodgePiece B) n x :=
  DirectSum.of_eq_of_heq h.symm (castHodgePiece_heq B h x)

/-- **The Koszul sign rule on homogeneous generators**: `x ∪ y = (-1)^{ij} y ∪ x` in
`H^*_{Hodge}(X/S)` for `x` of degree `i` and `y` of degree `j`. -/
theorem hodgeAlgebra_of_mul_of_comm {i j : ℤ} (x : hodgePiece B i) (y : hodgePiece B j) :
    (DirectSum.of (hodgePiece B) i x * DirectSum.of (hodgePiece B) j y : hodgeAlgebra B) =
      ((i * j).negOnePow : ℤ) •
        (DirectSum.of (hodgePiece B) j y * DirectSum.of (hodgePiece B) i x) := by
  rw [hodgeAlgebra_of_mul_of, hodgeAlgebra_of_mul_of, hodgePieceMul_comm, map_zsmul,
    of_castHodgePiece]

/-! ### Scalars -/

section Scalars

variable (A) in
/-- The global sections of the base ring sheaf, as a commutative ring, mapping identically to the
ring over which the groups `H^q(X, Ω^p)` are modules. -/
def globalSectionsRingHom :
    Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A) →+*
      (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤) :=
  RingHom.id _

variable {k : Type*} [CommRing k]
  (σ : k →+* (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))

/-- `k` acting on `H^n_{Hodge}(X/S)` through a ring map `σ` to the global sections of the base
ring sheaf. -/
abbrev hodgePieceModule (n : ℤ) : Module k (hodgePiece B n) :=
  Module.compHom _ σ

/-- `c ∈ k` acts on `H^n_{Hodge}(X/S)` as `σ(c)`. -/
theorem hodgePieceModule_smul (c : k) {n : ℤ} (x : hodgePiece B n) :
    letI := hodgePieceModule B σ n
    c • x = σ c • x :=
  rfl

/-- The class `σ(c) · 1 ∈ H^0_{Hodge}(X/S)` of a scalar. -/
def hodgeScalarClass : k →+ hodgePiece B 0 :=
  AddMonoidHom.mk' (fun c => σ c • hodgePieceOne B) fun c d => by rw [map_add, add_smul]

/-- `(σ(c) · 1) ∪ x = σ(c) · x`. -/
theorem gradedMonoid_mk_hodgeScalarClass_mul (c : k) {i : ℤ} (x : hodgePiece B i) :
    (GradedMonoid.mk (0 + i) (hodgePieceMul B 0 i (hodgeScalarClass B σ c) x) :
        GradedMonoid (hodgePiece B)) = GradedMonoid.mk i (σ c • x) := by
  show GradedMonoid.mk (0 + i) (hodgePieceMul B 0 i (σ c • hodgePieceOne B) x) = _
  rw [hodgePieceMul_smul_left, gradedMonoid_mk_castHodgePiece B (zero_add i), castHodgePiece_smul,
    hodgePieceMul_one_left]

/-- `x ∪ (σ(c) · 1) = σ(c) · x`. -/
theorem gradedMonoid_mk_mul_hodgeScalarClass (c : k) {i : ℤ} (x : hodgePiece B i) :
    (GradedMonoid.mk (i + 0) (hodgePieceMul B i 0 x (hodgeScalarClass B σ c)) :
        GradedMonoid (hodgePiece B)) = GradedMonoid.mk i (σ c • x) := by
  show GradedMonoid.mk (i + 0) (hodgePieceMul B i 0 x (σ c • hodgePieceOne B)) = _
  rw [hodgePieceMul_smul_right, gradedMonoid_mk_castHodgePiece B (add_zero i),
    castHodgePiece_smul, hodgePieceMul_one_right]

/-- **`H^*_{Hodge}(X/S)` is a graded `k`-algebra**, `k` acting through `σ`: the structure map
sends `c` to `σ(c) · 1`. -/
@[instance_reducible]
def hodgeGAlgebra :
    letI : ∀ n, Module k (hodgePiece B n) := hodgePieceModule B σ
    DirectSum.GAlgebra k (hodgePiece B) :=
  letI : ∀ n, Module k (hodgePiece B n) := hodgePieceModule B σ
  { toFun := hodgeScalarClass B σ
    map_one := by
      change σ 1 • hodgePieceOne B = hodgePieceOne B
      rw [map_one, one_smul]
    map_mul := fun c d => by
      change GradedMonoid.mk (A := hodgePiece B) 0 (σ (c * d) • hodgePieceOne B) =
        GradedMonoid.mk (A := hodgePiece B) (0 + 0)
          (hodgePieceMul B 0 0 (hodgeScalarClass B σ c) (hodgeScalarClass B σ d))
      rw [gradedMonoid_mk_hodgeScalarClass_mul, map_mul, mul_smul]
      rfl
    commutes := fun c x => by
      obtain ⟨i, x⟩ := x
      change GradedMonoid.mk (A := hodgePiece B) (0 + i)
          (hodgePieceMul B 0 i (hodgeScalarClass B σ c) x) =
        GradedMonoid.mk (A := hodgePiece B) (i + 0)
          (hodgePieceMul B i 0 x (hodgeScalarClass B σ c))
      rw [gradedMonoid_mk_hodgeScalarClass_mul, gradedMonoid_mk_mul_hodgeScalarClass]
    smul_def := fun c x => by
      obtain ⟨i, x⟩ := x
      change GradedMonoid.mk (A := hodgePiece B) i (σ c • x) =
        GradedMonoid.mk (A := hodgePiece B) (0 + i)
          (hodgePieceMul B 0 i (hodgeScalarClass B σ c) x)
      rw [gradedMonoid_mk_hodgeScalarClass_mul] }

/-- **`H^*_{Hodge}(X/S)` as a `k`-algebra**, `k` acting through `σ`. -/
@[instance_reducible]
def hodgeAlgebraAlgebra : Algebra k (hodgeAlgebra B) :=
  letI : ∀ n, Module k (hodgePiece B n) := hodgePieceModule B σ
  letI := hodgeGAlgebra B σ
  inferInstance

/-- **The degree-`n` part** `H^n_{Hodge}(X/S)` of `H^*_{Hodge}(X/S)`, as a `k`-submodule. -/
def hodgeGrade (n : ℤ) :
    letI := hodgeAlgebraAlgebra B σ
    Submodule k (hodgeAlgebra B) :=
  letI : ∀ n, Module k (hodgePiece B n) := hodgePieceModule B σ
  DirectSum.rangeGrading k (hodgePiece B) n

/-- A class lies in the degree-`n` part exactly when it is the image of a class of
`H^n_{Hodge}(X/S)`. -/
theorem mem_hodgeGrade (n : ℤ) (a : hodgeAlgebra B) :
    a ∈ hodgeGrade B σ n ↔ ∃ x : hodgePiece B n, a = DirectSum.of (hodgePiece B) n x :=
  let : ∀ n, Module k (hodgePiece B n) := hodgePieceModule B σ
  DirectSum.mem_rangeGrading k (hodgePiece B) n a

/-- A class of `H^n_{Hodge}(X/S)` lies in the degree-`n` part. -/
theorem of_mem_hodgeGrade (n : ℤ) (x : hodgePiece B n) :
    DirectSum.of (hodgePiece B) n x ∈ hodgeGrade B σ n :=
  (mem_hodgeGrade B σ n _).2 ⟨x, rfl⟩

/-- **The grading** `H^*_{Hodge}(X/S) = ⨁_{n ∈ 𝐙} H^n_{Hodge}(X/S)` of the `k`-algebra. -/
@[instance_reducible]
def hodgeGradedAlgebra :
    letI := hodgeAlgebraAlgebra B σ
    _root_.GradedAlgebra (hodgeGrade B σ) :=
  letI : ∀ n, Module k (hodgePiece B n) := hodgePieceModule B σ
  letI := hodgeAlgebraAlgebra B σ
  { DirectSum.rangeGradingDecomposition k (hodgePiece B) with
    one_mem := of_mem_hodgeGrade B σ 0 _
    mul_mem := fun i j a b ha hb => by
      obtain ⟨x, rfl⟩ := (mem_hodgeGrade B σ i a).1 ha
      obtain ⟨y, rfl⟩ := (mem_hodgeGrade B σ j b).1 hb
      rw [DirectSum.of_mul_of]
      exact of_mem_hodgeGrade B σ (i + j) _ }

/-- **The Koszul sign rule** on `H^*_{Hodge}(X/S)` (Tag 0FM5): `a ∪ b = (-1)^{ij} b ∪ a` for `a`
homogeneous of degree `i` and `b` homogeneous of degree `j`. -/
theorem hodgeAlgebra_graded_comm (i j : ℤ) (a b : hodgeAlgebra B) (ha : a ∈ hodgeGrade B σ i)
    (hb : b ∈ hodgeGrade B σ j) :
    a * b = (Int.negOnePow (i * j) : ℤ) • (b * a) := by
  obtain ⟨x, rfl⟩ := (mem_hodgeGrade B σ i a).1 ha
  obtain ⟨y, rfl⟩ := (mem_hodgeGrade B σ j b).1 hb
  exact hodgeAlgebra_of_mul_of_comm B x y

end Scalars

end Stacks.HodgeWeil

end
