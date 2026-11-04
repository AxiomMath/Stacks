module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProductLawsReduction

/-!
# The cup product of Cohomology, Section 0FKU on the groups `H^q(X, Ω^p)`

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^p` be the exterior powers of its sheaf of relative differentials. For a multiplication of
forms `m : Ω^p ⊗_A Ω^{p'} ⟶ Ω^r` the cup product of Cohomology, Section 0FKU gives a pairing

`H^q(X, Ω^p) × H^{q'}(X, Ω^{p'}) ⟶ H^{q+q'}(X, Ω^p ⊗^𝐋_A Ω^{p'}) ⟶ H^{q+q'}(X, Ω^p ⊗_A Ω^{p'})
⟶ H^{q+q'}(X, Ω^r)`,

and Section 50.5 of the source (Tag 0FM4) combines it with the wedge product. This file builds
that pairing with no parameter: it is the pairing
`AlgebraicGeometry.SheafOfModules.canonicalPairingModule` of the global cup product of the
ringed space `(X, A)`, for the multiplication of complexes concentrated in degree `0` induced by
`m`, read on the groups `H^q(X, Ω^p)` of
`AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.singleNat`: a sheaf of `A`-modules as an `ℕ`-indexed complex
  concentrated in degree `0`.
* `AlgebraicGeometry.SheafOfModules.singleMultiplication`: the multiplication
  `Tot(F[0] ⊗_A G[0]) ⟶ H[0]` induced by a morphism `F ⊗_A G ⟶ H`.
* `AlgebraicGeometry.SheafOfModules.hodgeComponentIso`: `H^q(X, Ω^p)` is the cohomology of the
  derived global sections of `Ω^p[0]` read as an `ℕ`-indexed complex.
* `AlgebraicGeometry.SheafOfModules.hodgeComponentCup`: **the cup product along `m`**.

## Main results

* `AlgebraicGeometry.SheafOfModules.multiplicationValue_singleMultiplication`: on local pure
  tensors in degree `0` the multiplication of complexes is the underlying morphism.
* `AlgebraicGeometry.SheafOfModules.singleMultiplication_assoc_value` and
  `AlgebraicGeometry.SheafOfModules.singleMultiplication_comm_value`: the laws on local pure
  tensors of the multiplications of complexes, from the laws of the underlying morphisms; these
  are the inputs of `AlgebraicGeometry.SheafOfModules.multiplicationInt_assoc` and
  `AlgebraicGeometry.SheafOfModules.multiplicationInt_braiding`.
* `AlgebraicGeometry.SheafOfModules.hodgeComponentCup_add_left` and its three companions: the
  pairing is bilinear over the ring `A(X)` of global sections of the base ring sheaf.

## Implementation notes

`hodgeCohomologyComponent B p q` is a module over the `RingCat`-valued section ring
`(underlyingRingSheaf A).obj.obj (op ⊤)`, while `canonicalPairingModule` is a morphism of modules
over the `CommRingCat`-valued `baseRing (baseRingedSpace A)`. The two rings are definitionally
equal, but instance search does not cross between them, so the classes are passed through
`AlgebraicGeometry.SheafOfModules.hodgeComponentBase`, the same group at the second spelling,
by the identity maps `toHodgeComponentBase` and `ofHodgeComponentBase`.

## References

* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape Opposite
open TopologicalSpace
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open scoped TensorProduct Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- A sheaf of `A`-modules as an `ℕ`-indexed complex concentrated in degree `0`. -/
abbrev singleNat
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) :
    CochainComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
      ℕ :=
  (HomologicalComplex.single _ (up ℕ) 0).obj F

/-- The degree-`0` component of `singleMultiplication`. -/
def singleMultiplicationX
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) :
    (HomologicalComplex.mapBifunctor (singleNat F) (singleNat G)
      (sheafTensor.{u, u, u, u, u} A) (up ℕ)).X 0 ⟶ H :=
  HomologicalComplex.mapBifunctorDesc fun i₁ i₂ h =>
    ((sheafTensor.{u, u, u, u, u} A).map
        (HomologicalComplex.singleObjXIsoOfEq (up ℕ) 0 F i₁ (by
          change i₁ + i₂ = 0 at h; omega)).hom).app _ ≫
      ((sheafTensor.{u, u, u, u, u} A).obj F).map
        (HomologicalComplex.singleObjXIsoOfEq (up ℕ) 0 G i₂ (by
          change i₁ + i₂ = 0 at h; omega)).hom ≫ m

/-- **The multiplication of complexes concentrated in degree `0` induced by a morphism
`F ⊗_A G ⟶ H`**: `Tot(F[0] ⊗_A G[0]) ⟶ H[0]`. -/
def singleMultiplication
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) :
    ((tensorBifunctorNat (A := A)).obj (singleNat F)).obj (singleNat G) ⟶ singleNat H :=
  HomologicalComplex.mkHomToSingle
    (K := HomologicalComplex.mapBifunctor (singleNat F) (singleNat G)
      (sheafTensor.{u, u, u, u, u} A) (up ℕ))
    (singleMultiplicationX m) (fun i hi => by change i + 1 = 0 at hi; omega)

/-- The degree-`0` component of `singleMultiplication m` is `singleMultiplicationX m`. -/
private theorem singleMultiplication_f_zero
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) :
    (singleMultiplication m).f 0 =
      singleMultiplicationX m ≫ (HomologicalComplex.singleObjXSelf (up ℕ) 0 H).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- The value of the multiplication of complexes concentrated in degree `0` on a local pure
tensor in degree `0` is the value of the underlying morphism. -/
theorem multiplicationValue_singleMultiplication
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((singleNat F).X 0).val.obj U) (y : ((singleNat G).X 0).val.obj U) :
    multiplicationValue (singleMultiplication m) 0 0 U x y =
      (HomologicalComplex.singleObjXSelf (up ℕ) 0 H).inv.val.app U
        (m.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj F.val G.val)).app U
            ((HomologicalComplex.singleObjXSelf (up ℕ) 0 F).hom.val.app U x ⊗ₜ[A.obj.obj U]
              (HomologicalComplex.singleObjXSelf (up ℕ) 0 G).hom.val.app U y))) := by
  change (HomologicalComplex.ιMapBifunctor (singleNat F) (singleNat G)
      (sheafTensor.{u, u, u, u, u} A) (up ℕ) 0 0 0 rfl ≫
      (singleMultiplication m).f 0).val.app U _ = _
  rw [singleMultiplication_f_zero, singleMultiplicationX,
    HomologicalComplex.ι_mapBifunctorDesc_assoc]
  refine congrArg (fun t => (HomologicalComplex.singleObjXSelf (up ℕ) 0 H).inv.val.app U
    (m.val.app U t)) ?_
  refine (congrArg (fun t => ((((sheafTensor.{u, u, u, u, u} A).obj F).map
      (HomologicalComplex.singleObjXSelf (up ℕ) 0 G).hom).val.app U) t)
    (Stacks.SheafOfModules.FlatSquareZero.tensorRight_map_tmul A ((singleNat G).X 0)
      (HomologicalComplex.singleObjXSelf (up ℕ) 0 F).hom U x y)).trans ?_
  exact Stacks.SheafOfModules.FlatSquareZero.tensorLeft_map_tmul A F
    (HomologicalComplex.singleObjXSelf (up ℕ) 0 G).hom U _ y

/-- The sections of a complex concentrated in degree `0` vanish in every other degree. -/
theorem subsingleton_singleNat_X
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    {n : ℕ} (hn : n ≠ 0) (U : (Opens X.carrier)ᵒᵖ) :
    Subsingleton (((singleNat F).X n).val.obj U) := by
  have hZ := HomologicalComplex.isZero_single_obj_X (up ℕ) 0 F n hn
  have hZ' : IsZero (((singleNat F).X n).val.obj U) :=
    (((_root_.SheafOfModules.forget _) ⋙ PresheafOfModules.evaluation _ U).map_isZero hZ)
  exact (ModuleCat.isZero_iff_subsingleton.mp hZ')

/-- Two sections of a complex concentrated in degree `0`, in a common nonzero degree, are
heterogeneously equal. -/
theorem heq_of_singleNat_X
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    {i j : ℕ} (hij : i = j) (hi : i ≠ 0) {U : (Opens X.carrier)ᵒᵖ}
    (x : ((singleNat F).X i).val.obj U) (y : ((singleNat F).X j).val.obj U) : HEq x y := by
  subst hij
  have := subsingleton_singleNat_X F hi U
  exact heq_of_eq (Subsingleton.elim x y)

/-- **Associativity on local pure tensors of the multiplications of complexes concentrated in
degree `0`**, from the associativity of the underlying morphisms of sheaves. -/
theorem singleMultiplication_assoc_value
    {F G H P Q N : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m₁ : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ P)
    (m₂ : ((sheafTensor.{u, u, u, u, u} A).obj P).obj H ⟶ N)
    (m₃ : ((sheafTensor.{u, u, u, u, u} A).obj G).obj H ⟶ Q)
    (m₄ : ((sheafTensor.{u, u, u, u, u} A).obj F).obj Q ⟶ N)
    (hm : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) (z : H.val.obj U),
      m₂.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj P.val H.val)).app U
            (m₁.val.app U (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
              (PresheafOfModules.tensorObj F.val G.val)).app U (x ⊗ₜ[A.obj.obj U] y))
              ⊗ₜ[A.obj.obj U] z)) =
        m₄.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj F.val Q.val)).app U
            (x ⊗ₜ[A.obj.obj U] m₃.val.app U (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
              (PresheafOfModules.tensorObj G.val H.val)).app U (y ⊗ₜ[A.obj.obj U] z))))) :
    ∀ (a b c : ℕ) (U : (Opens X.carrier)ᵒᵖ) (x : ((singleNat F).X a).val.obj U)
      (y : ((singleNat G).X b).val.obj U) (z : ((singleNat H).X c).val.obj U),
      HEq (multiplicationValue (singleMultiplication m₂) (a + b) c U
          (multiplicationValue (singleMultiplication m₁) a b U x y) z)
        (multiplicationValue (singleMultiplication m₄) a (b + c) U x
          (multiplicationValue (singleMultiplication m₃) b c U y z)) := by
  intro a b c U x y z
  by_cases h0 : a = 0 ∧ b = 0 ∧ c = 0
  · obtain ⟨rfl, rfl, rfl⟩ := h0
    refine heq_of_eq ?_
    change multiplicationValue (singleMultiplication m₂) 0 0 U
        (multiplicationValue (singleMultiplication m₁) 0 0 U x y) z =
      multiplicationValue (singleMultiplication m₄) 0 0 U x
        (multiplicationValue (singleMultiplication m₃) 0 0 U y z)
    rw [multiplicationValue_singleMultiplication, multiplicationValue_singleMultiplication,
      multiplicationValue_singleMultiplication, multiplicationValue_singleMultiplication,
      Stacks.SheafOfModules.hom_val_app_inv_val_app,
      Stacks.SheafOfModules.hom_val_app_inv_val_app, hm]
  · exact heq_of_singleNat_X N (Nat.add_assoc a b c) (by omega) _ _

/-- **Graded commutativity on local pure tensors of the multiplications of complexes
concentrated in degree `0`**: there is no sign, the degrees being `0`. -/
theorem singleMultiplication_comm_value
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H)
    (m' : ((sheafTensor.{u, u, u, u, u} A).obj G).obj F ⟶ H)
    (hm : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      m.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj F.val G.val)).app U (x ⊗ₜ[A.obj.obj U] y)) =
        m'.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj G.val F.val)).app U (y ⊗ₜ[A.obj.obj U] x))) :
    ∀ (a b : ℕ) (U : (Opens X.carrier)ᵒᵖ) (x : ((singleNat F).X a).val.obj U)
      (y : ((singleNat G).X b).val.obj U),
      HEq (multiplicationValue (singleMultiplication m) a b U x y)
        ((-1 : ℤ) ^ (a * b) • multiplicationValue (singleMultiplication m') b a U y x) := by
  intro a b U x y
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    refine heq_of_eq ?_
    rw [Nat.mul_zero, pow_zero, one_smul, multiplicationValue_singleMultiplication,
      multiplicationValue_singleMultiplication, hm]
  · exact heq_of_singleNat_X H (Nat.add_comm a b) (by omega) _ _

/-- The Hodge cohomology group `H^q(X, Ω^p)`, as a module over the `CommRingCat`-valued ring of
global sections `baseRing (baseRingedSpace A)`, the ring the cup product is bilinear over. It is
`hodgeCohomologyComponent B p q`; only the spelling of the ring differs. -/
abbrev hodgeComponentBase (p : ℕ) (q : ℤ) :
    ModuleCat.{u} (Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A)) :=
  (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A))) q).obj
    ((derivedSectionsBase A).obj ((DerivedCategory.singleFunctor _ 0).obj (deRhamTerm B p)))

/-- A Hodge cohomology class read in `hodgeComponentBase`; the identity on elements. -/
abbrev toHodgeComponentBase {p : ℕ} {q : ℤ} (ξ : hodgeCohomologyComponent B p q) :
    hodgeComponentBase B p q :=
  ξ

/-- A class of `hodgeComponentBase` read as a Hodge cohomology class; the identity on
elements. -/
abbrev ofHodgeComponentBase {p : ℕ} {q : ℤ} (ξ : hodgeComponentBase B p q) :
    hodgeCohomologyComponent B p q :=
  ξ

/-- **The Hodge cohomology group `H^q(X, Ω^p)` is the cohomology of the derived global sections
of `Ω^p[0]` read as an `ℕ`-indexed complex**, the module on which the cup product
`canonicalPairingModule` is stated: the extension by zero of an `ℕ`-indexed complex concentrated
in degree `0` is the `ℤ`-indexed complex concentrated in degree `0`. -/
def hodgeComponentIso (p : ℕ) (q : ℤ) :
    cohomologyModule (moduleDerived (singleNat (deRhamTerm B p))) q ≅
      hodgeComponentBase B p q :=
  (DerivedCategory.homologyFunctor _ q).mapIso
    ((Stacks.Cohomology.GlobalKunneth.baseSections (baseRingedSpace A)).mapIso
      (DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso embeddingUpNat
        (deRhamTerm B p) 0 0 rfl)))

/-- **The cup product of Cohomology, Section 0FKU on the groups `H^q(X, Ω^p)`, along a
multiplication of forms** `m : Ω^p ⊗_A Ω^{p'} ⟶ Ω^r`:

`H^q(X, Ω^p) × H^{q'}(X, Ω^{p'}) ⟶ H^{q+q'}(X, Ω^p ⊗^𝐋_A Ω^{p'}) ⟶ H^{q+q'}(X, Ω^p ⊗_A Ω^{p'})
⟶ H^{q+q'}(X, Ω^r)`,

the pairing `canonicalPairingModule` of the global cup product of the ringed space `(X, A)` for
the multiplication `Ω^p[0] ⊗ Ω^{p'}[0] ⟶ Ω^r[0]` induced by `m`. -/
def hodgeComponentCup {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeCohomologyComponent B r (q + q') :=
  ofHodgeComponentBase B ((hodgeComponentIso B r (q + q')).hom.hom
    ((canonicalPairingModule (singleMultiplication m) q q').hom
      ((hodgeComponentIso B p q).inv.hom (toHodgeComponentBase B ξ) ⊗ₜ
        (hodgeComponentIso B p' q').inv.hom (toHodgeComponentBase B ζ))))

/-- The cup product `hodgeComponentCup` is additive in its first argument. -/
theorem hodgeComponentCup_add_left {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ)
    (ξ ξ' : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeComponentCup B m q q' (ξ + ξ') ζ =
      hodgeComponentCup B m q q' ξ ζ + hodgeComponentCup B m q q' ξ' ζ := by
  unfold hodgeComponentCup
  erw [map_add, TensorProduct.add_tmul, map_add, map_add]
  rfl

/-- The cup product `hodgeComponentCup` is additive in its second argument. -/
theorem hodgeComponentCup_add_right {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ ζ' : hodgeCohomologyComponent B p' q') :
    hodgeComponentCup B m q q' ξ (ζ + ζ') =
      hodgeComponentCup B m q q' ξ ζ + hodgeComponentCup B m q q' ξ ζ' := by
  unfold hodgeComponentCup
  erw [map_add, TensorProduct.tmul_add, map_add, map_add]
  rfl

/-- The cup product `hodgeComponentCup` is linear in its first argument over the global sections
of the structure sheaf. -/
theorem hodgeComponentCup_smul_left {p p' r : ℕ} (m : FormsMultiplication B p p' r)
    (q q' : ℤ) (a : (underlyingRingSheaf A).obj.obj (op ⊤))
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeComponentCup B m q q' (a • ξ) ζ = a • hodgeComponentCup B m q q' ξ ζ := by
  let a' : Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A) := a
  unfold hodgeComponentCup
  rw [show toHodgeComponentBase B (a • ξ) = a' • toHodgeComponentBase B ξ from rfl,
    map_smul, ← TensorProduct.smul_tmul', map_smul, map_smul]
  rfl

/-- The cup product `hodgeComponentCup` is linear in its second argument over the global sections
of the structure sheaf. -/
theorem hodgeComponentCup_smul_right {p p' r : ℕ} (m : FormsMultiplication B p p' r)
    (q q' : ℤ) (a : (underlyingRingSheaf A).obj.obj (op ⊤))
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeComponentCup B m q q' ξ (a • ζ) = a • hodgeComponentCup B m q q' ξ ζ := by
  let a' : Stacks.Cohomology.GlobalKunneth.baseRing (baseRingedSpace A) := a
  unfold hodgeComponentCup
  rw [show toHodgeComponentBase B (a • ζ) = a' • toHodgeComponentBase B ζ from rfl,
    map_smul, TensorProduct.tmul_smul, map_smul, map_smul]
  rfl

/-- An associative quadruple of multiplications of forms, with a common target degree, satisfies
the associativity hypothesis of `singleMultiplication_assoc_value`. -/
theorem isAssociativeTriple_tmul {p p' p'' r s t : ℕ} {m₁ : FormsMultiplication B p p' r}
    {m₂ : FormsMultiplication B r p'' s} {m₃ : FormsMultiplication B p' p'' t}
    {m₄ : FormsMultiplication B p t s} (h : IsAssociativeTriple B m₁ m₂ m₃ m₄)
    (U : (Opens X.carrier)ᵒᵖ) (x : (deRhamTerm B p).val.obj U) (y : (deRhamTerm B p').val.obj U)
    (z : (deRhamTerm B p'').val.obj U) :
    m₂.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
        (PresheafOfModules.tensorObj (deRhamTerm B r).val (deRhamTerm B p'').val)).app U
          (m₁.val.app U (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
            (PresheafOfModules.tensorObj (deRhamTerm B p).val (deRhamTerm B p').val)).app U
              (x ⊗ₜ[A.obj.obj U] y)) ⊗ₜ[A.obj.obj U] z)) =
      m₄.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
        (PresheafOfModules.tensorObj (deRhamTerm B p).val (deRhamTerm B t).val)).app U
          (x ⊗ₜ[A.obj.obj U] m₃.val.app U (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
            (PresheafOfModules.tensorObj (deRhamTerm B p').val (deRhamTerm B p'').val)).app U
              (y ⊗ₜ[A.obj.obj U] z)))) :=
  eq_of_heq (h U x y z)

/-- A multiplication of forms which is `k` times the transpose of another, in a common target
degree, satisfies the commutativity hypothesis of `singleMultiplication_comm_value` against `k`
times the other. -/
theorem isScaledTranspose_tmul {p p' r : ℕ} {m : FormsMultiplication B p p' r}
    {m' : FormsMultiplication B p' p r} {k : ℤ} (h : IsScaledTranspose B m m' k)
    (U : (Opens X.carrier)ᵒᵖ) (x : (deRhamTerm B p).val.obj U)
    (y : (deRhamTerm B p').val.obj U) :
    m.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
        (PresheafOfModules.tensorObj (deRhamTerm B p).val (deRhamTerm B p').val)).app U
          (x ⊗ₜ[A.obj.obj U] y)) =
      (k • m').val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
        (PresheafOfModules.tensorObj (deRhamTerm B p').val (deRhamTerm B p).val)).app U
          (y ⊗ₜ[A.obj.obj U] x)) :=
  (eq_of_heq (h U x y)).trans (_root_.SheafOfModules.zsmul_val_app k m' U _).symm

/-- The multiplication of complexes concentrated in degree `0` is `ℤ`-linear in the underlying
morphism. -/
theorem singleMultiplication_zsmul
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (k : ℤ) (m : ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ H) :
    singleMultiplication (k • m) = k • singleMultiplication m := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    rw [singleMultiplication_f_zero, HomologicalComplex.zsmul_f_apply, singleMultiplication_f_zero]
    erw [← Preadditive.zsmul_comp]
    refine congrArg (· ≫ _) (HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_)
    rw [singleMultiplicationX, singleMultiplicationX, Preadditive.comp_zsmul,
      HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc,
      Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  · exact (HomologicalComplex.isZero_single_obj_X (up ℕ) 0 H n hn).eq_of_tgt _ _

end AlgebraicGeometry.SheafOfModules

end
