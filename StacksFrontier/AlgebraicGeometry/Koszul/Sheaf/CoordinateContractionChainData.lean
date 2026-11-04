module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.ContractionCocycle
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContractionDegreeOne

/-!
# The coordinate contraction as the Koszul differential of a coordinate projection

Let `O♯` be a sheaf of commutative rings on a site, let `F` be a sheaf of `O♯`-modules and let `A`
be a bundle of tensor, exterior and symmetric algebras of `F`. The Koszul differential of a
functional on `F` is transported onto the exterior powers of `A` in
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContractionTransport`, by conjugation with
the canonical degreewise comparison of `A` with the realized exterior algebra `⋀(F)`. What that
transport does not carry across is the **graded Leibniz rule**: the transported differential is
known there only to square to zero and to anticommute with the transported differential of another
functional.

This file carries the Leibniz rule across as well, in the direction opposite to
`Stacks.RegularSequence.KoszulChainData.isKoszulDerivation_sheafifiedD`, which carries a Leibniz
rule *from* the exterior powers of a bundle *to* the realized algebra. Conjugation by an
isomorphism that is multiplicative on homogeneous local sections preserves the rule in either
direction, and the signs are untouched.

The consequence is that for `F` free on a finite index type the contraction `δⱼ` is itself the
differential of a **Koszul chain complex**: taking the functional to be the `j`-th coordinate
projection `F ⟶ O♯`, the family `(δⱼ)` satisfies the graded Leibniz rule, takes a degree-one
generator to its `j`-th coordinate, and squares to zero, so it assembles into a term of
`Stacks.RegularSequence.KoszulChainData`. Everything that development proves of a Koszul chain
complex — in particular the alternating-sum formula on the exterior basis and the identification
of the induced map on stalks with the ring-level Koszul differential — is thereby available for
`δⱼ` with no further computation.

## Main definitions

* `SheafOfModules.TensorExteriorSymmetricAlgebras.coordChain`: the `ℤ`-indexed chain complex of
  the exterior powers of `A` whose differential is the coordinate contraction `δⱼ`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.coordKoszulChainData`: **`δⱼ` as the Koszul
  chain data of the `j`-th coordinate projection.**

## Main results

* `SheafOfModules.TensorExteriorSymmetricAlgebras.koszulD_mul`: **the graded Leibniz rule for the
  transported Koszul differential of a functional**, on the exterior powers of a bundle of
  algebras.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.tensorToExterior_tensorPieceIso_inv_eq_smul_one`:
  the degree-zero section of the exterior algebra that a scalar names is that scalar times the
  unit.
* `Stacks.SheafOfModules.coordExteriorFunctional_dual_eq_freeProj`: **the `j`-th coordinate
  functional is the `j`-th coordinate projection**, read on local sections.

## Implementation notes

**The Leibniz rule transports by writing each argument as an image.** A homogeneous local section
`a` of the bundle's exterior power is the image of `β a`, where `β` is the inverse of the
comparison; the product `a ∧ b` is then the image of `β a ∧ β b` because the comparison is
multiplicative, the Leibniz rule of the realized algebra applies to that product, and the image of
the result is read back termwise. The two transports along an equality of degrees that the two
statements use are identified by `Stacks.gradedCast_eq_degCast`, and each commutes with the
comparison by `Stacks.degCast_map`.

**The chain complex is built directly rather than by a general construction.** Its differential
from degree `p` to degree `q` is the contraction when `q + 1 = p` and zero otherwise, the two
cases being separated by the decidability of that equation; the shape axiom is the negative case
and the composition axiom is the vanishing of the square of a single contraction. The `chain_X`
field is then `rfl`, and the `chain_d` field is the two identity laws of the category together
with the positive case.

**Only `HasSheafify` is assumed where the degree-one value is used.** The value of the transported
differential on a degree-one generator, `exteriorPieceZeroIsoUnit_koszulD_exteriorGenerator` in
the namespace `SheafOfModules.TensorExteriorSymmetricAlgebras`, is proved under `HasSheafify`,
whereas the transport itself needs only `HasWeakSheafify`. The two hypotheses are therefore kept
in separate sections: with both in scope the weaker one is the one the statements elaborate
against, and the stronger one is then not available to the proofs.

**The coordinate functional and the coordinate projection.** `coordExteriorFunctional` is built
from the coordinate forms of `Stacks.SheafOfModules.freeCoordBasis`, whose coordinates are by
construction `Stacks.SheafOfModules.freeCoord`, which is the projection morphism evaluated on
sections. The identification of the two is therefore definitional, once the basis is unfolded to
the transport of the standard basis of a product along the coordinate isomorphism.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe v u w

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### The graded Leibniz rule for the transported Koszul differential -/

section Leibniz

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)} (A : TensorExteriorSymmetricAlgebras J F)

/-- The comparison with the realized exterior algebra is inverse to its inverse, read on local
sections. -/
theorem sheafifiedExteriorPieceIso_hom_inv_app (n : ℤ) (U : Cᵒᵖ)
    (y : (A.exterior.piece n).val.obj U) :
    (A.sheafifiedExteriorPieceIso n).hom.val.app U
        ((A.sheafifiedExteriorPieceIso n).inv.val.app U y) = y :=
  Eq.trans (SheafOfModules.comp_val_app_apply _ _ U y).symm
    (SheafOfModules.hom_congr_app_apply (A.sheafifiedExteriorPieceIso n).inv_hom_id U y)

/-- **The transported Koszul differential of a functional, read on local sections**: carry the
section back to the realized exterior algebra, differentiate there, and carry the result
forward. -/
theorem koszulD_val_app (ψ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val) {p q : ℤ}
    (h : q + 1 = p) (U : Cᵒᵖ) (z : (A.exterior.piece p).val.obj U) :
    (A.koszulD ψ h).val.app U z =
      (A.sheafifiedExteriorPieceIso q).hom.val.app U
        ((SheafOfModules.koszulD J F ψ h).val.app U
          ((A.sheafifiedExteriorPieceIso p).inv.val.app U z)) :=
  Eq.trans (SheafOfModules.comp_val_app_apply _ _ U z)
    (SheafOfModules.comp_val_app_apply _ _ U _)

/-- **The graded Leibniz rule for the transported Koszul differential of a functional**, on the
exterior powers of a bundle of tensor, exterior and symmetric algebras. On local sections `a` of
degree `n` and `b` of degree `m` the differential of the product is the product of `d a` with `b`
plus `(-1) ^ n` times the product of `a` with `d b`, each transported into the degree `n + m - 1`.

This is the shape the `d_mul` field of `Stacks.RegularSequence.KoszulChainData` takes, so a
bundle-level differential satisfying it is Koszul chain data for the morphism whose functional
it is. The proof writes `a` and `b` as images under the comparison with the realized exterior
algebra, applies the Leibniz rule there, and carries the two summands back; the comparison is
multiplicative on homogeneous local sections and commutes with transport along an equality of
degrees, so no sign changes. -/
theorem koszulD_mul (ψ : PresheafOfModules.ExteriorFunctional.{v, u, w, w} F.val)
    (n m : ℤ) (U : Cᵒᵖ)
    (a : (A.exterior.piece n).val.obj U) (b : (A.exterior.piece m).val.obj U) :
    (A.koszulD ψ (show n + m - 1 + 1 = n + m by ring)).val.app U
        ((A.exterior.mul n m).app U a b) =
      Stacks.degCast (F := fun q : ℤ => ((A.exterior.piece q).val.obj U : Type w))
          (by ring : (n - 1) + m = n + m - 1)
          ((A.exterior.mul (n - 1) m).app U
            ((A.koszulD ψ (show n - 1 + 1 = n by ring)).val.app U a) b) +
        (Int.negOnePow n : ℤ) •
          Stacks.degCast (F := fun q : ℤ => ((A.exterior.piece q).val.obj U : Type w))
            (by ring : n + (m - 1) = n + m - 1)
            ((A.exterior.mul n (m - 1)).app U a
              ((A.koszulD ψ (show m - 1 + 1 = m by ring)).val.app U b)) := by
  set a' := (A.sheafifiedExteriorPieceIso n).inv.val.app U a with ha'
  set b' := (A.sheafifiedExteriorPieceIso m).inv.val.app U b with hb'
  have ha : (A.sheafifiedExteriorPieceIso n).hom.val.app U a' = a :=
    A.sheafifiedExteriorPieceIso_hom_inv_app n U a
  have hb : (A.sheafifiedExteriorPieceIso m).hom.val.app U b' = b :=
    A.sheafifiedExteriorPieceIso_hom_inv_app m U b
  have hmul : (A.sheafifiedExteriorPieceIso (n + m)).inv.val.app U
      ((A.exterior.mul n m).app U a b) =
        ((SheafOfModules.sheafifiedExteriorAlgebra J F).mul n m).app U a' b' := by
    rw [← ha, ← hb, ← A.sheafifiedExteriorPieceIso_mul n m U a' b']
    exact SheafOfModules.iso_inv_hom_app_apply (A.sheafifiedExteriorPieceIso (n + m)) U _
  rw [A.koszulD_val_app ψ _ U _, hmul,
    SheafOfModules.koszulD_mul J F ψ (show n - 1 + 1 = n by ring) (show m - 1 + 1 = m by ring)
      (show n + m - 1 + 1 = n + m by ring) (by ring) (by ring) U a' b']
  rw [map_add (ConcreteCategory.hom
    ((A.sheafifiedExteriorPieceIso (n + m - 1)).hom.val.app U))]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Stacks.gradedCast_eq_degCast (by ring : (n - 1) + m = n + m - 1),
      ← Stacks.degCast_map (fun k => (A.sheafifiedExteriorPieceIso k).hom.val.app U)
        (by ring : (n - 1) + m = n + m - 1),
      A.sheafifiedExteriorPieceIso_mul (n - 1) m U _ b', hb, ← A.koszulD_val_app ψ _ U a]
  · rw [map_zsmul (ConcreteCategory.hom
      ((A.sheafifiedExteriorPieceIso (n + m - 1)).hom.val.app U)) (Int.negOnePow n : ℤ),
      Stacks.gradedCast_eq_degCast (by ring : n + (m - 1) = n + m - 1),
      ← Stacks.degCast_map (fun k => (A.sheafifiedExteriorPieceIso k).hom.val.app U)
        (by ring : n + (m - 1) = n + m - 1),
      A.sheafifiedExteriorPieceIso_mul n (m - 1) U a' _, ha, ← A.koszulD_val_app ψ _ U b]

/-- **The degree-zero exterior section a scalar names is that scalar times the unit.** The scalar
is read in through the degree-zero identification of the tensor algebra and the quotient map onto
the exterior algebra, which is the route the `d_generator` field of
`Stacks.RegularSequence.KoszulChainData` phrases its value in. -/
theorem tensorToExterior_tensorPieceIso_inv_eq_smul_one
    (φ : F ⟶ SheafOfModules.unit (toRingCat J Osharp)) (U : Cᵒᵖ) (e : F.val.obj U) :
    (A.tensorToExterior.app 0).val.app U
        ((A.tensorPieceIso 0).inv.val.app U (φ.val.app U e)) =
      Stacks.RegularSequence.unitScalar φ U e • A.exterior.one.eval U := by
  have hc : A.tensorPieceZeroIsoUnit.hom.val.app U
      ((A.tensorPieceIso 0).inv.val.app U (φ.val.app U e)) =
        Stacks.RegularSequence.unitScalar φ U e :=
    Stacks.RegularSequence.iso_hom_val_app_inv_val_app (A.tensorPieceIso 0) U (φ.val.app U e)
  rw [← A.tensorPieceZeroIsoUnit_smul_one U _ _ hc, map_smul, A.tensorToExterior.map_one U]

end Leibniz

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace Stacks.SheafOfModules

/-! ### The coordinate functional is the coordinate projection -/

section Coordinates

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]

/-- **The `j`-th coordinate functional of a finite free sheaf of modules is the `j`-th coordinate
projection**, read on local sections. The functional is the `j`-th coordinate form of
`Stacks.SheafOfModules.freeCoordBasis`, which is the standard basis of a product transported along
the coordinate isomorphism, and the coordinates of that isomorphism are by construction the values
of the projection morphisms. -/
theorem coordExteriorFunctional_dual_eq_freeProj (j : ι) (U : Cᵒᵖ)
    (e : (_root_.SheafOfModules.free (R := toRingCat J Osharp) ι).val.obj U) :
    (coordExteriorFunctional (Osharp := Osharp) j).dual U e =
      (freeProj (S := toRingCat J Osharp) j).val.app U e := by
  rw [coordExteriorFunctional_dual_apply, freeCoordBasis]
  rfl

end Coordinates

end Stacks.SheafOfModules

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### The coordinate contraction as Koszul chain data -/

section ChainData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  (A : TensorExteriorSymmetricAlgebras J (SheafOfModules.free (R := toRingCat J Osharp) ι))

/-- **The chain complex of the exterior powers of `A` whose differential is the coordinate
contraction `δⱼ`.** From degree `p` to degree `q` the differential is `δⱼ` when `q + 1 = p` and
zero otherwise; the composition of two successive differentials vanishes because the square of a
single coordinate contraction does. -/
def coordChain (j : ι) : ChainComplex (SheafOfModules.{w} (toRingCat J Osharp)) ℤ where
  X n := A.exterior.piece n
  d p q := if h : q + 1 = p then A.coordKoszulD j h else 0
  shape p q hpq := dite_eq_right (fun h : q + 1 = p => hpq h)
  d_comp_d' p q s hpq hqs := by
    have h1 : q + 1 = p := hpq
    have h2 : s + 1 = q := hqs
    rw [dite_eq_left h1, dite_eq_left h2]
    exact A.coordKoszulD_comp_coordKoszulD_self j h1 h2

/-- In adjacent degrees the differential of `coordChain` is the coordinate contraction. -/
theorem coordChain_d (j : ι) {p q : ℤ} (h : q + 1 = p) :
    (A.coordChain j).d p q = A.coordKoszulD j h := dite_eq_left h

/-- **The coordinate contraction `δⱼ` as the Koszul chain data of the `j`-th coordinate
projection.** The differential is `δⱼ`; it satisfies the graded Leibniz rule because the
transported Koszul differential of any functional does; its value on a degree-one generator is the
`j`-th coordinate of that generator, which is the value of the `j`-th coordinate projection; and
the associated chain complex is `coordChain`.

Everything `Stacks.RegularSequence.KoszulChainData` proves of a Koszul chain complex therefore
applies to `δⱼ`, in particular the alternating-sum formula on the exterior basis and the
identification of the induced map on stalks with the ring-level Koszul differential. -/
def coordKoszulChainData (j : ι) :
    Stacks.RegularSequence.KoszulChainData A
      (Stacks.SheafOfModules.freeProj (S := toRingCat J Osharp) j) where
  d n := A.coordKoszulD j (show n - 1 + 1 = n by ring)
  d_mul n m U a b :=
    A.koszulD_mul (Stacks.SheafOfModules.coordExteriorFunctional j) n m U a b
  d_generator U e := by
    rw [A.tensorToExterior_tensorPieceIso_inv_eq_smul_one _ U e]
    refine (A.exteriorPieceZeroIsoUnit_smul_one U _ _ ?_).symm
    refine Eq.trans (A.exteriorPieceZeroIsoUnit_koszulD_exteriorGenerator
      (Stacks.SheafOfModules.coordExteriorFunctional j) U e) ?_
    exact Stacks.SheafOfModules.coordExteriorFunctional_dual_eq_freeProj j U e
  chain := A.coordChain j
  chain_X _ := rfl
  chain_d n :=
    Eq.trans (Eq.trans (Category.id_comp _) (Category.comp_id _))
      (A.coordChain_d j (show n - 1 + 1 = n by ring))

/-- The differential of the coordinate chain data is the coordinate contraction. -/
theorem coordKoszulChainData_d (j : ι) (n : ℤ) :
    (A.coordKoszulChainData j).d n = A.coordKoszulD j (show n - 1 + 1 = n by ring) := rfl

end ChainData

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
