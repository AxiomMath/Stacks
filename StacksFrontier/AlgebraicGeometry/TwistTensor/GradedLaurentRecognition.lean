module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PieceZeroUnit
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

/-!
# Recognising a Laurent algebra: the degreewise comparison

Let `T` be a scheme and `ℛ` a sheaf of `ℤ`-graded `𝒪_T`-algebras all of whose multiplications
`ℛ_i ⊗ ℛ_j ⟶ ℛ_{i+j}` are isomorphisms. Such a graded algebra is a "`ℤ`-torsor of invertible
modules": every piece is determined by the degree-one piece, and for an invertible `ℒ` with
`β : ℛ_1 ≅ ℒ` the pieces are the integral tensor powers of `ℒ`,

`ℛ_n ≅ ℒ^{⊗ n}` for every `n : ℤ`,

that is, the homogeneous pieces of the Laurent algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of Section 27.15. This
file constructs that **degreewise** comparison.

The reason this is wanted is [Stacks, Tag 01O1]. The source of that tag's `θ` is
`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd))`, which
`Stacks.AlgebraicGeometry.RelativeVeroneseTwists.pullbackTwistVeronese` builds out of the glued
twists of [Stacks, Tag 01NR], and its target is `⨁_{n ∈ ℤ} ℒ^{⊗ n}`; the `d`-divisible glued twists
have invertible multiplications and invertible pieces, by
`...RelativeVeroneseTwists.isIso_mulSheaf_twistVeronese` and `isInvertible_twistVeronese_piece`, so
the comparison `θ` asks for is an instance of the recognition statement. The relative form of
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt` — `𝒪(d)^{⊗ n} ≅ 𝒪(nd)` on `Proj_S(𝒜)` — is the same
instance.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.PieceCmp`: the type of the comparison in a
  single degree.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.succStep` and `predStep`: the two steps of the
  induction, raising and lowering the degree by one.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso`: **the comparison `ℛ_n ≅ ℒ^{⊗ n}`,
  in every integer degree.**

## Main results

* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso_zero`, `pieceIso_succ` and
  `pieceIso_pred`: the recursion the comparison satisfies.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.succStep_hom`: the raising step written out.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.mulSheaf_comp_pieceIso_succ`: **the
  multiplicativity of the comparison in the bidegree `(n, 1)`**, which holds by construction in
  both directions of the induction. This is the anchoring column of the two-variable induction
  that full multiplicativity runs on, in
  `StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul`.

## The construction

Exactly the two-sided induction of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback.pieceIso`, with the pullback
comparison of the twists replaced by the multiplication of `ℛ`.

* Degree `0`: both sides are the structure sheaf. On the right by [Stacks, Tag 01CU]; on the left
  by `Stacks.AlgebraicGeometry.ProjRepresentsF1.pieceZeroIsoUnit`, the inverse of the algebra
  unit, which is an isomorphism because the degree-`(0,0)` multiplication is one and `ℛ_0` is
  invertible.
* Upwards: `ℛ_{n+1} ≅ ℛ_n ⊗ ℛ_1 ≅ ℛ_n ⊗ ℒ ≅ ℒ^{⊗ n} ⊗ ℒ ≅ ℒ^{⊗ (n+1)}`, the first step being the
  inverse of the multiplication in the bidegree `(n, 1)` and the last the successor comparison of
  [Stacks, Tag 01CU].
* Downwards: there is no recursion available, because the negative tensor powers of [Stacks, Tag
  01CU] are iterates of a chosen quasi-inverse of right tensoring by `ℒ`. The step is taken by
  cancellation instead: `- ⊗ ℒ` is an equivalence, hence fully faithful, and the comparison at `n`
  is the unique preimage of the comparison at `n + 1` read through the two splittings.

## Where multiplicativity is proved

Not here. `mulSheaf_comp_pieceIso_succ` is the bidegree `(n, 1)` column; the two-variable
statement

`ℛ_n ⊗ ℛ_m ⟶ ℛ_{n+m}` followed by `pieceIso (n + m)` equals
`pieceIso n ⊗ pieceIso m` followed by `ℒ^{⊗ n} ⊗ ℒ^{⊗ m} ≅ ℒ^{⊗ (n+m)}`

is `Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso_mul` of
`StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul`, which runs the induction of
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul` on the column below with
`Stacks.AlgebraicGeometry.ThetaMul.square_step` and `Stacks.Monoidal.square_step_left`, fed with
the associativity constraints `Stacks.TensorSheafWorld.mulSheaf_assoc` on the left and
`...RelativeProjQcohSheaf.LaurentPullback.mulIso_assoc` on the right. The same file assembles the
degreewise family into the recognition theorem `ℛ ≅ ⨁_n ℒ^{⊗ n}`
(`...GradedLaurentRecognition.gradedIso`), through
`Stacks.AlgebraicGeometry.GradedVeronese.isoOfPiecesOfHoms`, and
`StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison` applies that to build the
comparison [Stacks, Tag 01O1] needs.

No `stacks` attribute is attached: the statement here is an auxiliary comparison, not an assertion
of a tag.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.GradedLaurentRecognition

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T : Scheme.{u}}
  (R : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace))
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (β : R.piece 1 ≅ L)
  (hmul : ∀ i j : ℤ, IsIso (SheafOfModules.GradedAlgebra.mulSheaf R i j))

/-- **Tensoring on the right by `ℒ` is an equivalence**: the instance
`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible` with its two site
data given explicitly. -/
local instance isEquivalence_tensorRight :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).IsEquivalence :=
  Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible
    T.toRingedSpace.presheaf (isSheafStruct T) L

/-- The comparison of the degree-`n` piece of `ℛ` with the `n`-th integral tensor power of `ℒ`. -/
abbrev PieceCmp (n : ℤ) : Type u := R.piece n ≅ (laurent L).piece n

/-- The multiplication of `ℛ` in a bidegree, as an isomorphism. -/
abbrev mulIsoR (i j : ℤ) : R.piece i ⊗ R.piece j ≅ R.piece (i + j) :=
  @asIso _ _ _ _ (SheafOfModules.GradedAlgebra.mulSheaf R i j) (hmul i j)

/-- **Splitting off the top factor upstairs**: `ℛ_{n+1} ≅ ℛ_n ⊗ ℒ`, the inverse of the
multiplication in the bidegree `(n, 1)` followed by `β` on the second factor, with target written
as the image of `ℛ_n` under right tensoring by `ℒ`. -/
def climbIso (n : ℤ) :
    R.piece (n + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).obj (R.piece n) :=
  (mulIsoR R hmul n 1).symm ≪≫ MonoidalCategory.whiskerLeftIso (R.piece n) β

/-- **Raising the degree by one.** Split the extra factor off by `climbIso`, apply the comparison
at `n` in the first factor, and reassemble by the successor comparison of [Stacks, Tag 01CU]. -/
def succStep (n : ℤ) (φ : PieceCmp R L n) : PieceCmp R L (n + 1) :=
  climbIso R L β hmul n ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).mapIso φ ≪≫
    tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T) L n

/-- **Lowering the degree by one**, by cancellation: tensoring on the right by `ℒ` is an
equivalence, hence fully faithful, and the two sides of the comparison at `n` tensored by `ℒ` are
the two sides of the comparison at `n + 1`. -/
def predStep (n : ℤ) (ψ : PieceCmp R L (n + 1)) : PieceCmp R L n :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).preimageIso
    ((climbIso R L β hmul n).symm ≪≫ ψ ≪≫
      (tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T) L n).symm)

/-- Tensoring the lowering step by `ℒ` undoes the cancellation it was defined by. -/
theorem mapIso_predStep (n : ℤ) (ψ : PieceCmp R L (n + 1)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).mapIso
        (predStep R L β hmul n ψ) =
      (climbIso R L β hmul n).symm ≪≫ ψ ≪≫
        (tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T) L n).symm :=
  Iso.ext (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).map_preimage _)

/-- Lowering and then raising the degree is the identity. -/
@[simp] theorem succStep_predStep (n : ℤ) (ψ : PieceCmp R L (n + 1)) :
    succStep R L β hmul n (predStep R L β hmul n ψ) = ψ := by
  simp only [succStep, mapIso_predStep]
  exact iso_conj_left _ _ _

/-- Raising and then lowering the degree is the identity. -/
@[simp] theorem predStep_succStep (n : ℤ) (φ : PieceCmp R L n) :
    predStep R L β hmul n (succStep R L β hmul n φ) = φ := by
  simp only [predStep, succStep]
  exact (congrArg _ (iso_conj_right _ _ _)).trans (Functor.preimageIso_mapIso _ _)

variable (hinv : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
  (R.piece 0))

/-- **The comparison in degree `0`**: both sides are the structure sheaf, the left one by the
inverse of the algebra unit. -/
def zeroCmp : PieceCmp R L 0 :=
  Stacks.AlgebraicGeometry.ProjRepresentsF1.pieceZeroIsoUnit R (isSheafStruct T) hinv (hmul 0 0)

/-- The comparison in the nonnegative degrees, by recursion. -/
def pieceIsoNat : (j : ℕ) → PieceCmp R L (j : ℤ)
  | 0 => zeroCmp R L hmul hinv
  | j + 1 => succStep R L β hmul (j : ℤ) (pieceIsoNat j)

/-- The comparison in the negative degrees, by recursion downwards. -/
def pieceIsoNeg : (j : ℕ) → PieceCmp R L (Int.negSucc j)
  | 0 => predStep R L β hmul (Int.negSucc 0) (zeroCmp R L hmul hinv)
  | j + 1 => predStep R L β hmul (Int.negSucc (j + 1)) (pieceIsoNeg j)

/-- **The comparison `ℛ_n ≅ ℒ^{⊗ n}`, in every integer degree.** -/
def pieceIso : (n : ℤ) → PieceCmp R L n
  | Int.ofNat j => pieceIsoNat R L β hmul hinv j
  | Int.negSucc j => pieceIsoNeg R L β hmul hinv j

/-- In a nonnegative degree the comparison is `pieceIsoNat`. -/
@[simp] theorem pieceIso_ofNat (j : ℕ) :
    pieceIso R L β hmul hinv (j : ℤ) = pieceIsoNat R L β hmul hinv j := rfl

/-- In a negative degree the comparison is `pieceIsoNeg`. -/
@[simp] theorem pieceIso_negSucc (j : ℕ) :
    pieceIso R L β hmul hinv (Int.negSucc j) = pieceIsoNeg R L β hmul hinv j := rfl

/-- The comparison in degree zero is the inverse of the algebra unit. -/
theorem pieceIso_zero : pieceIso R L β hmul hinv 0 = zeroCmp R L hmul hinv := rfl

/-- **The comparison satisfies the raising recursion in every degree.** -/
theorem pieceIso_succ (n : ℤ) :
    pieceIso R L β hmul hinv (n + 1) = succStep R L β hmul n (pieceIso R L β hmul hinv n) := by
  match n with
  | Int.ofNat j => rfl
  | Int.negSucc 0 =>
      exact (succStep_predStep R L β hmul (Int.negSucc 0) (zeroCmp R L hmul hinv)).symm
  | Int.negSucc (j + 1) =>
      exact (succStep_predStep R L β hmul (Int.negSucc (j + 1))
        (pieceIsoNeg R L β hmul hinv j)).symm

/-- **The comparison satisfies the lowering recursion in every degree.** -/
theorem pieceIso_pred (n : ℤ) :
    pieceIso R L β hmul hinv n = predStep R L β hmul n (pieceIso R L β hmul hinv (n + 1)) := by
  rw [pieceIso_succ R L β hmul hinv n, predStep_succStep]

/-- Cancelling an isomorphism against its inverse in the middle of a four-fold composite, in a
bare category and with every object and morphism free. -/
theorem column {D : Type*} [Category D] {X Y P Q V : D}
    (m : X ⟶ Y) (mi : Y ⟶ X) (hm : m ≫ mi = CategoryStruct.id X)
    (w : X ⟶ P) (p : P ⟶ Q) (s : Q ⟶ V) (t : X ⟶ Q) (ht : w ≫ p = t) :
    m ≫ (mi ≫ w) ≫ p ≫ s = t ≫ s := by
  subst ht
  simp [reassoc_of% hm]

/-- The raising step written out: the inverse of the multiplication in the bidegree `(n, 1)`, then
`β` on the second factor, then the comparison at `n` on the first, then the successor comparison of
[Stacks, Tag 01CU]. -/
theorem succStep_hom (n : ℤ) (φ : PieceCmp R L n) :
    (succStep R L β hmul n φ).hom =
      ((mulIsoR R hmul n 1).inv ≫ MonoidalCategoryStruct.whiskerLeft (R.piece n) β.hom) ≫
        (φ.hom ▷ L) ≫
          (tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T) L n).hom := by
  change ((mulIsoR R hmul n 1).inv ≫ MonoidalCategoryStruct.whiskerLeft (R.piece n) β.hom) ≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).mapIso φ).hom ≫
        (tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T) L n).hom = _
  have h : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨T.toRingedSpace.presheaf, T.toRingedSpace.IsSheaf⟩).flip.obj L).mapIso φ).hom =
      φ.hom ▷ L :=
    bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T) φ.hom L
  rw [h]
  rfl

/-- **The multiplicativity of the comparison in the bidegree `(n, 1)`**: the multiplication of `ℛ`
in that bidegree, followed by the comparison at `n + 1`, is the comparison at `n` on the first
factor and `β` on the second, followed by the successor comparison of [Stacks, Tag 01CU]. -/
theorem mulSheaf_comp_pieceIso_succ (n : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf R n 1 ≫ (pieceIso R L β hmul hinv (n + 1)).hom =
      ((pieceIso R L β hmul hinv n).hom ⊗ₘ β.hom) ≫
        (tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T) L n).hom := by
  rw [pieceIso_succ R L β hmul hinv n, succStep_hom]
  exact column _ _ (mulIsoR R hmul n 1).hom_inv_id _ _ _ _
    (MonoidalCategory.tensorHom_def' _ _).symm

end Stacks.AlgebraicGeometry.GradedLaurentRecognition

end
