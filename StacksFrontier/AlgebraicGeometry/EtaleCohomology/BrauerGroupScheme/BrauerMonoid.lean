module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Monoidal

/-!
# The Brauer group of a scheme is a commutative monoid

Let `S` be a scheme. `Stacks.EtaleCohomology.BrauerScheme.BrauerGroup S` is the set of
similarity classes of Azumaya `𝒪_S`-algebras of [Stacks, Tag 0A2J], and
`Stacks.EtaleCohomology.BrauerScheme.BrauerGroup.mul` is the operation induced by the tensor
product. This file equips `Br(S)` with the rest of the algebraic structure that operation
carries: the associativity, commutativity and unit laws, hence a `CommMonoid` instance, hence
the powers `x ^ n`.

The neutral element is the class of the `1 × 1` matrix algebra `Mat_1(𝒪_S)`, which is Azumaya
because `S` covers itself étale-locally by the identity (`idCover`), and which is a unit for
the tensor product up to similarity (`isSimilar_matrixAlgebraOne_tensor`). More generally an
algebra sheaf with trivial Brauer class — one that is the endomorphism algebra of a finite
locally free sheaf of modules of positive rank — is similar to `Mat_1(𝒪_S)`, so its class is
the neutral element (`brauerClass_eq_one_of_isTrivialClass`). The unit *algebra* sheaf `𝒪_S`
itself is similar to `Mat_1(𝒪_S)` (`isSimilar_tensorUnit_matrixAlgebraOne`), which is what
identifies the `n`-fold tensor power `A^{⊗ n}` of `Stacks.TensorPowers.natTensorPow` — whose
zeroth term is the unit algebra sheaf — with the Azumaya-packaged power `Azumaya.tensorPow`.

`Br(S)` is not known to be a group here: the inverse of the class of `A` is the class of the
opposite algebra `Aᵒᵖ`, and that needs the identification `A ⊗ Aᵒᵖ ≅ 𝓗om(A, A)` for an Azumaya
`A`, which the library does not have (see
`Stacks.EtaleCohomology.BrauerScheme.oppositeAlgebra`).

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.idCover`: the one-member étale covering of a scheme by
  itself.
* `Stacks.EtaleCohomology.BrauerScheme.Azumaya.one`: the trivial Azumaya algebra
  `Mat_1(𝒪_S)`, whose class is the neutral element of `Br(S)`.
* `Stacks.EtaleCohomology.BrauerScheme.Azumaya.tensorPow`: the `n`-fold tensor power of an
  Azumaya algebra sheaf, as an Azumaya algebra sheaf.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.isAzumaya_matrixAlgebra`: **`Mat_d(𝒪_S)` is Azumaya for
  `d ≥ 1`.**
* `Stacks.EtaleCohomology.BrauerScheme.IsAzumaya.of_iso`: the Azumaya condition depends only on
  the isomorphism class.
* `Stacks.EtaleCohomology.BrauerScheme.isSimilar_matrixAlgebraOne_tensor`: `Mat_1(𝒪_S)` is a
  unit for the tensor product up to similarity.
* `Stacks.EtaleCohomology.BrauerScheme.isSimilar_tensorUnit_matrixAlgebraOne`: the unit algebra
  sheaf `𝒪_S` is similar to `Mat_1(𝒪_S)`.
* `Stacks.EtaleCohomology.BrauerScheme.isSimilar_matrixAlgebraOne_of_isTrivialClass`: an
  algebra sheaf with trivial Brauer class is similar to `Mat_1(𝒪_S)`.
* **`Stacks.EtaleCohomology.BrauerScheme.instCommMonoidBrauerGroup`: the Brauer group of a
  scheme is a commutative monoid** for the operation of Tag 0A2J.
* `Stacks.EtaleCohomology.BrauerScheme.brauerClass_eq_one_of_isTrivialClass`: an Azumaya algebra
  sheaf with trivial Brauer class has class the neutral element.
* `Stacks.EtaleCohomology.BrauerScheme.IsAzumaya.natTensorPow`: a positive tensor power of an
  Azumaya algebra sheaf is Azumaya.
* `Stacks.EtaleCohomology.BrauerScheme.brauerClass_tensorPow` and
  `Stacks.EtaleCohomology.BrauerScheme.isSimilar_natTensorPow`: the class of the `n`-fold tensor
  power is the `n`-th power of the class, and the packaged power is similar to the monoidal one.
* `Stacks.EtaleCohomology.BrauerScheme.brauerClass_pow_eq_one_of_isTrivialClass_natTensorPow`:
  **if the `d`-fold tensor power of `A` has trivial Brauer class, then the class of `A` is
  annihilated by `d`.** This is the shape in which Tag 0A2L reduces to a statement about
  `A^{⊗ d}` alone.

## Implementation notes

The neutral element is taken to be the class of `Mat_1(𝒪_S)` rather than that of the unit
algebra sheaf `𝒪_S`, even though the two are similar: the Azumaya condition for `Mat_1(𝒪_S)`
is `nonempty_matrixAlgebraPullbackIso` on the identity covering, whereas for `𝒪_S` it would
need `𝓗om(𝒪_S, 𝒪_S) ≅ 𝒪_S` as algebra sheaves, i.e. the internal endomorphism monoid of the
monoidal unit, which the library does not identify with the unit monoid.

Every similarity below is exhibited by a chain of coherence isomorphisms together with
`endAlgebraTensorIso`, which is where the hypotheses on the auxiliary modules — finite local
freeness, needed for `𝓗om(E,E) ⊗ 𝓗om(F,F) ≅ 𝓗om(E ⊗ F, E ⊗ F)`, and positive rank, demanded
by `IsSimilar` itself — are consumed.

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

/-- The one-member étale covering of a scheme by itself, through the identity. -/
def idCover (S : Scheme.{u}) : Scheme.Cover.{u} Scheme.etalePrecoverage S :=
  Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ ↦ S) (fun _ ↦ 𝟙 S)
    (fun x ↦ ⟨⟨⟩, x, by simp⟩) (fun _ ↦ inferInstance)

/-- The only member of the identity covering is the identity. -/
@[simp]
lemma idCover_f (S : Scheme.{u}) (i : PUnit.{u + 1}) : (idCover S).f i = 𝟙 S := rfl

/-- **The matrix algebra `Mat_d(𝒪_S)` is Azumaya for `d ≥ 1`**: it is already a matrix algebra
on the one-member covering of `S` by itself. -/
theorem isAzumaya_matrixAlgebra (S : Scheme.{u}) {d : ℕ} (hd : 1 ≤ d) :
    IsAzumaya (matrixAlgebra S d) :=
  ⟨idCover S, fun _ ↦ d, fun _ ↦ hd, fun _ ↦ nonempty_matrixAlgebraPullbackIso (𝟙 S) d⟩

/-- **The Azumaya condition depends only on the isomorphism class** of a sheaf of
`𝒪_S`-algebras: the pullback along a member of a trivialising covering is a functor, so it
carries an isomorphism of algebra sheaves to one of their pullbacks. -/
theorem IsAzumaya.of_iso {S : Scheme.{u}} {A B : AlgebraSheaf S} (e : A ≅ B)
    (hA : IsAzumaya A) : IsAzumaya B := by
  obtain ⟨𝒰, d, hd, h⟩ := hA
  refine ⟨𝒰, d, hd, fun i ↦ ?_⟩
  obtain ⟨m⟩ := h i
  exact ⟨((algebraPullback (𝒰.f i)).mapIso e).symm ≪≫ m⟩

variable {S : Scheme.{u}}

/-- The free sheaf of `𝒪_S`-modules of rank one; `Mat_1(𝒪_S)` is its endomorphism algebra. -/
abbrev freeOne (S : Scheme.{u}) : ModuleSheaf S :=
  SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf)
    (ULift.{u, 0} (Fin 1))

/-- The free sheaf of modules of rank one is finite locally free. -/
theorem isFiniteLocallyFree_freeOne (S : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) (freeOne S) :=
  isFiniteLocallyFree_free _

/-- The free sheaf of modules of rank one has positive rank. -/
theorem hasPositiveRank_freeOne (S : Scheme.{u}) : HasPositiveRank (freeOne S) :=
  have : Nonempty (ULift.{u, 0} (Fin 1)) := ⟨⟨0⟩⟩
  hasPositiveRank_free _

/-- The tensor square of the free sheaf of rank one is finite locally free. -/
private theorem isFiniteLocallyFree_freeOne_tensor (S : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (C := Opens S)
      (J := Opens.grothendieckTopology S) (freeOne S ⊗ freeOne S) :=
  isFiniteLocallyFree_tensor (isFiniteLocallyFree_freeOne S) (isFiniteLocallyFree_freeOne S)

/-- The tensor square of the free sheaf of rank one has positive rank. -/
private theorem hasPositiveRank_freeOne_tensor (S : Scheme.{u}) :
    HasPositiveRank (freeOne S ⊗ freeOne S) :=
  hasPositiveRank_tensor (hasPositiveRank_freeOne S) (hasPositiveRank_freeOne S)

/-- `Mat_1(𝒪_S) ⊗ Mat_1(𝒪_S)` is the endomorphism algebra of the tensor square of `𝒪_S`. -/
private def endAlgebraFreeOneTensorIso (S : Scheme.{u}) :
    endAlgebra (freeOne S) ⊗ endAlgebra (freeOne S) ≅ endAlgebra (freeOne S ⊗ freeOne S) :=
  endAlgebraTensorIso (isFiniteLocallyFree_freeOne S) (isFiniteLocallyFree_freeOne S)

/-- **`Mat_1(𝒪_S)` is a unit for the tensor product up to similarity.** -/
theorem isSimilar_matrixAlgebraOne_tensor (A : AlgebraSheaf S) :
    IsSimilar (matrixAlgebra S 1 ⊗ A) A := by
  refine ⟨freeOne S, freeOne S ⊗ freeOne S, isFiniteLocallyFree_freeOne S,
    hasPositiveRank_freeOne S, isFiniteLocallyFree_freeOne_tensor S,
    hasPositiveRank_freeOne_tensor S, ⟨?_⟩⟩
  calc (matrixAlgebra S 1 ⊗ A) ⊗ endAlgebra (freeOne S)
      ≅ (A ⊗ matrixAlgebra S 1) ⊗ endAlgebra (freeOne S) :=
        tensorIso (β_ (matrixAlgebra S 1) A) (Iso.refl _)
    _ ≅ A ⊗ (matrixAlgebra S 1 ⊗ endAlgebra (freeOne S)) := α_ _ _ _
    _ ≅ A ⊗ endAlgebra (freeOne S ⊗ freeOne S) :=
        whiskerLeftIso A (endAlgebraFreeOneTensorIso S)

/-- **The unit algebra sheaf `𝒪_S` is similar to `Mat_1(𝒪_S)`.** -/
theorem isSimilar_tensorUnit_matrixAlgebraOne (S : Scheme.{u}) :
    IsSimilar (𝟙_ (AlgebraSheaf S)) (matrixAlgebra S 1) := by
  refine ⟨freeOne S ⊗ freeOne S, freeOne S, isFiniteLocallyFree_freeOne_tensor S,
    hasPositiveRank_freeOne_tensor S, isFiniteLocallyFree_freeOne S,
    hasPositiveRank_freeOne S, ⟨?_⟩⟩
  calc 𝟙_ (AlgebraSheaf S) ⊗ endAlgebra (freeOne S ⊗ freeOne S)
      ≅ endAlgebra (freeOne S ⊗ freeOne S) := λ_ _
    _ ≅ endAlgebra (freeOne S) ⊗ endAlgebra (freeOne S) := (endAlgebraFreeOneTensorIso S).symm

/-- **An algebra sheaf with trivial Brauer class is similar to `Mat_1(𝒪_S)`.** -/
theorem isSimilar_matrixAlgebraOne_of_isTrivialClass {C : AlgebraSheaf S}
    (h : IsTrivialClass C) : IsSimilar C (matrixAlgebra S 1) := by
  obtain ⟨E, hE, hEp, ⟨e⟩⟩ := h
  refine ⟨freeOne S, E, isFiniteLocallyFree_freeOne S, hasPositiveRank_freeOne S, hE, hEp, ⟨?_⟩⟩
  calc C ⊗ endAlgebra (freeOne S)
      ≅ endAlgebra E ⊗ endAlgebra (freeOne S) := tensorIso e (Iso.refl _)
    _ ≅ endAlgebra (E ⊗ freeOne S) := endAlgebraTensorIso hE (isFiniteLocallyFree_freeOne S)
    _ ≅ endAlgebra (freeOne S ⊗ E) := endAlgebraCongr (β_ E (freeOne S))
    _ ≅ endAlgebra (freeOne S) ⊗ endAlgebra E :=
        (endAlgebraTensorIso (isFiniteLocallyFree_freeOne S) hE).symm

/-- The trivial Azumaya `𝒪_S`-algebra `Mat_1(𝒪_S)`, whose class is the neutral element of
`Br(S)`. -/
def Azumaya.one (S : Scheme.{u}) : Azumaya S :=
  ⟨matrixAlgebra S 1, isAzumaya_matrixAlgebra S le_rfl⟩

/-- The element `1` of `Br(S)` is the class of the trivial Azumaya algebra `Mat_1(𝒪_S)`. -/
instance : One (BrauerGroup S) := ⟨brauerClass (Azumaya.one S)⟩

/-- The neutral element of `Br(S)` is the class of `Mat_1(𝒪_S)`. -/
lemma one_eq_brauerClass_one (S : Scheme.{u}) :
    (1 : BrauerGroup S) = brauerClass (Azumaya.one S) := rfl

/-- **The operation of the Brauer group is associative**, by the associator of the tensor
product of sheaves of algebras. -/
theorem BrauerGroup.mul_assoc (x y z : BrauerGroup S) : x * y * z = x * (y * z) := by
  refine Quotient.inductionOn₃ x y z fun A B C ↦ ?_
  exact Quotient.sound (IsSimilar.of_iso (α_ A.1 B.1 C.1))

/-- **The operation of the Brauer group is commutative**, by the symmetry of the tensor product
of sheaves of algebras. -/
theorem BrauerGroup.mul_comm (x y : BrauerGroup S) : x * y = y * x := by
  refine Quotient.inductionOn₂ x y fun A B ↦ ?_
  exact Quotient.sound (IsSimilar.of_iso (β_ A.1 B.1))

/-- **The class of `Mat_1(𝒪_S)` is a left unit** for the operation of the Brauer group. -/
theorem BrauerGroup.one_mul (x : BrauerGroup S) : 1 * x = x := by
  refine Quotient.inductionOn x fun A ↦ ?_
  exact Quotient.sound (isSimilar_matrixAlgebraOne_tensor A.1)

/-- **The Brauer group of a scheme is a commutative monoid** for the operation of Tag 0A2J,
with the class of `Mat_1(𝒪_S)` as neutral element. -/
instance : CommMonoid (BrauerGroup S) where
  mul := (· * ·)
  one := 1
  mul_assoc := BrauerGroup.mul_assoc
  one_mul := BrauerGroup.one_mul
  mul_one x := (BrauerGroup.mul_comm x 1).trans (BrauerGroup.one_mul x)
  mul_comm := BrauerGroup.mul_comm

/-- **An Azumaya algebra sheaf with trivial Brauer class has class the neutral element of
`Br(S)`.** -/
theorem brauerClass_eq_one_of_isTrivialClass (A : Azumaya S) (h : IsTrivialClass A.1) :
    brauerClass A = 1 :=
  Quotient.sound (isSimilar_matrixAlgebraOne_of_isTrivialClass h)

/-- The `n`-fold tensor power of an Azumaya `𝒪_S`-algebra, as an Azumaya `𝒪_S`-algebra; the
zeroth power is the trivial one. -/
def Azumaya.tensorPow (A : Azumaya S) : ℕ → Azumaya S
  | 0 => Azumaya.one S
  | n + 1 => Azumaya.tensor A (Azumaya.tensorPow A n)

/-- **The class of the `n`-fold tensor power is the `n`-th power of the class.** -/
@[simp]
theorem brauerClass_tensorPow (A : Azumaya S) (n : ℕ) :
    brauerClass (A.tensorPow n) = brauerClass A ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    show brauerClass (Azumaya.tensor A (A.tensorPow n)) = _
    rw [brauerClass_tensor, ih, pow_succ']

/-- **The monoidal `n`-fold tensor power of an Azumaya algebra sheaf is similar to its
Azumaya-packaged power.** The two differ only in the zeroth term — the unit algebra sheaf
`𝒪_S` against `Mat_1(𝒪_S)` — and those are similar. -/
theorem isSimilar_natTensorPow (A : Azumaya S) (n : ℕ) :
    IsSimilar (Stacks.TensorPowers.natTensorPow A.1 n) (A.tensorPow n).1 := by
  induction n with
  | zero => exact isSimilar_tensorUnit_matrixAlgebraOne S
  | succ n ih =>
    refine IsSimilar.trans (IsSimilar.tensor ih (IsSimilar.refl A.1)) ?_
    exact IsSimilar.of_iso (β_ (A.tensorPow n).1 A.1)

/-- **A positive tensor power of an Azumaya algebra sheaf is Azumaya.** The zeroth power is the
unit algebra sheaf, for which the Azumaya condition is not available here; see the
implementation notes. -/
theorem IsAzumaya.natTensorPow {A : AlgebraSheaf S} (hA : IsAzumaya A) {d : ℕ} (hd : 1 ≤ d) :
    IsAzumaya (Stacks.TensorPowers.natTensorPow A d) := by
  induction d with
  | zero => exact absurd hd (by omega)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact IsAzumaya.of_iso (λ_ A).symm hA
    · exact IsAzumaya.tensor (ih hn) hA

/-- **If the `d`-fold tensor product `A^{⊗ d}` of an Azumaya `𝒪_S`-algebra has trivial Brauer
class, then the class of `A` in `Br(S)` is annihilated by `d`.** This is the shape in which
[Stacks, Tag 0A2L] reduces to a statement about `A^{⊗ d}` alone: that lemma's hypothesis is
that `A` is locally free of rank `d ^ 2`, and its proof produces a finite locally free sheaf of
modules `H` of positive rank with `A^{⊗ d} ≅ 𝓗om(H, H)`, which is exactly
`IsTrivialClass (A^{⊗ d})`. -/
theorem brauerClass_pow_eq_one_of_isTrivialClass_natTensorPow (A : Azumaya S) (d : ℕ)
    (h : IsTrivialClass (Stacks.TensorPowers.natTensorPow A.1 d)) :
    brauerClass A ^ d = 1 := by
  rw [← brauerClass_tensorPow]
  exact Quotient.sound (IsSimilar.trans (isSimilar_natTensorPow A d).symm
    (isSimilar_matrixAlgebraOne_of_isTrivialClass h))

end Stacks.EtaleCohomology.BrauerScheme
