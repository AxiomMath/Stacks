module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerPullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SheafInternalHomFirstVariable

/-!
# Ranks of the sheaves of modules occurring in the Brauer group of a scheme

[Stacks, Tag 0A2L] says that an Azumaya `𝒪_S`-algebra whose underlying sheaf of modules is
finite locally free of rank `d ^ 2` has Brauer class annihilated by `d`. Reading the hypothesis
and recovering `d` from a local trivialisation is a bookkeeping exercise about the rank
predicate `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, and this file collects
the pieces of it.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.hasPositiveRank_of_rank`: a sheaf of modules of rank
  `r` with `0 < r` has positive rank in the sense of
  `Stacks.EtaleCohomology.BrauerScheme.HasPositiveRank`.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPow_X`: the underlying sheaf of modules of a
  tensor power of a sheaf of algebras is that tensor power of the underlying sheaf of modules.
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFreeOfRank_tensor` and
  `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFreeOfRank_natTensorPow`: the rank of a
  tensor product is the product of the ranks, and the rank of an `n`-th tensor power is the
  `n`-th power of the rank.
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFreeOfRank_matrixAlgebra`: **the sheaf of
  `d × d` matrices over `𝒪_S` is finite locally free of rank `d ^ 2`.**
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFreeOfRank_modulePullback`: the rank is
  unchanged by pullback along a morphism of schemes.
* `Stacks.EtaleCohomology.BrauerScheme.rank_eq_of_point`: **the rank is unique** on a scheme
  with a point, Tag 01C9.
* `Stacks.EtaleCohomology.BrauerScheme.eq_of_pullback_matrixAlgebra_iso`: **the size of a matrix
  algebra trivialising a sheaf of algebras is determined by the rank of its underlying sheaf of
  modules.** For `A` with `A.X` of rank `d ^ 2` and `φ^* A ≅ Mat_m(𝒪_T)` with `T` carrying a
  point, `m = d`. This is the step by which [Stacks, Tag 0A2L] reads its `d` off a
  trivialisation.

## Implementation notes

`isFiniteLocallyFreeOfRank_matrixAlgebra` goes through duality rather than through the
coproduct decomposition of the free module. The free sheaf `F` of rank `d` is dualizable
(`Stacks.EtaleCohomology.BrauerScheme.nonempty_hasRightDual_of_isFiniteLocallyFree`), so
`𝓗om(F, F) ≅ F ⊗ F^∨` by `CategoryTheory.MonoidalClosed.ihomDualHom`; a dual of `F` is
isomorphic to `F` itself by `Stacks.EtaleCohomology.BrauerScheme.dualFreeIso`, which reads the
dual as `𝓗om(F, 𝒪_S)`, a finite product of copies of `𝒪_S`, hence their coproduct, which is
`F`; and `F ⊗ F` is free on the product of the index types. The index set `Fin d × Fin d` then
has cardinality `d ^ 2`.

`rank_eq_of_point` is read off `LocallyFreeRank.locallyFreeRank`, the bundled locally constant
rank function of Tag 01C9. The hypothesis there is that the sheaf of modules is typed over
`LocallyFreeRank.toRingSheaf`, which is the same type as `ModuleSheaf` but not the same term, so
the sheaf and both of its local-generator presentations are re-ascribed by `let` before the rank
identification is applied; the final equality of cardinals is assembled as a chain of `Eq.trans`
rather than by `rw`, whose motive check at those re-ascribed terms exhausts the elaborator.

## References

* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

variable {S : Scheme.{u}}

/-- **A sheaf of `𝒪_S`-modules of positive rank `r` has positive rank** in the sense of
`Stacks.EtaleCohomology.BrauerScheme.HasPositiveRank`: the local bases are the ones witnessing
the rank, and each of their index types is equivalent to `Fin r`, hence inhabited. -/
theorem hasPositiveRank_of_rank {E : ModuleSheaf S} {r : ℕ} (hr : 0 < r)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) E r) : HasPositiveRank E := by
  obtain ⟨q, hq, hrk⟩ := h.exists_isFiniteLocallyFreeOfRankData
  exact ⟨q, hq, fun i => ⟨(hrk i).some.symm ⟨0, hr⟩⟩⟩

/-- **The underlying sheaf of modules of a tensor power of a sheaf of `𝒪_S`-algebras** is the
tensor power of its underlying sheaf of modules: the tensor product of sheaves of algebras is
the tensor product of the underlying sheaves of modules, and the unit algebra is `𝒪_S`. -/
theorem natTensorPow_X (A : AlgebraSheaf S) :
    ∀ n : ℕ, (Stacks.TensorPowers.natTensorPow A n).X =
      Stacks.TensorPowers.natTensorPow A.X n
  | 0 => rfl
  | n + 1 => congrArg (· ⊗ A.X) (natTensorPow_X A n)

/-- **The rank of a tensor product of sheaves of `𝒪_S`-modules is the product of the ranks.**
The local bases of the tensor product are indexed by the products of the two index types, so
`Fin r × Fin s ≃ Fin (r * s)` supplies the rank condition. -/
theorem isFiniteLocallyFreeOfRank_tensor {E F : ModuleSheaf S} {r s : ℕ}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) E r)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) F s) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) (E ⊗ F) (r * s) := by
  obtain ⟨qE, hqE, hrE⟩ := hE.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨qF, hqF, hrF⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  let := hqE
  let := hqF
  exact ⟨Stacks.SheafOfModules.localGeneratorsDataTensor S.sheaf qE qF,
    Stacks.SheafOfModules.isLocallyFreeData_localGeneratorsDataTensor S.sheaf qE qF,
    fun z => ⟨((hrE z.1).some.prodCongr (hrF z.2.1).some).trans finProdFinEquiv⟩⟩

/-- **The unit sheaf of `𝒪_S`-modules is finite locally free of rank `1`.** -/
theorem isFiniteLocallyFreeOfRank_tensorUnit (S : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) (𝟙_ (ModuleSheaf S)) 1 :=
  AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit S

/-- **The rank of a tensor power of a sheaf of `𝒪_S`-modules is the power of the rank**: the
zeroth power is `𝒪_S`, of rank `1`, and each further factor multiplies the rank by `r`. -/
theorem isFiniteLocallyFreeOfRank_natTensorPow {E : ModuleSheaf S} {r : ℕ}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) E r) :
    ∀ n : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) (Stacks.TensorPowers.natTensorPow E n) (r ^ n)
  | 0 => isFiniteLocallyFreeOfRank_tensorUnit S
  | n + 1 => (pow_succ r n).symm ▸
      isFiniteLocallyFreeOfRank_tensor (isFiniteLocallyFreeOfRank_natTensorPow hE n) hE

/-- **A free sheaf of `𝒪_S`-modules on a finite index type is self-dual**: any dual of it is
isomorphic to it. A dual is `𝓗om(F, 𝒪_S)`, which is the `ι`-fold product of `𝒪_S` because the
internal hom is continuous in its first variable, and a finite product of copies of `𝒪_S` is the
coproduct of those copies, i.e. the free module again. -/
def dualFreeIso (S : Scheme.{u}) (ι : Type u) [Finite ι] (Y : ModuleSheaf S)
    [ExactPairing (SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) ι) Y] :
    Y ≅ SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) ι :=
  letI : Limits.HasFiniteBiproducts (ModuleSheaf S) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  rightDualIsoIhomUnit (SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) ι) Y ≪≫
    Stacks.SheafOfModules.InternalHom.ihomFreeIsoProduct S.sheaf
      (SheafOfModules.unit (Tensor.ringSheaf S.sheaf)) ι ≪≫
    Limits.biproductIso _

/-- **The sheaf of `d × d` matrices over `𝒪_S` is finite locally free of rank `d ^ 2`.** The free
sheaf `F` of rank `d` is dualizable, so `𝓗om(F, F) ≅ F ⊗ F^∨`, and `F^∨ ≅ F` by `dualFreeIso`;
a tensor product of free sheaves is free on the product of the index types. -/
theorem isFiniteLocallyFreeOfRank_matrixAlgebra (S : Scheme.{u}) (d : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) (matrixAlgebra S d).X (d ^ 2) := by
  obtain ⟨hdual⟩ := nonempty_hasRightDual_of_isFiniteLocallyFree
    (isFiniteLocallyFree_free (S := S) (ULift.{u, 0} (Fin d)))
  let := hdual
  have e : (matrixAlgebra S d).X ≅
      SheafOfModules.free (R := Tensor.ringSheaf S.sheaf)
        (ULift.{u, 0} (Fin d) × ULift.{u, 0} (Fin d)) :=
    (asIso (MonoidalClosed.ihomDualHom
        (SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d)))
        ((SheafOfModules.free (R := Tensor.ringSheaf S.sheaf) (ULift.{u, 0} (Fin d)))ᘁ)
        (SheafOfModules.free (R := Tensor.ringSheaf S.sheaf)
          (ULift.{u, 0} (Fin d))))).symm ≪≫
      whiskerLeftIso _ (dualFreeIso S (ULift.{u, 0} (Fin d)) _) ≪≫
      Stacks.SheafOfModules.freeTensorFreeIso (Opens.grothendieckTopology S) (Osharp := S.sheaf)
        _ _
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
    (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv _ (d ^ 2)
      ((Equiv.ulift.prodCongr Equiv.ulift).trans
        (finProdFinEquiv.trans (finCongr (pow_two d).symm))))

/-- **The pullback of a sheaf of `𝒪_S`-modules of rank `r` has rank `r`.** This is
`Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData` read at the spelling of this
namespace: `modulePullback φ` is `AlgebraicGeometry.Scheme.Modules.pullback φ`. -/
theorem isFiniteLocallyFreeOfRank_modulePullback {T S : Scheme.{u}} (φ : T ⟶ S)
    {E : ModuleSheaf S} {r : ℕ}
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens T)
      (J := Opens.grothendieckTopology T) ((modulePullback φ).obj E) r :=
  have : (_root_.SheafOfModules.pushforward.{u} φ.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction φ).isRightAdjoint
  Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData φ.base φ.toRingCatSheafHom E r h

/-- **The rank of a finite locally free sheaf of modules on a scheme with a point is unique.**
A point of the scheme lies in a member of each of the two local-generator presentations, and the
two index types there both compute the rank of the sheaf at that point, Tag 01C9. -/
theorem rank_eq_of_point {T : Scheme.{u}} (x : T) (M : ModuleSheaf T) {r s : ℕ}
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens T)
      (J := Opens.grothendieckTopology T) M r)
    (hs : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens T)
      (J := Opens.grothendieckTopology T) M s) : r = s := by
  have hO := LocallyFreeRank.scheme_stalksNontrivial T
  let M' : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf T.toTopCat T.sheaf) := M
  obtain ⟨q, hq, -⟩ := hr.exists_isFiniteLocallyFreeOfRankData
  have : M'.IsLocallyFree := ⟨q, hq⟩
  have key : ∀ n : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens T)
      (J := Opens.grothendieckTopology T) M n →
      (n : Cardinal.{u}) = LocallyFreeRank.locallyFreeRank M' hO x := by
    intro n h
    obtain ⟨q, hq, hrk⟩ := h.exists_isFiniteLocallyFreeOfRankData
    have hx : x ∈ ⨆ i, q.X i := by
      rw [(Opens.coversTop_iff _ q.X).mp q.coversTop]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    let q₀ : _root_.SheafOfModules.LocalGeneratorsData.{u} M' := q
    have hq₀ : q₀.IsLocallyFreeData := hq
    exact (Cardinal.mk_eq_nat_iff.mpr ⟨(hrk i).some⟩).symm.trans
      (LocallyFreeRank.locallyFreeRank_eq_mk_generators M' hO q₀ hq₀ i x hi).symm
  exact Nat.cast_injective ((key r hr).trans (key s hs).symm)

/-- **The size of a matrix algebra trivialising an Azumaya algebra sheaf is determined by the
rank of that sheaf.** If the underlying sheaf of modules of `A` is finite locally free of rank
`d ^ 2` and `A` becomes the algebra of `m × m` matrices on a scheme `T` with a point above `S`,
then `m = d`. This is how [Stacks, Tag 0A2L] reads its `d` off a trivialisation. -/
theorem eq_of_pullback_matrixAlgebra_iso {T S : Scheme.{u}} (φ : T ⟶ S) (x : T)
    {A : AlgebraSheaf S} {d m : ℕ}
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) A.X (d ^ 2))
    (e : (algebraPullback φ).obj A ≅ matrixAlgebra T m) : m = d := by
  have h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens T)
      (J := Opens.grothendieckTopology T) ((matrixAlgebra T m).X) (d ^ 2) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((Mon.forget (ModuleSheaf T)).mapIso e)
      (isFiniteLocallyFreeOfRank_modulePullback φ hA)
  exact Nat.pow_left_injective (by decide)
    (rank_eq_of_point x _ (isFiniteLocallyFreeOfRank_matrixAlgebra T m) h₁)

end Stacks.EtaleCohomology.BrauerScheme

end

end
