module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0AYU]: the degree is unchanged by a modification that does not move the curve

[Stacks, Tag 0AYU] says that for `g : X' ⟶ X` a morphism of proper schemes of dimension at most
one over a field which induces a bijection on the one-dimensional irreducible components and an
isomorphism of local rings at the corresponding generic points, `deg(g^*ℰ) = deg(ℰ)` for every
finite locally free `ℰ` of constant rank. Its proof is a computation: `g` is finite, so the
higher direct images vanish and the projection formula gives
`Rg_*g^*ℰ = ℰ ⊗ g_*𝒪_{X'}`; the kernel `𝒦` and cokernel `𝒬` of `𝒪_X ⟶ g_*𝒪_{X'}` have
zero-dimensional support by the hypothesis on generic points; and then additivity of the Euler
characteristic ([Stacks, Tag 08AA]) together with `χ(𝒢 ⊗ ℰ) = n·χ(𝒢)` for zero-dimensional
support (clause (5) of [Stacks, Tag 0AYT]) collapses the difference to zero.

This file proves the computation, in the form that does not mention `g` at all. What the
computation uses of `g` is only that `𝒫 = g_*𝒪_{X'}` sits in a four-term exact sequence

`0 ⟶ 𝒦 ⟶ 𝒪_X ⟶ 𝒫 ⟶ 𝒬 ⟶ 0`

whose two ends satisfy clause (5) of [Stacks, Tag 0AYT]; the four-term sequence is taken here as
a pair of short exact sequences sharing their middle object, which is what breaking it at the
image produces. The conclusion is that `𝒫` computes the degree of `ℰ`:

`χ(X, 𝒫 ⊗ ℰ) − n · χ(X, 𝒫) = deg(ℰ)`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair`: the computation of
  [Stacks, Tag 0AYU], `χ(𝒫 ⊗ ℰ) − n·χ(𝒫) = deg(ℰ)`, from the two short exact sequences and
  clause (5) of [Stacks, Tag 0AYT] at `𝒦` and at `𝒬`.
* `curveDegree_eq_of_isClosedImmersion_of_shortExact_pair`: the same at `𝒫 = i_*𝒪_Z` for a single
  closed immersion `i : Z ⟶ X`, where the left-hand side becomes `deg(ℰ|_Z)` outright — so
  `deg(ℰ) = deg(ℰ|_Z)`, which is [Stacks, Tag 0AYU] for a closed immersion.

## Implementation notes

Both short exact sequences are hypotheses, and so is the finiteness of [Stacks, Tag 02O6], in the
shape produced by the dévissage reductions of
`StacksFrontier/AlgebraicGeometry/CurveTensorEulerUnit/BaseCases.lean`.

Clause (5) of [Stacks, Tag 0AYT] is written as the equation `χ(𝒢 ⊗ ℰ) = n·χ(𝒢)`, the only
consequence of the support condition this computation uses.

## References

* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The computation of [Stacks, Tag 0AYU].** Let `ℰ` be finite locally free of rank `n` on a
proper `X` of dimension at most one over `k`, and let

`0 ⟶ 𝒦 ⟶ 𝒪_X ⟶ 𝒥 ⟶ 0`,  `0 ⟶ 𝒥 ⟶ 𝒫 ⟶ 𝒬 ⟶ 0`

be short exact sequences of coherent modules — the four-term sequence
`0 ⟶ 𝒦 ⟶ 𝒪_X ⟶ 𝒫 ⟶ 𝒬 ⟶ 0` broken at its image. If clause (5) of [Stacks, Tag 0AYT] holds at
`𝒦` and at `𝒬`, that is `χ(𝒦 ⊗ ℰ) = n·χ(𝒦)` and `χ(𝒬 ⊗ ℰ) = n·χ(𝒬)`, then

`χ(𝒫 ⊗ ℰ) − n·χ(𝒫) = deg(ℰ)`.

The middle object `𝒥` cancels: the two tensored sequences give
`χ(𝒥 ⊗ ℰ) = χ(ℰ) − χ(𝒦 ⊗ ℰ)` and `χ(𝒫 ⊗ ℰ) = χ(𝒥 ⊗ ℰ) + χ(𝒬 ⊗ ℰ)`, the two untensored ones give
the same two identities without `ℰ`, and substituting the two clause-(5) equations leaves
`χ(ℰ) − n·χ(𝒪_X)`. -/
theorem eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair [IsProper f]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (Kr J Q P : X.Modules)
    (hKr : SheafOfModules.IsCoherent Kr) (hJ : SheafOfModules.IsCoherent J)
    (hQ : SheafOfModules.IsCoherent Q) (hP : SheafOfModules.IsCoherent P)
    (hE : SheafOfModules.IsCoherent E)
    (hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
    (hS₁ : (ShortComplex.mk a b wab).ShortExact)
    (c : J ⟶ P) (d : P ⟶ Q) (wcd : c ≫ d = 0)
    (hS₂ : (ShortComplex.mk c d wcd).ShortExact)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (h0AYTK : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (Kr)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Kr E hKr hE) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Kr hKr)
    (h0AYTQ : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (Q)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Q E hQ hE) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Q hQ) :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (P)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace P E hP hE) -
        (n : ℤ) * @eulerCharacteristic k _ X f _ P hP =
      curveDegree k f hX E n := by
  classical
  -- flatness of `E`, used to tensor both sequences
  have hfl :=
    @Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      _ _ _ X.presheaf X.ringCatSheaf.2 _ _ E n (by assumption)
  have hflat : Stacks.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) E :=
    @Scheme.Modules.isFlat_of_isFiniteLocallyFree X E hfl
  have tc : ∀ (M : X.Modules), SheafOfModules.IsCoherent M →
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj (E))).IsCoherent :=
        fun M hM =>
    @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace M E hM hE
  -- additivity along the two sequences
  have hadd₁ : @eulerCharacteristic k _ X f _ (SheafOfModules.unit X.ringCatSheaf) hOX =
      @eulerCharacteristic k _ X f _ Kr hKr + @eulerCharacteristic k _ X f _ J hJ :=
    @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hS₁
      hKr hOX hJ (h02O6 _ hKr) (h02O6 _ hJ)
  have hadd₂ : @eulerCharacteristic k _ X f _ P hP =
      @eulerCharacteristic k _ X f _ J hJ + @eulerCharacteristic k _ X f _ Q hQ :=
    @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hS₂
      hJ hP hQ (h02O6 _ hJ) (h02O6 _ hQ)
  -- additivity along the two sequences tensored with `E`
  obtain ⟨z₁, hse₁⟩ :=
    Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor
      (ShortComplex.mk a b wab) E hS₁ hflat
  obtain ⟨z₂, hse₂⟩ :=
    Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor
      (ShortComplex.mk c d wcd) E hS₂ hflat
  have haddT₁ : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj ((SheafOfModules.unit X.ringCatSheaf))).obj (E)))
        (tc _ hOX) =
      @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (Kr)).obj (E)))
          (tc _ hKr) +
        @eulerCharacteristic k _ X f _
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (J)).obj (E)))
          (tc _ hJ) :=
    @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hse₁
      (tc _ hKr) (tc _ hOX) (tc _ hJ) (h02O6 _ (tc _ hKr)) (h02O6 _ (tc _ hJ))
  have haddT₂ : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (P)).obj (E))) (tc _ hP) =
      @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (J)).obj (E)))
          (tc _ hJ) +
        @eulerCharacteristic k _ X f _
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (Q)).obj (E)))
          (tc _ hQ) :=
    @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hse₂
      (tc _ hJ) (tc _ hP) (tc _ hQ) (h02O6 _ (tc _ hJ)) (h02O6 _ (tc _ hQ))
  have hunit : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj ((SheafOfModules.unit X.ringCatSheaf))).obj (E)))
        (tc _ hOX) =
      @eulerCharacteristic k _ X f _ E hE :=
    eulerCharacteristic_unit_tensorSheaf k f E hE hOX
  have hdeg : curveDegree k f hX E n =
      @eulerCharacteristic k _ X f _ E hE -
        (n : ℤ) * @eulerCharacteristic k _ X f _ (SheafOfModules.unit X.ringCatSheaf) hOX :=
    @curveDegree_eq_eulerCharacteristic_sub k _ X f _ hX E n _ hE hOX
  rw [hdeg, hadd₂, haddT₂, h0AYTQ]
  rw [hunit] at haddT₁
  rw [h0AYTK] at haddT₁
  linear_combination (-1 : ℤ) * haddT₁ + (n : ℤ) * hadd₁

/-- **[Stacks, Tag 0AYU] for a closed immersion**: if the kernel and cokernel of
`𝒪_X ⟶ i_*𝒪_Z` satisfy clause (5) of [Stacks, Tag 0AYT], then `deg(ℰ) = deg(ℰ|_Z)`.

The left-hand side of
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair` at
`𝒫 = i_*𝒪_Z` is `χ(Z, ℰ|_Z) − n·χ(Z, 𝒪_Z)`, by the projection formula and the cohomology
comparison along a closed immersion, and that is `deg(ℰ|_Z)`. -/
theorem curveDegree_eq_of_isClosedImmersion_of_shortExact_pair [IsProper f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hX : topologicalKrullDim X ≤ 1) (hZ : topologicalKrullDim Z ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (Kr J Q : X.Modules)
    (hKr : SheafOfModules.IsCoherent Kr) (hJ : SheafOfModules.IsCoherent J)
    (hQ : SheafOfModules.IsCoherent Q)
    (hE : SheafOfModules.IsCoherent E)
    (hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (hOZ : SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf))
    (hEZ : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E))
    (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
    (hS₁ : (ShortComplex.mk a b wab).ShortExact)
    (c : J ⟶ (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (d : (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶ Q)
    (wcd : c ≫ d = 0) (hS₂ : (ShortComplex.mk c d wcd).ShortExact)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (h0AYTK : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (Kr)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Kr E hKr hE) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Kr hKr)
    (h0AYTQ : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (Q)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Q E hQ hE) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Q hQ) :
    curveDegree k f hX E n =
      @curveDegree k _ Z (i ≫ f) _ hZ ((Scheme.Modules.pullback i).obj E) n
        (isFiniteLocallyFreeOfRank_pullback i E n) := by
  have hpushOZ : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) :=
    @isCoherent_pushforward_of_isClosedImmersion Z X i _ _ _ hOZ
  have hmain := eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair k f hX E n
    Kr J Q _ hKr hJ hQ hpushOZ hE hOX a b wab hS₁ c d wcd hS₂ h02O6 h0AYTK h0AYTQ
  have htens : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))).obj (E)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hpushOZ hE) =
      @eulerCharacteristic k _ Z (i ≫ f) _ ((Scheme.Modules.pullback i).obj E) hEZ :=
    eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion k i f E hE hOZ
      hpushOZ hEZ
  have hbase : @eulerCharacteristic k _ X f _
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) hpushOZ =
      @eulerCharacteristic k _ Z (i ≫ f) _ (SheafOfModules.unit Z.ringCatSheaf) hOZ :=
    eulerCharacteristic_pushforward_of_isClosedImmersion k i f _ hOZ hpushOZ
  have hdegZ : @curveDegree k _ Z (i ≫ f) _ hZ ((Scheme.Modules.pullback i).obj E) n
        (isFiniteLocallyFreeOfRank_pullback i E n) =
      @eulerCharacteristic k _ Z (i ≫ f) _ ((Scheme.Modules.pullback i).obj E) hEZ -
        (n : ℤ) * @eulerCharacteristic k _ Z (i ≫ f) _
          (SheafOfModules.unit Z.ringCatSheaf) hOZ :=
    @curveDegree_eq_eulerCharacteristic_sub k _ Z (i ≫ f) _ hZ _ n
      (isFiniteLocallyFreeOfRank_pullback i E n) hEZ hOZ
  rw [hdegZ, ← htens, ← hbase, hmain]

end AlgebraicGeometry

end
