module

public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.FiniteFamily
public import StacksFrontier.AlgebraicGeometry.EulerCharDirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank

/-!
# The filtration of `g_*𝒪_{X'}` by partial biproducts

For closed immersions `iⱼ : Zⱼ ⟶ X`, `j < N`, and `X' = ∐_{j < N} Zⱼ`, the module `g_*𝒪_{X'}` is
the biproduct `⨁_{j < N} (iⱼ)_*𝒪_{Zⱼ}`. A finite biproduct is filtered by its summands: the
partial sums `𝒫ⱼ = ⨁_{l < j} (i_l)_*𝒪_{Z_l}` satisfy `𝒫_{j+1} = 𝒫ⱼ ⊞ (iⱼ)_*𝒪_{Zⱼ}`, so
`0 ⟶ 𝒫ⱼ ⟶ 𝒫_{j+1} ⟶ (iⱼ)_*𝒪_{Zⱼ} ⟶ 0` is the split sequence of that biproduct. With this
filtration, paragraph 1 of the proof of [Stacks, Tag 0AYW] gives, for a finite family of closed
subschemes,

`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`.

## Main definitions

The elided prefix is `AlgebraicGeometry`.

* `Scheme.Modules.biprodSeries`: the partial biproducts `𝒫ⱼ = ⨁_{l < j} 𝒢_l` of a family of
  modules, by recursion on `j`, starting at the zero object.
* `Scheme.Modules.pushforwardUnitSeries`: that construction at `𝒢ⱼ = (iⱼ)_*𝒪_{Zⱼ}`, which is
  `g_*𝒪_{X'}` for `X' = ∐_{j < N} Zⱼ ⟶ X`.

## Main results

* `Scheme.Modules.exists_shortExact_biprodSeries_succ`: the successive quotients of the partial
  biproducts are the members of the family.
* `curveDegree_eq_sum_biprodSeries_of_shortExact_pair`: `deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`, given
  the two short exact sequences of [Stacks, Tag 0AYU] at
  `Scheme.Modules.pushforwardUnitSeries i N`, [Stacks, Tag 02O6], and clause (5) of
  [Stacks, Tag 0AYT] at their outer terms.
* `curveDegree_eq_sum_biprodSeries_of_isProper`: the same, with the dimension bounds on the
  `Zⱼ`, the local Noetherianness and the coherence of `ℰ`, `𝒪_X`, `𝒪_{Zⱼ}` and `ℰ|_{Zⱼ}`
  deduced from `[IsProper f]`.
* `curveDegree_eq_sum_biprodSeries_of_topologicalKrullDim_supp_le_zero`: the same, with the two
  clause-(5) equations replaced by the hypothesis that the two outer terms of the
  [Stacks, Tag 0AYU] sequences have zero-dimensional support.

## Implementation notes

`open scoped ZeroObject` is required: the `0` of `Scheme.Modules.biprodSeries`'s base case is the
zero object, whose `Zero` instance is `scoped[ZeroObject]` in Mathlib.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The partial biproducts of a family of modules -/

/-- **The partial biproducts `𝒫ⱼ = ⨁_{l < j} 𝒢_l` of a family of modules**, by recursion on `j`.
At `j = 0` it is the zero object, and `𝒫_{j+1}` is `𝒫ⱼ ⊞ 𝒢ⱼ`. -/
noncomputable def Scheme.Modules.biprodSeries (G : ℕ → X.Modules) : ℕ → X.Modules
  | 0 => 0
  | (j + 1) => Scheme.Modules.biprodSeries G j ⊞ G j

/-- **The partial biproducts start at a zero object.** -/
theorem Scheme.Modules.isZero_biprodSeries_zero (G : ℕ → X.Modules) :
    IsZero (Scheme.Modules.biprodSeries G 0) :=
  isZero_zero X.Modules

/-- **Every partial biproduct of coherent modules is coherent.** -/
theorem SheafOfModules.isCoherent_biprodSeries (G : ℕ → X.Modules)
    (hG : ∀ j, SheafOfModules.IsCoherent (G j)) :
    ∀ j, SheafOfModules.IsCoherent (Scheme.Modules.biprodSeries G j)
  | 0 =>
    SheafOfModules.isCoherent_of_isZero (Scheme.Modules.isZero_biprodSeries_zero G)
  | (j + 1) =>
    SheafOfModules.isCoherent_biprod (Scheme.Modules.biprodSeries G j) (G j)
      (SheafOfModules.isCoherent_biprodSeries G hG j) (hG j)

/-- **The successive quotients of the partial biproducts are the members of the family**:
`0 ⟶ 𝒫ⱼ ⟶ 𝒫_{j+1} ⟶ 𝒢ⱼ ⟶ 0` is short exact, being the split sequence
`AlgebraicGeometry.biprodShortComplex` of the biproduct `𝒫_{j+1} = 𝒫ⱼ ⊞ 𝒢ⱼ`. -/
theorem Scheme.Modules.exists_shortExact_biprodSeries_succ (G : ℕ → X.Modules) (j : ℕ) :
    ∃ (p : Scheme.Modules.biprodSeries G j ⟶ Scheme.Modules.biprodSeries G (j + 1))
      (q : Scheme.Modules.biprodSeries G (j + 1) ⟶ G j) (w : p ≫ q = 0),
      (ShortComplex.mk p q w).ShortExact :=
  ⟨biprod.inl, biprod.snd, biprod.inl_snd,
    (biprodShortComplexSplitting (Scheme.Modules.biprodSeries G j) (G j)).shortExact⟩

/-! ### `g_*𝒪_{X'}` for a disjoint union of closed subschemes -/

/-- **`g_*𝒪_{X'}` for `X' = ∐_{j < N} Zⱼ ⟶ X`**, as the partial biproducts of the direct images
`(iⱼ)_*𝒪_{Zⱼ}`. -/
noncomputable def Scheme.Modules.pushforwardUnitSeries {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) : ℕ → X.Modules :=
  Scheme.Modules.biprodSeries fun j =>
    (Scheme.Modules.pushforward (i j)).obj (SheafOfModules.unit (Zs j).ringCatSheaf)

/-! ### The degree of `ℰ` as a sum over a finite family of closed subschemes -/

/-- **Paragraph 1 of the proof of [Stacks, Tag 0AYW] for a finite family**:
`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`, given the two short exact sequences of [Stacks, Tag 0AYU] at
`g_*𝒪_{X'} = ` `AlgebraicGeometry.Scheme.Modules.pushforwardUnitSeries i N`, [Stacks, Tag 02O6],
and clause (5) of [Stacks, Tag 0AYT] at their outer terms. -/
theorem curveDegree_eq_sum_biprodSeries_of_shortExact_pair
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [IsLocallyNoetherian X] {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hX : topologicalKrullDim X ≤ 1) (hZ : ∀ j, topologicalKrullDim (Zs j) ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hE : SheafOfModules.IsCoherent E)
    (hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (hOZ : ∀ j, SheafOfModules.IsCoherent (SheafOfModules.unit (Zs j).ringCatSheaf))
    (hEZ : ∀ j, SheafOfModules.IsCoherent ((Scheme.Modules.pullback (i j)).obj E))
    (Kr J Q : X.Modules)
    (hKr : SheafOfModules.IsCoherent Kr) (hJ : SheafOfModules.IsCoherent J)
    (hQ : SheafOfModules.IsCoherent Q) (N : ℕ)
    (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
    (hS₁ : (ShortComplex.mk a b wab).ShortExact)
    (c : J ⟶ Scheme.Modules.pushforwardUnitSeries i N)
    (d : Scheme.Modules.pushforwardUnitSeries i N ⟶ Q) (wcd : c ≫ d = 0)
    (hS₂ : (ShortComplex.mk c d wcd).ShortExact)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (h0AYTK : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Kr)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Kr E hKr hE) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Kr hKr)
    (h0AYTQ : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Q)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Q E hQ hE) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Q hQ) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range N, @curveDegree k _ (Zs j) (i j ≫ f) _ (hZ j)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) :=
  curveDegree_eq_sum_of_filtration_pushforward_unit_of_shortExact_pair k f i hX hZ E n hE hOX
    hOZ hEZ Kr J Q hKr hJ hQ (Scheme.Modules.pushforwardUnitSeries i)
    (SheafOfModules.isCoherent_biprodSeries _
      fun j => @isCoherent_pushforward_of_isClosedImmersion _ X (i j) _ _ _ (hOZ j))
    N (Scheme.Modules.isZero_biprodSeries_zero _)
    (fun j _ => Scheme.Modules.exists_shortExact_biprodSeries_succ _ j)
    a b wab hS₁ c d wcd hS₂ h02O6 h0AYTK h0AYTQ

/-- **Paragraph 1 of the proof of [Stacks, Tag 0AYW] for a finite family**: for `ℰ` finite
locally free of rank `n` on `X` proper over `k` of dimension at most one and closed immersions
`iⱼ : Zⱼ ⟶ X`, `deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`, given the two short exact sequences of
[Stacks, Tag 0AYU] at `g_*𝒪_{X'} = ` `AlgebraicGeometry.Scheme.Modules.pushforwardUnitSeries i N`,
[Stacks, Tag 02O6], and clause (5) of [Stacks, Tag 0AYT] at their outer terms. -/
theorem curveDegree_eq_sum_biprodSeries_of_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (Kr J Q : X.Modules)
    (hKr : SheafOfModules.IsCoherent Kr) (hJ : SheafOfModules.IsCoherent J)
    (hQ : SheafOfModules.IsCoherent Q) (N : ℕ)
    (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
    (hS₁ : (ShortComplex.mk a b wab).ShortExact)
    (c : J ⟶ Scheme.Modules.pushforwardUnitSeries i N)
    (d : Scheme.Modules.pushforwardUnitSeries i N ⟶ Q) (wcd : c ≫ d = 0)
    (hS₂ : (ShortComplex.mk c d wcd).ShortExact)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (h0AYTK : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Kr)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Kr E hKr
            (@isCoherent_of_isFiniteLocallyFreeOfRank X
              (LocallyOfFiniteType.isLocallyNoetherian f) E n _)) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Kr hKr)
    (h0AYTQ : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Q)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Q E hQ
            (@isCoherent_of_isFiniteLocallyFreeOfRank X
              (LocallyOfFiniteType.isLocallyNoetherian f) E n _)) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Q hQ) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range N, @curveDegree k _ (Zs j) (i j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (i j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) :=
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hLNZ : ∀ j, IsLocallyNoetherian (Zs j) := fun j =>
    isLocallyNoetherian_of_isClosedImmersion (i j)
  have hE : SheafOfModules.IsCoherent E :=
    @isCoherent_of_isFiniteLocallyFreeOfRank X hLN E n _
  @curveDegree_eq_sum_biprodSeries_of_shortExact_pair k _ X f _ hLN Zs i _ hX
    (fun j => le_trans (IsClosedImmersion.isClosedEmbedding
      (i j)).isInducing.topologicalKrullDim_le hX)
    E n _ hE
    (@Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X hLN)
    (fun j => @Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent _ (hLNZ j))
    (fun j => @isCoherent_pullback _ _ (hLNZ j) (i j) E hE)
    Kr J Q hKr hJ hQ N a b wab hS₁ c d wcd hS₂ h02O6 h0AYTK h0AYTQ

/-- **Paragraph 1 of the proof of [Stacks, Tag 0AYW] for a finite family**: for `ℰ` finite
locally free of rank `n` on `X` proper over `k` of dimension at most one and closed immersions
`iⱼ : Zⱼ ⟶ X`, `deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`, given the two short exact sequences of
[Stacks, Tag 0AYU] at `AlgebraicGeometry.Scheme.Modules.pushforwardUnitSeries i N` whose outer
terms `𝒦` and `𝒬` satisfy `dim Supp 𝒦 ≤ 0` and `dim Supp 𝒬 ≤ 0`, and [Stacks, Tag 02O6]. -/
theorem curveDegree_eq_sum_biprodSeries_of_topologicalKrullDim_supp_le_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (Kr J Q : X.Modules)
    (hKr : SheafOfModules.IsCoherent Kr) (hJ : SheafOfModules.IsCoherent J)
    (hQ : SheafOfModules.IsCoherent Q) (N : ℕ)
    (hsuppKr : topologicalKrullDim (_root_.SheafOfModules.supp Kr) ≤ 0)
    (hsuppQ : topologicalKrullDim (_root_.SheafOfModules.supp Q) ≤ 0)
    (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
    (hS₁ : (ShortComplex.mk a b wab).ShortExact)
    (c : J ⟶ Scheme.Modules.pushforwardUnitSeries i N)
    (d : Scheme.Modules.pushforwardUnitSeries i N ⟶ Q) (wcd : c ≫ d = 0)
    (hS₂ : (ShortComplex.mk c d wcd).ShortExact)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m)) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range N, @curveDegree k _ (Zs j) (i j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (i j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) := by
  have hE : SheafOfModules.IsCoherent E :=
    @isCoherent_of_isFiniteLocallyFreeOfRank X (LocallyOfFiniteType.isLocallyNoetherian f) E n _
  have hχ : ∀ (M : X.Modules) (hM : SheafOfModules.IsCoherent M),
      topologicalKrullDim (_root_.SheafOfModules.supp M) ≤ 0 →
      @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj (E)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace M E hM hE) =
      (n : ℤ) * @eulerCharacteristic k _ X f _ M hM := fun M hM hsupp =>
    (@exists_eulerCharacteristic_tensorSheaf_eq_rank_mul X k _ f _ M hM hsupp E n _).2
  exact curveDegree_eq_sum_biprodSeries_of_isProper k f i hX E n Kr J Q hKr hJ hQ N
    a b wab hS₁ c d wcd hS₂ h02O6 (hχ Kr hKr hsuppKr) (hχ Q hQ hsuppQ)

end AlgebraicGeometry

end
