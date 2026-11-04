module

public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0AYW], paragraph 1: the reduction to the irreducible case

The proof of [Stacks, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW) opens by reducing to
an irreducible `X`. For each one-dimensional irreducible component `Cᵢ` of `X` it forms the open
`Uᵢ = X ∖ (⋃_{j ≠ i} Cⱼ)`, takes `Xᵢ ⊆ X` to be the **scheme-theoretic closure** of `Uᵢ`
([Stacks, Tag 01RG]), and applies [Stacks, Tag 0AYU] to `X' = ∐ Xᵢ ⟶ X`. Since `Cᵢ` sits inside
`Xᵢ` with the multiplicity it has in `X`, the general case follows from the irreducible one.

## The schemes `Xᵢ` are already in Mathlib

`AlgebraicGeometry.Scheme.irreducibleComponent` is exactly that construction: the closed
subscheme of a Noetherian `X` cut out by `(irreducibleComponentOpen X Z).ι.ker`, the kernel of
the restriction to the complement of the union of the other irreducible components — i.e. the
scheme-theoretic image of `Uᵢ ↪ X`. It comes with `Scheme.irreducibleComponentι`, an
`IsClosedImmersion` instance, an `IrreducibleSpace` instance on the subscheme, and
`CategoryTheory.IsIso (X.irreducibleComponentι Z hZ)` when `X` is already irreducible — which is
paragraph 1's base case. Nothing of that has to be built here.

What this file supplies is the input that unlocks it and the arithmetic that consumes it.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `isNoetherian_of_isProper`: **a scheme proper over a field is Noetherian.** This is what
  licenses `Scheme.irreducibleComponent`, whose every declaration carries `[IsNoetherian X]`, in
  the setting of [Stacks, Tag 0AYW]. Neither half is automatic by instance search: local
  Noetherianness is `LocallyOfFiniteType.isLocallyNoetherian` and compactness is
  `quasiCompact_iff_compactSpace`.
* `finite_irreducibleComponents_of_isProper`: hence `X` has only finitely many irreducible
  components, so paragraph 1's index set is finite.
* `topologicalKrullDim_irreducibleComponent_le`: each `Xᵢ` has dimension at most that of `X`, so
  the restriction `ℰ|_{Xᵢ}` has a degree whenever `ℰ` does.
* `isCoherent_of_isFiniteLocallyFreeOfRank`: a finite locally free module of constant rank on a
  locally Noetherian scheme is coherent.
* `curveDegree_eq_curveDegree_irreducibleComponent`: [Stacks, Tag 0AYU] at
  `i = X.irreducibleComponentι Z hZ`, with every side condition of
  `curveDegree_eq_of_isClosedImmersion_of_shortExact_pair` discharged from `[IsProper f]` and
  `[IsNoetherian X]` — the dimension bound on the component, the local Noetherianness, and the
  four coherence hypotheses.
* `curveDegree_eq_add_of_extension_pushforward_unit_of_shortExact_pair`: **paragraph 1's
  arithmetic for two components**, `deg(ℰ) = deg(ℰ|_{Z₁}) + deg(ℰ|_{Z₂})`, from the
  [Stacks, Tag 0AYU] computation at a module `𝒫` that is an extension of `(i₂)_*𝒪_{Z₂}` by
  `(i₁)_*𝒪_{Z₁}`.

## Implementation notes

**`𝒫` is taken as an extension, not as a biproduct.** The Stacks proof takes
`𝒫 = g_*𝒪_{X'}` for `X' = ∐ Xᵢ`, which for two components is the biproduct
`(i₁)_*𝒪_{Z₁} ⊞ (i₂)_*𝒪_{Z₂}`. The statement below assumes only a short exact sequence
`0 ⟶ (i₁)_*𝒪_{Z₁} ⟶ 𝒫 ⟶ (i₂)_*𝒪_{Z₂} ⟶ 0`, which the biproduct supplies through
`AlgebraicGeometry.biprodShortComplexSplitting`. That is weaker than being the biproduct, and it
is also what makes the proof possible: writing `⊞` for these two particular modules fails
`synthInstanceFailed` on `HasBinaryBiproduct` *even with that instance in the binder list*, while
the same `⊞` elaborates for two anonymous modules of the same type. Additivity of `χ` needs only
exactness, not splitness — `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_outer` —
and tensoring the sequence with the flat `ℰ` keeps it exact, so no distributivity of the tensor
product over a biproduct is needed anywhere. Mathlib's distributivity isomorphism
`CategoryTheory.rightDistributor` is therefore not needed here.

**The vanishing input of [Stacks, Tag 01XJ] is free here.**
`AlgebraicGeometry.exists_isZero_cohomologyOverField_of_isProper` gives one bound `N` uniformly
in the quasi-coherent module, and coherence implies quasi-coherence, so the `hvan` hypotheses of
the two-out-of-three additivity are discharged from `[IsProper f]` alone. Only the finite
dimensionality of [Stacks, Tag 02O6] is carried, in the same shape as in
`StacksFrontier/AlgebraicGeometry/CurveDegreeInvariance/Basic.lean`.

**No attribute for [Stacks, Tag 0AYW], [Stacks, Tag 0AYU] or [Stacks, Tag 01RG] is attached.**
Nothing here states one of those tags: the degree identities carry the two short exact sequences,
[Stacks, Tag 02O6] and clause (5) of [Stacks, Tag 0AYT] as hypotheses, and the component
construction is Mathlib's, not this file's.

**A general closed immersion lowers the dimension bound too**, and that statement is already
proved as `StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion`
(`StacksFrontier/AlgebraicGeometry/IrreducibleComponentSubscheme/Basic.lean`); it is not
restated here, only used in the specialised form above.

**The components of [Stacks, Tag 0AYW] come in two flavours and they are different schemes.**
Paragraph 1's `Xᵢ` is the scheme-theoretic closure above, which is in general *not* reduced and
carries the multiplicity; paragraph 2's `Cᵢ` is the *reduced* induced structure
`(Scheme.IdealSheafData.vanishingIdeal ⟨closure {ξ}, _⟩).subscheme`, which is what the
`reducedComponent` declarations and `StacksTag09NX` use. `Scheme.irreducibleComponent` is the
former.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Noetherianness, and the component subschemes it licenses -/

/-- **A scheme proper over a field is Noetherian.** It is locally of finite type over a
Noetherian base, hence locally Noetherian, and quasi-compact over a point, hence compact.

Neither half is found by instance search in this library, so this is the lemma a consumer of
`AlgebraicGeometry.Scheme.irreducibleComponent` — every declaration of which carries
`[IsNoetherian X]` — needs in order to use it under the hypotheses of [Stacks, Tag 0AYW]. -/
@[ega "II 7.4.1" "special case", ega "IV 4.4.1" "special case"]
theorem isNoetherian_of_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : AlgebraicGeometry.IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := (AlgebraicGeometry.quasiCompact_iff_compactSpace f).mp inferInstance
  ⟨⟩

/-- **A scheme proper over a field has only finitely many irreducible components**, so the index
set of paragraph 1 of [Stacks, Tag 0AYW] is finite. -/
@[ega "IV 4.4.1" "special case"]
theorem finite_irreducibleComponents_of_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] : Finite (irreducibleComponents X) :=
  have := isNoetherian_of_isProper k f
  AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian

/-- **A component subscheme has no larger dimension than the scheme it sits in.** Its inclusion
is a closed immersion, hence a topological embedding, hence inducing.

With `hdim : topologicalKrullDim X ≤ 1` this gives the dimension bound that
`AlgebraicGeometry.curveDegree` needs on `X.irreducibleComponent Z hZ`. -/
theorem topologicalKrullDim_irreducibleComponent_le {X : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    topologicalKrullDim (X.irreducibleComponent Z hZ) ≤ topologicalKrullDim X :=
  (IsClosedImmersion.isClosedEmbedding
    (X.irreducibleComponentι Z hZ)).isInducing.topologicalKrullDim_le

/-- **A finite locally free module of constant rank on a locally Noetherian scheme is
coherent**, by [Stacks, Tag 01XZ].

This is `AlgebraicGeometry.SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve`
with `[IsCurve k f]` weakened to `[IsLocallyNoetherian X]`, which is all that
[Stacks, Tag 01XZ] asks for. -/
theorem isCoherent_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} [IsLocallyNoetherian X]
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    SheafOfModules.IsCoherent E :=
  @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X _ E
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} E n)

/-! ### [Stacks, Tag 0AYU] at a component subscheme -/

/-- **[Stacks, Tag 0AYU] at `i = X.irreducibleComponentι Z hZ`.** If the kernel and cokernel of
`𝒪_X ⟶ i_*𝒪_{Xᵢ}` satisfy clause (5) of [Stacks, Tag 0AYT], then `deg(ℰ) = deg(ℰ|_{Xᵢ})` for the
component subscheme `Xᵢ = X.irreducibleComponent Z hZ` of paragraph 1 of [Stacks, Tag 0AYW].

Every side condition of `AlgebraicGeometry.curveDegree_eq_of_isClosedImmersion_of_shortExact_pair`
that is a consequence of `[IsProper f]` and `[IsNoetherian X]` is discharged here: the closed
immersion itself and the dimension bound on the component, the local Noetherianness of `X` and of
the component, and the coherence of `ℰ`, of `𝒪_X`, of `𝒪_{Xᵢ}` and of `ℰ|_{Xᵢ}`. What remains are
the two short exact sequences, [Stacks, Tag 02O6] and the two clause-(5) equations. -/
theorem curveDegree_eq_curveDegree_irreducibleComponent
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [AlgebraicGeometry.IsNoetherian X]
    (hX : topologicalKrullDim X ≤ 1)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (Kr J Q : X.Modules)
    (hKr : SheafOfModules.IsCoherent Kr) (hJ : SheafOfModules.IsCoherent J)
    (hQ : SheafOfModules.IsCoherent Q)
    (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
    (hS₁ : (ShortComplex.mk a b wab).ShortExact)
    (c : J ⟶ (Scheme.Modules.pushforward (X.irreducibleComponentι Z hZ)).obj
      (SheafOfModules.unit (X.irreducibleComponent Z hZ).ringCatSheaf))
    (d : (Scheme.Modules.pushforward (X.irreducibleComponentι Z hZ)).obj
      (SheafOfModules.unit (X.irreducibleComponent Z hZ).ringCatSheaf) ⟶ Q)
    (wcd : c ≫ d = 0) (hS₂ : (ShortComplex.mk c d wcd).ShortExact)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (h0AYTK : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Kr)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Kr E hKr
            (isCoherent_of_isFiniteLocallyFreeOfRank E n)) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Kr hKr)
    (h0AYTQ : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Q)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Q E hQ
            (isCoherent_of_isFiniteLocallyFreeOfRank E n)) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Q hQ) :
    curveDegree k f hX E n =
      @curveDegree k _ (X.irreducibleComponent Z hZ) (X.irreducibleComponentι Z hZ ≫ f) _
        (le_trans (topologicalKrullDim_irreducibleComponent_le Z hZ) hX)
        ((Scheme.Modules.pullback (X.irreducibleComponentι Z hZ)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback _ E n) := by
  have hE : SheafOfModules.IsCoherent E := isCoherent_of_isFiniteLocallyFreeOfRank E n
  have hLNZ : IsLocallyNoetherian (X.irreducibleComponent Z hZ) :=
    isLocallyNoetherian_of_isClosedImmersion (X.irreducibleComponentι Z hZ)
  have hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hOZ : SheafOfModules.IsCoherent
      (SheafOfModules.unit (X.irreducibleComponent Z hZ).ringCatSheaf) :=
    @Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent _ hLNZ
  have hEZ : SheafOfModules.IsCoherent
      ((Scheme.Modules.pullback (X.irreducibleComponentι Z hZ)).obj E) :=
    @isCoherent_pullback _ _ hLNZ (X.irreducibleComponentι Z hZ) E hE
  exact curveDegree_eq_of_isClosedImmersion_of_shortExact_pair k f
    (X.irreducibleComponentι Z hZ) hX
    (le_trans (topologicalKrullDim_irreducibleComponent_le Z hZ) hX) E n
    Kr J Q hKr hJ hQ hE hOX hOZ hEZ a b wab hS₁ c d wcd hS₂ h02O6 h0AYTK h0AYTQ

/-! ### Paragraph 1's arithmetic for two components -/

/-- For a closed immersion `i : Z ⟶ X`, `χ(i_*𝒪_Z ⊗ ℰ) − n·χ(i_*𝒪_Z)` is the degree of `ℰ|_Z`. -/
private theorem eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_pushforward_unit
    (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : topologicalKrullDim Z ≤ 1) (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] (hE : SheafOfModules.IsCoherent E)
    (hOZ : SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf))
    (hc : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hEZ : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E)) :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))).obj (E)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hc hE) -
      (n : ℤ) * @eulerCharacteristic k _ X f _
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) hc =
    @curveDegree k _ Z (i ≫ f) _ hZ ((Scheme.Modules.pullback i).obj E) n
      (isFiniteLocallyFreeOfRank_pullback i E n) := by
  rw [@curveDegree_eq_eulerCharacteristic_sub k _ Z (i ≫ f) _ hZ _ n
      (isFiniteLocallyFreeOfRank_pullback i E n) hEZ hOZ,
    eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion k i f E hE hOZ hc hEZ,
    eulerCharacteristic_pushforward_of_isClosedImmersion k i f _ hOZ hc]

/-- **Paragraph 1 of [Stacks, Tag 0AYW] for two components**:
`deg(ℰ) = deg(ℰ|_{Z₁}) + deg(ℰ|_{Z₂})`.

Let `i₁ : Z₁ ⟶ X` and `i₂ : Z₂ ⟶ X` be closed immersions and let `𝒫` be an extension

`0 ⟶ (i₁)_*𝒪_{Z₁} ⟶ 𝒫 ⟶ (i₂)_*𝒪_{Z₂} ⟶ 0`,

which is what `g_*𝒪_{X'}` is for `X' = Z₁ ⊔ Z₂ ⟶ X`. If `𝒫` also sits in the two short exact
sequences of [Stacks, Tag 0AYU] with clause (5) of [Stacks, Tag 0AYT] at their outer terms, then
the degree of `ℰ` is the sum of the degrees of its restrictions to `Z₁` and `Z₂`.

The proof is three applications of additivity. The [Stacks, Tag 0AYU] computation
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair` gives
`χ(𝒫 ⊗ ℰ) − n·χ(𝒫) = deg(ℰ)`; the extension splits `χ(𝒫)` into `χ((i₁)_*𝒪_{Z₁}) +
χ((i₂)_*𝒪_{Z₂})`; tensoring the extension with the flat `ℰ` splits `χ(𝒫 ⊗ ℰ)` the same way; and
each summand's pair of Euler characteristics is read off on `Zᵢ` by the projection formula and
cohomology comparison along a closed immersion, where it is `deg(ℰ|_{Zᵢ})`. -/
theorem curveDegree_eq_add_of_extension_pushforward_unit_of_shortExact_pair
    (k : Type u) [Field k] {X Z₁ Z₂ : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsLocallyNoetherian X]
    (i₁ : Z₁ ⟶ X) [IsClosedImmersion i₁] (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₂]
    (hX : topologicalKrullDim X ≤ 1)
    (hZ₁ : topologicalKrullDim Z₁ ≤ 1) (hZ₂ : topologicalKrullDim Z₂ ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hE : SheafOfModules.IsCoherent E)
    (hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf))
    (hOZ₁ : SheafOfModules.IsCoherent (SheafOfModules.unit Z₁.ringCatSheaf))
    (hOZ₂ : SheafOfModules.IsCoherent (SheafOfModules.unit Z₂.ringCatSheaf))
    (hEZ₁ : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i₁).obj E))
    (hEZ₂ : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i₂).obj E))
    (Kr J Q P : X.Modules)
    (hKr : SheafOfModules.IsCoherent Kr) (hJ : SheafOfModules.IsCoherent J)
    (hQ : SheafOfModules.IsCoherent Q) (hP : SheafOfModules.IsCoherent P)
    (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
    (hS₁ : (ShortComplex.mk a b wab).ShortExact)
    (c : J ⟶ P) (d : P ⟶ Q) (wcd : c ≫ d = 0)
    (hS₂ : (ShortComplex.mk c d wcd).ShortExact)
    (p : (Scheme.Modules.pushforward i₁).obj (SheafOfModules.unit Z₁.ringCatSheaf) ⟶ P)
    (q : P ⟶ (Scheme.Modules.pushforward i₂).obj (SheafOfModules.unit Z₂.ringCatSheaf))
    (wpq : p ≫ q = 0) (hS₃ : (ShortComplex.mk p q wpq).ShortExact)
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
      @curveDegree k _ Z₁ (i₁ ≫ f) _ hZ₁ ((Scheme.Modules.pullback i₁).obj E) n
          (isFiniteLocallyFreeOfRank_pullback i₁ E n) +
        @curveDegree k _ Z₂ (i₂ ≫ f) _ hZ₂ ((Scheme.Modules.pullback i₂).obj E) n
          (isFiniteLocallyFreeOfRank_pullback i₂ E n) := by
  classical
  have hc1 : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i₁).obj (SheafOfModules.unit Z₁.ringCatSheaf)) :=
    @isCoherent_pushforward_of_isClosedImmersion Z₁ X i₁ _ _ _ hOZ₁
  have hc2 : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i₂).obj (SheafOfModules.unit Z₂.ringCatSheaf)) :=
    @isCoherent_pushforward_of_isClosedImmersion Z₂ X i₂ _ _ _ hOZ₂
  have tc : ∀ (M : X.Modules), SheafOfModules.IsCoherent M →
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj
            (E))).IsCoherent :=
        fun M hM =>
    @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace M E hM hE
  -- the [Stacks, Tag 0AYU] computation at `𝒫`
  have hmain := eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair k f hX E n
    Kr J Q P hKr hJ hQ hP hE hOX a b wab hS₁ c d wcd hS₂ h02O6 h0AYTK h0AYTQ
  -- the vanishing bound of [Stacks, Tag 01XJ], uniform over quasi-coherent modules
  obtain ⟨N, hN⟩ := exists_isZero_cohomologyOverField_of_isProper k f
  have hvan : ∀ M : X.Modules, SheafOfModules.IsCoherent M →
      ∀ m, N ≤ m → IsZero (cohomologyOverField k f M m) := fun M hM m hm =>
    hN M (@_root_.isQuasicoherent_of_isCoherent _ _ _ M hM) m hm
  -- `χ` splits along the extension
  have hsumP : @eulerCharacteristic k _ X f _ P hP =
      @eulerCharacteristic k _ X f _
          ((Scheme.Modules.pushforward i₁).obj (SheafOfModules.unit Z₁.ringCatSheaf)) hc1 +
        @eulerCharacteristic k _ X f _
          ((Scheme.Modules.pushforward i₂).obj (SheafOfModules.unit Z₂.ringCatSheaf)) hc2 :=
    @eulerCharacteristic_add_of_shortExact_of_outer k _ X f _ _ hS₃ hc1 hP hc2 N
      (fun m _ => h02O6 _ hc1 m) (fun m _ => h02O6 _ hc2 m) (hvan _ hc1) (hvan _ hc2)
  -- and along the extension tensored with `ℰ`, which is exact because `ℰ` is flat
  have hfl :=
    @Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      _ _ _ X.presheaf X.ringCatSheaf.2 _ _ E n (by assumption)
  have hflat : Stacks.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) E :=
    @Scheme.Modules.isFlat_of_isFiniteLocallyFree X E hfl
  obtain ⟨z, hse⟩ :=
    Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor
      (ShortComplex.mk p q wpq) E hS₃ hflat
  have hsumPE : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (P)).obj (E)))
          (tc _ hP) =
      @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                (((Scheme.Modules.pushforward i₁).obj
                  (SheafOfModules.unit Z₁.ringCatSheaf)))).obj (E)))
          (tc _ hc1) +
        @eulerCharacteristic k _ X f _
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                  (((Scheme.Modules.pushforward i₂).obj
                    (SheafOfModules.unit Z₂.ringCatSheaf)))).obj (E)))
          (tc _ hc2) :=
    @eulerCharacteristic_add_of_shortExact_of_outer k _ X f _ _ hse
      (tc _ hc1) (tc _ hP) (tc _ hc2) N
      (fun m _ => h02O6 _ (tc _ hc1) m) (fun m _ => h02O6 _ (tc _ hc2) m)
      (hvan _ (tc _ hc1)) (hvan _ (tc _ hc2))
  -- each summand's two Euler characteristics, read off on `Zᵢ`
  rw [← hmain, hsumP, hsumPE,
    ← eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_pushforward_unit k f i₁ hZ₁ E n hE
      hOZ₁ hc1 hEZ₁,
    ← eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_pushforward_unit k f i₂ hZ₂ E n hE
      hOZ₂ hc2 hEZ₂]
  ring

end AlgebraicGeometry

end
