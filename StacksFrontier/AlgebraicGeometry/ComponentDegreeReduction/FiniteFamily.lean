module

public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.Basic

/-!
# [Stacks, Tag 0AYW], paragraph 1: the degree is the sum over the components

`StacksFrontier/AlgebraicGeometry/ComponentDegreeReduction/Basic.lean` proves paragraph 1 of
[Stacks, Tag 0AYW] for **two** components, `deg(ℰ) = deg(ℰ|_{Z₁}) + deg(ℰ|_{Z₂})`. This file runs
the induction and gets the finite family:

`deg(ℰ) = ∑ⱼ deg(ℰ|_{Zⱼ})`.

## The quantity the induction is about

The computation of [Stacks, Tag 0AYU],
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair`,
produces the degree of `ℰ` from a single coherent module `𝒫` as

`χ(X, 𝒫 ⊗ ℰ) − n · χ(X, 𝒫)`,

and it is that expression, not the degree, which is additive along a short exact sequence of
coherent modules. `AlgebraicGeometry.eulerCharacteristicTensorSheafSub` names it, and the three
facts the induction needs are stated about it: it is additive, it vanishes on a zero module, and
at `𝒫 = i_*𝒪_Z` for a closed immersion `i : Z ⟶ X` it is `deg(ℰ|_Z)`.

Taking `𝒫 = g_*𝒪_{X'}` for `X' = ∐ⱼ Zⱼ` as in [Stacks, Tag 0AYW], a filtration of `𝒫` whose
successive quotients are the `(iⱼ)_*𝒪_{Zⱼ}` then turns the single [Stacks, Tag 0AYU] computation
into the sum over `j`. The filtration is a hypothesis here: the direct image of the structure
sheaf of a disjoint union is not constructed in this library, and — as recorded in
`ComponentDegreeReduction/Basic.lean` — the biproduct of two such direct images cannot even be
written down at the concrete modules.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `eulerCharacteristicTensorSheafSub`: the quantity `χ(𝒫 ⊗ ℰ) − n·χ(𝒫)` of [Stacks, Tag 0AYU].
* `eulerCharacteristicTensorSheafSub_add_of_shortExact`: it is **additive** along a short exact
  sequence of coherent modules. Both halves are additivity of `χ` ([Stacks, Tag 08AA]), the
  second applied to the sequence tensored with `ℰ`, which stays exact because `ℰ` is flat.
* `eulerCharacteristicTensorSheafSub_eq_zero_of_isZero`: it **vanishes on a zero module** — the
  base case of the induction, obtained from additivity along `0 ⟶ 0 ⟶ 0 ⟶ 0 ⟶ 0`.
* `eulerCharacteristicTensorSheafSub_eq_curveDegree_pullback_of_isClosedImmersion`: at
  `𝒫 = i_*𝒪_Z` for a closed immersion it is `deg(ℰ|_Z)`, by the projection formula and the
  cohomology comparison along a closed immersion.
* `eulerCharacteristicTensorSheafSub_eq_add_sum_of_filtration`: **the induction.** For a
  filtration `P 0 ⊆ P 1 ⊆ ⋯ ⊆ P N` with successive quotients `G 0, …, G (N-1)`,
  `D(P N) = D(P 0) + ∑_{j < N} D(G j)`.
* `curveDegree_eq_sum_of_filtration_pushforward_unit_of_shortExact_pair`: **paragraph 1 of
  [Stacks, Tag 0AYW] for a finite family**, `deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`.
* `curveDegree_eq_zero_of_eulerCharacteristic_unit_tensorSheaf_eq`: **a zero-dimensional
  component contributes nothing to the sum**, given clause (5) of [Stacks, Tag 0AYT] at its
  structure sheaf. This is what makes the mismatch between the source's open `Uᵢ` and Mathlib's
  `Scheme.irreducibleComponentOpen` harmless; see the implementation notes.

## Implementation notes

**The two flavours of `Uᵢ`, and why the difference does not matter.** The source forms
`Uᵢ = X ∖ (⋃_{j ≠ i} Cⱼ)` with `Cⱼ` ranging over the **one-dimensional** irreducible components,
whereas `AlgebraicGeometry.Scheme.irreducibleComponentOpen` removes **every** other irreducible
component. The two differ exactly when `X` has an isolated point, which a scheme proper over a
field with `topologicalKrullDim X ≤ 1` may well have — `Spec k ⊔ ℙ¹_k` does — so the case cannot
be excluded by a proof, and no hypothesis forbidding it is imposed here. It is harmless for two
reasons, and both are visible in the statements below. First, the family of closed immersions is
taken abstractly: nothing in this file depends on how the `Zⱼ` were produced, so either
construction may be fed to it. Second, with Mathlib's open the index set of the sum is all of
`irreducibleComponents X`, and the extra, zero-dimensional terms are zero by
`curveDegree_eq_zero_of_eulerCharacteristic_unit_tensorSheaf_eq`; while at the generic point of a
one-dimensional component both opens contain that point, so both give the same local ring there
and both satisfy the hypothesis of [Stacks, Tag 0AYU].

**The filtration is indexed by `ℕ` and only its first `N + 1` stages are used.** Totality costs
a caller nothing: the families `Zⱼ`, `iⱼ`, `Pⱼ` may be extended past `N` by anything at all, for
instance by `X` and `𝟙 X`, and the hypotheses are then satisfied for the extended indices as
well. Indexing by `Fin (N + 1)` would have made the induction step change the index type.

**Discharging the base of the filtration.** `P 0` may be taken to be the zero object, whose
`IsZero` is `CategoryTheory.Limits.isZero_zero` and whose coherence is
`Stacks.SheafOfModules.isCoherent_of_isZero` — except that the latter proves the coherence class
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`, while the statements here use
the identically-named and identically-signatured class of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`. The two are
different constants and the conversion is
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent'`.

**What is assumed is unchanged from the two-component case.** The two short exact sequences of
[Stacks, Tag 0AYU], the finite dimensionality of [Stacks, Tag 02O6] and clause (5) of
[Stacks, Tag 0AYT] at the outer terms are hypotheses, in the same shapes as in
`ComponentDegreeReduction/Basic.lean`. The only new hypothesis is the filtration.

**No attribute for [Stacks, Tag 0AYW] is attached.** The headline theorem below is paragraph 1 of
its *proof*, not the tag: it carries the filtration, the two short exact sequences,
[Stacks, Tag 02O6] and clause (5) of [Stacks, Tag 0AYT] as hypotheses, and says nothing about
paragraph 2's induction on the ideal of the reduction.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The quantity of [Stacks, Tag 0AYU] and its additivity -/

/-- **The quantity `χ(X, 𝒫 ⊗ ℰ) − n · χ(X, 𝒫)` of the computation of [Stacks, Tag 0AYU].**

`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair` says
that this is `deg(ℰ)` when `𝒫` sits in the four-term sequence of that tag; the point of naming it
is that, unlike the degree, it is additive along short exact sequences in `𝒫`, which is what
turns the single computation into a sum over the components in [Stacks, Tag 0AYW]. -/
noncomputable def eulerCharacteristicTensorSheafSub [IsProper f]
    (E : X.Modules) (hE : SheafOfModules.IsCoherent E) (n : ℕ)
    (P : X.Modules) (hP : SheafOfModules.IsCoherent P) : ℤ :=
  @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (P)).obj (E)))
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace P E hP hE) -
    (n : ℤ) * @eulerCharacteristic k _ X f _ P hP

/-- **The quantity of [Stacks, Tag 0AYU] at a module satisfying that tag's hypotheses is the
degree**, which is
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair`
restated through `AlgebraicGeometry.eulerCharacteristicTensorSheafSub`. -/
theorem eulerCharacteristicTensorSheafSub_eq_curveDegree_of_shortExact_pair [IsProper f]
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
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Kr)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Kr E hKr hE) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Kr hKr)
    (h0AYTQ : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (Q)).obj (E)))
          (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace Q E hQ hE) =
        (n : ℤ) * @eulerCharacteristic k _ X f _ Q hQ) :
    eulerCharacteristicTensorSheafSub k f E hE n P hP = curveDegree k f hX E n :=
  eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair k f hX E n
    Kr J Q P hKr hJ hQ hP hE hOX a b wab hS₁ c d wcd hS₂ h02O6 h0AYTK h0AYTQ

/-- **Additivity of the quantity of [Stacks, Tag 0AYU] along a short exact sequence.** For a
short exact sequence `0 ⟶ 𝒫₁ ⟶ 𝒫₂ ⟶ 𝒫₃ ⟶ 0` of coherent modules,

`χ(𝒫₂ ⊗ ℰ) − n·χ(𝒫₂) = (χ(𝒫₁ ⊗ ℰ) − n·χ(𝒫₁)) + (χ(𝒫₃ ⊗ ℰ) − n·χ(𝒫₃))`.

Both halves are [Stacks, Tag 08AA] in the shape
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional`, the second
applied to the sequence tensored with `ℰ`, which is still short exact because a finite locally
free module is flat. This is the only property of the quantity that the induction of
[Stacks, Tag 0AYW] uses, and it is the property the degree itself does not have. -/
theorem eulerCharacteristicTensorSheafSub_add_of_shortExact [IsProper f]
    (E : X.Modules) (hE : SheafOfModules.IsCoherent E) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : SheafOfModules.IsCoherent S.X₁) (h₂ : SheafOfModules.IsCoherent S.X₂)
    (h₃ : SheafOfModules.IsCoherent S.X₃)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m)) :
    eulerCharacteristicTensorSheafSub k f E hE n S.X₂ h₂ =
      eulerCharacteristicTensorSheafSub k f E hE n S.X₁ h₁ +
        eulerCharacteristicTensorSheafSub k f E hE n S.X₃ h₃ := by
  classical
  have hfl :=
    @Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      _ _ _ X.presheaf X.ringCatSheaf.2 _ _ E n (by assumption)
  have hflat : Stacks.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) E :=
    @Scheme.Modules.isFlat_of_isFiniteLocallyFree X E hfl
  have tc : ∀ (M : X.Modules), SheafOfModules.IsCoherent M →
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj (E))).IsCoherent :=
        fun M hM =>
    @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace M E hM hE
  have hadd : @eulerCharacteristic k _ X f _ S.X₂ h₂ =
      @eulerCharacteristic k _ X f _ S.X₁ h₁ + @eulerCharacteristic k _ X f _ S.X₃ h₃ :=
    @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hS
      h₁ h₂ h₃ (h02O6 _ h₁) (h02O6 _ h₃)
  obtain ⟨z, hse⟩ :=
    Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor S E hS hflat
  have haddT : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (S.X₂)).obj (E))) (tc _ h₂)
          =
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (S.X₁)).obj (E)))
          (tc _ h₁) +
        @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (S.X₃)).obj (E)))
          (tc _ h₃) :=
    @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hse
      (tc _ h₁) (tc _ h₂) (tc _ h₃) (h02O6 _ (tc _ h₁)) (h02O6 _ (tc _ h₃))
  simp only [eulerCharacteristicTensorSheafSub]
  rw [hadd, haddT]
  ring

/-- **The quantity of [Stacks, Tag 0AYU] vanishes on a zero module.** This is the base case of
the induction of [Stacks, Tag 0AYW]: a filtration of `g_*𝒪_{X'}` starts at `0`.

The proof is additivity along the short exact sequence `0 ⟶ 𝒫 ⟶ 𝒫 ⟶ 𝒫 ⟶ 0` whose maps are the
identity of the zero module `𝒫`, which gives `D(𝒫) = D(𝒫) + D(𝒫)`. -/
theorem eulerCharacteristicTensorSheafSub_eq_zero_of_isZero [IsProper f]
    (E : X.Modules) (hE : SheafOfModules.IsCoherent E) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (P : X.Modules) (hP : SheafOfModules.IsCoherent P) (hz : IsZero P)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m)) :
    eulerCharacteristicTensorSheafSub k f E hE n P hP = 0 := by
  have hse : (ShortComplex.mk (𝟙 P) (𝟙 P) (hz.eq_of_src (𝟙 P ≫ 𝟙 P) 0)).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hz }
  have h : eulerCharacteristicTensorSheafSub k f E hE n P hP =
      eulerCharacteristicTensorSheafSub k f E hE n P hP +
        eulerCharacteristicTensorSheafSub k f E hE n P hP :=
    eulerCharacteristicTensorSheafSub_add_of_shortExact k f E hE n hse hP hP hP h02O6
  linear_combination -h

/-! ### The quantity of [Stacks, Tag 0AYU] at the structure sheaf of a closed subscheme -/

/-- **At `𝒫 = i_*𝒪_Z` for a closed immersion `i : Z ⟶ X`, the quantity of [Stacks, Tag 0AYU] is
the degree of the restriction**: `χ(i_*𝒪_Z ⊗ ℰ) − n·χ(i_*𝒪_Z) = deg(ℰ|_Z)`.

The two Euler characteristics are read off on `Z` — the first by the projection formula for a
closed immersion together with the cohomology comparison along it,
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion`, the
second by that comparison alone — and there the difference is the defining formula for
`AlgebraicGeometry.curveDegree`. -/
theorem eulerCharacteristicTensorSheafSub_eq_curveDegree_pullback_of_isClosedImmersion
    [IsProper f] [IsLocallyNoetherian X] {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : topologicalKrullDim Z ≤ 1)
    (E : X.Modules) (hE : SheafOfModules.IsCoherent E) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hOZ : SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf))
    (hpush : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hEZ : SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E)) :
    eulerCharacteristicTensorSheafSub k f E hE n
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) hpush =
      @curveDegree k _ Z (i ≫ f) _ hZ ((Scheme.Modules.pullback i).obj E) n
        (isFiniteLocallyFreeOfRank_pullback i E n) := by
  have htens : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))).obj (E)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hpush hE) =
      @eulerCharacteristic k _ Z (i ≫ f) _ ((Scheme.Modules.pullback i).obj E) hEZ :=
    eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion k i f E hE hOZ
      hpush hEZ
  have hbase : @eulerCharacteristic k _ X f _
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)) hpush =
      @eulerCharacteristic k _ Z (i ≫ f) _ (SheafOfModules.unit Z.ringCatSheaf) hOZ :=
    eulerCharacteristic_pushforward_of_isClosedImmersion k i f _ hOZ hpush
  have hdeg : @curveDegree k _ Z (i ≫ f) _ hZ ((Scheme.Modules.pullback i).obj E) n
        (isFiniteLocallyFreeOfRank_pullback i E n) =
      @eulerCharacteristic k _ Z (i ≫ f) _ ((Scheme.Modules.pullback i).obj E) hEZ -
        (n : ℤ) * @eulerCharacteristic k _ Z (i ≫ f) _
          (SheafOfModules.unit Z.ringCatSheaf) hOZ :=
    @curveDegree_eq_eulerCharacteristic_sub k _ Z (i ≫ f) _ hZ _ n
      (isFiniteLocallyFreeOfRank_pullback i E n) hEZ hOZ
  rw [eulerCharacteristicTensorSheafSub, hdeg, htens, hbase]

/-! ### The induction over the components -/

/-- **The induction of paragraph 1 of [Stacks, Tag 0AYW], for the quantity of
[Stacks, Tag 0AYU].** Let `P 0, P 1, …, P N` be coherent modules fitting into short exact
sequences

`0 ⟶ P j ⟶ P (j + 1) ⟶ G j ⟶ 0`,  `j < N`,

that is a filtration of `P N` with successive quotients `G 0, …, G (N - 1)`. Then

`D(P N) = D(P 0) + ∑_{j < N} D(G j)`

for `D = ` `AlgebraicGeometry.eulerCharacteristicTensorSheafSub`. Only additivity is used, so
nothing is assumed about the quotients beyond coherence; the application in
[Stacks, Tag 0AYW] takes `G j = (iⱼ)_*𝒪_{Zⱼ}` and `P 0 = 0`. -/
theorem eulerCharacteristicTensorSheafSub_eq_add_sum_of_filtration [IsProper f]
    (E : X.Modules) (hE : SheafOfModules.IsCoherent E) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (P G : ℕ → X.Modules)
    (hP : ∀ j, SheafOfModules.IsCoherent (P j))
    (hG : ∀ j, SheafOfModules.IsCoherent (G j)) (N : ℕ)
    (hfilt : ∀ j < N, ∃ (p : P j ⟶ P (j + 1)) (q : P (j + 1) ⟶ G j) (w : p ≫ q = 0),
      (ShortComplex.mk p q w).ShortExact) :
    eulerCharacteristicTensorSheafSub k f E hE n (P N) (hP N) =
      eulerCharacteristicTensorSheafSub k f E hE n (P 0) (hP 0) +
        ∑ j ∈ Finset.range N, eulerCharacteristicTensorSheafSub k f E hE n (G j) (hG j) := by
  induction N with
  | zero => simp
  | succ m ih =>
      obtain ⟨p, q, w, hse⟩ := hfilt m (Nat.lt_succ_self m)
      have h : eulerCharacteristicTensorSheafSub k f E hE n (P (m + 1)) (hP (m + 1)) =
          eulerCharacteristicTensorSheafSub k f E hE n (P m) (hP m) +
            eulerCharacteristicTensorSheafSub k f E hE n (G m) (hG m) :=
        eulerCharacteristicTensorSheafSub_add_of_shortExact k f E hE n hse
          (hP m) (hP (m + 1)) (hG m) h02O6
      rw [Finset.sum_range_succ, ← add_assoc,
        ← ih (fun j hj => hfilt j (Nat.lt_succ_of_lt hj))]
      exact h

/-- **Paragraph 1 of [Stacks, Tag 0AYW] for a finite family of components**:
`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`.

Let `iⱼ : Zⱼ ⟶ X` be closed immersions and let `𝒫 = P N` carry a filtration

`0 = P 0 ⊆ P 1 ⊆ ⋯ ⊆ P N = 𝒫`,  `P (j + 1) / P j ≅ (iⱼ)_*𝒪_{Zⱼ}`,

which is what `g_*𝒪_{X'}` carries for `X' = ∐_{j < N} Zⱼ ⟶ X`. If `𝒫` also sits in the two
short exact sequences of [Stacks, Tag 0AYU] with clause (5) of [Stacks, Tag 0AYT] at their outer
terms, then the degree of `ℰ` is the sum of the degrees of its restrictions to the `Zⱼ`.

`AlgebraicGeometry.curveDegree_eq_add_of_extension_pushforward_unit_of_shortExact_pair` is the
case `N = 2` with the filtration spelled out as a single extension. -/
theorem curveDegree_eq_sum_of_filtration_pushforward_unit_of_shortExact_pair
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
    (hQ : SheafOfModules.IsCoherent Q)
    (P : ℕ → X.Modules) (hP : ∀ j, SheafOfModules.IsCoherent (P j))
    (N : ℕ) (hP0 : IsZero (P 0))
    (hfilt : ∀ j < N, ∃ (p : P j ⟶ P (j + 1))
        (q : P (j + 1) ⟶ (Scheme.Modules.pushforward (i j)).obj
          (SheafOfModules.unit (Zs j).ringCatSheaf)) (w : p ≫ q = 0),
        (ShortComplex.mk p q w).ShortExact)
    (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
    (hS₁ : (ShortComplex.mk a b wab).ShortExact)
    (c : J ⟶ P N) (d : P N ⟶ Q) (wcd : c ≫ d = 0)
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
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) := by
  have hpush : ∀ j, SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward (i j)).obj (SheafOfModules.unit (Zs j).ringCatSheaf)) :=
    fun j => @isCoherent_pushforward_of_isClosedImmersion _ X (i j) _ _ _ (hOZ j)
  have hmain : eulerCharacteristicTensorSheafSub k f E hE n (P N) (hP N) =
      curveDegree k f hX E n :=
    eulerCharacteristicTensorSheafSub_eq_curveDegree_of_shortExact_pair k f hX E n
      Kr J Q (P N) hKr hJ hQ (hP N) hE hOX a b wab hS₁ c d wcd hS₂ h02O6 h0AYTK h0AYTQ
  have hsum := eulerCharacteristicTensorSheafSub_eq_add_sum_of_filtration k f E hE n h02O6
    P (fun j => (Scheme.Modules.pushforward (i j)).obj
      (SheafOfModules.unit (Zs j).ringCatSheaf)) hP hpush N hfilt
  have hzero : eulerCharacteristicTensorSheafSub k f E hE n (P 0) (hP 0) = 0 :=
    eulerCharacteristicTensorSheafSub_eq_zero_of_isZero k f E hE n (P 0) (hP 0) hP0 h02O6
  have hterm : ∀ j, eulerCharacteristicTensorSheafSub k f E hE n
        ((Scheme.Modules.pushforward (i j)).obj
          (SheafOfModules.unit (Zs j).ringCatSheaf)) (hpush j) =
      @curveDegree k _ (Zs j) (i j ≫ f) _ (hZ j)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) := fun j =>
    eulerCharacteristicTensorSheafSub_eq_curveDegree_pullback_of_isClosedImmersion k f
      (i j) (hZ j) E hE n (hOZ j) (hpush j) (hEZ j)
  rw [← hmain, hsum, hzero, zero_add]
  exact Finset.sum_congr rfl fun j _ => hterm j

/-! ### A zero-dimensional component contributes nothing -/

/-- **A component on which clause (5) of [Stacks, Tag 0AYT] holds at the structure sheaf has
degree zero.** If `χ(Z, 𝒪_Z ⊗ ℱ) = n · χ(Z, 𝒪_Z)` — which is clause (5) of [Stacks, Tag 0AYT]
at `𝒢 = 𝒪_Z`, hence available whenever `topologicalKrullDim Z ≤ 0`, the support of `𝒪_Z` being
`Z` itself — then `deg(ℱ) = 0`.

This is what makes the index set of
`AlgebraicGeometry.curveDegree_eq_sum_of_filtration_pushforward_unit_of_shortExact_pair`
insensitive to the zero-dimensional irreducible components of `X`, and hence makes the mismatch
between the open `Uᵢ` of [Stacks, Tag 0AYW] and
`AlgebraicGeometry.Scheme.irreducibleComponentOpen` harmless: the terms of the sum that the
former omits and the latter keeps are zero. -/
theorem curveDegree_eq_zero_of_eulerCharacteristic_unit_tensorSheaf_eq
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsProper g]
    (hZ : topologicalKrullDim Z ≤ 1)
    (F : Z.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F n]
    (hF : SheafOfModules.IsCoherent F)
    (hOZ : SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf))
    (h0AYT5 : @eulerCharacteristic k _ Z g _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩).obj
              ((SheafOfModules.unit Z.ringCatSheaf))).obj (F)))
          (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ F hOZ hF) =
        (n : ℤ) * @eulerCharacteristic k _ Z g _ (SheafOfModules.unit Z.ringCatSheaf) hOZ) :
    curveDegree k g hZ F n = 0 := by
  have hdeg : curveDegree k g hZ F n =
      @eulerCharacteristic k _ Z g _ F hF -
        (n : ℤ) * @eulerCharacteristic k _ Z g _ (SheafOfModules.unit Z.ringCatSheaf) hOZ :=
    @curveDegree_eq_eulerCharacteristic_sub k _ Z g _ hZ F n _ hF hOZ
  have hunit : @eulerCharacteristic k _ Z g _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩).obj
            ((SheafOfModules.unit Z.ringCatSheaf))).obj (F)))
        (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ F hOZ hF) =
      @eulerCharacteristic k _ Z g _ F hF :=
    eulerCharacteristic_unit_tensorSheaf k g F hF hOZ
  rw [hdeg, ← hunit, h0AYT5]
  ring

end AlgebraicGeometry

end
