module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Symmetry
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# The Euler characteristic of a tensor product on a proper curve, assembled from its dévissage

[Stacks, Tag 0AYV] computes `χ(X, ℰ ⊗ ℱ)` on a proper curve over a field, for `ℰ` finite
locally free of rank `n` and `ℱ` coherent, as `r · deg(ℰ) + n · χ(X, ℱ)` where `r` is the rank
of `ℱ` at the generic point. Its proof runs the dévissage of [Stacks, Tag 01YH] over the
property "the formula holds for `ℱ`", whose two base cases are `ℱ = 𝒪_X` and a sheaf whose
support is a proper closed subset.

This file proves the conclusion of the tag from three inputs, each taken as an explicit
hypothesis. The resulting statement carries three hypotheses the tag does not.

## The three inputs

* **[Stacks, Tag 02O6]**, finite dimensionality over `k` of the cohomology of a coherent
  module on a proper scheme over a field. This is the only hypothesis of
  `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional`, which is
  [Stacks, Tag 08AA].
* **The dévissage of [Stacks, Tag 01YH]**, in the "two out of three along a short exact
  sequence, plus the structure sheaf, plus modules supported on a proper closed subset" shape.
* **[Stacks, Tag 0AYT] (5)**, the formula for a coherent module whose support has dimension at
  most zero, where it reads `χ(X, ℰ ⊗ 𝒢) = n · χ(X, 𝒢)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fiberRank_unit_eq_one`: the fibre rank of the structure
  sheaf is one at every point.
* `AlgebraicGeometry.Scheme.Modules.fiberRank_eq_zero_of_notMem_supp`: the fibre rank vanishes
  off the support.
* `AlgebraicGeometry.notMem_of_isClosed_of_ne_univ`: the generic point of an irreducible sober
  space lies in no proper closed subset.
* `AlgebraicGeometry.topologicalKrullDim_le_zero_of_isClosed_of_ne_univ`: a proper closed subset
  of an irreducible space of dimension at most one has dimension at most zero.
* `AlgebraicGeometry.eulerCharacteristic_tensorSheaf_add_of_shortExact_of_finiteDimensional`:
  additivity of `χ(X, ℰ ⊗ −)` along a short exact sequence of coherent modules, given
  [Stacks, Tag 02O6]. Tensoring is exact because `ℰ` is finite locally free, hence flat.
* `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add`:
  **the conclusion of [Stacks, Tag 0AYV], from the three inputs above.**

## Implementation notes

**The two argument orders of the tensor product.** Flatness is stated for the endofunctor
`− ⊗ ℰ` (`Stacks.sheafTensorRight`), whose value at `𝒢` is *definitionally*
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X 𝒢 ℰ`, while Tag 0AYV writes the tensor
product as `ℰ ⊗ 𝒢`. The two are compared once, by
`AlgebraicGeometry.eulerCharacteristic_tensorSheaf_comm`, and the additivity statement below is
phrased in the tag's order.

**Why the finite-dimensionality hypothesis is quantified over all coherent modules** rather
than being imposed on the three modules of the sequence: the modules it is needed for are the
tensor products `ℰ ⊗ 𝒢`, not the `𝒢`, and inside the dévissage they vary. Quantifying over all
coherent modules is exactly the statement of Tag 02O6, so the hypothesis is the tag rather than
an artefact of the proof.

**Why the dévissage's closed-support clause is stated with `supp 𝒢 ⊆ Z`** for `Z` closed and
proper, rather than with a bound on the dimension of the support: that is the shape in which
the dévissage of Tag 01YH produces it, from a closed immersion whose range contains the
support. The passage to the dimension form in which Tag 0AYT (5) is stated is
`topologicalKrullDim_le_zero_of_isClosed_of_ne_univ`.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open _root_.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The fibre rank of the structure sheaf is one at every point.** The structure sheaf is
finite locally free of rank one, and the fibre rank of a finite locally free module of constant
rank is that rank. -/
@[sga "6 I 6.0" "Clause (iii) for schemes"]
theorem fiberRank_unit_eq_one {X : Scheme.{u}} (x : X) :
    fiberRank (_root_.SheafOfModules.unit X.ringCatSheaf) x = 1 :=
  fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank _ 1 x

/-- **The fibre rank vanishes off the support.** Away from the support the stalk has no nonzero
element, so the residue-field fibre is zero. -/
theorem fiberRank_eq_zero_of_notMem_supp {X : Scheme.{u}} (F : X.Modules) (x : X)
    (hx : x ∉ _root_.SheafOfModules.supp F) : fiberRank F x = 0 := by
  refine fiberRank_eq_zero_of_subsingleton_stalk F x ⟨fun a b => ?_⟩
  have h (c : ToType (F.presheaf.stalk x)) : c = 0 := by_contra fun hc => hx ⟨c, hc⟩
  rw [h a, h b]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- **The generic point of an irreducible sober space lies in no proper closed subset**: its
closure is the whole space, so a closed set containing it is everything. -/
theorem notMem_of_isClosed_of_ne_univ {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    [QuasiSober X] (Z : Set X) (hZ : IsClosed Z) (hne : Z ≠ Set.univ) :
    genericPoint X ∉ Z := by
  intro hx
  refine hne (Set.eq_univ_of_univ_subset ?_)
  rw [← genericPoint_closure X]
  exact closure_minimal (Set.singleton_subset_iff.mpr hx) hZ

/-- **A proper closed subset of an irreducible space of dimension at most one has dimension at
most zero.** The inclusion of a closed subspace is strictly monotone on irreducible closed
subsets and misses the top one, so a chain of length one inside `Z` would give a chain of
length two in `X`. -/
theorem topologicalKrullDim_le_zero_of_isClosed_of_ne_univ {X : Type*} [TopologicalSpace X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1) (Z : Set X) (hZ : IsClosed Z)
    (hne : Z ≠ Set.univ) : topologicalKrullDim Z ≤ 0 := by
  let : OrderTop (IrreducibleCloseds X) :=
    { top := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
      le_top := fun _ => Set.subset_univ _ }
  let g := IrreducibleCloseds.map (Subtype.val : Z → X) continuous_subtype_val
  have hg : StrictMono g :=
    IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  have hne' (W : IrreducibleCloseds Z) : g W ≠ ⊤ := by
    intro he
    have hsub : (g W : Set X) ⊆ Z := by
      show closure (Subtype.val '' (W : Set Z)) ⊆ Z
      exact closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact y.property) hZ
    rw [he] at hsub
    exact hne (Set.eq_univ_of_univ_subset hsub)
  refine Order.krullDim_nonpos_iff_forall_isMin.mpr fun W V hVW => ?_
  have hback := (Order.krullDim_le_one_iff_forall_isMin.mp hdim) (g W) (hne' W) (hg.monotone hVW)
  by_contra hn
  exact (not_lt_of_ge hback) (hg (lt_of_le_not_ge hVW hn))

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Additivity of `χ(X, ℰ ⊗ −)` along a short exact sequence of coherent modules on a proper
curve**, given the finite dimensionality of [Stacks, Tag 02O6] for the cohomology of the tensor
products: `χ(X, ℰ ⊗ 𝒢₂) = χ(X, ℰ ⊗ 𝒢₁) + χ(X, ℰ ⊗ 𝒢₃)` for a short exact sequence
`0 → 𝒢₁ → 𝒢₂ → 𝒢₃ → 0` of coherent modules and `ℰ` finite locally free of rank `n`. -/
theorem eulerCharacteristic_tensorSheaf_add_of_shortExact_of_finiteDimensional [IsCurve k f]
    [IsProper f] (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [h₁ : SheafOfModules.IsCoherent S.X₁] [h₂ : SheafOfModules.IsCoherent S.X₂]
    [h₃ : SheafOfModules.IsCoherent S.X₃] :
    @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (S.X₂)))
        (isCoherent_tensorSheaf_of_isCurve k f E n S.X₂) =
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (S.X₁)))
          (isCoherent_tensorSheaf_of_isCurve k f E n S.X₁) +
        @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (S.X₃)))
          (isCoherent_tensorSheaf_of_isCurve k f E n S.X₃) := by
  have hE : SheafOfModules.IsCoherent E :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f E n
  have hfl :=
    @Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      _ _ _ X.presheaf X.ringCatSheaf.2 _ _ E n (by assumption)
  have hflat : Stacks.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) E :=
    @Scheme.Modules.isFlat_of_isFiniteLocallyFree X E hfl
  obtain ⟨h0, hse⟩ :=
    Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor S E hS hflat
  have c (G : X.Modules) [h : SheafOfModules.IsCoherent G] :
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj G).obj E)).IsCoherent :=
    @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace G E h hE
  have e (G : X.Modules) [h : SheafOfModules.IsCoherent G] :=
    @eulerCharacteristic_tensorSheaf_comm k _ X f _ G E h hE
  exact (e S.X₂).symm.trans
    ((@eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hse
      (c S.X₁) (c S.X₂) (c S.X₃) (h02O6 _ (c S.X₁)) (h02O6 _ (c S.X₃))).trans
      (congrArg₂ (· + ·) (e S.X₁) (e S.X₃)))

/-- **The conclusion of [Stacks, Tag 0AYV]**, from three inputs: the finite dimensionality of
[Stacks, Tag 02O6], the dévissage of [Stacks, Tag 01YH], and the formula of [Stacks, Tag 0AYT] (5)
for a module with zero-dimensional support.

For `ℰ` finite locally free of rank `n` and `ℱ` coherent on a proper curve over a field,
`χ(X, ℰ ⊗ ℱ) = r · deg(ℰ) + n · χ(X, ℱ)`, where `r` is the fibre rank of `ℱ` at the generic
point. -/
theorem exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add [IsCurve k f]
    [IsProper f] (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (h0AYT : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G),
      topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0 →
      ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))).IsCoherent,
        @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hT =
          (n : ℤ) * @eulerCharacteristic k _ X f _ G hG)
    (F : X.Modules) [SheafOfModules.IsCoherent F] :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))) h =
        (Scheme.Modules.fiberRank F (genericPoint X) : ℤ) *
            curveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E n +
          (n : ℤ) * eulerCharacteristic k f F := by
  have hdim : topologicalKrullDim X ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))
  have hE : SheafOfModules.IsCoherent E :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f E n
  have hO : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1
  let P : X.Modules → Prop := fun G => ∀ hG : SheafOfModules.IsCoherent G,
    ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
          (G))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hT =
        (Scheme.Modules.fiberRank G (genericPoint X) : ℤ) * curveDegree k f hdim E n +
          (n : ℤ) * @eulerCharacteristic k _ X f _ G hG
  have hPF : P F := by
    apply hdev P ?_ ?_ ?_ F inferInstance
    · intro T hT t₁ t₂ t₃
      have := t₁
      have := t₂
      have := t₃
      have hχT := eulerCharacteristic_tensorSheaf_add_of_shortExact_of_finiteDimensional
        k f E n h02O6 T hT
      have hχ := @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ T hT
        t₁ t₂ t₃ (h02O6 T.X₁ t₁) (h02O6 T.X₃ t₃)
      have hr : (Scheme.Modules.fiberRank T.X₂ (genericPoint X) : ℤ) =
          (Scheme.Modules.fiberRank T.X₁ (genericPoint X) : ℤ) +
            (Scheme.Modules.fiberRank T.X₃ (genericPoint X) : ℤ) := by
        exact_mod_cast Scheme.Modules.fiberRank_genericPoint_add_of_shortExact T hT
      have hrd := congrArg (fun r : ℤ => r * curveDegree k f hdim E n) hr
      have hnχ := congrArg (fun b : ℤ => (n : ℤ) * b) hχ
      dsimp only [P] at hrd hnχ ⊢
      refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨p, q⟩ _
      all_goals
        obtain ⟨_, e⟩ := p ‹_›
        obtain ⟨_, e'⟩ := q ‹_›
        exact ⟨isCoherent_tensorSheaf_of_isCurve k f E n _, by linarith⟩
    · intro G Z hZ hne hsub hG
      have := hG
      have hft : G.IsFiniteType := hG.isFiniteType
      have hξ : genericPoint X ∉ _root_.SheafOfModules.supp G := fun h =>
        notMem_of_isClosed_of_ne_univ Z hZ hne (hsub h)
      have hr : Scheme.Modules.fiberRank G (genericPoint X) = 0 :=
        Scheme.Modules.fiberRank_eq_zero_of_notMem_supp G _ hξ
      have hne' : _root_.SheafOfModules.supp G ≠ Set.univ := fun he =>
        hξ (he ▸ Set.mem_univ _)
      have hdimG := topologicalKrullDim_le_zero_of_isClosed_of_ne_univ hdim
        (_root_.SheafOfModules.supp G) (_root_.SheafOfModules.isClosed_supp G) hne'
      obtain ⟨hTG, hχG⟩ := h0AYT G hG hdimG
      exact ⟨hTG, by rw [hχG, hr]; push_cast; ring⟩
    · intro hO'
      refine ⟨isCoherent_tensorSheaf_of_isCurve k f E n _, ?_⟩
      rw [Scheme.Modules.fiberRank_unit_eq_one]
      push_cast
      exact @eulerCharacteristic_tensor_unit_eq_curveDegree_add k _ X f _ hdim E n _ hE hO
  exact hPF inferInstance

end AlgebraicGeometry

end
