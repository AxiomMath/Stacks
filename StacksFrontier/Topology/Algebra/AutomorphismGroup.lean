module
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# The topology on the automorphism group of a discrete space

For a discrete space `E`, the space of self-maps `E → E` carries the product topology, which here
coincides with the compact-open topology; a fundamental system of neighbourhoods of `f` is given by
the sets of maps agreeing with `f` on a finite subset. The action, composition and inversion maps
are continuous, so the permutation group `Equiv.Perm E` with the induced topology is a topological
group.

## Main definitions

* `U_S`: the self-maps agreeing with a given `f` on a finite subset.
* `autTopology`: the topology on `Equiv.Perm E` induced from the product topology on `E → E`.

## Main results

* `mapTopology_nhds_hasBasis`: the sets `U_S S f` form a neighbourhood basis of `f`.
* `continuous_action`: the evaluation map `(E → E) × E → E` is continuous.
* `continuous_iff_uncurry_continuous`: a map into `E → E` is continuous exactly when its uncurrying
  is continuous.
* `continuous_comp`: composition of self-maps is continuous.
* `continuous_perm_inv`: inversion on `Equiv.Perm E` is continuous.
* `isTopologicalGroup_aut`: `Equiv.Perm E` is a topological group.
-/

@[expose] public section

universe u
variable {E : Type u} [TopologicalSpace E] [DiscreteTopology E]

/-- The set `U_S(f) = { f' : E → E | ∀ s ∈ S, f' s = f s }` of self-maps that agree
with `f` on the finite subset `S ⊆ E`. These form a fundamental system of
neighbourhoods of `f` in the product topology on `E → E` (which, when `E` is
discrete, coincides with the compact-open topology). -/
def U_S (S : Finset E) (f : E → E) : Set (E → E) :=
  { f' : E → E | ∀ s ∈ S, f' s = f s }

/-- The topology on `Aut(E) ≃ Equiv.Perm E` induced from the product topology on
`E → E` via the inclusion `σ ↦ (σ : E → E)`. -/
instance autTopology : TopologicalSpace (Equiv.Perm E) :=
  TopologicalSpace.induced (fun σ : Equiv.Perm E => (σ : E → E)) inferInstance

/-- The maps `E → E` taking a given value at a given point form an open set. -/
private lemma isOpen_setOf_apply_eq (e c : E) : IsOpen {f : E → E | f e = c} :=
  (isOpen_discrete ({c} : Set E)).preimage (f := fun f : E → E => f e) (continuous_apply e)

/-- `U_S S f` is a neighbourhood of `f`: it is the finite intersection of the
open preimages `(· s)⁻¹' {f s}` for `s ∈ S`. -/
lemma U_S_mem_nhds (S : Finset E) (f : E → E) : U_S S f ∈ nhds f := by
  have hopen : IsOpen (U_S S f) := by
    rw [show U_S S f = ⋂ s ∈ S, {f' : E → E | f' s = f s} by ext; simp [U_S]]
    exact Set.Finite.isOpen_biInter (Finset.finite_toSet S) fun s _ => isOpen_setOf_apply_eq s _
  exact hopen.mem_nhds fun _ _ => rfl

section
omit [DiscreteTopology E]

/-- Every neighbourhood of `f` in the product topology on `E → E` contains a set `U_S S f` of maps
agreeing with `f` on a finite subset `S`. -/
lemma exists_U_S_subset_of_mem_nhds (f : E → E) {V : Set (E → E)}
    (hV : V ∈ nhds f) : ∃ S : Finset E, U_S S f ⊆ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, hI_fin, t, ht, hIt⟩ := hV
  refine ⟨hI_fin.toFinset, fun f' hf' => hIt fun i hi => ?_⟩
  rw [hf' i (hI_fin.mem_toFinset.mpr hi)]
  exact mem_of_mem_nhds (ht i)

/-- A map `g : X → (E → E)` into the product topology is continuous whenever its uncurrying
`X × E → E`, `(x, e) ↦ g x e`, is continuous. -/
lemma continuous_of_uncurry_continuous
    {X : Type*} [TopologicalSpace X] (g : X → (E → E))
    (hu : Continuous (fun p : X × E => g p.1 p.2)) :
    Continuous g :=
  continuous_pi_iff.mpr fun _ => hu.comp (continuous_id.prodMk continuous_const)

end

/-- The action `(f, e) ↦ f e` is locally constant on `(E → E) × E`: a witness
neighbourhood of `(f₀, e₀)` is `{f | f e₀ = f₀ e₀} ×ˢ {e₀}`. -/
lemma isLocallyConstant_action :
    IsLocallyConstant (fun p : (E → E) × E => p.1 p.2) := by
  intro s
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨f₀, e₀⟩ hmem
  refine ⟨({f : E → E | f e₀ = f₀ e₀} : Set (E → E)) ×ˢ ({e₀} : Set E), ?_, ?_, rfl, rfl⟩
  · rintro ⟨f, e⟩ ⟨hf₀, he₀⟩
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hf₀ he₀
    rw [Set.mem_preimage, he₀]
    dsimp only
    rw [hf₀]
    exact hmem
  · exact (isOpen_setOf_apply_eq e₀ _).prod (isOpen_discrete _)

/-- Continuity of inversion on `Equiv.Perm E`, viewed as a map into `E → E`. -/
lemma continuous_inv_toFun :
    Continuous (fun σ : Equiv.Perm E => ((σ⁻¹ : Equiv.Perm E) : E → E)) := by
  rw [continuous_pi_iff]
  intro e
  rw [continuous_iff_continuousAt]
  intro σ₀
  set a : E := (σ₀⁻¹ : Equiv.Perm E) e
  have h_comp : Continuous (fun σ : Equiv.Perm E => (σ : E → E) a) :=
    (continuous_apply a).comp continuous_induced_dom
  have hU_open : IsOpen {σ : Equiv.Perm E | (σ : E → E) a = e} :=
    h_comp.isOpen_preimage {e} (isOpen_discrete _)
  unfold ContinuousAt
  rw [show nhds ((σ₀⁻¹ : Equiv.Perm E) e) = pure ((σ₀⁻¹ : Equiv.Perm E) e) by
        rw [nhds_discrete], Filter.tendsto_pure]
  filter_upwards [hU_open.mem_nhds (σ₀.apply_symm_apply e)] with σ hσ
  rw [Equiv.Perm.inv_def]
  have : σ.symm (σ a) = a := σ.symm_apply_apply a
  rwa [hσ] at this

/-- **Stacks 0BMC**.
For every `f : E → E`, the family `{ U_S S f | S : Finset E }` of sets of maps agreeing with `f` on
a finite subset `S` is a basis of neighbourhoods of `f` in the product (equivalently, when `E` is
discrete, the compact-open) topology. -/
@[stacks 0BMC]
theorem mapTopology_nhds_hasBasis (f : E → E) :
    (nhds f).HasBasis (fun _ : Finset E => True) (fun S => U_S S f) :=
  ⟨fun _ => ⟨fun hV => (exists_U_S_subset_of_mem_nhds f hV).imp fun _ h => ⟨trivial, h⟩,
    fun ⟨S, _, hSV⟩ => Filter.mem_of_superset (U_S_mem_nhds S f) hSV⟩⟩

/-- **Stacks 0BMC**.
The action map `Map(E, E) × E → E`, `(f, e) ↦ f e`, is continuous when `E` carries the discrete
topology and `Map(E, E) = (E → E)` carries the product (= compact-open) topology. -/
@[stacks 0BMC]
theorem continuous_action :
    Continuous (fun p : (E → E) × E => p.1 p.2) :=
  isLocallyConstant_action.continuous

/-- **Stacks 0BMC**.
A map `g : X → (E → E)` is continuous if and only if the uncurried map `X × E → E`,
`(x, e) ↦ g x e`, is continuous. -/
@[stacks 0BMC]
theorem continuous_iff_uncurry_continuous
    {X : Type*} [TopologicalSpace X] (g : X → (E → E)) :
    Continuous g ↔ Continuous (fun p : X × E => g p.1 p.2) :=
  ⟨fun hg => continuous_action.comp (hg.prodMap continuous_id),
    continuous_of_uncurry_continuous g⟩

/-- **Stacks 0BMC**.
Composition `Map(E, E) × Map(E, E) → Map(E, E)`, `(f, g) ↦ f ∘ g`, is continuous. -/
@[stacks 0BMC]
theorem continuous_comp :
    Continuous (fun p : (E → E) × (E → E) => p.1 ∘ p.2) :=
  (continuous_iff_uncurry_continuous _).mpr <|
    continuous_action.comp (continuous_fst.fst.prodMk
      (continuous_action.comp (continuous_fst.snd.prodMk continuous_snd)))

/-- Multiplication on `Equiv.Perm E`, viewed as a map into `E → E`, is the
composition of the underlying functions, hence continuous. -/
lemma continuous_mul_toFun :
    Continuous
      (fun p : Equiv.Perm E × Equiv.Perm E => ((p.1 * p.2 : Equiv.Perm E) : E → E)) :=
  show Continuous ((fun q : (E → E) × (E → E) => q.1 ∘ q.2) ∘
      fun p : Equiv.Perm E × Equiv.Perm E =>
        (((p.1 : Equiv.Perm E) : E → E), ((p.2 : Equiv.Perm E) : E → E))) from
    continuous_comp.comp ((continuous_induced_dom.comp continuous_fst).prodMk
      (continuous_induced_dom.comp continuous_snd))

/-- **Stacks 0BMC**.
Inversion `σ ↦ σ⁻¹` on `Aut(E) = Equiv.Perm E` is continuous. -/
@[stacks 0BMC]
theorem continuous_perm_inv :
    Continuous (fun σ : Equiv.Perm E => σ⁻¹) :=
  continuous_induced_rng.mpr continuous_inv_toFun

/-- **Stacks 0BMC**.
`Aut(E) = Equiv.Perm E`, with the subspace topology induced from `Map(E, E)`, is a topological
group. -/
@[stacks 0BMC]
theorem isTopologicalGroup_aut :
    IsTopologicalGroup (Equiv.Perm E) where
  continuous_mul := continuous_induced_rng.mpr continuous_mul_toFun
  continuous_inv := continuous_perm_inv
