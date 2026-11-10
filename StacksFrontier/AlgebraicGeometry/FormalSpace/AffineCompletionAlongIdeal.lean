module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# Completion of an affine scheme along the closed subscheme of an ideal

Let `S` be a scheme contained in a big fppf site `B`, let `X = Spec A` be an affine scheme of
that site over `S` and let `Z ⊆ X` be the closed subscheme cut out by an ideal `I ⊆ A`. The
`n`-th infinitesimal neighbourhood of `Z` in `X` is `Spec (A ⧸ I ^ (n + 1))`, and the
completion of `X` along `Z` is the colimit of these neighbourhoods in the fppf sheaves over
`S`.

This file constructs that colimit and proves the first three assertions of **Stacks 0GXX**:
the completion is a weakly adic affine formal algebraic space; when `I` is finitely generated
it is the formal spectrum of the `I`-adic completion `A^∧` of `A` taken with its `I`-adic
topology; and it is then adic\*. The ring presenting it is `A^∧ = lim A ⧸ I ^ n`, carrying the
topology of the inverse limit of the discrete quotients.

## Main definitions

* `AlgebraicGeometry.FormalSpace.adicCompletionLimitTopology`: the inverse-limit topology on
  the `I`-adic completion of `A`, the quotients `A ⧸ I ^ n` being discrete.
* `AlgebraicGeometry.FormalSpace.quotientOver`: the spectrum of a quotient of `A`, as an
  affine object of the big fppf site over `S`.
* `AlgebraicGeometry.FormalSpace.infinitesimalNeighbourhoodDiagram`: the diagram of
  infinitesimal neighbourhoods `n ↦ Spec (A ⧸ I ^ (n + 1))` of the closed subscheme of `I`.
* `AlgebraicGeometry.FormalSpace.completionAlongIdeal`: the completion of `Spec A` along the
  closed subscheme of `I`, the fppf-sheaf colimit of that diagram.
* `AlgebraicGeometry.FormalSpace.adicCompletionQuotientSystem`: the `I`-adic completion of
  `A`, presented as a topological ring over `S` by the spectra of its discrete quotients.

## Main results

* `AlgebraicGeometry.FormalSpace.isWeaklyAdic_adicCompletion`: the `I`-adic completion of `A`
  with its inverse-limit topology is a weakly adic — in particular weakly admissible —
  topological ring.
* `AlgebraicGeometry.FormalSpace.completionAlongIdealIsoFormalSpectrum`: the completion of
  `Spec A` along the closed subscheme of `I` is the formal spectrum of the `I`-adic completion
  of `A`.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_completionAlongIdeal`: that
  completion is an affine formal algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.isWeaklyAdic_completionAlongIdeal`: **Stacks 0GXX (1)**, it
  is weakly adic.
* `AlgebraicGeometry.FormalSpace.isAdic_adicCompletion` and
  `AlgebraicGeometry.FormalSpace.map_pow_eq_adicCompletionKernel`: for a finitely generated
  `I`, the inverse-limit topology of `A^∧` is the adic topology of `I A^∧`, that ideal being a
  finitely generated ideal of definition.
* `AlgebraicGeometry.FormalSpace.isAdic_and_iso_formalSpectrum_adicCompletion`:
  **Stacks 0GXX (2)**, for a finitely generated `I` the completion is `Spf (A^∧)` for the
  `I`-adic completion `A^∧` of `A`.
* `AlgebraicGeometry.FormalSpace.isAdicStar_completionAlongIdeal`: **Stacks 0GXX (3)**, for a
  finitely generated `I` the completion is adic\*.

## Implementation notes

The completion is formed as a colimit over `ULift ℕ` rather than over `ℕ`, because the index
of a presentation of a formal algebraic space lives one universe above the schemes. The index
being countable, the set-theoretic condition of Stacks 0AIS comes from
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_colimit`, so no
representability hypothesis on the coproduct of the stages is needed.

The presenting ring is Mathlib's `AdicCompletion I A`, the ring of compatible families of
elements of the quotients `A ⧸ I ^ n`, topologized as a subspace of the product of those
discrete quotients. This is *not* in general the `I`-adic topology of that ring: the two agree
when `I` is finitely generated, which is the hypothesis of assertions (2) and (3) and is not
needed for assertion (1). What is needed for (1) is that the kernels `K n` of the
projections `A^∧ → A ⧸ I ^ n` are weak ideals of definition — an element of `K (n + 1)` has
its `m`-th coordinate in the image of `I` for every `m`, so its `m`-th power dies in
`A ⧸ I ^ m` — and that they are cofinal among all weak ideals of definition, since they are a
neighbourhood basis of zero. Cofinality enters as the finality of the induced functor on
index categories, which is how the colimit over `ℕ` is compared with the colimit over all
weak ideals of definition defining the formal spectrum.

Weak adicness of `A^∧` is witnessed by the ideal `I A^∧`: the closure of its `n`-th power is
exactly `K n`, because `K n` is closed, contains `I ^ n A^∧`, and every element of it is
approximated by elements of `I ^ n A^∧` along the tower of coordinates.

Assertion (4), that the completion is Noetherian when `X` is, is *not* proved here. It asks
for a presenting ring that is both adic and a Noetherian ring, and the Noetherianness of the
`I`-adic completion of a Noetherian ring is not available.

The site-smallness of each stage is not a hypothesis: `Spec (A ⧸ J)` is a closed subscheme of
`Spec A` for a quotient `A ⧸ J` of `A`, and `Spec (A^∧ ⧸ J)` for a weak ideal of definition
`J` is a closed subscheme of some `Spec (A ⧸ I ^ n)`, so all of them lie in the site as soon
as `Spec A` does.

## References

* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GXF](https://stacks.math.columbia.edu/tag/0GXF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### The inverse-limit topology on an adic completion -/

/-- The inverse-limit topology on the `I`-adic completion of `A`: the topology induced from
the product of the quotients `A ⧸ I ^ n`, each taken discrete. -/
@[instance_reducible]
public def adicCompletionLimitTopology (A : Type u) [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  let : ∀ n : ℕ, TopologicalSpace (A ⧸ (I ^ n • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  TopologicalSpace.induced Subtype.val inferInstance

section Ring

variable {A : Type u} [CommRing A]

private theorem evalₐ_eq_zero_iff (I : Ideal A) (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ I n x = 0 ↔ x.val n = 0 := by
  let e := Ideal.quotientEquivAlgOfEq A
    (show (I ^ n • (⊤ : Ideal A)) = I ^ n by ext a; simp)
  change e (x.val n) = 0 ↔ x.val n = 0
  exact map_eq_zero_iff e e.injective

private theorem continuous_val_apply (I : Ideal A) (n : ℕ) :
    letI : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    Continuous fun x : AdicCompletion I A ↦ x.val n := by
  let : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  exact (continuous_apply n).comp continuous_subtype_val

private theorem hasBasis_coordinates (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    (nhds (0 : AdicCompletion I A)).HasBasis (fun s : Set ℕ ↦ s.Finite)
      (fun s ↦ {y : AdicCompletion I A | ∀ i ∈ s, y.val i = 0}) := by
  let : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let : ∀ k : ℕ, DiscreteTopology (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⟨rfl⟩
  let : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  rw [nhds_induced, nhds_pi]
  simp only [nhds_discrete]
  exact (Filter.hasBasis_pi_pure (fun _ ↦ (0 : A ⧸ _))).comap Subtype.val

/-- The kernel of the `n`-th projection of the `I`-adic completion of `A`, an ideal with
quotient `A ⧸ I ^ n`. -/
public def adicCompletionKernel (I : Ideal A) (n : ℕ) : Ideal (AdicCompletion I A) :=
  RingHom.ker (AdicCompletion.evalₐ I n).toRingHom

private theorem mem_adicCompletionKernel (I : Ideal A) (n : ℕ) (x : AdicCompletion I A) :
    x ∈ adicCompletionKernel I n ↔ x.val n = 0 := by
  rw [adicCompletionKernel, RingHom.mem_ker]
  exact evalₐ_eq_zero_iff I n x

/-- The kernels of the projections of the `I`-adic completion of `A` decrease with the
index. -/
public theorem adicCompletionKernel_antitone (I : Ideal A) :
    Antitone (adicCompletionKernel I) := by
  intro n m hnm x hx
  rw [mem_adicCompletionKernel]
  have hm := (mem_adicCompletionKernel I m x).mp hx
  have h := AdicCompletion.transitionMap_comp_eval_apply I A hnm x
  rw [hm, map_zero] at h
  exact h.symm

/-- The kernel of the `n`-th projection is the preimage of `0` under the `n`-th coordinate. -/
private theorem coe_adicCompletionKernel_eq_preimage (I : Ideal A) (n : ℕ) :
    (adicCompletionKernel I n : Set (AdicCompletion I A)) =
      (fun x : AdicCompletion I A ↦ x.val n) ⁻¹' {0} := by
  ext x
  exact (mem_adicCompletionKernel I n x).trans Set.mem_singleton_iff.symm

private theorem isOpen_adicCompletionKernel (I : Ideal A) (n : ℕ) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    IsOpen (adicCompletionKernel I n : Set (AdicCompletion I A)) := by
  let : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let : ∀ k : ℕ, DiscreteTopology (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⟨rfl⟩
  let : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  rw [coe_adicCompletionKernel_eq_preimage]
  exact (continuous_val_apply I n).isOpen_preimage _ (isOpen_discrete _)

private theorem isClosed_adicCompletionKernel (I : Ideal A) (n : ℕ) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    IsClosed (adicCompletionKernel I n : Set (AdicCompletion I A)) := by
  let : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let : ∀ k : ℕ, DiscreteTopology (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⟨rfl⟩
  let : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  rw [coe_adicCompletionKernel_eq_preimage]
  exact (isClosed_discrete _).preimage (continuous_val_apply I n)

private theorem hasBasis_adicCompletionKernel (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    (nhds (0 : AdicCompletion I A)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (adicCompletionKernel I n : Set (AdicCompletion I A))) := by
  classical
  let _ : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  refine (hasBasis_coordinates I).to_hasBasis (fun s hs ↦ ?_) (fun n _ ↦ ?_)
  · refine ⟨hs.toFinset.sup id, trivial, fun x hx i hi ↦ ?_⟩
    exact (mem_adicCompletionKernel I i x).mp (adicCompletionKernel_antitone I
      (Finset.le_sup (f := fun j : ℕ ↦ j) (hs.mem_toFinset.mpr hi)) hx)
  · exact ⟨{n}, Set.finite_singleton n,
      fun x hx ↦ (mem_adicCompletionKernel I n x).mpr (hx n rfl)⟩

/-- Every open ideal of the `I`-adic completion of `A` contains the kernel of one of its
projections: those kernels are a neighbourhood basis of zero. -/
public theorem exists_adicCompletionKernel_le (I : Ideal A) (J : Ideal (AdicCompletion I A))
    (hJ : @IsOpen (AdicCompletion I A) (adicCompletionLimitTopology A I)
      (J : Set (AdicCompletion I A))) :
    ∃ n : ℕ, adicCompletionKernel I n ≤ J := by
  let : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  obtain ⟨n, -, hn⟩ := (hasBasis_adicCompletionKernel I).mem_iff.mp (hJ.mem_nhds (by simp))
  exact ⟨n, hn⟩

/-- The `I`-adic completion of `A` is a topological ring for its inverse-limit topology:
addition, multiplication and negation are computed coordinatewise in the discrete
quotients. -/
public theorem isTopologicalRing_adicCompletion (A : Type u) [CommRing A] (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    IsTopologicalRing (AdicCompletion I A) := by
  let : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let : ∀ k : ℕ, DiscreteTopology (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⟨rfl⟩
  let : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  refine
    { toIsTopologicalSemiring :=
        { toContinuousAdd := ⟨?_⟩
          toContinuousMul := ⟨?_⟩ }
      toContinuousNeg := ⟨?_⟩ }
  · refine continuous_induced_rng.2 (continuous_pi fun n ↦ ?_)
    exact continuous_add.comp
      (((continuous_val_apply I n).comp continuous_fst).prodMk
        ((continuous_val_apply I n).comp continuous_snd))
  · refine continuous_induced_rng.2 (continuous_pi fun n ↦ ?_)
    exact continuous_mul.comp
      (((continuous_val_apply I n).comp continuous_fst).prodMk
        ((continuous_val_apply I n).comp continuous_snd))
  · refine continuous_induced_rng.2 (continuous_pi fun n ↦ ?_)
    exact continuous_neg.comp (continuous_val_apply I n)

attribute [local instance] isTopologicalRing_adicCompletion

/-- The inverse-limit topology of the `I`-adic completion of `A` is linear: the finite
intersections of the kernels of its projections are open ideals forming a neighbourhood basis
of zero. -/
public theorem isLinearTopology_adicCompletion (A : Type u) [CommRing A] (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    IsLinearTopology (AdicCompletion I A) (AdicCompletion I A) := by
  classical
  let : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  let cylinder (s : Set ℕ) : Ideal (AdicCompletion I A) :=
    ⨅ n : s, adicCompletionKernel I n.1
  have hbasis : (nhds (0 : AdicCompletion I A)).HasBasis (fun s : Set ℕ ↦ s.Finite)
      (fun s ↦ (cylinder s : Set (AdicCompletion I A))) := by
    refine (hasBasis_coordinates I).congr (fun _ ↦ Iff.rfl) (fun s _ ↦ ?_)
    ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, cylinder, Ideal.mem_iInf]
    constructor
    · exact fun hx i ↦ (mem_adicCompletionKernel I i.1 x).mpr (hx i.1 i.2)
    · exact fun hx i hi ↦ (mem_adicCompletionKernel I i x).mp (hx ⟨i, hi⟩)
  exact IsLinearTopology.mk_of_hasBasis' (AdicCompletion I A)
    (p := fun s : Set ℕ ↦ s.Finite) (s := cylinder) hbasis
    (fun J r _ hm ↦ Ideal.mul_mem_left J r hm)

attribute [local instance] isLinearTopology_adicCompletion

/-- An element of `A` whose class in `A ⧸ I ^ k` maps to zero in `A ⧸ I ^ q` lies in `I ^ q`. -/
private theorem mem_pow_of_transitionMap_eq_zero (I : Ideal A) {q k : ℕ} (hqk : q ≤ k) (a : A)
    (h : AdicCompletion.transitionMap I A hqk (Submodule.Quotient.mk a) = 0) : a ∈ I ^ q := by
  have ha_zero : a ∈ I ^ q • (⊤ : Submodule A A) := by
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    simpa [AdicCompletion.transitionMap, Submodule.factorPow] using h
  simpa [Ideal.mul_top] using ha_zero

private theorem val_pow_eq_zero (I : Ideal A) (q k : ℕ) (x : AdicCompletion I A)
    (hx : x.val q = 0) (m : ℕ) (hm : 1 ≤ m) (hkm : k ≤ q * m) : (x ^ m).val k = 0 := by
  have hvalpow : (x ^ m).val k = x.val k ^ m := rfl
  by_cases hkq : k ≤ q
  · have htransition := AdicCompletion.transitionMap_comp_eval_apply I A hkq x
    rw [hx, map_zero] at htransition
    rw [hvalpow, htransition.symm]
    exact zero_pow (by omega)
  · have hqk : q ≤ k := by omega
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
      (I ^ k • (⊤ : Submodule A A)) (x.val k)
    have htransition : AdicCompletion.transitionMap I A hqk (x.val k) = 0 := by
      rw [AdicCompletion.transitionMap_comp_eval_apply I A hqk x, hx]
    have haI : a ∈ I ^ q := mem_pow_of_transitionMap_eq_zero I hqk a (by rwa [ha])
    have hamk : a ^ m ∈ I ^ k :=
      Ideal.pow_le_pow_right hkm (by simpa [pow_mul] using Ideal.pow_mem_pow haI m)
    have hpow : (Submodule.Quotient.mk a : A ⧸ (I ^ k • (⊤ : Submodule A A))) ^ m = 0 :=
      (Submodule.Quotient.mk_eq_zero _ (x := a ^ m)).mpr (by simpa [Ideal.mul_top] using hamk)
    rwa [hvalpow, ← ha]

/-- The kernel of the `(n + 1)`-st projection of the `I`-adic completion of `A` is a weak
ideal of definition: it is open, and the `m`-th coordinate of one of its elements lies in the
image of `I`, hence has vanishing `m`-th power in `A ⧸ I ^ m`. -/
public theorem isWeakIdealOfDefinition_adicCompletionKernel (I : Ideal A) (n : ℕ) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    TopologicalRing.IsWeakIdealOfDefinition (adicCompletionKernel I (n + 1)) := by
  classical
  let _ : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  refine ⟨isOpen_adicCompletionKernel I (n + 1), fun x hx ↦ ?_⟩
  have hxq : x.val (n + 1) = 0 := (mem_adicCompletionKernel I (n + 1) x).mp hx
  rw [IsTopologicallyNilpotent, (hasBasis_coordinates I).tendsto_right_iff]
  intro s hs
  refine Filter.eventually_atTop.2 ⟨max 1 (hs.toFinset.sup id), fun m hm i hi ↦ ?_⟩
  have hm₁ : 1 ≤ m := le_trans (le_max_left _ _) hm
  have hik : i ≤ hs.toFinset.sup id :=
    Finset.le_sup (f := fun j : ℕ ↦ j) (hs.mem_toFinset.mpr hi)
  have him : i ≤ (n + 1) * m :=
    le_trans (le_trans hik (le_trans (le_max_right 1 _) hm))
      (by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right m (Nat.succ_pos n))
  exact val_pow_eq_zero I (n + 1) i x hxq m hm₁ him

/-- The `n`-th power of the ideal generated by the image of `I` in the `I`-adic completion of
`A` is contained in the kernel of the `n`-th projection. -/
public theorem map_pow_le_adicCompletionKernel (I : Ideal A) (n : ℕ) :
    (Ideal.map (algebraMap A (AdicCompletion I A)) I) ^ n ≤ adicCompletionKernel I n := by
  rw [← Ideal.map_pow]
  refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
  rw [Ideal.mem_comap, adicCompletionKernel, RingHom.mem_ker]
  change AdicCompletion.evalₐ I n (AdicCompletion.of I A a) = 0
  rw [AdicCompletion.evalₐ_of]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- The kernel of the `n`-th projection of the `I`-adic completion of `A` is the closure of
the `n`-th power of the ideal generated by the image of `I`. -/
@[ega "0 7.2.12" "partial"]
public theorem adicCompletionKernel_eq_closure_pow (A : Type u) [CommRing A] (I : Ideal A)
    (n : ℕ) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    (adicCompletionKernel I n : Set (AdicCompletion I A)) =
      closure (((Ideal.map (algebraMap A (AdicCompletion I A)) I) ^ n :
        Ideal (AdicCompletion I A)) : Set (AdicCompletion I A)) := by
  classical
  let _ : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let _ : ∀ k : ℕ, DiscreteTopology (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⟨rfl⟩
  let _ : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  ext x
  constructor
  · intro hx
    have hxraw : x.val n = 0 := (mem_adicCompletionKernel I n x).mp hx
    have hb : (nhds x).HasBasis (fun s : Set ℕ ↦ s.Finite)
        (fun s ↦ {y : AdicCompletion I A | ∀ i ∈ s, y.val i = x.val i}) := by
      rw [nhds_induced, nhds_pi]
      simp only [nhds_discrete]
      exact (Filter.hasBasis_pi_pure x.val).comap Subtype.val
    rw [mem_closure_iff_nhds_basis hb]
    intro s hs
    have hnm : n ≤ max n (hs.toFinset.sup id) := le_max_left _ _
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
      (I ^ max n (hs.toFinset.sup id) • (⊤ : Submodule A A))
      (x.val (max n (hs.toFinset.sup id)))
    have haI : a ∈ I ^ n := mem_pow_of_transitionMap_eq_zero I hnm a (by
      rw [ha, AdicCompletion.transitionMap_comp_eval_apply I A hnm x, hxraw])
    refine ⟨AdicCompletion.of I A a, ?_, fun i hi ↦ ?_⟩
    · rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) haI
    · have hym : (AdicCompletion.of I A a).val (max n (hs.toFinset.sup id)) =
          x.val (max n (hs.toFinset.sup id)) := by
        change (AdicCompletion.eval I A (max n (hs.toFinset.sup id)) ∘ₗ
          AdicCompletion.of I A) a = _
        rw [AdicCompletion.eval_comp_of]
        simpa using ha
      have him : i ≤ max n (hs.toFinset.sup id) :=
        le_trans (Finset.le_sup (f := fun j : ℕ ↦ j) (hs.mem_toFinset.mpr hi))
          (Nat.le_max_right n _)
      calc (AdicCompletion.of I A a).val i
          = AdicCompletion.transitionMap I A him
            ((AdicCompletion.of I A a).val (max n (hs.toFinset.sup id))) :=
            (AdicCompletion.transitionMap_comp_eval_apply I A him _).symm
        _ = AdicCompletion.transitionMap I A him (x.val (max n (hs.toFinset.sup id))) := by
            rw [hym]
        _ = x.val i := AdicCompletion.transitionMap_comp_eval_apply I A him x
  · exact fun hx ↦ (isClosed_adicCompletionKernel I n).closure_subset_iff.mpr
      (SetLike.coe_subset_coe.mpr (map_pow_le_adicCompletionKernel I n)) hx

private theorem isWeaklyPreAdic_adicCompletion (A : Type u) [CommRing A] (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    TopologicalRing.IsWeaklyPreAdic (AdicCompletion I A) := by
  let _ : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  have hcl (n : ℕ) : (((Ideal.map (algebraMap A (AdicCompletion I A)) I)
      ^ n).topologicalClosure : Set (AdicCompletion I A)) =
      (adicCompletionKernel I n : Set (AdicCompletion I A)) := by
    rw [Submodule.topologicalClosure_coe]
    exact (adicCompletionKernel_eq_closure_pow A I n).symm
  refine ⟨Ideal.map (algebraMap A (AdicCompletion I A)) I, fun n ↦ ?_, ?_⟩
  · rw [hcl n]
    exact isOpen_adicCompletionKernel I n
  · exact (hasBasis_adicCompletionKernel I).congr (fun _ ↦ Iff.rfl) (fun n _ ↦ (hcl n).symm)

attribute [local instance] isWeaklyPreAdic_adicCompletion

private theorem t2Space_adicCompletion (A : Type u) [CommRing A] (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    T2Space (AdicCompletion I A) := by
  let _ : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let _ : ∀ k : ℕ, DiscreteTopology (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⟨rfl⟩
  let _ : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  exact T2Space.of_injective_continuous Subtype.val_injective continuous_subtype_val

attribute [local instance] t2Space_adicCompletion

private theorem completeSpace_adicCompletion (A : Type u) [CommRing A] (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    @CompleteSpace (AdicCompletion I A)
      (IsTopologicalAddGroup.rightUniformSpace (AdicCompletion I A)) := by
  let : ∀ k : ℕ, TopologicalSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let : ∀ k : ℕ, DiscreteTopology (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⟨rfl⟩
  let : ∀ k : ℕ, UniformSpace (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun _ ↦ ⊥
  let : ∀ k : ℕ, IsUniformAddGroup (A ⧸ (I ^ k • (⊤ : Submodule A A))) := fun k ↦
    ⟨DiscreteUniformity.uniformContinuous
      (X := (A ⧸ (I ^ k • (⊤ : Submodule A A))) × (A ⧸ (I ^ k • (⊤ : Submodule A A))))
      (fun p ↦ p.1 - p.2)⟩
  let : UniformSpace (AdicCompletion I A) :=
    UniformSpace.comap (Subtype.val : AdicCompletion I A →
      ∀ k : ℕ, A ⧸ (I ^ k • (⊤ : Submodule A A))) inferInstance
  let : IsUniformAddGroup (AdicCompletion I A) := ⟨by
    refine uniformContinuous_comap' ?_
    exact uniformContinuous_sub.comp
      ((uniformContinuous_subtype_val.comp uniformContinuous_fst).prodMk
        (uniformContinuous_subtype_val.comp uniformContinuous_snd))⟩
  have hclosed : IsClosed {x : ∀ k : ℕ, A ⧸ (I ^ k • (⊤ : Submodule A A)) |
      ∀ (m k : ℕ) (h : m ≤ k), AdicCompletion.transitionMap I A h (x k) = x m} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun m ↦ isClosed_iInter fun k ↦ isClosed_iInter fun h ↦
      isClosed_eq ((continuous_of_discreteTopology
        (f := AdicCompletion.transitionMap I A h)).comp (continuous_apply k))
        (continuous_apply m)
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact hclosed.completeSpace_coe

/-- **Stacks 0GXX, ring input.** The `I`-adic completion of `A`, with the topology of the
inverse limit of the discrete quotients `A ⧸ I ^ n`, is a weakly adic topological ring: the
closures of the powers of the ideal generated by `I` are open and form a neighbourhood basis
of zero, and the ring is complete and separated. -/
@[ega "0 7.2.1" "special case"]
public theorem isWeaklyAdic_adicCompletion (A : Type u) [CommRing A] (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    TopologicalRing.IsWeaklyAdic (AdicCompletion I A) := by
  let _ : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  exact TopologicalRing.IsWeaklyAdic.mk (completeSpace_adicCompletion A I)

/-- The `I`-adic completion of `A`, with its inverse-limit topology, is weakly admissible: the
kernel of the projection to `A ⧸ I` is a weak ideal of definition, and the ring is complete
and separated. -/
public theorem isWeaklyAdmissible_adicCompletion (A : Type u) [CommRing A] (I : Ideal A) :
    letI : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
    TopologicalRing.IsWeaklyAdmissible (AdicCompletion I A) := by
  let _ : TopologicalSpace (AdicCompletion I A) := adicCompletionLimitTopology A I
  exact ⟨⟨adicCompletionKernel I 1, isWeakIdealOfDefinition_adicCompletionKernel I 0⟩,
    completeSpace_adicCompletion A I, t2Space_adicCompletion A I⟩

end Ring

section Geometry

attribute [local instance] sheaf_hasColimits

/-! ### The infinitesimal neighbourhoods of the closed subscheme of an ideal -/

/-- A quotient of `A` has its spectrum in the big fppf site as soon as `Spec A` does: the
quotient map makes it a closed subscheme of `Spec A`. -/
public theorem contains_spec_quotient (B : BigFppfSite.{u}) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (J : Ideal A) : B.Contains (Spec (.of (A ⧸ J))) := by
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact Scheme.size_lt_of_isClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) hA

/-- The spectrum of a quotient `A ⧸ J`, as an affine object of the big fppf site over `S`; its
structure morphism is the one induced by a chosen morphism `Spec A ⟶ S`. -/
public def quotientOver (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (J : Ideal A) : BigAffineFppf B S hS :=
  ⟨Over.mk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ f) :
      B.obj (contains_spec_quotient B hA J) ⟶ B.obj hS), by
    change IsAffine (Spec (.of (A ⧸ J)))
    infer_instance⟩

/-- The closed immersion `Spec (A ⧸ K) ⟶ Spec (A ⧸ J)` over `S` attached to an inclusion
`J ≤ K` of ideals of `A`. -/
public def quotientOverTransition (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {J K : Ideal A} (h : J ≤ K) :
    quotientOver B S hS f hA K ⟶ quotientOver B S hS f hA J :=
  ObjectProperty.homMk <| Over.homMk
    (U := (quotientOver B S hS f hA K).1) (V := (quotientOver B S hS f hA J).1)
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ f) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ f
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        Ideal.Quotient.factor_comp_mk])

/-- The transition attached to an equality of ideals is the identity. -/
public theorem quotientOverTransition_id (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (J : Ideal A) (h : J ≤ J) :
    quotientOverTransition B S hS f hA h = 𝟙 (quotientOver B S hS f hA J) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) = 𝟙 _
  simp [Ideal.Quotient.factor_eq]

/-- The transitions attached to a chain `J ≤ K ≤ L` of ideals compose to the one attached to
`J ≤ L`. -/
public theorem quotientOverTransition_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) {J K L : Ideal A} (h₁ : J ≤ K) (h₂ : K ≤ L) :
    quotientOverTransition B S hS f hA h₂ ≫ quotientOverTransition B S hS f hA h₁ =
      quotientOverTransition B S hS f hA (h₁.trans h₂) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h₂)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h₁)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h₁.trans h₂)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp h₁ h₂]

/-- The diagram of infinitesimal neighbourhoods of the closed subscheme of `I ⊆ A`: the `n`-th
stage is `Spec (A ⧸ I ^ (n + 1))` and the transitions are the canonical closed immersions. -/
public def infinitesimalNeighbourhoodDiagram (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    ULift.{u + 1} ℕ ⥤ BigAffineFppf B S hS where
  obj n := quotientOver B S hS f hA (I ^ (n.down + 1))
  map {n m} g := quotientOverTransition B S hS f hA
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (show n ≤ m from leOfHom g) 1))
  map_id _ := quotientOverTransition_id B S hS f hA _ _
  map_comp _ _ := (quotientOverTransition_comp B S hS f hA _ _).symm

/-- The completion of `Spec A` along the closed subscheme of `I ⊆ A`: the colimit, in fppf
sheaves over `S`, of the infinitesimal neighbourhoods `Spec (A ⧸ I ^ (n + 1))`. -/
public def completionAlongIdeal (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (I : Ideal A) : FppfSheaf B S hS :=
  colimit (infinitesimalNeighbourhoodDiagram B S hS f hA I ⋙
    BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))

private theorem isThickening_infinitesimalNeighbourhood_map (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) {n m : ULift.{u + 1} ℕ} (g : n ⟶ m) :
    Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map
      ((infinitesimalNeighbourhoodDiagram B S hS f hA I).map g)) := by
  have hd : n ≤ m := leOfHom g
  have hle : I ^ (m.down + 1) ≤ I ^ (n.down + 1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right hd 1)
  let q := Ideal.Quotient.factor hle
  have hker : RingHom.ker q ≤ nilradical (A ⧸ I ^ (m.down + 1)) := by
    rw [Ideal.Quotient.factor_ker hle]
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [Ideal.mem_comap, mem_nilradical]
    refine ⟨m.down + 1, Ideal.Quotient.eq_zero_iff_mem.mpr ?_⟩
    exact Ideal.pow_le_pow_right
      (Nat.le_mul_of_pos_left (m.down + 1) (Nat.succ_pos n.down))
      (by simpa [← pow_mul] using Ideal.pow_mem_pow hx (m.down + 1))
  have hqSurj : Function.Surjective q := Ideal.Quotient.factor_surjective hle
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom q)).base := by
    change Function.Surjective (PrimeSpectrum.comap q)
    intro p
    refine ⟨⟨p.asIdeal.map q, Ideal.map_isPrime_of_surjective hqSurj
      (hker.trans (nilradical_le_prime p.asIdeal))⟩, ?_⟩
    apply PrimeSpectrum.ext
    change (p.asIdeal.map q).comap q = p.asIdeal
    rw [Ideal.comap_map_of_surjective q hqSurj p.asIdeal, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr (hker.trans (nilradical_le_prime p.asIdeal))]
  change Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom q))
  exact ⟨IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q) hqSurj, hsurj⟩

/-- The completion of `Spec A` along the closed subscheme of an ideal satisfies the
set-theoretic condition of Stacks 0AIS, the colimit defining it being countable. -/
public theorem satisfiesSetTheoreticCondition_completionAlongIdeal (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    SatisfiesSetTheoreticCondition B S hS (completionAlongIdeal B S hS f hA I) :=
  satisfiesSetTheoreticCondition_of_countable_colimit B S hS
    (infinitesimalNeighbourhoodDiagram B S hS f hA I)
    (fun _ _ g ↦ isThickening_infinitesimalNeighbourhood_map B S hS f hA I g)
    _ ⟨Iso.refl _⟩

/-- **The completion of `Spec A` along the closed subscheme of an ideal is countably indexed.**
It is by construction the colimit of the infinitesimal neighbourhoods `Spec (A ⧸ I ^ (n + 1))`
indexed by `ULift ℕ`, so restricting that diagram along `ULift.up` — which is cofinal, being a
bijection — presents it over `ℕ`, which is what `IsCountablyIndexed` asks for. -/
public theorem isCountablyIndexed_completionAlongIdeal (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    IsCountablyIndexed B S hS (completionAlongIdeal B S hS f hA I) := by
  let hu : Monotone (ULift.up.{u + 1, 0} : ℕ → ULift.{u + 1, 0} ℕ) := fun _ _ h => h
  let e := hu.functor
  have : Functor.Final e := hu.final_functor_iff.mpr fun n => ⟨n.down, le_rfl⟩
  exact ⟨e ⋙ infinitesimalNeighbourhoodDiagram B S hS f hA I,
    fun ⦃_ _⦄ g ↦ isThickening_infinitesimalNeighbourhood_map B S hS f hA I (e.map g),
    ⟨(Functor.Final.colimitIso e (infinitesimalNeighbourhoodDiagram B S hS f hA I ⋙
      BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))).symm⟩⟩

end Geometry

/-! ### Comparison with the formal spectrum of the adic completion -/

section Comparison

attribute [local instance] adicCompletionLimitTopology isTopologicalRing_adicCompletion
  isLinearTopology_adicCompletion

variable {A : Type u} [CommRing A]

private theorem factor_evalₐ (I : Ideal A) {n m : ℕ} (hnm : n ≤ m) (x : AdicCompletion I A) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hnm) (AdicCompletion.evalₐ I m x) =
      AdicCompletion.evalₐ I n x := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (I ^ m • (⊤ : Submodule A A)) (x.val m)
  have hn : x.val n = Submodule.Quotient.mk a := by
    have h := AdicCompletion.transitionMap_comp_eval_apply I A hnm x
    rw [← h, ← ha]
    exact Submodule.factor_mk (Submodule.smul_mono (Ideal.pow_le_pow_right hnm) le_rfl) a
  rw [AdicCompletion.evalₐ_eq_mk I m x a ha.symm, AdicCompletion.evalₐ_eq_mk I n x a hn,
    Ideal.Quotient.factor_mk]

/-- The quotient of the `I`-adic completion of `A` by the kernel of its `n`-th projection is
the quotient `A ⧸ I ^ n`. -/
public def adicCompletionQuotientEquiv (I : Ideal A) (n : ℕ) :
    AdicCompletion I A ⧸ adicCompletionKernel I n ≃+* A ⧸ I ^ n :=
  RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ I n)

private theorem adicCompletionQuotientEquiv_mk (I : Ideal A) (n : ℕ)
    (x : AdicCompletion I A) :
    adicCompletionQuotientEquiv I n (Ideal.Quotient.mk _ x) = AdicCompletion.evalₐ I n x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk (AdicCompletion.surjective_evalₐ I n) x

private theorem adicCompletionQuotientEquiv_comp_mk_comp_algebraMap (I : Ideal A) (n : ℕ) :
    ((adicCompletionQuotientEquiv I n).toRingHom.comp
        (Ideal.Quotient.mk (adicCompletionKernel I n))).comp
      (algebraMap A (AdicCompletion I A)) = Ideal.Quotient.mk (I ^ n) := by
  refine RingHom.ext fun a ↦ ?_
  change adicCompletionQuotientEquiv I n
    (Ideal.Quotient.mk _ (algebraMap A (AdicCompletion I A) a)) = _
  rw [adicCompletionQuotientEquiv_mk]
  exact AdicCompletion.evalₐ_of I n a

/-- The `I`-adic completion of `A`, with its inverse-limit topology, presented as a
topological ring over `S`: the spectrum of each of its quotients by a weak ideal of definition
lies in the site and carries the structure morphism induced by `Spec A ⟶ S`. -/
public def adicCompletionQuotientSystem (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    QuotientSystem B S hS (AdicCompletion I A) :=
  { inSite := by
      intro J
      obtain ⟨n, hker⟩ := exists_adicCompletionKernel_le I J.1 J.2.1
      let g : A ⧸ I ^ n →+* AdicCompletion I A ⧸ J.1 :=
        Ideal.Quotient.lift (I ^ n)
          ((Ideal.Quotient.mk J.1).comp (algebraMap A (AdicCompletion I A))) (by
            intro a ha
            refine Ideal.Quotient.eq_zero_iff_mem.mpr (hker ?_)
            exact map_pow_le_adicCompletionKernel I n
              (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha))
      have hgsurj : Function.Surjective g := by
        intro z
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n c)
        refine ⟨Ideal.Quotient.mk (I ^ n) a, ?_⟩
        rw [Ideal.Quotient.lift_mk, ← hc]
        refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 ?_
        have hof : AdicCompletion.evalₐ I n (algebraMap A (AdicCompletion I A) a) =
            Ideal.Quotient.mk (I ^ n) a := by
          change AdicCompletion.evalₐ I n (AdicCompletion.of I A a) = _
          exact AdicCompletion.evalₐ_of I n a
        have hdiff : c - algebraMap A (AdicCompletion I A) a ∈ J.1 := by
          refine hker (RingHom.mem_ker.mpr ?_)
          change AdicCompletion.evalₐ I n (c - algebraMap A (AdicCompletion I A) a) = 0
          rw [map_sub, hof, ← ha, sub_self]
        simpa [neg_sub] using J.1.neg_mem hdiff
      let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) :=
        IsClosedImmersion.spec_of_surjective _ hgsurj
      exact Scheme.size_lt_of_isClosedImmersion (Spec.map (CommRingCat.ofHom g))
        (contains_spec_quotient B hA (I ^ n))
    overS := fun J ↦
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫ f
    compatible := by
      intro J L h
      have hstage : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L.1)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
      exact congrArg (fun k ↦ k ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫ f) hstage }

/-- The kernels of the projections of the `I`-adic completion of `A`, as a monotone map from
`ULift ℕ` to the weak ideals of definition ordered by reverse inclusion. -/
public def adicCompletionKernelIndex {A : Type u} [CommRing A] (I : Ideal A) :
    ULift.{u + 1} ℕ →o WeakIdeals (AdicCompletion I A) :=
  { toFun := fun n ↦ ⟨adicCompletionKernel I (n.down + 1),
      isWeakIdealOfDefinition_adicCompletionKernel I n.down⟩
    monotone' := fun _ _ h ↦
      adicCompletionKernel_antitone I (Nat.add_le_add_right (show _ ≤ _ from h) 1) }

/-- The kernels of the projections are cofinal among the weak ideals of definition of the
`I`-adic completion of `A`, so the functor they induce on index categories is final. -/
public theorem final_adicCompletionKernelIndex {A : Type u} [CommRing A] (I : Ideal A) :
    (adicCompletionKernelIndex I).monotone.functor.Final := by
  refine (adicCompletionKernelIndex I).monotone.final_functor_iff.mpr fun J ↦ ?_
  obtain ⟨n, hn⟩ := exists_adicCompletionKernel_le I J.1 J.2.1
  exact ⟨ULift.up n, (adicCompletionKernel_antitone I (Nat.le_succ n)).trans hn⟩

attribute [local instance] sheaf_hasColimits

/-- The `n`-th infinitesimal neighbourhood of the closed subscheme of `I` is the quotient
spectrum of the `I`-adic completion of `A` by the kernel of its `(n + 1)`-st projection. -/
public def kernelStageIso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (I : Ideal A) (n : ULift.{u + 1} ℕ) :
    (infinitesimalNeighbourhoodDiagram B S hS f hA I).obj n ≅
      ((adicCompletionKernelIndex I).monotone.functor ⋙
        (adicCompletionQuotientSystem B S hS f hA I).diagram).obj n :=
  ObjectProperty.isoMk _ <| Over.isoMk
    (ObjectProperty.isoMk _ (Scheme.Spec.mapIso
      (adicCompletionQuotientEquiv I (n.down + 1)).toCommRingCatIso.op)) (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom
        (adicCompletionQuotientEquiv I (n.down + 1)).toRingHom) ≫
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (adicCompletionKernel I (n.down + 1)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion I A))) ≫ f) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.down + 1)))) ≫ f
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k) ≫ f)
      (adicCompletionQuotientEquiv_comp_mk_comp_algebraMap I (n.down + 1)))

/-- The identifications of the infinitesimal neighbourhoods with the quotient spectra of the
`I`-adic completion commute with the transition morphisms. -/
public theorem kernelStageIso_naturality (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) {n m : ULift.{u + 1} ℕ} (g : n ⟶ m) :
    (infinitesimalNeighbourhoodDiagram B S hS f hA I).map g ≫
        (kernelStageIso B S hS f hA I m).hom =
      (kernelStageIso B S hS f hA I n).hom ≫
        ((adicCompletionKernelIndex I).monotone.functor ⋙
          (adicCompletionQuotientSystem B S hS f hA I).diagram).map g := by
  have hd : n ≤ m := leOfHom g
  have hle : I ^ (m.down + 1) ≤ I ^ (n.down + 1) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_right hd 1)
  have hK : adicCompletionKernel I (m.down + 1) ≤ adicCompletionKernel I (n.down + 1) :=
    adicCompletionKernel_antitone I (Nat.add_le_add_right hd 1)
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle)) ≫
      Spec.map (CommRingCat.ofHom
        (adicCompletionQuotientEquiv I (m.down + 1)).toRingHom) =
    Spec.map (CommRingCat.ofHom
        (adicCompletionQuotientEquiv I (n.down + 1)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hK))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  refine RingHom.ext fun y ↦ ?_
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  change Ideal.Quotient.factor hle (adicCompletionQuotientEquiv I (m.down + 1)
      (Ideal.Quotient.mk _ c)) =
    adicCompletionQuotientEquiv I (n.down + 1)
      (Ideal.Quotient.factor hK (Ideal.Quotient.mk _ c))
  rw [adicCompletionQuotientEquiv_mk, Ideal.Quotient.factor_mk,
    adicCompletionQuotientEquiv_mk]
  exact factor_evalₐ I (Nat.add_le_add_right hd 1) c

/-- The diagram of infinitesimal neighbourhoods of the closed subscheme of `I` is the diagram
of quotient spectra of the `I`-adic completion of `A` along the kernels of its projections. -/
public def infinitesimalNeighbourhoodDiagramIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    infinitesimalNeighbourhoodDiagram B S hS f hA I ≅
      (adicCompletionKernelIndex I).monotone.functor ⋙
        (adicCompletionQuotientSystem B S hS f hA I).diagram :=
  NatIso.ofComponents (kernelStageIso B S hS f hA I)
    (fun g ↦ kernelStageIso_naturality B S hS f hA I g)

/-- **Stacks 0GXX, comparison.** The completion of `Spec A` along the closed subscheme of
`I ⊆ A` is the formal spectrum of the `I`-adic completion of `A`: the kernels of the
projections of that completion are cofinal among its weak ideals of definition, and the
corresponding quotient spectra are the infinitesimal neighbourhoods. -/
public def completionAlongIdealIsoFormalSpectrum (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    completionAlongIdeal B S hS f hA I ≅
      formalSpectrum (adicCompletionQuotientSystem B S hS f hA I) :=
  let : (adicCompletionKernelIndex I).monotone.functor.Final :=
    final_adicCompletionKernelIndex I
  HasColimit.isoOfNatIso (Functor.isoWhiskerRight
      (infinitesimalNeighbourhoodDiagramIso B S hS f hA I)
      (BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) ≪≫
    Functor.Final.colimitIso (adicCompletionKernelIndex I).monotone.functor
      (formalSpectrumDiagram (adicCompletionQuotientSystem B S hS f hA I))

/-- The `I`-adic completion of `A` presents the completion of `Spec A` along the closed
subscheme of `I` as the colimit of the spectra of its quotients by weak ideals of
definition. -/
public def adicCompletionWeakIdealPresentation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    WeakIdealColimitPresentation B S hS (AdicCompletion I A)
      (completionAlongIdeal B S hS f hA I) :=
  { diagram := (adicCompletionQuotientSystem B S hS f hA I).diagram
    quotientIso := fun _ ↦ Iso.refl _
    quotientIso_natural := fun _ _ _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm
    colimitIso := completionAlongIdealIsoFormalSpectrum B S hS f hA I }

/-- The completion of `Spec A` along the closed subscheme of an ideal is an affine formal
algebraic space over `S`. -/
public theorem isAffineFormalAlgebraicSpace_completionAlongIdeal (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    IsAffineFormalAlgebraicSpace B S hS (completionAlongIdeal B S hS f hA I) :=
  isAffineFormalAlgebraicSpace_of_weakIdealColimitPresentation B S hS
    (AdicCompletion I A) (isWeaklyAdmissible_adicCompletion A I)
    (satisfiesSetTheoreticCondition_completionAlongIdeal B S hS f hA I)
    (adicCompletionWeakIdealPresentation B S hS f hA I)

/-- The completion along an ideal has a surjective presentation. -/
private theorem hasSomeSurjectivePresentation_completionAlongIdeal (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    HasSomeSurjectivePresentation B S hS (completionAlongIdeal B S hS f hA I) :=
  (hasAllSurjectivePresentations_of_weakIdealColimitPresentation B S hS
    (AdicCompletion I A) (isWeaklyAdmissible_adicCompletion A I)
    (satisfiesSetTheoreticCondition_completionAlongIdeal B S hS f hA I)
    (adicCompletionWeakIdealPresentation B S hS f hA I)).hasSomeSurjectivePresentation

/-- **Stacks 0GXX (1).** For an affine scheme `X = Spec A` over `S` and the closed subscheme
`Z ⊆ X` of an ideal `I ⊆ A`, the completion `X^∧_Z` of `X` along `Z` is a weakly adic affine
formal algebraic space: it is the formal spectrum of the `I`-adic completion of `A`, whose
topology is given by the closures of the powers of the ideal generated by `I`. -/
@[stacks 0GXX "clause (1): weakly adic"]
public theorem isWeaklyAdic_completionAlongIdeal (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) :
    IsWeaklyAdic B S hS (completionAlongIdeal B S hS f hA I) := by
  exact ⟨hasSomeSurjectivePresentation_completionAlongIdeal B S hS f hA I, AdicCompletion I A,
    inferInstance, adicCompletionLimitTopology A I,
    isTopologicalRing_adicCompletion A I, isLinearTopology_adicCompletion A I,
    ⟨isWeaklyAdmissible_adicCompletion A I, ⟨adicCompletionWeakIdealPresentation B S hS f hA I⟩⟩,
    isWeaklyAdic_adicCompletion A I⟩

end Comparison

/-! ### The finitely generated case -/

section FinitelyGenerated

attribute [local instance] adicCompletionLimitTopology isTopologicalRing_adicCompletion
  isLinearTopology_adicCompletion

variable {A : Type u} [CommRing A]

/-- For a finitely generated ideal `I`, the extension of `I ^ n` to the `I`-adic completion of
`A` is exactly the kernel of the `n`-th projection; no closure is needed. -/
public theorem map_pow_eq_adicCompletionKernel (I : Ideal A) (hI : I.FG) (n : ℕ) :
    Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ n) = adicCompletionKernel I n := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rw [Ideal.map_pow]
    exact map_pow_le_adicCompletionKernel I n
  · have hx' : x ∈ LinearMap.ker (AdicCompletion.eval I A n) := by
      rw [LinearMap.mem_ker]
      exact (mem_adicCompletionKernel I n x).mp hx
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map] at hx'
    exact hx'

/-- For finitely generated `I`, the `n`-th power of the extension of `I` is the `n`-th kernel. -/
private theorem pow_map_eq_adicCompletionKernel (I : Ideal A) (hI : I.FG) (n : ℕ) :
    (Ideal.map (algebraMap A (AdicCompletion I A)) I) ^ n = adicCompletionKernel I n := by
  rw [← Ideal.map_pow]
  exact map_pow_eq_adicCompletionKernel I hI n

/-- For a finitely generated ideal `I`, the inverse-limit topology on the `I`-adic completion
of `A` is the adic topology of the ideal generated by the image of `I`. -/
public theorem isAdic_map_adicCompletion (I : Ideal A) (hI : I.FG) :
    _root_.IsAdic (Ideal.map (algebraMap A (AdicCompletion I A)) I) := by
  have hpow := pow_map_eq_adicCompletionKernel I hI
  refine isAdic_iff.mpr ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hpow n]
    exact isOpen_adicCompletionKernel I n
  · obtain ⟨n, -, hn⟩ := (hasBasis_adicCompletionKernel I).mem_iff.mp hs
    exact ⟨n, by rw [hpow n]; exact hn⟩

/-- For a finitely generated ideal `I`, the ideal generated by the image of `I` in the
`I`-adic completion of `A` is a finitely generated ideal of definition. -/
public theorem isIdealOfDefinition_map_adicCompletion (I : Ideal A) (hI : I.FG) :
    TopologicalRing.IsIdealOfDefinition
      (Ideal.map (algebraMap A (AdicCompletion I A)) I) := by
  have hpow := pow_map_eq_adicCompletionKernel I hI
  refine ⟨?_, fun U hU ↦ ?_⟩
  · have h1 := isOpen_adicCompletionKernel I 1
    rw [← hpow 1, pow_one] at h1
    exact h1
  · obtain ⟨n, -, hn⟩ := (hasBasis_adicCompletionKernel I).mem_iff.mp hU
    exact ⟨n, by rw [hpow n]; exact hn⟩

/-- For a finitely generated ideal `I`, the `I`-adic completion of `A` is an adic topological
ring: its topology is the adic topology of the finitely generated ideal of definition
generated by the image of `I`, and it is complete and separated. -/
public theorem isAdic_adicCompletion (I : Ideal A) (hI : I.FG) :
    TopologicalRing.IsAdic (AdicCompletion I A) :=
  ⟨⟨Ideal.map (algebraMap A (AdicCompletion I A)) I,
      isIdealOfDefinition_map_adicCompletion I hI, isAdic_map_adicCompletion I hI⟩,
    t2Space_adicCompletion A I, completeSpace_adicCompletion A I⟩

/-- **Stacks 0GXX (2).** If `I` is finitely generated then the completion `X^∧_Z` of
`X = Spec A` along the closed subscheme `Z` of `I` is `Spf (A^∧)` for the `I`-adic completion
`A^∧` of `A`: the topology of `A^∧` is the adic topology of the ideal `I A^∧`, and `X^∧_Z` is
the formal spectrum of `A^∧`. -/
@[stacks 0GXX "clause (2): formal spectrum of the adic completion",
  ega "I 10.8.5" "affine case Spf(Â)",
  ega "I 10.10.1" "Spf(A) = X_{/X}",
  ega "III 5.1.1" "Spf(A) ≅ Ŷ"]
public theorem isAdic_and_iso_formalSpectrum_adicCompletion (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) (hI : I.FG) :
    _root_.IsAdic (Ideal.map (algebraMap A (AdicCompletion I A)) I) ∧
      Nonempty (completionAlongIdeal B S hS f hA I ≅
        formalSpectrum (adicCompletionQuotientSystem B S hS f hA I)) :=
  ⟨isAdic_map_adicCompletion I hI, ⟨completionAlongIdealIsoFormalSpectrum B S hS f hA I⟩⟩

/-- **Stacks 0GXX (3).** If `I` is finitely generated — equivalently, if the closed subscheme
`Z ⊆ X = Spec A` of `I` is of finite presentation over `X` — then the completion `X^∧_Z` is an
adic\* affine formal algebraic space: it is presented by the `I`-adic completion of `A`, which
is adic with the finitely generated ideal of definition `I A^∧`. -/
@[stacks 0GXX "clause (3): adic star"]
public theorem isAdicStar_completionAlongIdeal (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : Type u} [CommRing A] (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (I : Ideal A) (hI : I.FG) :
    IsAdicStar B S hS (completionAlongIdeal B S hS f hA I) := by
  exact ⟨hasSomeSurjectivePresentation_completionAlongIdeal B S hS f hA I, AdicCompletion I A,
    inferInstance, adicCompletionLimitTopology A I,
    isTopologicalRing_adicCompletion A I, isLinearTopology_adicCompletion A I,
    ⟨isWeaklyAdmissible_adicCompletion A I, ⟨adicCompletionWeakIdealPresentation B S hS f hA I⟩⟩,
    isAdic_adicCompletion I hI, Ideal.map (algebraMap A (AdicCompletion I A)) I,
    isIdealOfDefinition_map_adicCompletion I hI, hI.map _⟩

end FinitelyGenerated

end AlgebraicGeometry.FormalSpace

end
