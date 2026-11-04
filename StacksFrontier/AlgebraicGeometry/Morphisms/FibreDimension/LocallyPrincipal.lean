module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic points of a locally principal closed subscheme, and their fibres

Let `X` be a locally Noetherian scheme and let `I` be a locally principal ideal sheaf on `X`,
cutting out a closed subscheme `Z` with support `I.support`. Krull's principal ideal theorem says
that the local ring of `X` at a generic point of an irreducible component of `Z` has dimension at
most one.

Now let `f : X ⟶ S` be a morphism to an irreducible scheme, with `X` irreducible and `f` dominant,
and suppose `Z` misses the generic fibre. Then at a generic point `ξ'` of an irreducible component
of `Z` there is no room for a nontrivial specialization inside the fibre through `ξ'`: the generic
point `ξ` of `X` lies over the generic point of `S`, hence off the fibre, so a chain
`ξ ⤳ ξ₁ ⤳ ξ'` with `ξ₁` in the fibre through `ξ'` would exhibit two strict specializations onto
`ξ'` and force the local ring at `ξ'` to have dimension at least two. Consequently `ξ'` is itself a
generic point of an irreducible component of its own fibre.

These are the third and fourth steps of the Noetherian case of the proof of Stacks 053R.

## Main results

* `closure_singleton_mem_irreducibleComponents_of_forall_specializes`: in a quasi-sober space, the
  closure of a point that no other point specializes to is an irreducible component.
* `Set.eq_sUnion_irreducibleComponents_of_forall`: a subset is the union of the ambient irreducible
  components it contains as soon as each of its points lies in such a component. This is the shape
  in which Stacks 053R states its conclusion.
* `succ_le_topologicalKrullDim_of_ssubset` and `topologicalKrullDim_le_pred_of_ssubset`: a closed
  subset properly contained in an irreducible set of dimension at most `n` has dimension at most
  `n - 1`, because every chain of irreducible closed subsets of it extends by one step.
* `Stacks.Divisors.ringKrullDim_stalk_le_one_of_isLocallyPrincipal`: **Krull's principal ideal
  theorem for a locally principal closed subscheme.** At a generic point of an irreducible
  component of the support, the local ring of a locally Noetherian scheme has dimension at most
  one.
* `Stacks.Divisors.eq_of_specializes_of_isLocallyPrincipal`: a point of the fibre through such a
  generic point `ξ'` that specializes to `ξ'` equals `ξ'`.
* `Stacks.Divisors.closure_asFiber_mem_irreducibleComponents_of_isLocallyPrincipal`: therefore
  `ξ'` is a generic point of an irreducible component of its fibre.

## Implementation notes

"`ξ` is a generic point of an irreducible component of `I.support`" is expressed by the
specialization condition `∀ y ∈ I.support, y ⤳ ξ → y = ξ` together with `ξ ∈ I.support`, rather
than by `closure {ξ} ∈ irreducibleComponents (I.support : Set X)`: the subspace form forces every
statement through a subtype coercion, while the specialization form is what both the ring-level
minimality of a prime and the dimension count actually consume. The two agree on a quasi-sober
space, which is the content of
`closure_singleton_mem_irreducibleComponents_of_forall_specializes`.

Emptiness of the generic fibre of `Z` is likewise taken in the pointwise form
`∀ y ∈ I.support, f y ≠ genericPoint S`, which is what `IsEmpty ((I.subschemeι ≫ f).fiber ⋯)`
amounts to under `Scheme.IdealSheafData.range_subschemeι` and `Scheme.Hom.range_fiberι`.

The dimension count runs through `Order.coheight` in the specialization preorder, where Mathlib's
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` identifies the dimension of a stalk, and
`Order.coheight_add_one_le` adds one unit per strict specialization. Two instances in this file
have to be supplied as terms rather than by `inferInstance`: `IsNoetherianRing Γ(X, V.1)` for an
affine open `V` of a locally Noetherian scheme, and `IsOpenImmersion V.2.fromSpec`, whose
discrimination-tree keys do not match when the affine open is presented as the second component
of an element of `X.affineOpens`.

## References

* [Stacks Project, Tag 00KV](https://stacks.math.columbia.edu/tag/00KV)
* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- In a quasi-sober space, the closure of a point `y` such that no other point specializes to `y`
is an irreducible component: any irreducible closed set containing `y` has a generic point, which
specializes to `y` and is therefore `y` itself. -/
public theorem closure_singleton_mem_irreducibleComponents_of_forall_specializes
    {T : Type*} [TopologicalSpace T] [QuasiSober T] {y : T}
    (hy : ∀ z : T, z ⤳ y → z = y) :
    closure {y} ∈ irreducibleComponents T := by
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, ?_⟩
  rintro C ⟨hCcl, hCirr⟩ hle
  obtain ⟨z, hzC⟩ := QuasiSober.sober hCirr hCcl
  have hyC : y ∈ C := hle (subset_closure rfl)
  have : z = y := hy z (specializes_iff_mem_closure.mpr (hzC ▸ hyC))
  exact hzC.symm.trans_le (this ▸ le_rfl)

/-- A subset is the union of the irreducible components of the ambient space that it contains, as
soon as every one of its points lies in such a component. This is the form in which Stacks 053R
states that a fibre of a closed subscheme is set-theoretically a union of irreducible components
of the fibre. -/
public theorem Set.eq_sUnion_irreducibleComponents_of_forall {T : Type*} [TopologicalSpace T]
    (W : Set T) (h : ∀ y ∈ W, ∃ C ∈ irreducibleComponents T, y ∈ C ∧ C ⊆ W) :
    W = ⋃₀ {C : Set T | C ∈ irreducibleComponents T ∧ C ⊆ W} := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · obtain ⟨C, hC, hyC, hCW⟩ := h y hy
    exact ⟨C, ⟨hC, hCW⟩, hyC⟩
  · rintro y ⟨C, ⟨-, hCW⟩, hyC⟩
    exact hCW hyC

/-- A chain of irreducible closed subsets of a closed set `V` properly contained in an irreducible
set `C` extends by one step, namely by `C` itself: every member of the chain is contained in `V`,
which is a proper closed subset of `C`. -/
public theorem succ_le_topologicalKrullDim_of_ssubset {T : Type*} [TopologicalSpace T]
    {V C : Set T} (hV : IsClosed V) (hCirr : IsIrreducible C) (hVC : V ⊂ C)
    (p : LTSeries (IrreducibleCloseds (↥V))) :
    ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (↥C) := by
  have hincC : Topology.IsInducing (Set.inclusion hVC.le) :=
    (Topology.IsEmbedding.inclusion hVC.le).isInducing
  have : IrreducibleSpace (↥C) := isIrreducible_iff_irreducibleSpace.mp hCirr
  let F : IrreducibleCloseds (↥V) → IrreducibleCloseds (↥C) :=
    IrreducibleCloseds.map (Set.inclusion hVC.le) hincC.continuous
  have hF : StrictMono F := IrreducibleCloseds.map_strictMono_of_isInducing hincC
  let top : IrreducibleCloseds (↥C) :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ (↥C), isClosed_univ⟩
  have hVset : IsClosed {x : ↥C | (x : T) ∈ V} := hV.preimage continuous_subtype_val
  obtain ⟨c, hcC, hcV⟩ := Set.exists_of_ssubset hVC
  have hlt : F p.last < top := by
    refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun h => ?_
    have hc : (⟨c, hcC⟩ : ↥C) ∈ (F p.last : Set (↥C)) := by rw [h]; exact Set.mem_univ _
    have hsub : (F p.last : Set (↥C)) ⊆ {x : ↥C | (x : T) ∈ V} := by
      refine (IsClosed.closure_subset_iff hVset).mpr ?_
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    exact hcV (hsub hc)
  have hq := Order.LTSeries.length_le_krullDim ((p.map F hF).snoc top hlt)
  have hlen : ((p.map F hF).snoc top hlt).length = p.length + 1 := by
    simp [RelSeries.snoc, RelSeries.append, RelSeries.singleton]
  rw [hlen] at hq
  simpa [topologicalKrullDim] using hq

/-- A closed subset properly contained in an irreducible set of dimension at most `n` has
dimension at most `n - 1`. This is how the second paragraph of the proof of Stacks 053R, which
pins the local dimension of every fibre, bounds the dimension of a component of the fibre of a
locally principal closed subscheme that is not a component of the fibre itself. -/
public theorem topologicalKrullDim_le_pred_of_ssubset {T : Type*} [TopologicalSpace T]
    {V C : Set T} (hV : IsClosed V) (hCirr : IsIrreducible C) (hVC : V ⊂ C) {n : ℕ}
    (hn : topologicalKrullDim (↥C) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim (↥V) ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le fun p => ?_
  have h := (succ_le_topologicalKrullDim_of_ssubset hV hCirr hVC p).trans hn
  have h2 : ((p.length + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp h
  have h' : p.length + 1 ≤ n := by exact_mod_cast h2
  have h'' : ((p.length : ℕ) : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.le_sub_one_of_lt (by omega : p.length < n)
  exact WithBot.coe_le_coe.mpr h''

namespace Stacks.Divisors

/-- **Krull's principal ideal theorem for a locally principal closed subscheme.** Let `I` be a
locally principal ideal sheaf on a locally Noetherian scheme `X` and let `ξ` be a generic point of
an irreducible component of its support, i.e. a point of the support to which no other point of
the support specializes. Then the local ring of `X` at `ξ` has dimension at most one. -/
@[ega "IV 5.1.8" "more general"]
public theorem ringKrullDim_stalk_le_one_of_isLocallyPrincipal {X : Scheme.{u}}
    [IsLocallyNoetherian X] {I : X.IdealSheafData} (hI : IsLocallyPrincipal I) {ξ : X}
    (hξ : ξ ∈ (I.support : Set X))
    (hmin : ∀ y ∈ (I.support : Set X), y ⤳ ξ → y = ξ) :
    ringKrullDim (X.presheaf.stalk ξ) ≤ 1 := by
  obtain ⟨V, hξV, hprin⟩ := hI ξ
  have hNoeth : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  have hzl : ξ ∈ X.zeroLocus (U := V.1) (I.ideal V) := I.supportSet_subset_zeroLocus V hξ
  have hfs : V.2.fromSpec (V.2.primeIdealOf ⟨ξ, hξV⟩) = ξ := V.2.fromSpec_primeIdealOf ⟨ξ, hξV⟩
  have hzq : ∀ q : PrimeSpectrum Γ(X, V.1), (I.ideal V : Set Γ(X, V.1)) ⊆ q.asIdeal ↔
      V.2.fromSpec q ∈ X.zeroLocus (U := V.1) (I.ideal V) := fun q => by
    rw [← PrimeSpectrum.mem_zeroLocus, ← V.2.fromSpec_preimage_zeroLocus]
    exact Iff.rfl
  have hle : (I.ideal V : Set Γ(X, V.1)) ⊆ (V.2.primeIdealOf ⟨ξ, hξV⟩).asIdeal :=
    (hzq _).mpr (by rw [hfs]; exact hzl)
  have key : ∀ q : PrimeSpectrum Γ(X, V.1),
      (I.ideal V : Set Γ(X, V.1)) ⊆ q.asIdeal →
      q.asIdeal ≤ (V.2.primeIdealOf ⟨ξ, hξV⟩).asIdeal → q = V.2.primeIdealOf ⟨ξ, hξV⟩ := by
    intro q hq hqle
    have hy : V.2.fromSpec q ∈ (I.support : Set X) := by
      refine I.zeroLocus_inter_subset_supportSet V ⟨?_, ?_⟩
      · exact (hzq q).mp hq
      · exact V.2.range_fromSpec.le ⟨q, rfl⟩
    have hsp : V.2.fromSpec q ⤳ ξ := by
      rw [← hfs]
      exact ((PrimeSpectrum.le_iff_specializes _ _).mp hqle).map V.2.fromSpec.continuous
    have heq := hmin _ hy hsp
    have := V.2.isOpenImmersion_fromSpec
    exact V.2.fromSpec.isOpenEmbedding.injective (heq.trans hfs.symm)
  have hminp : (V.2.primeIdealOf ⟨ξ, hξV⟩).asIdeal ∈ (I.ideal V).minimalPrimes := by
    refine ⟨⟨(V.2.primeIdealOf ⟨ξ, hξV⟩).isPrime, hle⟩, ?_⟩
    exact fun q hq hqle => (congrArg PrimeSpectrum.asIdeal (key ⟨q, hq.1⟩ hq.2 hqle)).ge
  rw [V.2.ringKrullDim_stalk_eq_height ξ hξV]
  exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (I.ideal V) _ hminp

/-- **Stacks 053R, Noetherian case, the specialization step.** Let `f : X ⟶ S` be a dominant
morphism of irreducible schemes with `X` locally Noetherian, let `I` be a locally principal ideal
sheaf whose support misses the generic fibre, and let `ξ'` be a generic point of an irreducible
component of that support. Then no point of the fibre through `ξ'` other than `ξ'` specializes
to `ξ'`.

The chain `genericPoint X ⤳ ξ₁ ⤳ ξ'` has a strict first step because `ξ'` does not lie over the
generic point of `S` while `genericPoint X` does, so a strict second step would make the local
ring at `ξ'` at least two-dimensional. -/
public theorem eq_of_specializes_of_isLocallyPrincipal {X S : Scheme.{u}} (f : X ⟶ S)
    [IrreducibleSpace X] [IrreducibleSpace S] [IsDominant f] [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (hI : IsLocallyPrincipal I)
    (hgen : ∀ y ∈ (I.support : Set X), f y ≠ genericPoint S) {ξ' : X}
    (hξ' : ξ' ∈ (I.support : Set X))
    (hmin : ∀ y ∈ (I.support : Set X), y ⤳ ξ' → y = ξ') {ξ₁ : X}
    (hfib : f ξ₁ = f ξ') (hsp : ξ₁ ⤳ ξ') :
    ξ₁ = ξ' := by
  by_contra hne
  have h1 : ξ' < ξ₁ := ⟨hsp, fun h' => hne (h'.antisymm hsp).eq.symm⟩
  have hξne : genericPoint X ≠ ξ₁ := fun h =>
    hgen ξ' hξ' (by rw [← hfib, ← h, apply_genericPoint_eq_genericPoint f])
  have hgX : genericPoint X ⤳ ξ₁ := genericPoint_specializes ξ₁
  have h2 : ξ₁ < genericPoint X := ⟨hgX, fun h' => hξne (hgX.antisymm h').eq⟩
  have a1 := Order.coheight_add_one_le h1
  have a2 := Order.coheight_add_one_le h2
  have hle := ringKrullDim_stalk_le_one_of_isLocallyPrincipal hI hξ' hmin
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hle
  have h2le : (1 + 1 : ℕ∞) ≤ Order.coheight ξ' :=
    (add_le_add_left (le_trans (by simp) a2 : (1 : ℕ∞) ≤ Order.coheight ξ₁) 1).trans a1
  have := (WithBot.coe_le_coe.mpr h2le).trans hle
  norm_num at this

/-- **Stacks 053R, Noetherian case, the conclusion of the specialization step.** Under the
hypotheses of `Stacks.Divisors.eq_of_specializes_of_isLocallyPrincipal`, the generic point `ξ'` of
an irreducible component of the support is a generic point of an irreducible component of the
fibre through it. -/
public theorem closure_asFiber_mem_irreducibleComponents_of_isLocallyPrincipal
    {X S : Scheme.{u}} (f : X ⟶ S) [IrreducibleSpace X] [IrreducibleSpace S] [IsDominant f]
    [IsLocallyNoetherian X] {I : X.IdealSheafData} (hI : IsLocallyPrincipal I)
    (hgen : ∀ y ∈ (I.support : Set X), f y ≠ genericPoint S) {ξ' : X}
    (hξ' : ξ' ∈ (I.support : Set X))
    (hmin : ∀ y ∈ (I.support : Set X), y ⤳ ξ' → y = ξ') :
    closure {f.asFiber ξ'} ∈ irreducibleComponents (f.fiber (f ξ')) := by
  refine closure_singleton_mem_irreducibleComponents_of_forall_specializes fun z hz => ?_
  have hιz : f (f.fiberι (f ξ') z) = f ξ' := (f.range_fiberι (f ξ')).le ⟨z, rfl⟩
  have hsp : f.fiberι (f ξ') z ⤳ ξ' := by
    have := hz.map (f.fiberι (f ξ')).continuous
    rwa [f.fiberι_asFiber ξ'] at this
  have heq := eq_of_specializes_of_isLocallyPrincipal f hI hgen hξ' hmin hιz hsp
  refine (f.fiberι (f ξ')).isEmbedding.injective ?_
  rw [f.fiberι_asFiber ξ']
  exact heq

end Stacks.Divisors

end
