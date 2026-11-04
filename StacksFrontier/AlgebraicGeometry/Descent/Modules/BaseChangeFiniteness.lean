module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Small
public import StacksCore.Algebra.Module.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.UniversalInjectivity

/-!
# Descent of module finiteness along universally injective ring maps

Let `R → S` be a universally injective map of commutative rings. An `R`-module is finitely
generated, respectively finitely presented, exactly when its scalar extension to `S` is.

## Main results

* `Module.finite_iff_baseChange_of_universallyInjective`: finite generation descends and
  ascends along a universally injective ring map.
* `Module.finitePresentation_iff_baseChange_of_universallyInjective`: the same for finite
  presentation.

## Implementation notes

The scalar extension is written `S ⊗[R] M`, with the scalar algebra as the left tensor
factor, so that it carries Mathlib's canonical `S`-module structure.

Finite generation descends because a generating set of `S ⊗[R] M` already lies in the base
change of a finitely generated submodule `N ≤ M`, and a universally injective ring map
reflects the vanishing of `M ⧸ N`. Finite presentation then descends in two steps: first in
a single universe, where a finite free presentation of `M` can be chosen and its relation
submodule replaced by a finitely generated submodule with the same base change, and then in
general by shrinking `M` — which is legitimate because finite generation is already known.

## References

* [Stacks Project, Tag 08XD](https://stacks.math.columbia.edu/tag/08XD)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module

/-- Finite generation descends and ascends along a universally injective ring map. -/
@[stacks 08XD "finite",
  sga "1 VIII 1.11" "finite type",
  sga "4½ Arcata 1.4.2" "(ii) finite type",
  ega "IV 2.5.2" "(i), affine case", ega "IV 2.5.4" "(i), affine case"]
theorem finite_iff_baseChange_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.Finite R M ↔ Module.Finite S (TensorProduct R S M) := by
  classical
  refine ⟨fun _ ↦ inferInstance, fun hM ↦ ?_⟩
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp hM.fg_top
  obtain ⟨N, hNfin, hsub⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite s hsfin
  have hbase : N.baseChange S = ⊤ := by
    rw [eq_top_iff, ← hs]
    exact Submodule.span_le.2 hsub
  have hN : N = ⊤ := by
    by_contra hn
    let Q := M ⧸ N
    have : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hn
    have : Subsingleton ((TensorProduct R S M) ⧸
        LinearMap.range (TensorProduct.map (LinearMap.id : S →ₗ[R] S) N.subtype)) := by
      change Subsingleton ((TensorProduct R S M) ⧸ (N.baseChange S).restrictScalars R)
      rw [hbase]
      change Subsingleton ((TensorProduct R S M) ⧸ (⊤ : Submodule R (TensorProduct R S M)))
      infer_instance
    have : Subsingleton (TensorProduct R S Q) :=
      Equiv.subsingleton (TensorProduct.tensorQuotientEquiv S N).toEquiv
    have : Subsingleton (TensorProduct R R Q) :=
      ⟨fun a b ↦ Algebra.rTensor_injective_of_universallyInjective R S hRS Q
        (Subsingleton.elim _ _)⟩
    have : Subsingleton Q := Equiv.subsingleton (TensorProduct.lid R Q).toEquiv.symm
    exact (not_nontrivial Q) inferInstance
  exact Module.Finite.of_surjective N.subtype fun x ↦ ⟨⟨x, hN ▸ Submodule.mem_top⟩, rfl⟩

/-- A submodule whose base change along `R → S` is finitely generated contains a finitely
generated submodule with the same base change. -/
private lemma exists_fg_submodule_baseChange
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {P : Type u} [AddCommGroup P] [Module R P] (K : Submodule R P)
    (hK : (K.baseChange S).FG) :
    ∃ K' : Submodule R P, K' ≤ K ∧ K'.FG ∧ K'.baseChange S = K.baseChange S := by
  classical
  obtain ⟨t, ht⟩ := hK
  let ι : P →ₗ[R] TensorProduct R S P := TensorProduct.mk R S P 1
  have hspan : K.baseChange S = Submodule.span S (ι '' (K : Set P)) := by
    simpa [ι] using (Submodule.baseChange_eq_span S K)
  have hmem (z : TensorProduct R S P) (hz : z ∈ (t : Set (TensorProduct R S P))) :
      z ∈ Submodule.span S (ι '' (K : Set P)) := hspan ▸ (ht ▸ Submodule.subset_span hz)
  choose V hVsub hVspan using fun z :
      {z : TensorProduct R S P // z ∈ (t : Set (TensorProduct R S P))} =>
    Submodule.mem_span_finite_of_mem_span (hmem z.1 z.2)
  let Vtot : Finset (TensorProduct R S P) := t.attach.biUnion V
  have hVtot : (Vtot : Set (TensorProduct R S P)) ⊆ ι '' (K : Set P) := by
    intro z hz
    simp only [Vtot, Finset.mem_coe, Finset.mem_biUnion] at hz
    obtain ⟨w, -, hz⟩ := hz
    exact hVsub w hz
  obtain ⟨U, hUK, hUimage⟩ := Finset.subset_set_image_iff.mp hVtot
  refine ⟨Submodule.span R (U : Set P), Submodule.span_le.mpr hUK, ⟨U, rfl⟩, ?_⟩
  have hVle : Submodule.span S (Vtot : Set (TensorProduct R S P)) ≤
      Submodule.span S (ι '' (U : Set P)) := by
    rw [Submodule.span_le]
    intro z hz
    rw [← hUimage] at hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hgen : Submodule.span S (t : Set (TensorProduct R S P)) ≤
      Submodule.span S (Vtot : Set (TensorProduct R S P)) := by
    rw [Submodule.span_le]
    intro z hz
    exact Submodule.span_mono
      (fun x hx ↦ Finset.mem_biUnion.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, hx⟩) (hVspan ⟨z, hz⟩)
  have hle : K.baseChange S ≤ Submodule.span S (ι '' (U : Set P)) := by
    rw [← ht]
    exact hgen.trans hVle
  have hge : Submodule.span S (ι '' (U : Set P)) ≤ K.baseChange S := by
    rw [hspan, Submodule.span_le]
    rintro z ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hUK hx, rfl⟩
  rw [Submodule.baseChange_span]
  simpa [ι] using le_antisymm hge hle

/-- The kernel of the base change of a surjective linear map is the base change of its kernel. -/
private lemma ker_baseChange_of_surjective
    {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (hf : Function.Surjective f) :
    LinearMap.ker (f.baseChange S) = (LinearMap.ker f).baseChange S := by
  have hx : Function.Exact ((LinearMap.ker f).subtype.baseChange S) (f.baseChange S) :=
    lTensor_exact S f.exact_subtype_ker_map hf
  rw [LinearMap.exact_iff] at hx
  simpa [Submodule.baseChange] using hx

/-- Finite presentation descends along a universally injective ring map for a module in the
same universe as the two rings. -/
private theorem finitePresentation_descends_same_universe
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hSM : Module.FinitePresentation S (TensorProduct R S M)) :
    Module.FinitePresentation R M := by
  classical
  have : Module.Finite R M :=
    (finite_iff_baseChange_of_universallyInjective hRS M).mpr
      (inferInstance : Module.Finite S (TensorProduct R S M))
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let P := Fin n → R
  let K : Submodule R P := LinearMap.ker f
  let fS : TensorProduct R S P →ₗ[S] TensorProduct R S M := f.baseChange S
  have hkerf : LinearMap.ker fS = K.baseChange S := ker_baseChange_of_surjective S f hf
  have hKbase : (K.baseChange S).FG := by
    rw [← hkerf]
    exact Module.FinitePresentation.fg_ker fS (LinearMap.lTensor_surjective S hf)
  obtain ⟨K', hK'K, hK'fg, hK'base⟩ := exists_fg_submodule_baseChange K hKbase
  let q : P →ₗ[R] P ⧸ K' := K'.mkQ
  let g : P ⧸ K' →ₗ[R] M := K'.liftQ f hK'K
  have hqsurj : Function.Surjective q := Submodule.mkQ_surjective K'
  have hgsurj : Function.Surjective g := by
    intro m
    obtain ⟨p, rfl⟩ := hf m
    exact ⟨q p, by simp [g, q]⟩
  have hqfp : Module.FinitePresentation R (P ⧸ K') :=
    Module.finitePresentation_of_surjective q hqsurj (by rwa [Submodule.ker_mkQ])
  let qS := q.baseChange S
  let gS := g.baseChange S
  have hqSsurj : Function.Surjective qS := by
    simpa only [qS, LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective S hqsurj
  have hkerq : LinearMap.ker qS = K'.baseChange S := by
    rw [ker_baseChange_of_surjective S q hqsurj, Submodule.ker_mkQ]
  have hcomp : gS.comp qS = fS := by
    rw [← LinearMap.baseChange_comp]
    simp [g, q]
    rfl
  have hgSsurj : Function.Surjective gS := LinearMap.lTensor_surjective S hgsurj
  have hgSinj : Function.Injective gS := by
    intro y z hyz
    obtain ⟨x, rfl⟩ := hqSsurj y
    obtain ⟨x', rfl⟩ := hqSsurj z
    have hdiff : x - x' ∈ LinearMap.ker qS := by
      rw [hkerq, hK'base, ← hkerf, LinearMap.mem_ker, map_sub, sub_eq_zero]
      simpa only [← hcomp, LinearMap.comp_apply] using hyz
    exact sub_eq_zero.mp (by simpa [map_sub] using LinearMap.mem_ker.mp hdiff)
  have hbijRT : Function.Bijective (LinearMap.rTensor S g) := by
    constructor
    · intro x y hxy
      apply (TensorProduct.comm R (P ⧸ K') S).injective
      apply hgSinj
      simpa only [gS, ← LinearMap.lTensor_comm, LinearMap.baseChange_eq_ltensor] using
        congrArg (TensorProduct.comm R M S) hxy
    · intro y
      obtain ⟨x, hx⟩ := hgSsurj ((TensorProduct.comm R M S) y)
      refine ⟨(TensorProduct.comm R S (P ⧸ K')) x, ?_⟩
      rw [LinearMap.rTensor_comm, ← LinearMap.baseChange_eq_ltensor, hx]
      exact (TensorProduct.comm R S M).apply_symm_apply y
  exact Module.FinitePresentation.of_equiv
    (LinearEquiv.ofBijective g (reflects_isomorphisms hRS g hbijRT))

/-- Finite presentation descends and ascends along a universally injective ring map. -/
@[stacks 08XD "finite_presentation",
  sga "1 VIII 1.11" "finite presentation",
  sga "4½ Arcata 1.4.2" "(ii) finite presentation",
  ega "IV 2.5.2" "(ii), affine case",
  ega "IV 2.5.4" "(ii), affine case"]
theorem finitePresentation_iff_baseChange_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.FinitePresentation R M ↔
    Module.FinitePresentation S (TensorProduct R S M) := by
  classical
  refine ⟨fun _ ↦ inferInstance, fun hSM ↦ ?_⟩
  have : Module.Finite R M :=
    (finite_iff_baseChange_of_universallyInjective hRS M).mpr
      (inferInstance : Module.Finite S (TensorProduct R S M))
  have : Small.{u} M := Module.Finite.small.{u} R M
  let e : Shrink.{u} M ≃ₗ[R] M := Shrink.linearEquiv R M
  have : Module.FinitePresentation R (Shrink.{u} M) :=
    finitePresentation_descends_same_universe hRS (Shrink.{u} M)
      (Module.FinitePresentation.of_equiv (LinearEquiv.baseChange R S (Shrink.{u} M) M e).symm)
  exact Module.FinitePresentation.of_equiv e

end Module

end
