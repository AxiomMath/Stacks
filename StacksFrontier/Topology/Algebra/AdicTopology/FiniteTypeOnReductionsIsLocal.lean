module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.RingHom.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FiniteType.Pi
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.RingTheory.Smooth.Reduced
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# Finite type on reductions is a local property

For a continuous homomorphism of countably indexed weakly admissible topological rings, being of
finite type on reductions — the induced map on the quotients by the topological nilradicals is of
finite type — satisfies the three locality axioms of Situation 0CBA.

The whole argument rests on one computation.  In a weakly pre-admissible ring the topological
nilradical `𝔫` is itself a weak ideal of definition, being open because it contains one; and it is
a radical ideal, because a root of a topologically nilpotent element is again one, the
neighbourhoods of zero containing open ideals.  So for an étale map `f : A → A'` the ring
`A' ⧸ 𝔫A'` is étale over the reduced ring `A ⧸ 𝔫`, hence reduced (Tag 033B).  The kernel of the
projection of the completion `(A')^∧ → A' ⧸ 𝔫A'` is a weak ideal of definition, hence contained in
`𝔫(A')^∧`; conversely that kernel is open, so a power of a topologically nilpotent element lies in
it, whose image is then a nilpotent element of a reduced ring.  The two ideals therefore agree, and
the reduction of `(A')^∧` *is* `A' ⧸ 𝔫A'`, étale over `A ⧸ 𝔫`.  This is the algebraic form of
Example 0GB6 and Lemma 0GB7.

Ascent then follows by composing reductions: the hypothesis makes `B ⧸ 𝔫 → A ⧸ 𝔫` of finite type,
the computation makes `A ⧸ 𝔫 → (A')^∧ ⧸ 𝔫` of finite type, and the square of reductions commutes,
so `(B')^∧ ⧸ 𝔫 → (A')^∧ ⧸ 𝔫` is of finite type because the composite out of `B ⧸ 𝔫` is.  Descent
is the same chain read backwards: `B ⧸ 𝔫 → (A')^∧ ⧸ 𝔫` is of finite type and
`A ⧸ 𝔫 → (A')^∧ ⧸ 𝔫` is, by the computation, faithfully flat and of finite presentation once
`A → A'` is faithfully flat, so Tag 0367 applies.  Finite products reduce to the fact that the
topological nilradical of a product is the product of the topological nilradicals, so that the
reduction of a finite product is the product of the reductions, together with finite type for a
finite product of algebras.

## Main results

* `TopologicalRing.isFiniteTypeOnReductions_propertyIsLocal`: **Stacks 0GC2**.
* `TopologicalRing.isFiniteTypeOnReductions_localizationPreserves`,
  `TopologicalRing.isFiniteTypeOnReductions_faithfullyFlatDescent`,
  `TopologicalRing.isFiniteTypeOnReductions_finiteProductPreserves`: the three axioms separately.

Auxiliary results of independent interest:

* `TopologicalRing.isTopologicallyNilpotent_of_pow` and
  `TopologicalRing.isRadical_topologicalNilradical`: the topological nilradical of a linearly
  topologized ring is a radical ideal.
* `TopologicalRing.isWeakIdealOfDefinition_topologicalNilradical`: in a weakly pre-admissible
  ring it is a weak ideal of definition.
* `TopologicalRing.topologicalNilradical_completionOver` and
  `TopologicalRing.reductionEquiv`: the reduction of a completion of an étale algebra.
* `TopologicalRing.topologicalNilradical_pi` and `TopologicalRing.piQuotEquiv`: products.

## Implementation notes

The property is packaged as `TopologicalRing.FiniteTypeOnReductionsProperty`, which quantifies
over the linear-topology instances and bundles continuity with finite type on reductions, so that
it has the unrestricted shape the locality axioms of Tag 0CBA consume.  The induced map on
reductions is `TopologicalRing.redMap`, definitionally the `Ideal.quotientMap` appearing in
`Rig.IsFiniteTypeOnReductions`; `redMap_comp` and `redMap_congr` are the two rewriting lemmas the
three axioms run on.

## References

* [Stacks Project, Tag 0GC2](https://stacks.math.columbia.edu/tag/0GC2)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GB6](https://stacks.math.columbia.edu/tag/0GB6)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
-/

@[expose] public section

namespace TopologicalRing

open Filter
open scoped Topology

section Nilradical

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsLinearTopology R R]

/-- A root of a topologically nilpotent element is topologically nilpotent: the powers of `x`
are the powers of `xⁿ` times a bounded factor, and the neighbourhoods of zero contain open
ideals. -/
public theorem isTopologicallyNilpotent_of_pow {x : R} {n : ℕ} (hn : 0 < n)
    (h : IsTopologicallyNilpotent (x ^ n)) : IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent, Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hV, hVsub⟩ := IsLinearTopology.hasBasis_ideal.mem_iff.mp hU
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (Filter.eventually_of_mem ((Filter.tendsto_def.mp h) (V : Set R) hV) fun _ hk ↦ hk)
  refine Filter.mem_of_superset (Filter.eventually_ge_atTop (K * n)) fun m hm ↦ ?_
  have hdiv : K ≤ m / n := (Nat.le_div_iff_mul_le hn).mpr hm
  have hmem : x ^ m ∈ V := by
    have hm' : x ^ m = (x ^ n) ^ (m / n) * x ^ (m % n) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hm']
    exact V.mul_mem_right _ (hK _ hdiv)
  exact hVsub hmem

/-- The topological nilradical of a linearly topologized ring is a radical ideal. -/
public theorem isRadical_topologicalNilradical : (topologicalNilradical R).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero] at hn
    exact (Ideal.eq_top_iff_one _).mpr hn ▸ Submodule.mem_top
  · exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      (isTopologicallyNilpotent_of_pow hpos
        (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hn))

/-- The reduction of a linearly topologized ring by its topological nilradical is reduced. -/
@[ega "0 1.1.1" "more general"]
public theorem isReduced_quotient_topologicalNilradical :
    IsReduced (R ⧸ topologicalNilradical R) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp isRadical_topologicalNilradical

/-- Every weak ideal of definition is contained in the topological nilradical. -/
public theorem le_topologicalNilradical_of_isWeakIdealOfDefinition {I : Ideal R}
    (hI : IsWeakIdealOfDefinition I) : I ≤ topologicalNilradical R :=
  fun _ hx ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hI.2 _ hx)

/-- In a weakly pre-admissible ring the topological nilradical is itself a weak ideal of
definition: it is open because it contains one, and all its elements are topologically
nilpotent by definition. -/
@[ega "0 7.1.3" "(ii), T is open"]
public theorem isWeakIdealOfDefinition_topologicalNilradical [IsTopologicalRing R]
    (hR : IsWeaklyPreAdmissible R) : IsWeakIdealOfDefinition (topologicalNilradical R) := by
  obtain ⟨I, hI⟩ := hR
  refine ⟨Ideal.isOpen_of_isOpen_subideal
    (le_topologicalNilradical_of_isWeakIdealOfDefinition hI) hI.1, fun x hx ↦ ?_⟩
  exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx

end Nilradical

section Reduction

universe u

variable {A A' : Type u} [CommRing A] [TopologicalSpace A] [IsLinearTopology A A] [CommRing A']

/-- The topological nilradical of `A`, as an index of the inverse system defining the completion
of a ring over `A`. -/
@[reducible] public def nilIdx [IsTopologicalRing A] (hA : IsWeaklyPreAdmissible A) :
    WeakIdealOfDefinitionIndex A :=
  ⟨topologicalNilradical A, isWeakIdealOfDefinition_topologicalNilradical hA⟩

/-- The reduction of an étale `A`-algebra by the topological nilradical of `A` is reduced: it is
étale, hence smooth, over the reduced ring `A ⧸ 𝔫`. -/
public theorem isReduced_quotient_map_topologicalNilradical {f : A →+* A'} (hf : f.Etale) :
    IsReduced (A' ⧸ (topologicalNilradical A).map f) := by
  have hq : (Ideal.quotientMap ((topologicalNilradical A).map f) f
      Ideal.le_comap_map).Etale :=
    quotientMap_of_isStableUnderBaseChange RingHom.Etale.isStableUnderBaseChange
      RingHom.Etale.respectsIso f hf (topologicalNilradical A)
  let instq : Algebra (A ⧸ topologicalNilradical A) (A' ⧸ (topologicalNilradical A).map f) :=
    (Ideal.quotientMap ((topologicalNilradical A).map f) f Ideal.le_comap_map).toAlgebra
  have : Algebra.Etale (A ⧸ topologicalNilradical A)
      (A' ⧸ (topologicalNilradical A).map f) := hq
  have : IsReduced (A ⧸ topologicalNilradical A) := isReduced_quotient_topologicalNilradical
  exact Algebra.isReduced_of_smooth (A ⧸ topologicalNilradical A)
    (A' ⧸ (topologicalNilradical A).map f)

/-- For an étale map out of a weakly pre-admissible ring, the topological nilradical of the
completion is the kernel of the projection at the topological nilradical of the base.

One inclusion holds because that kernel is a weak ideal of definition.  For the other, the
kernel is open, so a power of a topologically nilpotent element lies in it; its image in
`A' ⧸ 𝔫A'` is therefore nilpotent, hence zero, that ring being reduced. -/
public theorem topologicalNilradical_completionOver [IsTopologicalRing A] {f : A →+* A'}
    (hA : IsWeaklyPreAdmissible A) (hf : f.Etale) :
    topologicalNilradical (CompletionOver f) =
      RingHom.ker (CompletionOver.projection f (nilIdx hA)) := by
  refine le_antisymm (fun x hx ↦ ?_) (le_topologicalNilradical_of_isWeakIdealOfDefinition
    (projection_ker_isWeakIdealOfDefinition f (nilIdx hA)))
  have hnil := IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx
  have hopen := CompletionOver.isOpen_ker_projection f (nilIdx hA)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (Filter.eventually_of_mem
    ((Filter.tendsto_def.mp hnil) _ (hopen.mem_nhds (RingHom.ker _).zero_mem)) fun _ h ↦ h)
  have hpow : (CompletionOver.projection f (nilIdx hA) x) ^ k = 0 := by
    rw [← map_pow]
    exact RingHom.mem_ker.mp (hk k le_rfl)
  have : IsReduced (A' ⧸ (topologicalNilradical A).map f) :=
    isReduced_quotient_map_topologicalNilradical hf
  exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ⟨k, hpow⟩)

variable [IsTopologicalRing A]

/-- The reduction of the completion of `A'` over `A` identifies with `A' ⧸ 𝔫A'`. -/
public noncomputable def reductionEquiv {f : A →+* A'} (hA : IsWeaklyPreAdmissible A)
    (hf : f.Etale) :
    (CompletionOver f ⧸ topologicalNilradical (CompletionOver f)) ≃+*
      (A' ⧸ (topologicalNilradical A).map f) :=
  (Ideal.quotEquivOfEq (topologicalNilradical_completionOver hA hf)).trans
    (RingHom.quotientKerEquivOfSurjective
      (CompletionOver.projection_surjective f (nilIdx hA)))

/-- Under the identification of reductions, the canonical map `A → (A')^∧` reduces to the étale
map `A ⧸ 𝔫 → A' ⧸ 𝔫A'`. -/
public theorem reductionEquiv_comp_quotientMap {f : A →+* A'} (hA : IsWeaklyPreAdmissible A)
    (hf : f.Etale)
    (hle : topologicalNilradical A ≤
      (topologicalNilradical (CompletionOver f)).comap (CompletionOver.canonicalMap f)) :
    (reductionEquiv hA hf).toRingHom.comp
        (Ideal.quotientMap (topologicalNilradical (CompletionOver f))
          (CompletionOver.canonicalMap f) hle) =
      Ideal.quotientMap ((topologicalNilradical A).map f) f Ideal.le_comap_map := by
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingHom.comp_apply, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

/-- If a ring homomorphism becomes `h` after composing with an equivalence, it is the
composite of `h` with the inverse equivalence. -/
private theorem eq_symm_comp_of_comp_eq {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e : S ≃+* T) {g : R →+* S} {h : R →+* T} (H : e.toRingHom.comp g = h) :
    g = e.symm.toRingHom.comp h :=
  H ▸ RingHom.ext fun _ ↦ (e.symm_apply_apply _).symm

/-- If a ring homomorphism becomes `h` after composing with an equivalence and `h` is of finite
type, then it is of finite type. -/
private theorem finiteType_of_comp_equiv_eq {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (e : S ≃+* T) {g : R →+* S} {h : R →+* T} (H : e.toRingHom.comp g = h)
    (hh : h.FiniteType) : g.FiniteType := by
  rw [eq_symm_comp_of_comp_eq e H]
  exact (RingHom.FiniteType.of_surjective _ e.symm.surjective).comp hh

/-- **The canonical map into a completion is of finite type on reductions.**  The reduction of
`(A')^∧` is `A' ⧸ 𝔫A'`, which is étale over `A ⧸ 𝔫`. -/
public theorem isFiniteTypeOnReductions_canonicalMap {f : A →+* A'}
    (hA : IsWeaklyPreAdmissible A) (hf : f.Etale) :
    Rig.IsFiniteTypeOnReductions (CompletionOver.canonicalMap f)
      (continuous_canonicalMap f) :=
  finiteType_of_comp_equiv_eq (reductionEquiv hA hf) (reductionEquiv_comp_quotientMap hA hf _)
    (finiteType_of_etale (quotientMap_of_isStableUnderBaseChange
      RingHom.Etale.isStableUnderBaseChange RingHom.Etale.respectsIso f hf
      (topologicalNilradical A)))

end Reduction

section Functorial

variable {X Y Z : Type*} [CommRing X] [TopologicalSpace X] [IsLinearTopology X X]
  [CommRing Y] [TopologicalSpace Y] [IsLinearTopology Y Y]
  [CommRing Z] [TopologicalSpace Z] [IsLinearTopology Z Z]

/-- A continuous homomorphism carries topologically nilpotent elements to topologically
nilpotent elements. -/
@[sga "3 VIIB 0.1.3" "more general"]
public theorem topologicalNilradical_le_comap (φ : X →+* Y) (hφ : Continuous φ) :
    topologicalNilradical X ≤ (topologicalNilradical Y).comap φ := fun _ hx ↦
  IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
    ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hφ)

/-- The homomorphism induced on the reductions by the topological nilradicals. -/
@[reducible] public def redMap (φ : X →+* Y) (hφ : Continuous φ) :
    X ⧸ topologicalNilradical X →+* Y ⧸ topologicalNilradical Y :=
  Ideal.quotientMap (topologicalNilradical Y) φ (topologicalNilradical_le_comap φ hφ)

/-- Reduction depends only on the underlying homomorphism. -/
public theorem redMap_congr {φ ψ : X →+* Y} (h : φ = ψ) (hφ : Continuous φ)
    (hψ : Continuous ψ) : redMap φ hφ = redMap ψ hψ := by
  subst h; rfl

/-- Reduction is functorial. -/
public theorem redMap_comp (φ : X →+* Y) (ψ : Y →+* Z) (hφ : Continuous φ)
    (hψ : Continuous ψ) :
    redMap (ψ.comp φ) (hψ.comp hφ) = (redMap ψ hψ).comp (redMap φ hφ) := by
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [redMap, RingHom.comp_apply, Ideal.quotientMap_mk]

end Functorial

section CanonicalMap

universe u

variable {A A' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing A']

/-- The reduction of the canonical map into a completion is, up to the identification of
reductions, the étale map `A ⧸ 𝔫 → A' ⧸ 𝔫A'`. -/
public theorem redMap_canonicalMap_eq {f : A →+* A'} (hA : IsWeaklyPreAdmissible A)
    (hf : f.Etale) :
    redMap (CompletionOver.canonicalMap f) (continuous_canonicalMap f) =
      (reductionEquiv hA hf).symm.toRingHom.comp
        (Ideal.quotientMap ((topologicalNilradical A).map f) f Ideal.le_comap_map) := by
  exact eq_symm_comp_of_comp_eq _ (reductionEquiv_comp_quotientMap hA hf _)

/-- The canonical map into a completion is of finite type on reductions. -/
public theorem finiteType_redMap_canonicalMap {f : A →+* A'} (hA : IsWeaklyPreAdmissible A)
    (hf : f.Etale) :
    (redMap (CompletionOver.canonicalMap f) (continuous_canonicalMap f)).FiniteType :=
  isFiniteTypeOnReductions_canonicalMap hA hf

/-- The canonical map into a completion is faithfully flat on reductions as soon as the étale
map it completes is. -/
public theorem faithfullyFlat_redMap_canonicalMap {f : A →+* A'} (hA : IsWeaklyPreAdmissible A)
    (hf : f.Etale) (hff : f.FaithfullyFlat) :
    (redMap (CompletionOver.canonicalMap f) (continuous_canonicalMap f)).FaithfullyFlat := by
  rw [redMap_canonicalMap_eq hA hf]
  exact RingHom.FaithfullyFlat.respectsIso.1 _ (reductionEquiv hA hf).symm
    (faithfullyFlat_quotientMap f hff (topologicalNilradical A))

/-- The canonical map into a completion is of finite presentation on reductions. -/
public theorem finitePresentation_redMap_canonicalMap {f : A →+* A'}
    (hA : IsWeaklyPreAdmissible A) (hf : f.Etale) :
    (redMap (CompletionOver.canonicalMap f)
      (continuous_canonicalMap f)).FinitePresentation := by
  rw [redMap_canonicalMap_eq hA hf]
  exact RingHom.finitePresentation_respectsIso.1 _ (reductionEquiv hA hf).symm
    (finitePresentation_quotientMap f (RingHom.Etale.finitePresentation hf)
      (topologicalNilradical A))

end CanonicalMap

section Pi

variable {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)]

/-- The product of the reduction maps of a family of quotients. -/
public def piQuotHom (I : ∀ i, Ideal (A i)) : (∀ i, A i) →+* ∀ i, A i ⧸ I i :=
  RingHom.pi fun i ↦ (Ideal.Quotient.mk (I i)).comp (Pi.evalRingHom A i)

public theorem ker_piQuotHom (I : ∀ i, Ideal (A i)) :
    RingHom.ker (piQuotHom I) = Ideal.pi I := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_pi, funext_iff]
  simp [piQuotHom, Ideal.Quotient.eq_zero_iff_mem]

public theorem surjective_piQuotHom (I : ∀ i, Ideal (A i)) :
    Function.Surjective (piQuotHom I) := by
  intro y
  choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (y i)
  exact ⟨a, funext fun i ↦ ha i⟩

/-- The quotient of a product of rings by a product of ideals is the product of the
quotients. -/
public noncomputable def piQuotEquiv (I : ∀ i, Ideal (A i)) :
    ((∀ i, A i) ⧸ Ideal.pi I) ≃+* ∀ i, A i ⧸ I i :=
  (Ideal.quotEquivOfEq (ker_piQuotHom I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_piQuotHom I))

variable [∀ i, TopologicalSpace (A i)]

/-- An element of a product of topological rings is topologically nilpotent exactly
when each of its components is. -/
public theorem isTopologicallyNilpotent_pi_iff {x : ∀ i, A i} :
    IsTopologicallyNilpotent x ↔ ∀ i, IsTopologicallyNilpotent (x i) := by
  simp only [IsTopologicallyNilpotent, tendsto_pi_nhds]
  rfl

/-- The topological nilradical of a product is the product of the topological nilradicals. -/
public theorem topologicalNilradical_pi [∀ i, IsLinearTopology (A i) (A i)]
    [IsLinearTopology (∀ i, A i) (∀ i, A i)] :
    topologicalNilradical (∀ i, A i) = Ideal.pi fun i ↦ topologicalNilradical (A i) := by
  ext x
  rw [IsTopologicallyNilpotent.mem_topologicalNilradical_iff, Ideal.mem_pi]
  simp only [IsTopologicallyNilpotent.mem_topologicalNilradical_iff]
  exact isTopologicallyNilpotent_pi_iff

end Pi

section Local

universe u

/-- The morphism property of being continuous and of finite type on reductions, extended to the
unrestricted interface of local properties.  On linearly topologized weakly admissible rings
this is the property of Tag 0GC2. -/
public abbrev FiniteTypeOnReductionsProperty {B A : Type u}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) : Prop :=
  ∀ [IsLinearTopology B B] [IsLinearTopology A A],
    ∃ hφ : Continuous φ, Rig.IsFiniteTypeOnReductions φ hφ

/-- In a localization diagram the square of reductions commutes. -/
private theorem redMap_square {A B A' B' : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A'] [CommRing B'] (D : LocalizationDiagram A B A' B') :
    (redMap (CompletionOver.canonicalMap D.toA') (continuous_canonicalMap _)).comp
        (redMap D.map D.continuousMap) =
      (redMap D.completedMap D.continuousCompletedMap).comp
        (redMap (CompletionOver.canonicalMap D.toB') (continuous_canonicalMap _)) :=
  (redMap_comp _ _ _ _).symm.trans ((redMap_congr D.commutes _ _).trans (redMap_comp _ _ _ _))

/-- **Stacks 0GC2**, axiom 0AND: finite type on reductions ascends along a completed étale
localization diagram. -/
public theorem isFiniteTypeOnReductions_localizationPreserves :
    LocalizationPreserves.{u} IsCountablyWeaklyAdmissible
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        FiniteTypeOnReductionsProperty φ) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D _ _ _ _ hP _ _
  obtain ⟨hcont, hred⟩ := hP
  have hfin : ((redMap D.completedMap D.continuousCompletedMap).comp
      (redMap (CompletionOver.canonicalMap D.toB') (continuous_canonicalMap _))).FiniteType := by
    rw [← redMap_square D]
    exact (finiteType_redMap_canonicalMap D.weaklyAdmissibleA.1 D.etaleA).comp hred
  exact ⟨D.continuousCompletedMap, RingHom.FiniteType.of_comp_finiteType hfin⟩

/-- **Stacks 0GC2**, axiom 0ANE: finite type on reductions descends along a completed étale
localization diagram whose upper horizontal ring map is faithfully flat. -/
public theorem isFiniteTypeOnReductions_faithfullyFlatDescent :
    FaithfullyFlatDescent.{u} IsCountablyWeaklyAdmissible
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        FiniteTypeOnReductionsProperty φ) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D _ _ _ _ hff hP _ _
  obtain ⟨hcontCM, hredCM⟩ := hP
  have hfin : ((redMap (CompletionOver.canonicalMap D.toA') (continuous_canonicalMap _)).comp
      (redMap D.map D.continuousMap)).FiniteType := by
    rw [redMap_square D]
    exact hredCM.comp (finiteType_redMap_canonicalMap D.weaklyAdmissibleB.1 D.etaleB)
  exact ⟨D.continuousMap,
    RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation hfin
      (faithfullyFlat_redMap_canonicalMap D.weaklyAdmissibleA.1 D.etaleA hff)
      (finitePresentation_redMap_canonicalMap D.weaklyAdmissibleA.1 D.etaleA)⟩

/-- **Stacks 0GC2**, axiom 0ANF: finite type on reductions is preserved by finite products of
targets.  The reduction of a product is the product of the reductions, and a product of
finitely many algebras of finite type is of finite type. -/
public theorem isFiniteTypeOnReductions_finiteProductPreserves :
    FiniteProductPreserves.{u} IsCountablyWeaklyAdmissible
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        FiniteTypeOnReductionsProperty φ) := by
  intro B _ _ _ _ _ _ ι _ A _ _ _ _ _ _ f hfc _ _ hP _ _
  have hcont : Continuous (RingHom.pi f) := continuous_pi fun i ↦ hfc i
  refine ⟨hcont, ?_⟩
  let e : ((∀ i, A i) ⧸ topologicalNilradical (∀ i, A i)) ≃+*
      ∀ i, A i ⧸ topologicalNilradical (A i) :=
    (Ideal.quotEquivOfEq topologicalNilradical_pi).trans
      (piQuotEquiv fun i ↦ topologicalNilradical (A i))
  have hcomp : e.toRingHom.comp (redMap (RingHom.pi f) hcont) =
      RingHom.pi fun i ↦ redMap (f i) (hfc i) := by
    refine RingHom.ext fun z ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine funext fun i ↦ ?_
    simp only [RingHom.coe_comp, Function.comp_apply, redMap, Ideal.quotientMap_mk,
      RingHom.pi_apply, e, piQuotEquiv]
    rfl
  exact finiteType_of_comp_equiv_eq e hcomp
    (RingHom.FiniteType.pi _ fun i ↦ (hP i).2)

/-- **Finite type on reductions is a local property of morphisms of countably indexed weakly
admissible topological rings** (Stacks 0GC2). -/
public theorem isFiniteTypeOnReductions_propertyIsLocal :
    PropertyIsLocal.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        FiniteTypeOnReductionsProperty φ) where
  localizationPreserves := isFiniteTypeOnReductions_localizationPreserves
  faithfullyFlatDescent := isFiniteTypeOnReductions_faithfullyFlatDescent
  finiteProduct := isFiniteTypeOnReductions_finiteProductPreserves

end Local

end TopologicalRing

end
