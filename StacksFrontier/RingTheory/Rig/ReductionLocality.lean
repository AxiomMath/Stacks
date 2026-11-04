module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.RingTheory.RingHom.QuotientBaseChange
public import StacksFrontier.RingTheory.Smooth.Reduced
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal

/-!
# Finite type on reductions as a property of topological ring homomorphisms

Reduction by the ideal of topologically nilpotent elements is defined for a continuous
homomorphism of linearly topologized rings, so finite type on reductions depends on a
continuity proof and on linear topologies.  The locality framework for morphisms of countably
indexed weakly admissible rings instead accepts a property of bare homomorphisms of
topological rings.  `TopologicalRing.FiniteTypeOnReductionsProperty` bridges the two: it
quantifies over linear topologies and asserts the existence of a continuity proof together
with finite type of the induced homomorphism on reductions, so that on the continuous arrows
between linearly topologized rings it is exactly finite type on reductions.

Ascent along a completed étale localization diagram rests on the fact that, in a weakly
pre-admissible ring `A`, the topological nilradical is itself a weak ideal of definition, hence
an index of the inverse system defining the completion of an `A`-algebra `A'`.  The associated
projection is surjective with kernel inside the topological nilradical of the completion, which
exhibits the reduction of the completion as a quotient of `A' / N(A)A'`; the latter is of finite
type over `A / N(A)` because `A → A'` is étale.

Descent along a diagram whose horizontal map `A → A'` is faithfully flat needs that quotient
map to be an isomorphism, and it is: the topological nilradical of the completion is exactly
the kernel of the projection at the index `N(A)`.  Indeed `A / N(A)` is reduced because the
topological nilradical is a radical ideal, and `A' / N(A)A'` is étale, hence smooth, over it,
so it is reduced as well; a topologically nilpotent element of the completion therefore has
nilpotent, hence zero, image under that projection.  Reduction of the canonical map into the
completion is consequently the faithfully flat, finitely presented base change of `A → A'`
along `A → A / N(A)`, and finite type of the reduced diagonal descends through it.

## Main definitions


## Main results

* `Rig.isWeakIdealOfDefinition_topologicalNilradical` — the topological nilradical of a weakly
  pre-admissible linearly topologized ring is a weak ideal of definition.
* `Rig.isFiniteTypeOnReductions_canonicalMap` — the canonical map into the completion of an
  étale algebra is of finite type on reductions.
* `Rig.finiteTypeOnReductionsProperty_localizationPreserves` — finite type on reductions
  ascends along completed étale localization diagrams.
* `Rig.finiteTypeOnReductionsProperty_faithfullyFlatDescent` — finite type on reductions
  descends along completed étale localization diagrams with faithfully flat horizontal map.
* `Rig.finiteTypeOnReductionsProperty_finiteProductPreserves` — finite type on reductions is
  preserved by finite products of targets.
* `Rig.isFiniteTypeOnReductions_local` — finite type on reductions is a local property of
  morphisms of countably indexed weakly admissible topological rings.

## References

* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GC2](https://stacks.math.columbia.edu/tag/0GC2)
-/

@[expose] public section

namespace Rig

open TopologicalRing (FiniteTypeOnReductionsProperty)

section

/-- A surjection whose kernel is contained in an ideal of its source descends to a surjection
of its target onto the quotient by that ideal. -/
private theorem exists_desc_of_ker_le {R S : Type*} [CommRing R] [CommRing S] {π : R →+* S}
    (hπ : Function.Surjective π) {I : Ideal R} (h : RingHom.ker π ≤ I) :
    ∃ ψ : S →+* R ⧸ I, Function.Surjective ψ ∧ ψ.comp π = Ideal.Quotient.mk I := by
  set ψ : S →+* R ⧸ I := (Ideal.Quotient.factor h).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom with hψ
  have key : ∀ x : R, ψ (π x) = Ideal.Quotient.mk I x := by
    intro x
    have hs : (RingHom.quotientKerEquivOfSurjective hπ).symm (π x)
        = Ideal.Quotient.mk (RingHom.ker π) x := by
      rw [RingEquiv.symm_apply_eq]; simp
    change (Ideal.Quotient.factor h)
      ((RingHom.quotientKerEquivOfSurjective hπ).symm (π x)) = _
    rw [hs, Ideal.Quotient.factor_mk]
  refine ⟨ψ, ?_, RingHom.ext key⟩
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) y
  exact ⟨π x, key x⟩

/-- A continuous homomorphism carries topologically nilpotent elements to topologically
nilpotent elements. -/
@[sga "3 VIIB 0.1.3" "more general"]
private theorem topologicalNilradical_le_comap {R S : Type*} [CommRing R] [TopologicalSpace R]
    [IsLinearTopology R R] [CommRing S] [TopologicalSpace S] [IsLinearTopology S S]
    (φ : R →+* S) (hφ : Continuous φ) :
    topologicalNilradical R ≤ Ideal.comap φ (topologicalNilradical S) := fun _ hx ↦
  IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
    ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hφ)

/-- The topological nilradical of a weakly pre-admissible linearly topologized ring is a weak
ideal of definition; by construction it contains every other one. -/
public theorem isWeakIdealOfDefinition_topologicalNilradical {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyPreAdmissible A) :
    TopologicalRing.IsWeakIdealOfDefinition (topologicalNilradical A) := by
  obtain ⟨I, hIopen, hInil⟩ := hA
  refine ⟨?_, fun x hx ↦ IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx⟩
  exact (topologicalNilradical A).toAddSubgroup.isOpen_of_mem_nhds <|
    Filter.mem_of_superset (hIopen.mem_nhds (Ideal.zero_mem I)) fun x hx ↦
      IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hInil x hx)

end

section

universe u

open TopologicalRing

/-- The reductions of the maps of a localization diagram form a commutative square. -/
private theorem quotientMap_comp_quotientMap_eq {A B A' B' : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A'] [CommRing B'] (D : LocalizationDiagram A B A' B')
    (hB' : topologicalNilradical B ≤ Ideal.comap (CompletionOver.canonicalMap D.toB')
      (topologicalNilradical (CompletionOver D.toB')))
    (hA' : topologicalNilradical A ≤ Ideal.comap (CompletionOver.canonicalMap D.toA')
      (topologicalNilradical (CompletionOver D.toA')))
    (hcm : topologicalNilradical (CompletionOver D.toB') ≤
      Ideal.comap D.completedMap (topologicalNilradical (CompletionOver D.toA')))
    (hmap : topologicalNilradical B ≤ Ideal.comap D.map (topologicalNilradical A)) :
    (Ideal.quotientMap _ D.completedMap hcm).comp
        (Ideal.quotientMap _ (CompletionOver.canonicalMap D.toB') hB')
      = (Ideal.quotientMap _ (CompletionOver.canonicalMap D.toA') hA').comp
        (Ideal.quotientMap _ D.map hmap) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
  have h := RingHom.congr_fun D.commutes x
  simp only [RingHom.comp_apply] at h
  rw [h]

/-- The canonical map from a weakly pre-admissible linearly topologized ring into the
completion of an étale algebra over it is of finite type on reductions: the reduction of the
completion is a quotient of `A' / N(A)A'`, which is of finite type over `A / N(A)`. -/
public theorem isFiniteTypeOnReductions_canonicalMap {A A' : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [CommRing A']
    (g : A →+* A') (hg : g.Etale) (hA : TopologicalRing.IsWeaklyPreAdmissible A) :
    Rig.IsFiniteTypeOnReductions (TopologicalRing.CompletionOver.canonicalMap g)
      (TopologicalRing.continuous_canonicalMap g) := by
  let J₀ : TopologicalRing.WeakIdealOfDefinitionIndex A :=
    ⟨topologicalNilradical A, isWeakIdealOfDefinition_topologicalNilradical hA⟩
  have hker : RingHom.ker (TopologicalRing.CompletionOver.projection g J₀)
      ≤ topologicalNilradical (TopologicalRing.CompletionOver g) := fun x hx ↦
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      ((TopologicalRing.projection_ker_isWeakIdealOfDefinition g J₀).2 x hx)
  obtain ⟨ψ, hψsurj, hψ⟩ := exists_desc_of_ker_le
    (TopologicalRing.CompletionOver.projection_surjective g J₀) hker
  have hcomap : topologicalNilradical A ≤ Ideal.comap g (TopologicalRing.extendedIdeal g J₀) :=
    fun _ hx ↦ Ideal.mem_map_of_mem g hx
  have hcan := topologicalNilradical_le_comap
    (TopologicalRing.CompletionOver.canonicalMap g) (TopologicalRing.continuous_canonicalMap g)
  have hquot : (Ideal.quotientMap (TopologicalRing.extendedIdeal g J₀) g hcomap).FiniteType := by
    refine RingHom.FiniteType.of_comp_finiteType
      (f := Ideal.Quotient.mk (topologicalNilradical A)) ?_
    rw [Ideal.quotientMap_comp_mk]
    exact RingHom.FiniteType.comp
      (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective)
      (RingHom.FiniteType.of_finitePresentation
        (RingHom.Etale.iff_flat_and_formallyUnramified.mp hg).2.2)
  have heq : Ideal.quotientMap (topologicalNilradical (TopologicalRing.CompletionOver g))
        (TopologicalRing.CompletionOver.canonicalMap g) hcan
      = ψ.comp (Ideal.quotientMap (TopologicalRing.extendedIdeal g J₀) g hcomap) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    rw [← TopologicalRing.CompletionOver.projection_canonicalMap g J₀ x]
    exact (RingHom.congr_fun hψ (TopologicalRing.CompletionOver.canonicalMap g x)).symm
  change (Ideal.quotientMap (topologicalNilradical (TopologicalRing.CompletionOver g))
    (TopologicalRing.CompletionOver.canonicalMap g) hcan).FiniteType
  rw [heq]
  exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective ψ hψsurj) hquot

/-- Finite type on reductions ascends along a completed étale localization diagram of countably
indexed weakly admissible rings: the first locality axiom of Situation 0CBA. -/
@[stacks 0GC2 "localization_preserves"]
public theorem finiteTypeOnReductionsProperty_localizationPreserves :
    TopologicalRing.LocalizationPreserves.{u} TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA _ _ _ hP instB instA
  obtain ⟨_, hred⟩ := hP
  refine ⟨D.continuousCompletedMap, ?_⟩
  have hB' := topologicalNilradical_le_comap
    (TopologicalRing.CompletionOver.canonicalMap D.toB')
    (TopologicalRing.continuous_canonicalMap D.toB')
  have hA' := topologicalNilradical_le_comap
    (TopologicalRing.CompletionOver.canonicalMap D.toA')
    (TopologicalRing.continuous_canonicalMap D.toA')
  have hcm := topologicalNilradical_le_comap D.completedMap D.continuousCompletedMap
  have hmap := topologicalNilradical_le_comap D.map D.continuousMap
  have hcommutes := quotientMap_comp_quotientMap_eq D hB' hA' hcm hmap
  change (Ideal.quotientMap _ D.completedMap hcm).FiniteType
  refine RingHom.FiniteType.of_comp_finiteType
    (f := Ideal.quotientMap _ (TopologicalRing.CompletionOver.canonicalMap D.toB') hB') ?_
  rw [hcommutes]
  exact RingHom.FiniteType.comp
    (isFiniteTypeOnReductions_canonicalMap D.toA' D.etaleA hA.1.1) hred

end

section

/-- A single coordinate of a product of rings is multiplicative. -/
private theorem pi_single_mul {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    [∀ i, MulZeroClass (S i)] (i : ι) (y z : S i) :
    Pi.single i (y * z) = Pi.single i y * Pi.single i z := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/-- A finite product of algebras of finite type is of finite type: adjoining the coordinate
idempotents to the coordinatewise generators generates the product. -/
private theorem algebra_finiteType_pi {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (h : ∀ i, Algebra.FiniteType R (S i)) : Algebra.FiniteType R (∀ i, S i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  choose s hs using fun i ↦ (h i).out
  refine ⟨⟨Finset.univ.biUnion fun i ↦ (insert (1 : S i) (s i)).image (Pi.single i), ?_⟩⟩
  have hmemT : ∀ (i : ι) (y : S i), y ∈ insert (1 : S i) (s i) →
      Pi.single i y ∈ Algebra.adjoin R
        ((Finset.univ.biUnion fun i ↦ (insert (1 : S i) (s i)).image (Pi.single i) :
          Finset (∀ i, S i)) : Set (∀ i, S i)) := fun i y hy ↦
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hy⟩))
  have key : ∀ (i : ι) (y : S i),
      Pi.single i y ∈ Algebra.adjoin R
        ((Finset.univ.biUnion fun i ↦ (insert (1 : S i) (s i)).image (Pi.single i) :
          Finset (∀ i, S i)) : Set (∀ i, S i)) := by
    intro i y
    have hy : y ∈ Algebra.adjoin R (s i : Set (S i)) := by rw [hs i]; exact Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem z hz => exact hmemT i z (Finset.mem_insert_of_mem hz)
    | algebraMap r =>
        have hr : Pi.single i (algebraMap R (S i) r)
            = algebraMap R (∀ j, S j) r * Pi.single i 1 := by
          funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Pi.single_eq_of_ne hj]
        rw [hr]
        exact mul_mem (Subalgebra.algebraMap_mem _ r) (hmemT i 1 (Finset.mem_insert_self _ _))
    | add u v _ _ hu hv => rw [Pi.single_add]; exact add_mem hu hv
    | mul u v _ _ hu hv => rw [pi_single_mul]; exact mul_mem hu hv
  rw [eq_top_iff]
  intro x _
  rw [show x = ∑ i, Pi.single i (x i) from (Finset.univ_sum_single x).symm]
  exact sum_mem fun i _ ↦ key i (x i)

/-- The homomorphism into a finite product of targets of finite type is of finite type. -/
private theorem finiteType_pi {B : Type*} [CommRing B] {ι : Type*} [Finite ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] (f : ∀ i, B →+* A i)
    (hf : ∀ i, (f i).FiniteType) : (RingHom.pi f).FiniteType := by
  let _ : ∀ i, Algebra B (A i) := fun i ↦ (f i).toAlgebra
  exact RingHom.finiteType_algebraMap.mpr (algebra_finiteType_pi A hf)

end

section

universe u

open TopologicalRing

/-- Finite type on reductions is preserved by a finite product of targets: the third locality
axiom of Situation 0CBA.  Topological nilpotence in a product is a coordinatewise condition, so
the reduction of the product is a quotient of the product of the reductions. -/
@[stacks 0GC2 "finite_product"]
public theorem finiteTypeOnReductionsProperty_finiteProductPreserves :
    TopologicalRing.FiniteProductPreserves.{u} TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty := by
  classical
  intro B _ _ _ _ _ _ ι _ A _ _ _ _ _ _ f hf _ _ hP instB instPi
  refine ⟨continuous_pi fun i ↦ hf i, ?_⟩
  set Φ : (∀ i, A i) →+* ∀ i, A i ⧸ topologicalNilradical (A i) :=
    RingHom.pi fun i ↦ (Ideal.Quotient.mk (topologicalNilradical (A i))).comp
      (Pi.evalRingHom A i) with hΦ
  have hΦsurj : Function.Surjective Φ := by
    intro y
    refine ⟨fun i ↦ Classical.choose (Ideal.Quotient.mk_surjective (y i)), funext fun i ↦ ?_⟩
    exact Classical.choose_spec (Ideal.Quotient.mk_surjective (y i))
  have hkerΦ : RingHom.ker Φ ≤ topologicalNilradical (∀ i, A i) := by
    intro x hx
    have hcoord : ∀ i, IsTopologicallyNilpotent (x i) := by
      intro i
      refine IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
      exact congrFun (RingHom.mem_ker.mp hx) i
    exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      (tendsto_pi_nhds.mpr fun i ↦ hcoord i)
  obtain ⟨ψ, hψsurj, hψ⟩ := exists_desc_of_ker_le hΦsurj hkerΦ
  have hNB := topologicalNilradical_le_comap (RingHom.pi f) (continuous_pi fun i ↦ hf i)
  have hNi : ∀ i, topologicalNilradical B ≤ Ideal.comap (f i) (topologicalNilradical (A i)) :=
    fun i ↦ topologicalNilradical_le_comap (f i) (hf i)
  have heq : Ideal.quotientMap _ (RingHom.pi f) hNB
      = ψ.comp (RingHom.pi fun i ↦ Ideal.quotientMap _ (f i) (hNi i)) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    have hfac : (RingHom.pi fun i ↦ Ideal.quotientMap _ (f i) (hNi i))
        (Ideal.Quotient.mk (topologicalNilradical B) x) = Φ (RingHom.pi f x) :=
      funext fun i ↦ by simp [hΦ, Ideal.quotientMap_mk]
    rw [hfac]
    exact (RingHom.congr_fun hψ (RingHom.pi f x)).symm
  change (Ideal.quotientMap _ (RingHom.pi f) hNB).FiniteType
  rw [heq]
  refine RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective ψ hψsurj)
    (finiteType_pi _ fun i ↦ ?_)
  obtain ⟨_, hi⟩ := hP i
  exact hi

end

section

universe u

/-- The reduction of an étale algebra over a linearly topologized ring by the extension of the
topological nilradical of the base is reduced: it is étale, hence smooth, over the reduction of
the base, which is reduced because the topological nilradical is a radical ideal. -/
private theorem isReduced_quotient_map_topologicalNilradical {A A' : Type u} [CommRing A]
    [TopologicalSpace A] [IsLinearTopology A A] [CommRing A'] (g : A →+* A') (hg : g.Etale) :
    IsReduced (A' ⧸ (topologicalNilradical A).map g) := by
  have : IsReduced (A ⧸ topologicalNilradical A) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp TopologicalRing.topologicalNilradical_isRadical
  have hq : (Ideal.quotientMap ((topologicalNilradical A).map g) g
      (Ideal.map_le_iff_le_comap.mp le_rfl)).Etale :=
    RingHom.Etale.isStableUnderBaseChange.quotientMap RingHom.Etale.respectsIso g hg _
  let : Algebra (A ⧸ topologicalNilradical A) (A' ⧸ (topologicalNilradical A).map g) :=
    (Ideal.quotientMap ((topologicalNilradical A).map g) g
      (Ideal.map_le_iff_le_comap.mp le_rfl)).toAlgebra
  have : Algebra.Etale (A ⧸ topologicalNilradical A)
      (A' ⧸ (topologicalNilradical A).map g) := hq.toAlgebra
  exact Algebra.isReduced_of_smooth (A ⧸ topologicalNilradical A) _

/-- The topological nilradical of the completion of an étale algebra over a weakly
pre-admissible linearly topologized ring is the kernel of the projection indexed by the
topological nilradical of the base.  One inclusion holds for every weak ideal of definition;
the other uses that the quotient by that kernel is reduced, so that the nilpotent image of a
topologically nilpotent element vanishes. -/
private theorem topologicalNilradical_completionOver {A A' : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [CommRing A']
    (g : A →+* A') (hg : g.Etale) (hA : TopologicalRing.IsWeaklyPreAdmissible A) :
    topologicalNilradical (TopologicalRing.CompletionOver g) =
      RingHom.ker (TopologicalRing.CompletionOver.projection g
        ⟨topologicalNilradical A, isWeakIdealOfDefinition_topologicalNilradical hA⟩) := by
  set J₀ : TopologicalRing.WeakIdealOfDefinitionIndex A :=
    ⟨topologicalNilradical A, isWeakIdealOfDefinition_topologicalNilradical hA⟩ with hJ₀
  have : IsReduced (A' ⧸ TopologicalRing.extendedIdeal g J₀) :=
    isReduced_quotient_map_topologicalNilradical g hg
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
      ((TopologicalRing.projection_ker_isWeakIdealOfDefinition g J₀).2 x hx))
  obtain ⟨n, hn⟩ :=
    (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).exists_pow_mem_of_mem_nhds
      ((TopologicalRing.CompletionOver.isOpen_ker_projection g J₀).mem_nhds
        (Ideal.zero_mem (RingHom.ker (TopologicalRing.CompletionOver.projection g J₀))))
  have hnil : IsNilpotent (TopologicalRing.CompletionOver.projection g J₀ x) :=
    ⟨n, by rw [← map_pow]; exact RingHom.mem_ker.mp hn⟩
  exact RingHom.mem_ker.mpr hnil.eq_zero

/-- Reduction of the canonical map into the completion of a faithfully flat étale algebra over a
weakly pre-admissible linearly topologized ring is faithfully flat and of finite presentation:
it is the base change of `A → A'` along `A → A / N(A)`, the reduction of the completion being
`A' / N(A)A'`. -/
private theorem faithfullyFlat_and_finitePresentation_quotientMap_canonicalMap
    {A A' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing A'] (g : A →+* A') (hg : g.Etale)
    (hFF : g.FaithfullyFlat) (hA : TopologicalRing.IsWeaklyPreAdmissible A)
    (h : topologicalNilradical A ≤ Ideal.comap (TopologicalRing.CompletionOver.canonicalMap g)
      (topologicalNilradical (TopologicalRing.CompletionOver g))) :
    (Ideal.quotientMap (topologicalNilradical (TopologicalRing.CompletionOver g))
        (TopologicalRing.CompletionOver.canonicalMap g) h).FaithfullyFlat ∧
      (Ideal.quotientMap (topologicalNilradical (TopologicalRing.CompletionOver g))
        (TopologicalRing.CompletionOver.canonicalMap g) h).FinitePresentation := by
  set e : TopologicalRing.CompletionOver g ⧸
        topologicalNilradical (TopologicalRing.CompletionOver g) ≃+*
      A' ⧸ (topologicalNilradical A).map g :=
    (Ideal.quotEquivOfEq (topologicalNilradical_completionOver g hg hA)).trans
      (RingHom.quotientKerEquivOfSurjective
        (TopologicalRing.CompletionOver.projection_surjective g
          ⟨topologicalNilradical A, isWeakIdealOfDefinition_topologicalNilradical hA⟩)) with he
  have hveq : e.symm.toRingHom.comp (Ideal.quotientMap ((topologicalNilradical A).map g) g
        (Ideal.map_le_iff_le_comap.mp le_rfl))
      = Ideal.quotientMap (topologicalNilradical (TopologicalRing.CompletionOver g))
        (TopologicalRing.CompletionOver.canonicalMap g) h := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    change e.symm (Ideal.Quotient.mk ((topologicalNilradical A).map g) (g a))
      = Ideal.Quotient.mk (topologicalNilradical (TopologicalRing.CompletionOver g))
        (TopologicalRing.CompletionOver.canonicalMap g a)
    rw [RingEquiv.symm_apply_eq]
    simp only [he, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
    rfl
  exact ⟨hveq ▸ RingHom.FaithfullyFlat.respectsIso.1 _ e.symm
      (RingHom.FaithfullyFlat.quotientMap g hFF (topologicalNilradical A)),
    hveq ▸ RingHom.finitePresentation_respectsIso.1 _ e.symm
      (RingHom.FinitePresentation.quotientMap g (RingHom.Etale.finitePresentation hg)
        (topologicalNilradical A))⟩

/-- Finite type on reductions descends along a completed étale localization diagram of countably
indexed weakly admissible rings whose horizontal map is faithfully flat: the second locality
axiom of Situation 0CBA.  The reduced diagonal of the diagram is of finite type, being the
reduction of the canonical map into the completion of an étale algebra followed by the reduction
of the completed morphism, and finite type descends along the faithfully flat, finitely
presented reduction of the horizontal map. -/
@[stacks 0GC2 "faithfully_flat_descent"]
public theorem finiteTypeOnReductionsProperty_faithfullyFlatDescent :
    TopologicalRing.FaithfullyFlatDescent.{u} TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D _ _ _ _ hFF hP instB instA
  obtain ⟨_, hred⟩ := hP
  refine ⟨D.continuousMap, ?_⟩
  have hcB := topologicalNilradical_le_comap
    (TopologicalRing.CompletionOver.canonicalMap D.toB')
    (TopologicalRing.continuous_canonicalMap D.toB')
  have hcA := topologicalNilradical_le_comap
    (TopologicalRing.CompletionOver.canonicalMap D.toA')
    (TopologicalRing.continuous_canonicalMap D.toA')
  have hcm := topologicalNilradical_le_comap D.completedMap D.continuousCompletedMap
  have hmap := topologicalNilradical_le_comap D.map D.continuousMap
  have hcommutes := quotientMap_comp_quotientMap_eq D hcB hcA hcm hmap
  obtain ⟨hvFF, hvFP⟩ := faithfullyFlat_and_finitePresentation_quotientMap_canonicalMap
    D.toA' D.etaleA hFF D.weaklyAdmissibleA.1 hcA
  change (Ideal.quotientMap _ D.map hmap).FiniteType
  refine RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation ?_ hvFF hvFP
  rw [← hcommutes]
  exact RingHom.FiniteType.comp hred
    (isFiniteTypeOnReductions_canonicalMap D.toB' D.etaleB D.weaklyAdmissibleB.1)

/-- Finite type on reductions is a local property of morphisms of countably indexed weakly
admissible topological rings: it ascends along completed étale localization diagrams, descends
along those whose horizontal map is faithfully flat, and is preserved by finite products of
targets. -/
@[stacks 0GC2]
public theorem isFiniteTypeOnReductions_local :
    TopologicalRing.PropertyIsLocal.{u} TopologicalRing.FiniteTypeOnReductionsProperty
      TopologicalRing.IsCountablyWeaklyAdmissible where
  localizationPreserves := finiteTypeOnReductionsProperty_localizationPreserves
  faithfullyFlatDescent := finiteTypeOnReductionsProperty_faithfullyFlatDescent
  finiteProduct := finiteTypeOnReductionsProperty_finiteProductPreserves

end

end Rig

end
