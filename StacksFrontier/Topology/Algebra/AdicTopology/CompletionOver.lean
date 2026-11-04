module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Ring.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Completion of a ring along the weak ideals of definition of a subring

Given a ring map `A →+* B` with `A` linearly topologized, the completion of `B` along the
extensions of the weak ideals of definition of `A` is the inverse limit of the discrete
quotients.  This file constructs it, shows it is a complete separated linearly topologized
ring with open projection kernels, proves the canonical map is taut, and records that the
construction stays inside the weakly admissible, countably admissible, weakly adic and adic
classes.

## References

* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0ANB](https://stacks.math.columbia.edu/tag/0ANB)
-/

@[expose] public section

namespace TopologicalRing

section

universe u v

/-- The indexing type of weak ideals of definition of a topological ring. -/
public abbrev WeakIdealOfDefinitionIndex (B : Type u) [CommRing B] [TopologicalSpace B] :=
  { J : Ideal B // TopologicalRing.IsWeakIdealOfDefinition J }

/-- The weak ideals of definition of a topological ring, ordered by reverse inclusion, are
directed: the intersection of two weak ideals of definition is again one.  Reverse inclusion
is the order in which the discrete quotients `B ⧸ J` grow, so this is what makes the inverse
system of quotients a directed diagram. -/
public theorem isDirected_weakIdealOfDefinitionIndex (B : Type u) [CommRing B]
    [TopologicalSpace B] :
    IsDirected (OrderDual (WeakIdealOfDefinitionIndex B)) (· ≤ ·) :=
  ⟨fun J K ↦ ⟨OrderDual.toDual ⟨(OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1,
      isWeakIdealOfDefinition_inf_of_isOpen_right
        (OrderDual.ofDual J).2 (OrderDual.ofDual K).2.1⟩,
    (inf_le_left : (OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1 ≤ (OrderDual.ofDual J).1),
    (inf_le_right : (OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1 ≤ (OrderDual.ofDual K).1)⟩⟩

/-- A weakly pre-admissible ring has at least one weak ideal of definition, so its index of
discrete quotients is nonempty. -/
public theorem nonempty_weakIdealOfDefinitionIndex {B : Type u} [CommRing B]
    [TopologicalSpace B] (hB : IsWeaklyPreAdmissible B) :
    Nonempty (OrderDual (WeakIdealOfDefinitionIndex B)) :=
  ⟨OrderDual.toDual ⟨hB.choose, hB.choose_spec⟩⟩

/-- Extension to `A` of a weak ideal of definition of `B`. -/
public abbrev extendedIdeal {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) : Ideal A := J.1.map f

/-- The quotient transition map attached to an inclusion of weak ideals of definition. -/
public abbrev transitionMap {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) {J K : WeakIdealOfDefinitionIndex B}
    (h : (J.1 : Ideal B) ≤ K.1) :
    A ⧸ extendedIdeal f J →+* A ⧸ extendedIdeal f K :=
  Ideal.Quotient.factor (Ideal.map_mono h)

/-- The completion of `A` over `B` is the inverse limit, over the weak ideals of definition
`J` of `B`, of the rings `A / JA`. -/
@[stacks 0AN6 "completion_over"]
public def CompletionOver {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) :
    Subring (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J) where
  carrier := { x | ∀ (J K : WeakIdealOfDefinitionIndex B) (h : (J.1 : Ideal B) ≤ K.1),
    transitionMap f h (x J) = x K }
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by intro x y hx hy J K h; simp only [Pi.add_apply, map_add, hx J K h, hy J K h]
  mul_mem' := by intro x y hx hy J K h; simp only [Pi.mul_apply, map_mul, hx J K h, hy J K h]
  neg_mem' := by intro x hx J K h; simp only [Pi.neg_apply, map_neg, hx J K h]

namespace CompletionOver

/-- The inverse-limit topology on the completion over `B`, with every quotient ring in the
defining inverse system carrying the discrete topology. -/
@[stacks 0AN6 "completion_over", instance_reducible]
public noncomputable instance limitTopology {B : Type u} {A : Type v} [CommRing B]
    [CommRing A] [TopologicalSpace B] (f : B →+* A) :
    TopologicalSpace (CompletionOver f) :=
  TopologicalSpace.induced Subtype.val <|
    @Pi.topologicalSpace (WeakIdealOfDefinitionIndex B)
      (fun J ↦ A ⧸ extendedIdeal f J) (fun _ ↦ ⊥)

/-- The inverse-limit topology makes the completion over `B` a topological ring. -/
public noncomputable instance isTopologicalRing {B : Type u} {A : Type v} [CommRing B]
    [CommRing A] [TopologicalSpace B] (f : B →+* A) :
    IsTopologicalRing (CompletionOver f) := by
  let (J : WeakIdealOfDefinitionIndex B) : TopologicalSpace (A ⧸ extendedIdeal f J) := ⊥
  let (J : WeakIdealOfDefinitionIndex B) := discreteTopology_bot (A ⧸ extendedIdeal f J)
  exact (CompletionOver f).instIsTopologicalRing

/-- Projection from the completion over `B` to one quotient in its inverse system. -/
public abbrev projection {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    CompletionOver f →+* A ⧸ extendedIdeal f J :=
  (Pi.evalRingHom (fun K : WeakIdealOfDefinitionIndex B ↦ A ⧸ extendedIdeal f K) J).comp
    (CompletionOver f).subtype

/-- The canonical ring homomorphism from `B` to the completion of `A` over `B`. -/
@[stacks 0AN6 "completion_over"]
public def canonicalMap {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) : B →+* CompletionOver f where
  toFun b := ⟨fun J ↦ Ideal.Quotient.mk (extendedIdeal f J) (f b), by
    intro J K h; exact Ideal.Quotient.factor_mk (Ideal.map_mono h) (f b)⟩
  map_one' := by ext J; simp
  map_mul' b c := by ext J; simp
  map_zero' := by ext J; simp
  map_add' b c := by ext J; simp

/-- Projection of the canonical map is the quotient class of the image in `A`. -/
@[simp]
public lemma projection_canonicalMap {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) (b : B) :
    projection f J (canonicalMap f b) = Ideal.Quotient.mk (extendedIdeal f J) (f b) :=
  rfl

/-- The canonical ring homomorphism from `A` to the completion of `A` over `B`, sending `a` to
the compatible family of its classes mod `JA`. -/
public def ofTarget {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) : A →+* CompletionOver f where
  toFun a := ⟨fun K ↦ Ideal.Quotient.mk (extendedIdeal f K) a, by
    intro J K h
    exact Ideal.Quotient.factor_mk (Ideal.map_mono h) a⟩
  map_one' := by ext K; simp
  map_mul' a b := by ext K; simp
  map_zero' := by ext K; simp
  map_add' a b := by ext K; simp

/-- Projection of `ofTarget` is reduction mod the extended ideal. -/
@[simp]
public lemma projection_ofTarget {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (K : WeakIdealOfDefinitionIndex B) (a : A) :
    projection f K (ofTarget f a) = Ideal.Quotient.mk (extendedIdeal f K) a := rfl

/-- The canonical map from the base factors through the ring being completed. -/
public lemma ofTarget_comp {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) : (ofTarget f).comp f = canonicalMap f :=
  RingHom.ext fun _ ↦ rfl

end CompletionOver

end

section

namespace CompletionOver

open TopologicalRing
open TopologicalRing.CompletionOver

universe u v

/-- The intersection of two weak ideals of definition, again a weak ideal of definition. -/
public def weakInf {B : Type u} [CommRing B] [TopologicalSpace B]
    (J K : WeakIdealOfDefinitionIndex B) : WeakIdealOfDefinitionIndex B :=
  ⟨J.1 ⊓ K.1, ⟨J.2.1.inter K.2.1, fun x hx ↦ J.2.2 x hx.1⟩⟩

/-- Below a weak ideal of definition `J` and every member of a finite set `s` of weak ideals of
definition there is a further weak ideal of definition. -/
public theorem exists_weakIdeal_le_finset {B : Type u} [CommRing B] [TopologicalSpace B]
    (J : WeakIdealOfDefinitionIndex B) (s : Finset (WeakIdealOfDefinitionIndex B)) :
    ∃ L : WeakIdealOfDefinitionIndex B, L.1 ≤ J.1 ∧ ∀ K ∈ s, L.1 ≤ K.1 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨J, le_refl _, by simp⟩
  | @insert K s hK ih =>
    obtain ⟨L, hLJ, hLs⟩ := ih
    refine ⟨weakInf L K, inf_le_left.trans hLJ, fun M hM ↦ ?_⟩
    rcases Finset.mem_insert.mp hM with rfl | hMs
    · exact inf_le_right
    · exact inf_le_left.trans (hLs M hMs)

private theorem exists_ideal_approximation {B : Type u} {A : Type v}
    [CommRing B] [CommRing A] [TopologicalSpace B] (f : B →+* A)
    (J : WeakIdealOfDefinitionIndex B) (x : CompletionOver f)
    (hx : x ∈ RingHom.ker (projection f J))
    (s : Finset (WeakIdealOfDefinitionIndex B)) :
    ∃ y ∈ J.1.map (canonicalMap f), ∀ K ∈ s, projection f K y = projection f K x := by
  obtain ⟨L, hLJ, hLs⟩ := exists_weakIdeal_le_finset J s
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.1 L)
  have hmem : a ∈ extendedIdeal f J := Ideal.Quotient.eq_zero_iff_mem.mp (by
    have h := x.2 L J hLJ
    rw [← ha] at h
    change Ideal.Quotient.mk (extendedIdeal f J) a = x.1 J at h
    exact h.trans hx)
  have hymem : ofTarget f a ∈ J.1.map (canonicalMap f) := by
    simpa only [Ideal.map_map, ofTarget_comp f] using Ideal.mem_map_of_mem (ofTarget f) hmem
  refine ⟨ofTarget f a, hymem, ?_⟩
  intro K hK
  calc
    projection f K (ofTarget f a) = transitionMap f (hLs K hK) (x.1 L) := by
      rw [show projection f K (ofTarget f a) = Ideal.Quotient.mk (extendedIdeal f K) a from rfl,
        ← ha]
      rfl
    _ = projection f K x := x.2 L K (hLs K hK)

/-- Every projection from the relative completion to a defining quotient is surjective. -/
@[stacks 0AN6 "kernel_closure"]
public theorem projection_surjective {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    Function.Surjective (projection f J) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨ofTarget f a, rfl⟩

/-- The kernel of a projection from the relative completion is open. -/
@[stacks 0AN6 "kernel_closure"]
public theorem isOpen_ker_projection {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    IsOpen (RingHom.ker (projection f J) : Set (CompletionOver f)) := by
  let (K : WeakIdealOfDefinitionIndex B) : TopologicalSpace (A ⧸ extendedIdeal f K) := ⊥
  let (K : WeakIdealOfDefinitionIndex B) : DiscreteTopology (A ⧸ extendedIdeal f K) :=
    discreteTopology_bot _
  show IsOpen ((fun x : CompletionOver f => x.1 J) ⁻¹' {0})
  exact (isOpen_discrete ({0} : Set (A ⧸ extendedIdeal f J))).preimage
    ((continuous_apply J).comp continuous_subtype_val)

/-- The kernel of a projection from the relative completion is the closure of the ideal
extended from the corresponding weak ideal of definition of the base ring. -/
@[stacks 0AN6 "kernel_closure"]
public theorem ker_projection_eq_closure {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    RingHom.ker (projection f J) = Ideal.closure (J.1.map (canonicalMap f)) := by
  let (K : WeakIdealOfDefinitionIndex B) : TopologicalSpace (A ⧸ extendedIdeal f K) := ⊥
  have hclosed : IsClosed (RingHom.ker (projection f J) : Set (CompletionOver f)) :=
    (RingHom.ker (projection f J)).toAddSubgroup.isClosed_of_isOpen
      (isOpen_ker_projection f J)
  have hmap : J.1.map (canonicalMap f) ≤ RingHom.ker (projection f J) := by
    refine Ideal.map_le_iff_le_comap.mpr fun b hb ↦ ?_
    show projection f J (canonicalMap f b) = 0
    rw [projection_canonicalMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hb)
  apply le_antisymm
  · intro x hx
    show x ∈ closure (J.1.map (canonicalMap f) : Set (CompletionOver f))
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
    have hxV : x.1 ∈ V := by simpa [← hVU] using hxU
    obtain ⟨s, W, hW, hsub⟩ := isOpen_pi_iff.mp hV x.1 hxV
    obtain ⟨y, hy, hys⟩ := exists_ideal_approximation f J x hx s
    refine ⟨y, ?_, hy⟩
    rw [← hVU]
    apply hsub
    intro K hK
    have heq : y.1 K = x.1 K := hys K hK
    rw [heq]
    exact (hW K hK).2
  · exact closure_minimal hmap hclosed

end CompletionOver

end

section

open TopologicalRing
open TopologicalRing.CompletionOver

universe u v

/-- The inverse-limit topology on a completion over `B` is linear. -/
public noncomputable instance completionOverIsLinearTopology
    {B : Type u} {A : Type v} [CommRing B] [TopologicalSpace B] [CommRing A]
    (f : B →+* A) : IsLinearTopology (CompletionOver f) (CompletionOver f) := by
  let (J : WeakIdealOfDefinitionIndex B) :
      TopologicalSpace (A ⧸ extendedIdeal f J) := ⊥
  let (J : WeakIdealOfDefinitionIndex B) :
      DiscreteTopology (A ⧸ extendedIdeal f J) :=
    discreteTopology_bot _
  let cylinderIdeal (I : Set (WeakIdealOfDefinitionIndex B)) : Ideal (CompletionOver f) :=
    ⨅ J : I, RingHom.ker (projection f J.1)
  apply IsLinearTopology.mk_of_hasBasis' (CompletionOver f) (S := Ideal (CompletionOver f))
    (p := Set.Finite) (s := cylinderIdeal) ?_ (fun I r m hm ↦ I.mul_mem_left r hm)
  rw [nhds_induced, nhds_pi]
  have h := (Filter.hasBasis_pi_pure
    ((0 : CompletionOver f).1 :
      ∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J)).comap
      (Subtype.val : CompletionOver f →
        ∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J)
  simpa only [nhds_discrete] using h.to_hasBasis
    (fun I hI ↦ ⟨I, hI, by
      intro x hx
      simpa [cylinderIdeal, projection] using hx⟩)
    (fun I hI ↦ ⟨I, hI, by
      intro x hx
      simpa [cylinderIdeal, projection] using hx⟩)

variable {B : Type u} {A : Type v}
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [CommRing A]

/-- The discrete topology on the quotient `A / JA`. -/
local instance quotientTopology (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    TopologicalSpace (A ⧸ extendedIdeal f J) := ⊥

/-- The topology on the quotient `A / JA` is discrete. -/
local instance quotientDiscreteTopology (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    DiscreteTopology (A ⧸ extendedIdeal f J) :=
  discreteTopology_bot _

/-- The discrete uniformity on the quotient `A / JA`. -/
local instance quotientUniformSpace (f : B →+* A) (J : WeakIdealOfDefinitionIndex B) :
    UniformSpace (A ⧸ extendedIdeal f J) := ⊥

omit [IsLinearTopology B B] in
private theorem continuous_canonicalMap_of_weakIdeal (f : B →+* A) :
    Continuous (canonicalMap f) := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro J
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  let : UniformSpace (A ⧸ extendedIdeal f J) :=
    IsTopologicalAddGroup.rightUniformSpace (A ⧸ extendedIdeal f J)
  let : IsUniformAddGroup (A ⧸ extendedIdeal f J) :=
    isUniformAddGroup_of_addCommGroup
  let φ : B →+* A ⧸ extendedIdeal f J :=
    (Ideal.Quotient.mk (extendedIdeal f J)).comp f
  have hsubset : J.1.toAddSubgroup ≤ AddMonoidHom.ker φ.toAddMonoidHom := fun x hx ↦
    AddMonoidHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hx))
  exact ((IsUniformAddGroup.uniformContinuous_iff_isOpen_ker (f := φ.toAddMonoidHom)).2
    (show IsOpen (AddMonoidHom.ker φ.toAddMonoidHom : Set B) from
      AddSubgroup.isOpen_mono hsubset J.2.1)).continuous

/-- The kernel of every projection to `A / JA` is a weak ideal of definition of the completion. -/
@[stacks 0AN6 "weakly_admissible"]
public theorem projection_ker_isWeakIdealOfDefinition (f : B →+* A)
    (J : WeakIdealOfDefinitionIndex B) :
    TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (projection f J)) := by
  rw [TopologicalRing.IsWeakIdealOfDefinition]
  refine ⟨isOpen_ker_projection f J, fun x hx ↦ ?_⟩
  rw [ker_projection_eq_closure f J] at hx
  exact TopologicalRing.closure_map_le_topologicalNilradical (canonicalMap f)
    (continuous_canonicalMap_of_weakIdeal f) J.1 (fun y hy ↦ J.2.2 y hy) hx

omit [IsTopologicalRing B] [IsLinearTopology B B] in
private theorem completionOver_isClosed_in_product (f : B →+* A) :
    IsClosed (CompletionOver f : Set
      (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J)) := by
  show IsClosed {x : ∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J |
    ∀ (J K : WeakIdealOfDefinitionIndex B) (h : (J.1 : Ideal B) ≤ K.1),
      transitionMap f h (x J) = x K}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun J => isClosed_iInter fun K => isClosed_iInter fun h => isClosed_eq
    ((continuous_of_discreteTopology (f := transitionMap f h)).comp (continuous_apply J))
    (continuous_apply K)

omit [IsTopologicalRing B] [IsLinearTopology B B] in
private theorem completionOver_completeSpace_aux (f : B →+* A) :
    @CompleteSpace (CompletionOver f)
      (IsTopologicalAddGroup.rightUniformSpace (CompletionOver f)) := by
  let : UniformSpace (CompletionOver f) :=
    UniformSpace.comap (Subtype.val : CompletionOver f →
      ∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J) inferInstance
  let : IsUniformAddGroup (CompletionOver f) := ⟨by
    have h := (uniformContinuous_sub.comp
      ((uniformContinuous_subtype_val.comp uniformContinuous_fst).prodMk
       (uniformContinuous_subtype_val.comp uniformContinuous_snd))).subtype_mk
      (fun p : CompletionOver f × CompletionOver f => sub_mem p.1.property p.2.property)
    convert h using 1 <;> rfl⟩
  have huniform : IsTopologicalAddGroup.rightUniformSpace (CompletionOver f) =
      (inferInstance : UniformSpace (CompletionOver f)) :=
    IsUniformAddGroup.rightUniformSpace_eq
  have hclosed := completionOver_isClosed_in_product (B := B) (A := A) f
  exact huniform.symm ▸ hclosed.completeSpace_coe

/-- Completion over a weakly admissible topological ring is weakly admissible. -/
@[stacks 0AN6 "weakly_admissible"]
public theorem completionOver_isWeaklyAdmissible (f : B →+* A)
    (hB : TopologicalRing.IsWeaklyAdmissible B) :
    TopologicalRing.IsWeaklyAdmissible (CompletionOver f) := by
  rw [TopologicalRing.IsWeaklyAdmissible]
  obtain ⟨J, hJ⟩ := hB.1
  exact ⟨⟨RingHom.ker (projection f ⟨J, hJ⟩), projection_ker_isWeakIdealOfDefinition f ⟨J, hJ⟩⟩,
    completionOver_completeSpace_aux f, inferInstance⟩

end

section

open TopologicalRing

universe u v

variable {B : Type u} {A : Type v} [CommRing B] [TopologicalSpace B]
  [CommRing A]

private theorem completionOver_closed (f : B →+* A) :
    @IsClosed (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J)
      (@Pi.topologicalSpace (WeakIdealOfDefinitionIndex B) (fun J => A ⧸ extendedIdeal f J)
        (fun _ => ⊥))
      (CompletionOver f : Set (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J)) :=
  completionOver_isClosed_in_product f

add_to_stacks 0AN6 "complete_linearly_topologized"
  TopologicalRing.completionOverIsLinearTopology

/-- The completion over a ring is complete for its canonical additive
uniformity. -/
@[stacks 0AN6 "complete_linearly_topologized"]
public noncomputable instance completeSpace_completionOver (f : B →+* A) :
    @CompleteSpace (CompletionOver f)
      (IsTopologicalAddGroup.rightUniformSpace (CompletionOver f)) := by
  let (J : WeakIdealOfDefinitionIndex B) : TopologicalSpace (A ⧸ extendedIdeal f J) := ⊥
  let (J : WeakIdealOfDefinitionIndex B) : DiscreteTopology (A ⧸ extendedIdeal f J) :=
    discreteTopology_bot _
  let (J : WeakIdealOfDefinitionIndex B) : UniformSpace (A ⧸ extendedIdeal f J) := ⊥
  let (J : WeakIdealOfDefinitionIndex B) : DiscreteUniformity (A ⧸ extendedIdeal f J) :=
    inferInstance
  let : TopologicalSpace (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J) :=
    Pi.topologicalSpace
  let : UniformSpace (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J) :=
    Pi.uniformSpace (fun J : WeakIdealOfDefinitionIndex B => A ⧸ extendedIdeal f J)
  let : IsUniformAddGroup (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J) :=
    inferInstance
  let : UniformSpace (CompletionOver f) := inferInstance
  let : IsUniformAddGroup (CompletionOver f) := (CompletionOver f).toAddSubgroup.isUniformAddGroup
  have hcomplete : @CompleteSpace (CompletionOver f) inferInstance := by
    let : IsClosed
      (CompletionOver f : Set (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J)) :=
      completionOver_closed f
    exact IsClosed.completeSpace_coe
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact hcomplete

/-- The inverse-limit topology on the completion is separated. -/
@[stacks 0AN6 "complete_linearly_topologized"]
public noncomputable instance t2Space_completionOver (f : B →+* A) :
    T2Space (CompletionOver f) := by
  let (J : WeakIdealOfDefinitionIndex B) : TopologicalSpace (A ⧸ extendedIdeal f J) := ⊥
  let (J : WeakIdealOfDefinitionIndex B) : DiscreteTopology (A ⧸ extendedIdeal f J) :=
    discreteTopology_bot _
  let : TopologicalSpace (∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J) :=
    Pi.topologicalSpace
  infer_instance

end

section

open TopologicalRing
open TopologicalRing.CompletionOver
open Filter

universe u v

/-- The canonical map to the completion over a topological ring is continuous. -/
@[stacks 0AN6 "taut"]
public theorem continuous_canonicalMap {B : Type u} {A : Type v}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
    (f : B →+* A) : Continuous (canonicalMap f) :=
  continuous_canonicalMap_of_weakIdeal f

private theorem exists_weakIdeal_le_open_ideal {B : Type u} [CommRing B]
    [TopologicalSpace B] (hB : TopologicalRing.IsWeaklyPreAdmissible B)
    (I : Ideal B) (hI : IsOpen (I : Set B)) :
    ∃ J : WeakIdealOfDefinitionIndex B, J.1 ≤ I := by
  obtain ⟨J, hJ⟩ := hB
  exact ⟨⟨J ⊓ I, hJ.1.inter hI, fun x hx => hJ.2 x hx.1⟩, inf_le_right⟩

/-- The kernel of the projection to `A / JA` shrinks with `J`: if `J ≤ K` then the kernel at `J`
lies in the kernel at `K`. -/
theorem ker_projection_mono {B : Type u} {A : Type v}
    [CommRing B] [CommRing A] [TopologicalSpace B] (f : B →+* A)
    {J K : WeakIdealOfDefinitionIndex B} (h : J.1 ≤ K.1) :
  RingHom.ker (projection f J) ≤ RingHom.ker (projection f K) := by
  intro x hx
  change x.1 J = 0 at hx
  show x.1 K = 0
  simp [← x.2 J K h, hx]

private def cylinderSet {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    [TopologicalSpace B] (f : B →+* A) (S : Set (WeakIdealOfDefinitionIndex B)) :
    Set (CompletionOver f) :=
  {x | ∀ J : S, projection f J.1 x = 0}

/-- The canonical map to the completion over a weakly preadmissible ring is taut. -/
@[stacks 0AN6 "taut"]
public theorem isTaut_canonicalMap {B : Type u} {A : Type v}
    [CommRing B] [TopologicalSpace B] [CommRing A]
    (f : B →+* A) (hB : TopologicalRing.IsWeaklyPreAdmissible B) :
    RingHom.IsTaut (canonicalMap f) := by
  constructor
  · intro I hI
    obtain ⟨J, hJI⟩ := exists_weakIdeal_le_open_ideal hB I hI
    refine Ideal.isOpen_of_isOpen_subideal ?_ (isOpen_ker_projection f J)
    rw [ker_projection_eq_closure]
    exact closure_mono (Ideal.map_mono hJI)
  · let (J : WeakIdealOfDefinitionIndex B) :
        TopologicalSpace (A ⧸ extendedIdeal f J) := ⊥
    let (J : WeakIdealOfDefinitionIndex B) :
        DiscreteTopology (A ⧸ extendedIdeal f J) := discreteTopology_bot _
    have hProductBasis : (nhds (0 : CompletionOver f)).HasBasis Set.Finite
        (fun S : Set (WeakIdealOfDefinitionIndex B) =>
          cylinderSet f S) := by
      rw [nhds_induced, nhds_pi]
      have h := (Filter.hasBasis_pi_pure
        ((0 : CompletionOver f).1 :
          ∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J)).comap
          (Subtype.val : CompletionOver f →
            ∀ J : WeakIdealOfDefinitionIndex B, A ⧸ extendedIdeal f J)
      simpa only [nhds_discrete] using h.to_hasBasis
        (fun S hS => ⟨S, hS, by
          intro x hx
          simpa [cylinderSet, projection] using hx⟩)
        (fun S hS => ⟨S, hS, by
          intro x hx
          simpa [cylinderSet, projection] using hx⟩)
    obtain ⟨I₀, hI₀⟩ := hB
    refine Filter.HasBasis.mk fun U ↦ ⟨fun hU ↦ ?_, ?_⟩
    · obtain ⟨S, hS, hsub⟩ := hProductBasis.mem_iff.mp hU
      obtain ⟨J, -, hJS⟩ := exists_weakIdeal_le_finset ⟨I₀, hI₀⟩ hS.toFinset
      refine ⟨J.1, J.2.1, ?_⟩
      rw [← ker_projection_eq_closure]
      exact fun x hx ↦ hsub fun K ↦ ker_projection_mono f (hJS K.1 (by simp)) hx
    · rintro ⟨I, hI, hIU⟩
      obtain ⟨J, hJI⟩ := exists_weakIdeal_le_open_ideal ⟨I₀, hI₀⟩ I hI
      refine Filter.mem_of_superset ((isOpen_ker_projection f J).mem_nhds (Ideal.zero_mem _)) ?_
      rw [ker_projection_eq_closure]
      exact (closure_mono (Ideal.map_mono hJI)).trans hIU

end

section

open TopologicalRing RingHom
open Filter

/-- Completion over a weakly admissible ring with a countable fundamental system of open
ideals again has a countable fundamental system of open ideals. -/
@[stacks 0ANB "completion_in_sub_countable"]
public lemma completionOver_isCountablyGenerated_nhds_zero
    {B A : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] (f : B →+* A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hBcount : (nhds (0 : B)).IsCountablyGenerated) :
    (nhds (0 : CompletionOver f)).IsCountablyGenerated :=
  isCountablyGenerated_nhds_zero_of_isTaut (CompletionOver.canonicalMap f)
    (continuous_canonicalMap f) (isTaut_canonicalMap f hB.1) hBcount

end

section

open TopologicalRing
  TopologicalRing RingHom Filter

/-- Membership in the full subcategory `WAdm^cic` of weakly admissible rings. -/
public abbrev IsCountablyAdmissible (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] : Prop :=
  TopologicalRing.IsWeaklyAdmissible R ∧ TopologicalRing.IsAdmissible R ∧
    (nhds (0 : R)).IsCountablyGenerated

/-- Completion over a countably admissible ring is again countably admissible. -/
@[stacks 0ANB "completion_in_sub_cic"]
public theorem completionOver_isCountablyAdmissible
    {B A : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] (f : B →+* A)
    (hB : IsCountablyAdmissible B) :
    IsCountablyAdmissible (CompletionOver f) := by
  rcases hB with ⟨hBweak, hBadm, hBcount⟩
  exact ⟨completionOver_isWeaklyAdmissible f hBweak,
    ⟨isPreAdmissible_of_isTaut (CompletionOver.canonicalMap f)
      (continuous_canonicalMap f) (isTaut_canonicalMap f hBweak.1) hBadm.1,
      ⟨inferInstance, inferInstance⟩⟩,
    completionOver_isCountablyGenerated_nhds_zero f hBweak hBcount⟩

end

section

open TopologicalRing

/-- Completion relative to a weakly admissible, weakly adic ring is weakly adic. -/
@[stacks 0ANB "completion_in_sub_weakly_adic"]
public theorem completionOver_isWeaklyAdic
    {B A : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A] (f : B →+* A)
    (hB : TopologicalRing.IsWeaklyAdmissible B) [TopologicalRing.IsWeaklyAdic B] :
    TopologicalRing.IsWeaklyAdic (CompletionOver f) := by
  have h := TopologicalRing.completionOver_isWeaklyAdmissible f hB
  refine { toIsWeaklyPreAdic := ?_, toT2Space := h.2.2, completeSpace := h.2.1 }
  exact TopologicalRing.isWeaklyPreAdic_of_isTaut (CompletionOver.canonicalMap f)
    (TopologicalRing.continuous_canonicalMap f)
    (TopologicalRing.isTaut_canonicalMap f hB.1)

end

section

open TopologicalRing

/-- Completion relative to a weakly admissible adic-star ring is again adic-star: its
topology is defined by a finitely generated ideal. -/
@[stacks 0ANB "completion_in_sub_adic_star"]
public theorem completionOver_exists_fg_isAdic
    {B A : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] [CommRing A]
    (f : B →+* A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hB_adicStar : ∃ I : Ideal B, I.FG ∧ _root_.IsAdic I) :
    ∃ J : Ideal (CompletionOver f), J.FG ∧ _root_.IsAdic J :=
  RingHom.exists_fg_ideal_isAdic_of_isTaut (CompletionOver.canonicalMap f)
    (TopologicalRing.continuous_canonicalMap f) (TopologicalRing.isTaut_canonicalMap f hB.1)
    hB_adicStar

end

end TopologicalRing

end
