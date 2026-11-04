module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CompletionPointTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowupStepSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.SingularPointSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.EmbeddingDimensionThree
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUpsAssembly

/-!
# The termination order for blowing up rational double points

Section 54.12 of the source resolves a rational double point by repeatedly blowing up singular
points, and proves that the process stops by producing, from an infinite process, an infinite
sequence of blowups whose exceptional divisors are cut out by the transforms of one element,
over the completion `A^` ([Stacks, Tag 0BG2], [Stacks, Tag 0BG3]).

This file turns that argument into a well-founded relation. Singular points are measured by the
isomorphism class of the completion of their local ring. The relation
`AlgebraicGeometry.blowUpSingularRel` says that one class comes from a singular point of the
blowup of the spectrum of the ring of a Situation [Stacks, Tag 0BGC] in its maximal ideal, the
ring having the other class. Its predecessors are read off any representative
(`AlgebraicGeometry.exists_mem_singularLocus_of_blowUpSingularRel`): the singular points of the
blowups of two Situations with isomorphic completions correspond, through the completion
([Stacks, Tag 0805], [Stacks, Tag 0BG5]).

The engine is `AlgebraicGeometry.acc_completionClass_of_descent`: a property of an element of a
local ring which is carried by every singular point of the blowup that is not already known to
be accessible, together with the conditions of `AlgebraicGeometry.PointBlowupStep` (residue
field unchanged, exceptional divisor cut out by the element), makes the class of the ring
accessible. An infinite descent would otherwise produce a rule for choosing centres over the
completion, contradicting `AlgebraicGeometry.exists_isRegularLocalRing_of_pointBlowupStep`.

## Main definitions

* `AlgebraicGeometry.completionClass`: the isomorphism class of the completion of a local ring.
* `AlgebraicGeometry.blowUpSingularRel`: the termination relation.

## Main results

* `AlgebraicGeometry.exists_mem_singularLocus_of_blowUpSingularRel`: the predecessors of the
  class of a Situation 0BGC are the classes of the singular points of its blowup.
* `AlgebraicGeometry.acc_completionClass_of_descent`: the termination engine.

## References

* [Stacks Project, Tag 0BG2](https://stacks.math.columbia.edu/tag/0BG2)
* [Stacks Project, Tag 0BG3](https://stacks.math.columbia.edu/tag/0BG3)
* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The isomorphism class of the completion of a local ring along its maximal ideal. -/
def completionClass (R : Type u) [CommRing R] [IsLocalRing R] :
    Quotient (isIsomorphicSetoid CommRingCat.{u}) :=
  Quotient.mk _ (CommRingCat.of (AdicCompletion (maximalIdeal R) R))

/-- Isomorphic local rings have the same completion class. -/
theorem completionClass_eq_of_ringEquiv {R R' : Type u} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (e : R ≃+* R') : completionClass R = completionClass R' := by
  have e' := Stacks.LocalCohomology.adicCompletionRingEquivCongr e (maximalIdeal R)
  rw [IsLocalRing.map_ringEquiv_maximalIdeal] at e'
  exact Quotient.sound ⟨e'.toCommRingCatIso⟩

/-- Local rings with isomorphic completions have the same completion class. -/
theorem completionClass_eq_of_adicCompletion_ringEquiv {R R' : Type u} [CommRing R]
    [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (e : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal R') R') :
    completionClass R = completionClass R' :=
  Quotient.sound ⟨e.toCommRingCatIso⟩

/-- Equal completion classes come from isomorphic completions. -/
theorem nonempty_ringEquiv_of_completionClass_eq {R R' : Type u} [CommRing R]
    [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (h : completionClass R = completionClass R') :
    Nonempty (AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal R') R') := by
  obtain ⟨e⟩ := Quotient.exact h
  exact ⟨e.commRingCatIsoToRingEquiv⟩

/-- The completion of a Noetherian local ring has the completion class of the ring. -/
theorem completionClass_adicCompletion (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    completionClass (AdicCompletion (maximalIdeal R) R) = completionClass R := by
  have := isAdicComplete_maximalIdeal_adicCompletion R
  exact completionClass_eq_of_adicCompletion_ringEquiv
    (AdicCompletion.ofAlgEquiv (maximalIdeal (AdicCompletion (maximalIdeal R) R))).toRingEquiv.symm

/-- Regularity of a Noetherian local ring depends only on its completion class
([Stacks, Tag 07NY]). -/
theorem isRegularLocalRing_iff_of_completionClass_eq {R R' : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    (h : completionClass R = completionClass R') :
    IsRegularLocalRing R ↔ IsRegularLocalRing R' := by
  obtain ⟨e⟩ := nonempty_ringEquiv_of_completionClass_eq h
  rw [isRegularLocalRing_iff_adicCompletion_maximalIdeal,
    isRegularLocalRing_iff_adicCompletion_maximalIdeal (A := R')]
  exact ⟨fun _ => .of_ringEquiv e, fun _ => .of_ringEquiv e.symm⟩

/-! ### The blowup of a Situation 0BGC: singular points are closed -/

namespace RationalDoublePointSituation

/-- The blowup of `Spec(A)` in the maximal ideal is locally Noetherian. -/
theorem isLocallyNoetherian_blowUp (S : RationalDoublePointSituation.{u}) :
    IsLocallyNoetherian (blowUp (maximalIdealSheaf S.A)) :=
  LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf S.A))

/-- **A singular point of the blowup of a Situation 0BGC is closed.** -/
theorem isClosed_of_mem_singularLocus_blowUp (S : RationalDoublePointSituation.{u})
    (q : blowUp (maximalIdealSheaf S.A))
    (hq : q ∈ singularLocus (blowUp (maximalIdealSheaf S.A))) :
    IsClosed ({q} : Set (blowUp (maximalIdealSheaf S.A))) := by
  have := S.isLocallyNoetherian_blowUp
  have := S.isNormal_blowUp
  have hdim : topologicalKrullDim (blowUp (maximalIdealSheaf S.A)) ≤ 2 := by
    rw [topologicalKrullDim_eq_of_isModification_spec S.A _ S.isModification_blowUpToBase,
      S.dimension_two]
  exact isClosed_singleton_of_mem_singularLocus _ hdim q hq

/-- A singular point of the blowup of a Situation 0BGC lies over the closed point. -/
theorem blowUpToBase_eq_closedPoint_of_mem_singularLocus (S : RationalDoublePointSituation.{u})
    (q : blowUp (maximalIdealSheaf S.A))
    (hq : q ∈ singularLocus (blowUp (maximalIdealSheaf S.A))) :
    blowUpToBase (maximalIdealSheaf S.A) q = IsLocalRing.closedPoint S.A :=
  blowUpToBase_eq_closedPoint_of_isClosed S.A q (S.isClosed_of_mem_singularLocus_blowUp q hq)

/-- **The local ring at a singular point of the blowup of a Situation 0BGC is again the ring of a
Situation 0BGC.** -/
theorem exists_situation_of_mem_singularLocus_blowUp (S : RationalDoublePointSituation.{u})
    (q : blowUp (maximalIdealSheaf S.A))
    (hq : q ∈ singularLocus (blowUp (maximalIdealSheaf S.A))) :
    ∃ S' : RationalDoublePointSituation.{u},
      Nonempty (S'.A ≃+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk q) := by
  obtain ⟨x, hx⟩ := S.exists_span_range_eq_maximalIdeal
  exact ⟨S.singularPointSituation x hx q (S.isClosed_of_mem_singularLocus_blowUp q hq) hq,
    ⟨RingEquiv.refl _⟩⟩

end RationalDoublePointSituation

/-! ### The termination relation -/

/-- **The termination relation.** `blowUpSingularRel a' a` says that `a` is the completion class
of the ring of a Situation [Stacks, Tag 0BGC] and `a'` the completion class of the local ring at
a singular point of the blowup of its spectrum in the maximal ideal. -/
def blowUpSingularRel (a' a : Quotient (isIsomorphicSetoid CommRingCat.{u})) : Prop :=
  ∃ (S : RationalDoublePointSituation.{u}) (q : blowUp (maximalIdealSheaf S.A)),
    completionClass S.A = a ∧ q ∈ singularLocus (blowUp (maximalIdealSheaf S.A)) ∧
      completionClass ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk q) = a'

/-- **The predecessors of the class of a Situation 0BGC are the classes of the singular points of
its own blowup.** -/
theorem exists_mem_singularLocus_of_blowUpSingularRel (S : RationalDoublePointSituation.{u})
    {a' : Quotient (isIsomorphicSetoid CommRingCat.{u})}
    (h : blowUpSingularRel a' (completionClass S.A)) :
    ∃ z ∈ singularLocus (blowUp (maximalIdealSheaf S.A)),
      completionClass ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z) = a' := by
  obtain ⟨S', q', hcls, hq', rfl⟩ := h
  have := S.isLocallyNoetherian_blowUp
  have := S'.isLocallyNoetherian_blowUp
  obtain ⟨y, hy, ⟨e₁⟩⟩ := exists_blowUp_adicCompletion_point_of_blowUp S'.A q'
    (S'.blowUpToBase_eq_closedPoint_of_mem_singularLocus q' hq')
  obtain ⟨ε⟩ := nonempty_ringEquiv_of_completionClass_eq hcls
  obtain ⟨w, hw, ⟨e₂⟩⟩ := exists_blowUp_point_of_ringEquiv ε y hy
  obtain ⟨z, hz, ⟨e₃⟩⟩ := exists_blowUp_point_of_blowUp_adicCompletion S.A w hw
  have hclass : completionClass ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z) =
      completionClass ((blowUp (maximalIdealSheaf S'.A)).presheaf.stalk q') :=
    ((completionClass_eq_of_adicCompletion_ringEquiv e₃).trans
      (completionClass_eq_of_ringEquiv e₂)).trans
        (completionClass_eq_of_adicCompletion_ringEquiv e₁).symm
  exact ⟨z, fun hreg => hq' ((isRegularLocalRing_iff_of_completionClass_eq hclass).mp hreg),
    hclass⟩

/-- **A Situation 0BGC whose blowup has no singular point has an accessible class.** -/
theorem acc_completionClass_of_singularLocus_eq_empty (S : RationalDoublePointSituation.{u})
    (h : singularLocus (blowUp (maximalIdealSheaf S.A)) = ∅) :
    Acc blowUpSingularRel (completionClass S.A) := by
  refine Acc.intro _ fun a' ha' => ?_
  obtain ⟨z, hz, -⟩ := exists_mem_singularLocus_of_blowUpSingularRel S ha'
  simp [h] at hz

/-! ### The termination engine -/

/-- Surjectivity on residue fields transports along a compatible isomorphism of the targets. -/
theorem surjective_residue_of_ringEquiv {R O O' : Type*} [CommRing R] [CommRing O]
    [IsLocalRing O] [CommRing O'] [IsLocalRing O'] (ψ : R →+* O) (ε : O ≃+* O') (φ : R →+* O')
    (hcomp : ∀ a, ε (ψ a) = φ a)
    (h : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal O')).comp φ)) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal O)).comp ψ) := by
  intro t
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨a, ha⟩ := h (Ideal.Quotient.mk _ (ε y))
  refine ⟨a, ?_⟩
  simp only [RingHom.comp_apply, Ideal.Quotient.eq] at ha ⊢
  rw [← hcomp, ← map_sub] at ha
  have : IsLocalHom (ε : O →+* O') := IsLocalHom.of_surjective _ ε.surjective
  rwa [← IsLocalRing.maximalIdeal_comap (ε : O →+* O')]

/-- The exceptional condition transports along a compatible isomorphism of the targets. -/
theorem map_maximalIdeal_eq_span_of_ringEquiv {R O O' : Type*} [CommRing R]
    [IsLocalRing R] [CommRing O] [CommRing O'] (ψ : R →+* O) (ε : O ≃+* O') (φ : R →+* O')
    (hcomp : ∀ a, ε (ψ a) = φ a) (x : R)
    (h : Ideal.map φ (maximalIdeal R) = Ideal.span {φ x}) :
    Ideal.map ψ (maximalIdeal R) = Ideal.span {ψ x} := by
  have hψ : ψ = (ε.symm : O' →+* O).comp φ := RingHom.ext fun a => by simp [← hcomp]
  rw [hψ, ← Ideal.map_map, h, Ideal.map_span, Set.image_singleton]
  rfl

/-- Transport of the maximal ideal of a local ring along an equality of points. -/
private theorem eqRec_maximalIdeal_stalk {X : Scheme.{u}} {x x' : X} (h : x = x') :
    (h ▸ maximalIdeal (X.presheaf.stalk x) : Ideal (X.presheaf.stalk x')) =
      maximalIdeal (X.presheaf.stalk x') := by
  subst h
  rfl

/-- The property carried along the blowup sequence of the termination engine: the local ring is
the ring of a Situation [Stacks, Tag 0BGC], the element satisfies `Inv`, and the class of the ring
is not accessible. -/
abbrev descentStagePred (Inv : ∀ (R : Type u) [CommRing R] [IsLocalRing R], R → Prop) :
    (Y : Scheme.{u}) → (q : Y) → Y.presheaf.stalk q → Prop := fun Y q e =>
  (∃ S' : RationalDoublePointSituation.{u}, Nonempty (S'.A ≃+* Y.presheaf.stalk q)) ∧
    Inv (Y.presheaf.stalk q) e ∧
    ¬ Acc blowUpSingularRel (completionClass (Y.presheaf.stalk q))

/-- Under the descent hypothesis, every stage of the termination engine admits a blowup point
satisfying the conditions of `AlgebraicGeometry.PointBlowupStep`. -/
theorem exists_blowUp_point_of_descentStage
    (Inv : ∀ (R : Type u) [CommRing R] [IsLocalRing R], R → Prop)
    (hiso : ∀ (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
      (e : R ≃+* R') (x : R), Inv R x → Inv R' (e x))
    (hdesc : ∀ (S : RationalDoublePointSituation.{u}) (x : S.A), Inv S.A x →
      ∀ z ∈ singularLocus (blowUp (maximalIdealSheaf S.A)),
        Acc blowUpSingularRel
            (completionClass ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)) ∨
          (Function.Surjective ((Ideal.Quotient.mk (maximalIdeal
              ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z))).comp
                (maximalIdealBlowUpStalkHom S.A z)) ∧
            Ideal.map (maximalIdealBlowUpStalkHom S.A z) (maximalIdeal S.A) =
              Ideal.span {maximalIdealBlowUpStalkHom S.A z x} ∧
            Inv ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)
              (maximalIdealBlowUpStalkHom S.A z x)))
    (d : PointBlowupStage.{u} (descentStagePred Inv)) : ∃ q : blowUp d.centre,
      ∃ hq : blowUpToBase d.centre q = d.point,
        IsClosed ({q} : Set (blowUp d.centre)) ∧
        IsIso ((blowUpToBase d.centre).residueFieldMap q) ∧
        Ideal.map ((blowUpToBase d.centre).stalkMap q).hom
            (hq.symm ▸ maximalIdeal (d.scheme.presheaf.stalk d.point)) =
          Ideal.span {((blowUpToBase d.centre).stalkMap q).hom (hq.symm ▸ d.elem)} ∧
        descentStagePred Inv (blowUp d.centre) q
          (((blowUpToBase d.centre).stalkMap q).hom (hq.symm ▸ d.elem)) := by
  obtain ⟨⟨S', ⟨ε⟩⟩, hinv, hnacc⟩ := d.prop
  obtain ⟨a', hr, hna⟩ : ∃ a', blowUpSingularRel a' (completionClass S'.A) ∧
      ¬ Acc blowUpSingularRel a' := by
    rw [completionClass_eq_of_ringEquiv ε]
    by_contra hall
    push Not at hall
    exact hnacc (Acc.intro _ hall)
  obtain ⟨z, hz, rfl⟩ := exists_mem_singularLocus_of_blowUpSingularRel S' hr
  obtain ⟨hsurj, hexc, hinvz⟩ :=
    (hdesc S' (ε.symm d.elem) (hiso _ _ ε.symm _ hinv) z hz).resolve_left hna
  obtain ⟨q, hq, ε'', hcomp, hclosed⟩ : ∃ (q : blowUp d.centre)
      (hq : blowUpToBase d.centre q = d.point)
      (ε'' : (blowUp d.centre).presheaf.stalk q ≃+*
        (blowUp (maximalIdealSheaf S'.A)).presheaf.stalk z),
      (∀ a : S'.A, ε'' (((blowUpToBase d.centre).stalkMap q).hom (hq.symm ▸ ε a)) =
        maximalIdealBlowUpStalkHom S'.A z a) ∧
      (IsClosed ({z} : Set (blowUp (maximalIdealSheaf S'.A))) →
        IsClosed ({q} : Set (blowUp d.centre))) :=
    exists_blowUp_point_of_maximalIdealSheaf S'.A d.point d.point_closed ε z
      (S'.blowUpToBase_eq_closedPoint_of_mem_singularLocus z hz)
  let ψ : S'.A →+* (blowUp d.centre).presheaf.stalk q :=
    ((blowUpToBase d.centre).stalkMap q).hom.comp
      (((d.scheme.presheaf.stalkCongr (.of_eq hq.symm)).hom.hom).comp (ε : S'.A →+* _))
  have hψ : ∀ a, ε'' (ψ a) = maximalIdealBlowUpStalkHom S'.A z a := by
    intro a
    rw [← hcomp a, eqRec_stalk_eq_stalkCongr]
    rfl
  have helem : d.elem = ε (ε.symm d.elem) := (ε.apply_symm_apply _).symm
  refine ⟨q, hq, hclosed (S'.isClosed_of_mem_singularLocus_blowUp z hz), ?_, ?_, ?_⟩
  · refine isIso_residueFieldMap_of_surjective_stalkMap_residue _ q fun t => ?_
    obtain ⟨y, rfl⟩ := (blowUp d.centre).residue_surjective q t
    obtain ⟨a, ha⟩ := surjective_residue_of_ringEquiv ψ ε'' _ hψ hsurj (Ideal.Quotient.mk _ y)
    exact ⟨(d.scheme.presheaf.stalkCongr (.of_eq hq.symm)).hom (ε a), ha⟩
  · rw [eqRec_maximalIdeal_stalk, helem, eqRec_stalk_eq_stalkCongr]
    have hm : maximalIdeal (d.scheme.presheaf.stalk
        (blowUpToBase d.centre q)) =
        Ideal.map (((d.scheme.presheaf.stalkCongr (.of_eq hq.symm)).hom.hom).comp
          (ε : S'.A →+* _)) (maximalIdeal S'.A) :=
      (map_ringEquiv_maximalIdeal
        (ε.trans (d.scheme.presheaf.stalkCongr (.of_eq hq.symm)).commRingCatIsoToRingEquiv)).symm
    rw [hm, Ideal.map_map]
    exact map_maximalIdeal_eq_span_of_ringEquiv ψ ε'' _ hψ _ hexc
  · obtain ⟨Sz, ⟨εz⟩⟩ := S'.exists_situation_of_mem_singularLocus_blowUp z hz
    refine ⟨⟨Sz, ⟨εz.trans ε''.symm⟩⟩, ?_, ?_⟩
    · have h := hiso _ _ ε''.symm _ hinvz
      rw [← hψ, RingEquiv.symm_apply_apply] at h
      rwa [helem, eqRec_stalk_eq_stalkCongr]
    · rwa [completionClass_eq_of_ringEquiv ε'']

/-- **The termination engine.** Let `Inv` be a property of an element of a local ring,
invariant under ring isomorphisms, preserved by passing to the completion, and implying that the
element lies in the maximal ideal. Suppose that for every Situation [Stacks, Tag 0BGC] and every
element with `Inv`, each singular point of the blowup in the maximal ideal either has an
accessible class, or has residue field `κ`, has its exceptional divisor cut out by the element,
and carries `Inv` for the image of the element. Then every Situation 0BGC with an element
satisfying `Inv` has an accessible class. -/
theorem acc_completionClass_of_descent
    (Inv : ∀ (R : Type u) [CommRing R] [IsLocalRing R], R → Prop)
    (hiso : ∀ (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
      (e : R ≃+* R') (x : R), Inv R x → Inv R' (e x))
    (hcompl : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R),
      Inv R x → Inv (AdicCompletion (maximalIdeal R) R) (algebraMap _ _ x))
    (hmem : ∀ (R : Type u) [CommRing R] [IsLocalRing R] (x : R), Inv R x → x ∈ maximalIdeal R)
    (hdesc : ∀ (S : RationalDoublePointSituation.{u}) (x : S.A), Inv S.A x →
      ∀ z ∈ singularLocus (blowUp (maximalIdealSheaf S.A)),
        Acc blowUpSingularRel
            (completionClass ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)) ∨
          (Function.Surjective ((Ideal.Quotient.mk (maximalIdeal
              ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z))).comp
                (maximalIdealBlowUpStalkHom S.A z)) ∧
            Ideal.map (maximalIdealBlowUpStalkHom S.A z) (maximalIdeal S.A) =
              Ideal.span {maximalIdealBlowUpStalkHom S.A z x} ∧
            Inv ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)
              (maximalIdealBlowUpStalkHom S.A z x)))
    (S : RationalDoublePointSituation.{u}) (x : S.A) (hx : Inv S.A x) :
    Acc blowUpSingularRel (completionClass S.A) := by
  by_contra hacc
  let C := S.completion
  let eC : C.A ≃+* C.base.presheaf.stalk C.closedPoint :=
    (stalkClosedPointIso (.of C.A)).commRingCatIsoToRingEquiv.symm
  let xC : C.A := algebraMap S.A (AdicCompletion (maximalIdeal S.A) S.A) x
  have hxC : Inv C.A xC := hcompl S.A x hx
  have hcls : completionClass (C.base.presheaf.stalk C.closedPoint) = completionClass S.A :=
    (completionClass_eq_of_ringEquiv eC).symm.trans (completionClass_adicCompletion S.A)
  let d₀ : PointBlowupStage.{u} (descentStagePred Inv) :=
    { scheme := C.base
      point := C.closedPoint
      point_closed := IsLocalRing.isClosed_singleton_closedPoint C.A
      elem := eC xC
      prop := ⟨⟨C, ⟨eC⟩⟩, hiso _ _ eC _ hxC, by rwa [hcls]⟩ }
  have hmem₀ : d₀.elem ∈ maximalIdeal (d₀.scheme.presheaf.stalk d₀.point) := by
    change eC xC ∈ _
    rw [← map_ringEquiv_maximalIdeal eC]
    exact Ideal.mem_map_of_mem _ (hmem _ _ hxC)
  obtain ⟨Y, q, y, ⟨⟨S'', ⟨ε⟩⟩, -, -⟩, hreg⟩ :=
    exists_isRegularLocalRing_of_pointBlowupStep C.A C.dimension_two
      (PointBlowupStep.ofForallExists
        (exists_blowUp_point_of_descentStage Inv hiso hdesc)) d₀ (Iso.refl _) rfl hmem₀
  exact S''.not_isRegularLocalRing (IsRegularLocalRing.of_ringEquiv ε.symm)

/-- **Termination from a levelled descent.** Let `Inv n` be, for every level `n`, a property of an
element of a local ring, invariant under ring isomorphisms, preserved by passing to the
completion and implying that the element lies in the maximal ideal. Suppose that every singular
point of the blowup of a Situation [Stacks, Tag 0BGC] whose ring carries an element with
`Inv n` either is a Situation 0BGC whose own blowup is regular or carries an element at a lower
level, or has residue field `κ`, has its exceptional divisor cut out by the element and carries
its image at level `n`; and that every Situation 0BGC has a regular blowup or an element at some
level. Then the completion class of every Situation 0BGC is accessible. -/
theorem acc_completionClass_of_levels
    (Inv : ℕ → ∀ (R : Type u) [CommRing R] [IsLocalRing R], R → Prop)
    (hiso : ∀ (n : ℕ) (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
      (e : R ≃+* R') (x : R), Inv n R x → Inv n R' (e x))
    (hcompl : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R),
      Inv n R x → Inv n (AdicCompletion (maximalIdeal R) R) (algebraMap _ _ x))
    (hmem : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] (x : R),
      Inv n R x → x ∈ maximalIdeal R)
    (hstep : ∀ (n : ℕ) (S : RationalDoublePointSituation.{u}) (x : S.A), Inv n S.A x →
      ∀ z ∈ singularLocus (blowUp (maximalIdealSheaf S.A)),
        (∃ S' : RationalDoublePointSituation.{u},
            Nonempty (S'.A ≃+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk z) ∧
            (singularLocus (blowUp (maximalIdealSheaf S'.A)) = ∅ ∨
              ∃ i < n, ∃ y : S'.A, Inv i S'.A y)) ∨
          (Function.Surjective ((Ideal.Quotient.mk (maximalIdeal
              ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z))).comp
                (maximalIdealBlowUpStalkHom S.A z)) ∧
            Ideal.map (maximalIdealBlowUpStalkHom S.A z) (maximalIdeal S.A) =
              Ideal.span {maximalIdealBlowUpStalkHom S.A z x} ∧
            Inv n ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk z)
              (maximalIdealBlowUpStalkHom S.A z x)))
    (hall : ∀ S : RationalDoublePointSituation.{u},
      singularLocus (blowUp (maximalIdealSheaf S.A)) = ∅ ∨ ∃ (n : ℕ) (x : S.A), Inv n S.A x)
    (S : RationalDoublePointSituation.{u}) : Acc blowUpSingularRel (completionClass S.A) := by
  have hlevel : ∀ n (S : RationalDoublePointSituation.{u}) (x : S.A), Inv n S.A x →
      Acc blowUpSingularRel (completionClass S.A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S x hx
      refine acc_completionClass_of_descent (Inv n) (hiso n) (hcompl n) (hmem n)
        (fun S₁ x₁ hx₁ z hz => ?_) S x hx
      rcases hstep n S₁ x₁ hx₁ z hz with ⟨S', ⟨e⟩, hS'⟩ | h
      · left
        rw [← completionClass_eq_of_ringEquiv e]
        rcases hS' with hempty | ⟨i, hi, y, hy⟩
        · exact acc_completionClass_of_singularLocus_eq_empty S' hempty
        · exact ih i hi S' y hy
      · exact .inr h
  rcases hall S with hempty | ⟨n, x, hx⟩
  · exact acc_completionClass_of_singularLocus_eq_empty S hempty
  · exact hlevel n S x hx

end AlgebraicGeometry

end
