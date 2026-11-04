module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.StageSubmodule

/-!
# One step of the monotone family of bases of a variable extension

A homogeneous piece of a graded divided-power polynomial algebra is free as soon as the pieces of
its finite variable stages carry a family of bases increasing with the index set of adjoined
variables. This file provides the step of the induction that builds such a family: from a basis
of the homogeneous pieces of a stage, together with the successor presentation of the next stage,
it produces a basis of the homogeneous pieces of the next stage which *contains* the given one.

Everything happens inside the ambient algebra, which is where the bases of different stages can
be compared. The step therefore has three parts: pull the given basis back along the inclusion
of the stage, extend it by the step families of `GradeBasis.lean`, and push the result forward
along the successor equivalence. The middle part is already available; the first and third are
the transfer results of `StageSubmodule.lean`, and both rely on the successor presentation
stating that the stage's `R`-algebra structure restricts the ambient one.

## Main results

* `DividedPowers.TateResolution.exists_basis_insert_odd` — the step at an odd-degree variable.
* `DividedPowers.TateResolution.exists_basis_insert_even` — the step at an even-degree variable.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

section Step

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) {J : Type z} (T : J → A)
  (S U : Finset J) [Algebra R (finiteVariableStage γ ι T S)]
  (halg : ∀ r : R, (algebraMap R (finiteVariableStage γ ι T S) r : A) = algebraMap R A r)

/-- The inclusion of a finite variable stage into the ambient algebra, as an `R`-linear map. This
is `R`-linear exactly because the stage's own algebra structure restricts the ambient one. -/
public def stageInclusionLinearMap : finiteVariableStage γ ι T S →ₗ[R] A :=
  ringHomToLinearMap (finiteVariableStage γ ι T S).subtype halg

/-- The inclusion of a stage sends an element to itself. -/
public theorem stageInclusionLinearMap_apply (b : finiteVariableStage γ ι T S) :
    stageInclusionLinearMap 𝒜 γ ι T S halg b = (b : A) :=
  rfl

/-- The inclusion of a stage into the ambient algebra is injective. -/
public theorem injective_stageInclusionLinearMap :
    Function.Injective (stageInclusionLinearMap 𝒜 γ ι T S halg) :=
  fun _ _ h => Subtype.ext h

/-- A homogeneous piece of a stage maps onto the intersection of the corresponding ambient piece
with the stage, as soon as the stage's grading is the restriction of the ambient one. -/
public theorem map_stageInclusionLinearMap
    (Sᵢ : ℕ → Submodule R (finiteVariableStage γ ι T S))
    (hmem : ∀ (m : ℕ) (b : finiteVariableStage γ ι T S), b ∈ Sᵢ m ↔ (b : A) ∈ 𝒜 m) (m : ℕ) :
    (Sᵢ m).map (stageInclusionLinearMap 𝒜 γ ι T S halg) =
      𝒜 m ⊓ finiteVariableStageSubmodule γ ι T S :=
  map_grade_of_ringHom Sᵢ 𝒜 (finiteVariableStage γ ι T S).subtype halg
    (finiteVariableStageSubmodule γ ι T S) (fun b => b.2) (fun y hy => ⟨⟨y, hy⟩, rfl⟩) hmem m

/-- A basis of the homogeneous pieces of a stage, given inside the ambient algebra, pulls back to
a basis of the homogeneous pieces of the stage itself. -/
public theorem span_preimage_stageInclusionLinearMap
    (Sᵢ : ℕ → Submodule R (finiteVariableStage γ ι T S))
    (hmem : ∀ (m : ℕ) (b : finiteVariableStage γ ι T S), b ∈ Sᵢ m ↔ (b : A) ∈ 𝒜 m) (m : ℕ)
    (s : Set A) (hsub : s ⊆ finiteVariableStage γ ι T S)
    (hs : Submodule.span R s = 𝒜 m ⊓ finiteVariableStageSubmodule γ ι T S) :
    Submodule.span R (stageInclusionLinearMap 𝒜 γ ι T S halg ⁻¹' s) = Sᵢ m := by
  refine span_preimage_of_injective _ (injective_stageInclusionLinearMap 𝒜 γ ι T S halg) _ s
    (fun x hx => ⟨⟨x, hsub hx⟩, rfl⟩) ?_
  rw [hs, map_stageInclusionLinearMap 𝒜 γ ι T S halg Sᵢ hmem m]

/-- A basis of the homogeneous pieces of a stage, given inside the ambient algebra, is the image
of its pullback. -/
public theorem image_preimage_stageInclusionLinearMap (s : Set A)
    (hsub : s ⊆ finiteVariableStage γ ι T S) :
    stageInclusionLinearMap 𝒜 γ ι T S halg '' (stageInclusionLinearMap 𝒜 γ ι T S halg ⁻¹' s) =
      s :=
  Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hsub hx⟩, rfl⟩

include halg in
/-- **One step of the induction that builds a monotone family of bases**, at a variable of odd
degree.

A basis of the homogeneous pieces of a stage, presented inside the ambient algebra, extends to a
basis of the homogeneous pieces of the next stage, and the extension *contains* the given basis
— which is the monotonicity that `free_submodule_of_directed_bases` requires and that freeness of
the individual stages cannot replace.

All three hypotheses on the successor equivalence are components of the `successor` field of
`GradedDividedPowerPolynomial`: that it fixes the coefficients, that it detects the ambient
grading, and that the stage's own `R`-algebra structure is the restriction of the ambient one. The
last is what makes the equivalence `R`-linear when read in the ambient algebra, and without it no
transfer of spans or of independent sets is available. -/
public theorem exists_basis_insert_odd (d : ℕ)
    (Sᵢ : ℕ → Submodule R (finiteVariableStage γ ι T S)) [GradedAlgebra Sᵢ]
    (e : OddVariableExtension Sᵢ d ≃+* finiteVariableStage γ ι T U)
    (hcoeff : ∀ b : finiteVariableStage γ ι T S,
      ((e (OddVariableExtension.inclusion Sᵢ d b) : finiteVariableStage γ ι T U) : A) = b)
    (hgrade : ∀ (m : ℕ) (x : OddVariableExtension Sᵢ d),
      x ∈ OddVariableExtension.grade Sᵢ d m ↔
        ((e x : finiteVariableStage γ ι T U) : A) ∈ 𝒜 m)
    (b : ℕ → Set A) (hbsub : ∀ m, b m ⊆ finiteVariableStage γ ι T S)
    (hbspan : ∀ m, Submodule.span R (b m) = 𝒜 m ⊓ finiteVariableStageSubmodule γ ι T S)
    (hbind : ∀ m, LinearIndepOn R id (b m)) :
    ∃ b' : ℕ → Set A,
      (∀ m, b m ⊆ b' m) ∧
      (∀ m, b' m ⊆ finiteVariableStage γ ι T U) ∧
      (∀ m, Submodule.span R (b' m) = 𝒜 m ⊓ finiteVariableStageSubmodule γ ι T U) ∧
      (∀ m, LinearIndepOn R id (b' m)) := by
  have hmem : ∀ (m : ℕ) (x : finiteVariableStage γ ι T S), x ∈ Sᵢ m ↔ (x : A) ∈ 𝒜 m :=
    mem_iff_of_oddVariableEquiv 𝒜 Sᵢ d e Subtype.val Subtype.val hcoeff hgrade
  have hf : ∀ r : R, stageRingHom γ ι T U e (algebraMap R (OddVariableExtension Sᵢ d) r) =
      algebraMap R A r :=
    stageRingHom_commutes_odd γ ι T halg Sᵢ d U e hcoeff
  let t : ℕ → Set (finiteVariableStage γ ι T S) :=
    fun m => stageInclusionLinearMap 𝒜 γ ι T S halg ⁻¹' b m
  have htspan : ∀ m, Submodule.span R (t m) = Sᵢ m := fun m =>
    span_preimage_stageInclusionLinearMap 𝒜 γ ι T S halg Sᵢ hmem m (b m) (hbsub m) (hbspan m)
  have htind : ∀ m, LinearIndepOn R id (t m) := fun m =>
    linearIndepOn_preimage_of_injective _ (injective_stageInclusionLinearMap 𝒜 γ ι T S halg)
      (b m) (hbind m)
  refine ⟨fun m => stageRingHom γ ι T U e '' OddVariableExtension.oddStepBasis Sᵢ t d m,
    fun m x hx => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · exact ⟨OddVariableExtension.inclusionLinearMap Sᵢ d ⟨x, hbsub m hx⟩,
      Set.mem_union_left _ ⟨⟨x, hbsub m hx⟩, hx, rfl⟩, hcoeff ⟨x, hbsub m hx⟩⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e y).2
  · exact span_image_of_ringHom (OddVariableExtension.grade Sᵢ d) 𝒜
      (stageRingHom γ ι T U e) hf (finiteVariableStageSubmodule γ ι T U)
      (stageRingHom_mem γ ι T U e) (exists_stageRingHom_eq γ ι T U e) hgrade m _
      (OddVariableExtension.span_oddStepBasis Sᵢ t htspan d m)
  · exact linearIndepOn_image_of_ringHom (stageRingHom γ ι T U e) hf
      (injective_stageRingHom γ ι T U e) _
      (OddVariableExtension.linearIndepOn_oddStepBasis Sᵢ t htind d m)

include halg in
/-- **One step of the induction that builds a monotone family of bases**, at a variable of even
degree. This is the even counterpart of `exists_basis_insert_odd`, with the same hypotheses: the
extension of the given basis is its image under the degree-zero divided-power monomials, which is
the `n = 0` term of the even step family. -/
public theorem exists_basis_insert_even (d : ℕ)
    (Sᵢ : ℕ → Submodule R (finiteVariableStage γ ι T S))
    (e : EvenVariableAlgebra (finiteVariableStage γ ι T S) ≃+* finiteVariableStage γ ι T U)
    (hcoeff : ∀ b : finiteVariableStage γ ι T S,
      ((e (EvenVariableAlgebra.coeffEmbedding b) : finiteVariableStage γ ι T U) : A) = b)
    (hgrade : ∀ (m : ℕ) (x : EvenVariableAlgebra (finiteVariableStage γ ι T S)),
      x ∈ EvenVariableAlgebra.grade Sᵢ d m ↔
        ((e x : finiteVariableStage γ ι T U) : A) ∈ 𝒜 m)
    (b : ℕ → Set A) (hbsub : ∀ m, b m ⊆ finiteVariableStage γ ι T S)
    (hbspan : ∀ m, Submodule.span R (b m) = 𝒜 m ⊓ finiteVariableStageSubmodule γ ι T S)
    (hbind : ∀ m, LinearIndepOn R id (b m)) :
    ∃ b' : ℕ → Set A,
      (∀ m, b m ⊆ b' m) ∧
      (∀ m, b' m ⊆ finiteVariableStage γ ι T U) ∧
      (∀ m, Submodule.span R (b' m) = 𝒜 m ⊓ finiteVariableStageSubmodule γ ι T U) ∧
      (∀ m, LinearIndepOn R id (b' m)) := by
  have hmem : ∀ (m : ℕ) (x : finiteVariableStage γ ι T S), x ∈ Sᵢ m ↔ (x : A) ∈ 𝒜 m :=
    mem_iff_of_evenVariableEquiv 𝒜 Sᵢ d e Subtype.val Subtype.val hcoeff hgrade
  have hf : ∀ r : R, stageRingHom γ ι T U e
      (algebraMap R (EvenVariableAlgebra (finiteVariableStage γ ι T S)) r) = algebraMap R A r :=
    stageRingHom_commutes_even γ ι T halg U e hcoeff
  let t : ℕ → Set (finiteVariableStage γ ι T S) :=
    fun m => stageInclusionLinearMap 𝒜 γ ι T S halg ⁻¹' b m
  have htspan : ∀ m, Submodule.span R (t m) = Sᵢ m := fun m =>
    span_preimage_stageInclusionLinearMap 𝒜 γ ι T S halg Sᵢ hmem m (b m) (hbsub m) (hbspan m)
  have htind : ∀ m, LinearIndepOn R id (t m) := fun m =>
    linearIndepOn_preimage_of_injective _ (injective_stageInclusionLinearMap 𝒜 γ ι T S halg)
      (b m) (hbind m)
  refine ⟨fun m => stageRingHom γ ι T U e '' EvenVariableAlgebra.evenStepBasis t d m,
    fun m x hx => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · refine ⟨EvenVariableAlgebra.monomial 0 ⟨x, hbsub m hx⟩, Set.mem_iUnion.mpr ⟨0, ?_⟩,
      hcoeff ⟨x, hbsub m hx⟩⟩
    refine ⟨⟨x, hbsub m hx⟩, ?_, rfl⟩
    rwa [Nat.zero_mul, Nat.sub_zero, ite_eq_left (Nat.zero_le m)]
  · rintro _ ⟨y, -, rfl⟩
    exact (e y).2
  · exact span_image_of_ringHom (EvenVariableAlgebra.grade Sᵢ d) 𝒜
      (stageRingHom γ ι T U e) hf (finiteVariableStageSubmodule γ ι T U)
      (stageRingHom_mem γ ι T U e) (exists_stageRingHom_eq γ ι T U e) hgrade m _
      (EvenVariableAlgebra.span_evenStepBasis Sᵢ t htspan d m)
  · exact linearIndepOn_image_of_ringHom (stageRingHom γ ι T U e) hf
      (injective_stageRingHom γ ι T U e) _
      (EvenVariableAlgebra.linearIndepOn_evenStepBasis t htind d m)

end Step

end DividedPowers.TateResolution

end
