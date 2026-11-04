module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.StageAnnihilator
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.StageGrade

/-!
# Finite variable stages as submodules, and transfer of bases into the ambient algebra

A homogeneous piece of a graded divided-power polynomial algebra is exhausted by its
intersections with the finite variable stages, and a monotone family of bases for those
intersections makes it free. Both halves of that sentence need the stages as `R`-submodules of
the ambient algebra rather than as abstract algebras in their own right: the intersection does
not otherwise typecheck, and the bases of the successive stages have to be compared inside one
module.

This file supplies the submodule picture and the transfer. A stage is a subring containing every
scalar, hence an `R`-submodule; the stages increase with their index set and exhaust the algebra.
A ring homomorphism from a one-variable extension into the ambient algebra which commutes with
the base-ring structure maps is `R`-linear, and if it detects the ambient grading and lands onto
a stage it carries a basis of a homogeneous piece of the extension to a basis of the
corresponding piece of that stage.

Transfer is stated into the *ambient* algebra, not onto the next stage: the next stage carries no
`R`-algebra structure of its own until the successor clause is applied again at a further index,
whereas the composite of a successor equivalence with the inclusion of a stage is `R`-linear as
soon as the current stage's structure is the restriction of the ambient one.

## Main definitions

* `DividedPowers.TateResolution.subringSubmodule` — a subring stable under the scalars, as an
  `R`-submodule.
* `DividedPowers.TateResolution.finiteVariableStageSubmodule` — a finite variable stage as an
  `R`-submodule of the ambient algebra.
* `DividedPowers.TateResolution.ringHomToLinearMap` — a ring homomorphism commuting with the
  base-ring structure maps, as an `R`-linear map.
* `DividedPowers.TateResolution.stageRingHom` — a successor equivalence read in the ambient
  algebra.

## Main results

* `DividedPowers.TateResolution.finiteVariableStageSubmodule_mono` — the submodules of the stages
  increase with their index set.
* `DividedPowers.TateResolution.iSup_inf_finiteVariableStageSubmodule` — the stages exhaust every
  homogeneous piece.
* `DividedPowers.TateResolution.map_grade_of_ringHom`,
  `DividedPowers.TateResolution.span_image_of_ringHom` and
  `DividedPowers.TateResolution.linearIndepOn_image_of_ringHom` — a grading-detecting injection
  onto a stage carries a basis of a homogeneous piece to a basis of the corresponding piece of
  the stage.
* `DividedPowers.TateResolution.stageRingHom_commutes_odd` and `stageRingHom_commutes_even` — a
  successor equivalence, read in the ambient algebra, commutes with the base-ring structure
  maps. This is the hypothesis of the three transfer results above, and it uses both the
  coefficient clause of the successor presentation and its statement that the stage's algebra
  structure is the restriction of the ambient one.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

section SubringSubmodule

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- A subring of an `R`-algebra which is stable under the scalars, as an `R`-submodule. -/
public def subringSubmodule (s : Subring A) (hs : ∀ (r : R) (x : A), x ∈ s → r • x ∈ s) :
    Submodule R A where
  carrier := s
  add_mem' := s.add_mem
  zero_mem' := s.zero_mem
  smul_mem' r x hx := hs r x hx

/-- Membership in the submodule underlying a subring is membership in the subring. -/
public theorem mem_subringSubmodule (s : Subring A)
    (hs : ∀ (r : R) (x : A), x ∈ s → r • x ∈ s) (x : A) :
    x ∈ subringSubmodule s hs ↔ x ∈ s :=
  Iff.rfl

/-- An inclusion of subrings stable under the scalars is an inclusion of submodules. -/
public theorem subringSubmodule_le {s t : Subring A}
    (hs : ∀ (r : R) (x : A), x ∈ s → r • x ∈ s) (ht : ∀ (r : R) (x : A), x ∈ t → r • x ∈ t)
    (h : s ≤ t) :
    subringSubmodule s hs ≤ subringSubmodule t ht :=
  fun _ hx => h hx

end SubringSubmodule

section Stage

variable {R : Type u} {P : Type v} {A : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

/-- A finite variable stage, as an `R`-submodule of the ambient algebra. A stage is a subring
containing the image of every scalar, so this is the stage itself with its `R`-module
structure restricted from the ambient algebra. -/
public def finiteVariableStageSubmodule (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A)
    {J : Type z} (T : J → A) (S : Finset J) : Submodule R A :=
  subringSubmodule (finiteVariableStage γ ι T S) (by
    intro r x hx
    exact smul_mem_finiteVariableStage T S r hx)

/-- Membership in the submodule of a stage is membership in the stage. -/
public theorem mem_finiteVariableStageSubmodule (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A)
    {J : Type z} (T : J → A) (S : Finset J) (x : A) :
    x ∈ finiteVariableStageSubmodule γ ι T S ↔ x ∈ finiteVariableStage γ ι T S :=
  Iff.rfl

/-- The submodules of the finite variable stages increase with their index set. -/
public theorem finiteVariableStageSubmodule_mono (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A)
    {J : Type z} (T : J → A) {S U : Finset J} (h : S ⊆ U) :
    finiteVariableStageSubmodule γ ι T S ≤ finiteVariableStageSubmodule γ ι T U :=
  fun _ hx => finiteVariableStage_le_of_subset γ ι T h hx

/-- The finite variable stages exhaust every homogeneous piece of the ambient algebra: a
homogeneous element lies in one of them already, so the intersections of the stages with a
homogeneous piece have that piece as their join. This is the exhaustion hypothesis of
`free_submodule_of_directed_bases`. -/
public theorem iSup_inf_finiteVariableStageSubmodule (γ : DividedPowerStructure 𝒜)
    (ι : P →ₐ[R] A) {J : Type z} (T : J → A)
    (hfinite : ∀ x : A, ∃ S : Finset J, x ∈ finiteVariableStage γ ι T S) (m : ℕ) :
    ⨆ S : Finset J, (𝒜 m ⊓ finiteVariableStageSubmodule γ ι T S) = 𝒜 m := by
  refine le_antisymm (iSup_le fun _ => inf_le_left) fun x hx => ?_
  obtain ⟨S, hS⟩ := hfinite x
  exact Submodule.mem_iSup_of_mem S ⟨hx, hS⟩

end Stage

section AmbientTransfer

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- A ring homomorphism into an `R`-algebra which commutes with the base-ring structure maps, as
an `R`-linear map. -/
public def ringHomToLinearMap (f : B →+* A)
    (hf : ∀ r : R, f (algebraMap R B r) = algebraMap R A r) :
    B →ₗ[R] A where
  toFun := f
  map_add' := map_add f
  map_smul' r x := by
    change f (r • x) = r • f x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hf]

/-- The function underlying `ringHomToLinearMap` is the given ring homomorphism. -/
public theorem coe_ringHomToLinearMap (f : B →+* A)
    (hf : ∀ r : R, f (algebraMap R B r) = algebraMap R A r) (x : B) :
    ringHomToLinearMap f hf x = f x :=
  rfl

/-- An injective ring homomorphism commuting with the base-ring structure maps has trivial
kernel as a linear map. -/
public theorem ker_ringHomToLinearMap (f : B →+* A)
    (hf : ∀ r : R, f (algebraMap R B r) = algebraMap R A r) (hinj : Function.Injective f) :
    LinearMap.ker (ringHomToLinearMap f hf) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  exact hinj (hx.trans (map_zero f).symm)

/-- A grading-detecting ring homomorphism whose image is a prescribed submodule carries a
homogeneous piece onto the intersection of the corresponding ambient piece with that
submodule.

This is the shape in which the successor stages of a graded divided-power polynomial algebra are
presented, with the image taken to be the next stage: the homomorphism is the successor
equivalence followed by the inclusion of the stage. -/
public theorem map_grade_of_ringHom (Bᵢ : ℕ → Submodule R B) (𝒜 : ℕ → Submodule R A)
    (f : B →+* A) (hf : ∀ r : R, f (algebraMap R B r) = algebraMap R A r)
    (Q : Submodule R A) (hmem : ∀ x : B, f x ∈ Q) (hsurj : ∀ y ∈ Q, ∃ x : B, f x = y)
    (hgrade : ∀ (m : ℕ) (x : B), x ∈ Bᵢ m ↔ f x ∈ 𝒜 m) (m : ℕ) :
    (Bᵢ m).map (ringHomToLinearMap f hf) = 𝒜 m ⊓ Q := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨(hgrade m x).mp hx, hmem x⟩
  · obtain ⟨x, rfl⟩ := hsurj y hy.2
    exact ⟨x, (hgrade m x).mpr hy.1, rfl⟩

/-- A spanning set of a homogeneous piece transfers, along a grading-detecting ring homomorphism
onto a prescribed submodule, to a spanning set of the corresponding intersection. -/
public theorem span_image_of_ringHom (Bᵢ : ℕ → Submodule R B) (𝒜 : ℕ → Submodule R A)
    (f : B →+* A) (hf : ∀ r : R, f (algebraMap R B r) = algebraMap R A r)
    (Q : Submodule R A) (hmem : ∀ x : B, f x ∈ Q) (hsurj : ∀ y ∈ Q, ∃ x : B, f x = y)
    (hgrade : ∀ (m : ℕ) (x : B), x ∈ Bᵢ m ↔ f x ∈ 𝒜 m) (m : ℕ) (s : Set B)
    (hs : Submodule.span R s = Bᵢ m) :
    Submodule.span R (f '' s) = 𝒜 m ⊓ Q := by
  have himg : ringHomToLinearMap f hf '' s = f '' s := rfl
  rw [← himg, Submodule.span_image, hs,
    map_grade_of_ringHom Bᵢ 𝒜 f hf Q hmem hsurj hgrade m]

/-- An independent set transfers along an injective ring homomorphism commuting with the
base-ring structure maps. -/
public theorem linearIndepOn_image_of_ringHom (f : B →+* A)
    (hf : ∀ r : R, f (algebraMap R B r) = algebraMap R A r) (hinj : Function.Injective f)
    (s : Set B) (hs : LinearIndepOn R id s) :
    LinearIndepOn R id (f '' s) := by
  have himg : ringHomToLinearMap f hf '' s = f '' s := rfl
  rw [← himg]
  refine LinearIndepOn.image hs ?_
  rw [ker_ringHomToLinearMap f hf hinj]
  exact disjoint_bot_right

end AmbientTransfer

section StageEmbedding

variable {R : Type u} {P : Type v} {A : Type w} {B : Type w}
  [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A] [Ring B]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]

/-- The composite of a ring equivalence onto a finite variable stage with the inclusion of that
stage into the ambient algebra. This is the map along which the successor clause of a graded
divided-power polynomial algebra transfers bases. -/
public def stageRingHom (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) {J : Type z} (T : J → A)
    (U : Finset J) (e : B ≃+* finiteVariableStage γ ι T U) : B →+* A :=
  (finiteVariableStage γ ι T U).subtype.comp (e : B →+* finiteVariableStage γ ι T U)

/-- The composite of a successor equivalence with the inclusion of a stage is the equivalence
read in the ambient algebra. -/
public theorem stageRingHom_apply (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) {J : Type z}
    (T : J → A) (U : Finset J) (e : B ≃+* finiteVariableStage γ ι T U) (x : B) :
    stageRingHom γ ι T U e x = (e x : A) :=
  rfl

/-- A successor equivalence read in the ambient algebra is injective. -/
public theorem injective_stageRingHom (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) {J : Type z}
    (T : J → A) (U : Finset J) (e : B ≃+* finiteVariableStage γ ι T U) :
    Function.Injective (stageRingHom γ ι T U e) :=
  fun _ _ h => e.injective (Subtype.ext h)

/-- A successor equivalence read in the ambient algebra lands in the stage. -/
public theorem stageRingHom_mem (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) {J : Type z}
    (T : J → A) (U : Finset J) (e : B ≃+* finiteVariableStage γ ι T U) (x : B) :
    stageRingHom γ ι T U e x ∈ finiteVariableStageSubmodule γ ι T U :=
  (e x).2

/-- A successor equivalence read in the ambient algebra is onto the stage. -/
public theorem exists_stageRingHom_eq (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) {J : Type z}
    (T : J → A) (U : Finset J) (e : B ≃+* finiteVariableStage γ ι T U) (y : A)
    (hy : y ∈ finiteVariableStageSubmodule γ ι T U) :
    ∃ x : B, stageRingHom γ ι T U e x = y :=
  ⟨e.symm ⟨y, hy⟩, congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)⟩

/-- **The base-ring compatibility of an odd successor presentation.** The successor clause of a
graded divided-power polynomial algebra states both that the stage's own `R`-algebra structure is
the restriction of the ambient one and that the successor equivalence fixes the coefficients.
Together these say that the equivalence, read in the ambient algebra, commutes with the
base-ring structure maps — which is exactly the hypothesis under which spans, independent sets
and freeness transfer.

Neither half suffices alone: without the first, the stage's structure map is unconstrained and
the claim is not derivable from the clause. -/
public theorem stageRingHom_commutes_odd (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A)
    {J : Type z} (T : J → A) {S : Finset J} [Algebra R (finiteVariableStage γ ι T S)]
    (halg : ∀ r : R, (algebraMap R (finiteVariableStage γ ι T S) r : A) = algebraMap R A r)
    (Sᵢ : ℕ → Submodule R (finiteVariableStage γ ι T S)) [GradedAlgebra Sᵢ] (d : ℕ)
    (U : Finset J) (e : OddVariableExtension Sᵢ d ≃+* finiteVariableStage γ ι T U)
    (hcoeff : ∀ b : finiteVariableStage γ ι T S,
      ((e (OddVariableExtension.inclusion Sᵢ d b) : finiteVariableStage γ ι T U) : A) = b)
    (r : R) :
    stageRingHom γ ι T U e (algebraMap R (OddVariableExtension Sᵢ d) r) = algebraMap R A r := by
  rw [stageRingHom_apply, ← (OddVariableExtension.inclusionAlgHom Sᵢ d).commutes r,
    OddVariableExtension.inclusionAlgHom_apply, hcoeff, halg]

/-- **The base-ring compatibility of an even successor presentation.** This is the even
counterpart of `stageRingHom_commutes_odd`, with the same two hypotheses. -/
public theorem stageRingHom_commutes_even (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A)
    {J : Type z} (T : J → A) {S : Finset J} [Algebra R (finiteVariableStage γ ι T S)]
    (halg : ∀ r : R, (algebraMap R (finiteVariableStage γ ι T S) r : A) = algebraMap R A r)
    (U : Finset J)
    (e : EvenVariableAlgebra (finiteVariableStage γ ι T S) ≃+* finiteVariableStage γ ι T U)
    (hcoeff : ∀ b : finiteVariableStage γ ι T S,
      ((e (EvenVariableAlgebra.coeffEmbedding b) : finiteVariableStage γ ι T U) : A) = b)
    (r : R) :
    stageRingHom γ ι T U e
      (algebraMap R (EvenVariableAlgebra (finiteVariableStage γ ι T S)) r) =
      algebraMap R A r := by
  rw [stageRingHom_apply, EvenVariableAlgebra.algebraMap_apply,
    ← EvenVariableAlgebra.coeffEmbedding_apply, hcoeff, halg]

end StageEmbedding

section Pullback

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- Along an injective linear map, a spanning set of the image of a submodule pulls back to a
spanning set of that submodule. This is the direction the induction over the adjoined variables
needs: a basis of a homogeneous piece of a stage is produced inside the ambient algebra, and the
step lemmas consume it inside the stage. -/
public theorem span_preimage_of_injective (f : B →ₗ[R] A) (hf : Function.Injective f)
    (N : Submodule R B) (s : Set A) (hsub : s ⊆ Set.range f)
    (hs : Submodule.span R s = N.map f) :
    Submodule.span R (f ⁻¹' s) = N := by
  refine Submodule.map_injective_of_injective hf ?_
  rw [Submodule.map_span, Set.image_preimage_eq_of_subset hsub, hs]

/-- Along an injective linear map, an independent set pulls back to an independent set. -/
public theorem linearIndepOn_preimage_of_injective (f : B →ₗ[R] A) (hf : Function.Injective f)
    (s : Set A) (hs : LinearIndepOn R id s) :
    LinearIndepOn R id (f ⁻¹' s) := by
  refine LinearIndepOn.of_comp f ?_
  have hg : Function.Injective
      (fun x : (f ⁻¹' s : Set B) => (⟨f x, x.2⟩ : (s : Set A))) :=
    fun _ _ h => Subtype.ext (hf (Subtype.ext_iff.mp h))
  exact hs.comp _ hg

end Pullback

end DividedPowers.TateResolution

end
