module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.WildLayerDescent

/-!
# The prescribed family and the base of the layer recursion

`EppMember`, one layer of the prescribed base change at the package level, the prescribed-family
descent, and the base case `familyTowerSolvable_one` of `FamilyTowerSolvable` with the
prime-degree solver obligations.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe u

/-! ### The prescribed family at the ring-theoretic level

The three preceding sections are induction principles: `Solves` is a parameter, so none of them is
a weak-solution theorem.  This section instantiates the outer induction
(`Stacks.EppTheorem.forall_solves_of_family_descent`) at the package level, which means choosing
  the member
type, the measure and `Solves` concretely and *proving* the step.

**The setting is complete with a PERFECT residue field, not an algebraically closed one**, and this
is a correction to the setting one might first expect.  The reason is
that after the Cohen reduction the base residue field is
`perfectCore κ_B p`, which is perfect and in general *not* algebraically closed — `κ_A = κ_B =
𝔽_p(x)` has perfect core `𝔽_p` — and the published upgrade from perfect to algebraically closed
runs through Tag 09ET, whose weak-solution clause is false.
So a layer machinery stated over an algebraically
closed residue field would be machinery for a hypothesis the route cannot reach, and the members
here carry `PerfectField (IsLocalRing.ResidueField A)`.

Nothing in the section needed the stronger hypothesis, which is worth stating because it was
checked rather than assumed: `canonicalBaseChange` is unconditional,
`integralClosure_isCompleteDVR` and `integralClosure_factor_isExtension` want only completeness,
`finiteFieldFactors_compatible` and `isWeakSolution_of_iterated_packages` want neither, and the one
place the old setting was used — the residue-field ascent at the new member's base — is discharged
by `perfectField_residueField_of_finite` above, whose proof is shorter than the algebraically
closed one.

**The measure is `Module.finrank d.K K₂`, and that is a correction to the plan this section was
written from.** The plan proposed `deg d := Module.finrank d.K d.L`, the degree of the member's own
extension. That measure does not work with a single prescribed `K₂`, and the reason is worth
recording because it is structural rather than technical.

`isWeakSolution_of_iterated_packages` is the only composition in the tree whose hypotheses and
conclusion speak about **one** base change: it reduces a weak solution for `(A, B, K, L)` over `K₂`
to weak solutions for the factor members `(A₁, B₁, K₁, E i)` over the *same* `K₂`, where
`K ⊆ K₁ ⊆ K₂`.  So it moves the member's base *up* inside `K₂` and replaces `L` by the factors of
`(L ⊗[K] K₁) ⧸ nilradical`.  Those factors satisfy `∑ᵢ [E i : K₁] ≤ [L : K]`, so the extension
degree never increases — and never provably decreases either: with `K₁ = K` the reduction is the
identity, and with `L ⊗[K] K₁` a field the new member has exactly the old degree.  A strict drop in
`[L : K]` requires the *tower* split instead, which is Tag 09ES
(`isWeakSolution_of_prime_layer_of_forall_factor` above); but there the upper layer's base change
is a **factor** `E i` of the lower layer's, not `K₂`, so its members do not inhabit a family whose
resource is one fixed field.  The two are not interchangeable, and with `K₂` fixed only the first
is available.

What does strictly decrease is the part of the prescribed base change still to be made.  The
splitting lemma applied to `K₂ / d.K` produces a prime-degree layer `K₁`, and
`Module.finrank_mul_finrank` (inside
`exists_intermediateField_prime_finrank_of_isSolvable`) gives `[K₂ : K₁] < [K₂ : K]`.  So the
descent walks the prescribed extension one prime layer at a time, re-entering at the factor members
each time, and terminates when the member's base *is* `K₂`.

**Read the residual hypothesis literally.** `hterminal` is applied exactly at the members whose
base field is already `K₂`, where `Solves` unwinds to `d.A → d.B` being weakly unramified: for such
a member the base change is the trivial one.  That is the shared-solver obligation, and it is
*stronger* than a bare degree-`p` solver, since the
descent above does not reduce the extension degree.  Nothing here discharges it, nothing here is
tagged, and no unconditional Tag 09F9 follows.

**Two things that have to be said rather than left for a reader to notice.**

First, `hterminal` is **not** a theorem, and it is not merely unproved: quantified over all members
it is *false*, because a ramified extension of complete discrete valuation rings whose base field
is already `K₂` is a member.  So `forall_solves_of_prescribed_family` is an induction principle
with a concrete `Solves` — not a weak-solution theorem — and what it contributes is that the
package-level step is proved and compiled.  Discharging the obligation means restricting the
members to the ones the route actually produces, which is what `Stacks.EppTheorem.FactorSolutions`
  earlier in this file does.

Second, because the measure counts only the base change, the induction does no work a single step
would not: `exists_factorMembers_of_layer` at `K₁ := K₂` sends every member straight to members of
measure `1`.  That single step is stated unconditionally as
`Stacks.EppTheorem.exists_terminalMembers`, which is therefore the section's non-vacuous content,
  and the
form a consumer should prefer.  A layer induction that genuinely consumes degree-`p` solvers one
layer at a time has to reduce `[L : K]`, which — by the paragraph above — means the 09ES tower
split, and therefore members carrying the factor field they are checked against rather than one
field fixed for the whole family.  That is the next increment, and it is a change to the member
datum, not to the descent.

The Galois and solvability hypotheses are on `K₂ / d.K`, not on the member's own extension, and
they are threaded through the descent rather than assumed for every intermediate field, because the
splitting lemma re-supplies them for the layer it produces.  A caller has them: the wild
construction exposes `IsGalois K₁ K₂`, and a base change built as a tower of degree-`p` layers is
solvable. -/

section PrescribedFamily

open IsDiscreteValuationRing

/-- **A member of the prescribed family**: an extension of complete discrete valuation rings with
*perfect* residue field downstairs, presented over a base field that maps into the one prescribed
extension `K₂`.

**Perfect, not algebraically closed**, and that is the setting rather than a weakening of it: see
the section docstring.  Completeness is what the data needs
(the integral closure in a finite extension is again a complete discrete valuation ring, so the
member can be rebuilt at each factor); perfectness is what ascends along that rebuild and what the
consumers of a solved member want, since a perfect residue field makes every residue extension
separable and so sends a member to the carried, weakly unramified branch.

The carriers are all in `Type u`, which is what makes a step universe-closed — see
`Stacks.EppTheorem.exists_finiteFieldFactors_of_package`.  The structure therefore lives in `Type
  (u + 1)`,
which `Stacks.EppTheorem.forall_solves_of_family_descent` accepts, being universe-polymorphic.

The fields are exactly what is needed and nothing more.  Note in particular that `L / K` is **not**
assumed finite: `IntegralClosureBaseChange` does not require it, the factor family is finite over
`L` because `K₁ / K` is finite, and nothing in the step consumes it.  What is assumed finite is
`K₂ / K`, the prescribed base change.

`IsGalois K K₂` and solvability of its Galois group are the splitting lemma's hypotheses, on the
prescribed extension rather than on the member. -/
structure EppMember (K₂ : Type u) [Field K₂] where
  /-- The base discrete valuation ring. -/
  A : Type u
  /-- The discrete valuation ring extending `A`. -/
  B : Type u
  /-- The fraction field of `A`; it maps into the prescribed `K₂`. -/
  K : Type u
  /-- The fraction field of `B`. -/
  L : Type u
  [commRingA : CommRing A]
  [commRingB : CommRing B]
  [isDomainA : IsDomain A]
  [isDomainB : IsDomain B]
  [dvrA : IsDiscreteValuationRing A]
  [dvrB : IsDiscreteValuationRing B]
  [fieldK : Field K]
  [fieldL : Field L]
  [algebraAB : Algebra A B]
  [algebraAK : Algebra A K]
  [algebraAL : Algebra A L]
  [algebraBL : Algebra B L]
  [algebraKL : Algebra K L]
  [algebraKK₂ : Algebra K K₂]
  [algebraAK₂ : Algebra A K₂]
  [isExtensionAB : IsExtension A B]
  [isFractionRingAK : IsFractionRing A K]
  [isFractionRingBL : IsFractionRing B L]
  [towerABL : IsScalarTower A B L]
  [towerAKL : IsScalarTower A K L]
  [towerAKK₂ : IsScalarTower A K K₂]
  [finiteKK₂ : Module.Finite K K₂]
  [completeA : IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [completeB : IsAdicComplete (IsLocalRing.maximalIdeal B) B]
  [perfectA : PerfectField (IsLocalRing.ResidueField A)]
  [galoisKK₂ : IsGalois K K₂]
  [solvableKK₂ : Group.IsSolvable (K₂ ≃ₐ[K] K₂)]

attribute [instance] EppMember.commRingA EppMember.commRingB EppMember.isDomainA
  EppMember.isDomainB EppMember.dvrA EppMember.dvrB EppMember.fieldK EppMember.fieldL
  EppMember.algebraAB EppMember.algebraAK EppMember.algebraAL EppMember.algebraBL
  EppMember.algebraKL EppMember.algebraKK₂ EppMember.algebraAK₂ EppMember.isExtensionAB
  EppMember.isFractionRingAK EppMember.isFractionRingBL EppMember.towerABL EppMember.towerAKL
  EppMember.towerAKK₂ EppMember.finiteKK₂ EppMember.completeA EppMember.completeB
  EppMember.perfectA EppMember.galoisKK₂ EppMember.solvableKK₂

variable {K₂ : Type u} [Field K₂]

/-- The measure the descent recurses on: how much of the prescribed base change the member has
still to absorb.  It is `1` exactly when the member's base field is already `K₂`. -/
noncomputable def EppMember.deg (d : EppMember K₂) : ℕ := Module.finrank d.K K₂

/-- **What it means for the one prescribed `K₂` to solve a member**: the base change of
`d.A → d.B` along `K₂` is a weak solution, in the sense of Tag 09EN.

The existential is over the *package*, not over the extension: `K₂` is fixed outside, which is the
whole of the prescribed-extension discipline.  Packages exist unconditionally
(`IsDiscreteValuationRing.canonicalBaseChange`), so this says nothing about existence and
everything about ramification. -/
def EppMember.Solves (d : EppMember K₂) : Prop :=
  ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} d.A d.B d.K d.L K₂,
    D.IsWeakSolution

/-- **One layer of the prescribed base change, at the package level.**

Given an intermediate `K₁` of `K₂ / d.K`, the member is replaced by the finitely many factor
members over `K₁` — base `integralClosure d.A K₁`, extension `integralClosure d.B (E i)` for `E i`
the conjugate factors of `(d.L ⊗[d.K] K₁) ⧸ nilradical` — each of them again a member, and each
checked against the *same* `K₂`.  Solving all of them solves the original.

Every ingredient is an existing public result: `canonicalBaseChange` builds the two
packages, `exists_finiteFieldFactors_of_package` produces the factor family with every carrier in
`Type u`, `integralClosure_isCompleteDVR` and `integralClosure_factor_isExtension` rebuild the
member data at each factor, `perfectField_residueField_of_finite` carries the residue hypothesis
across, and `isWeakSolution_of_iterated_packages` is the composition.  None of them wants an
algebraically closed residue field; completeness is what rebuilds the data and perfectness is what
ascends.  No new mathematics is
claimed; what is new is that the output is again a family of members, so a descent can iterate it.

The new members' measure is `Module.finrank K₁ K₂`, recorded as an equality rather than an
inequality so that the caller can supply the strict decrease from the splitting lemma. -/
private theorem exists_factorMembers_of_layer (d : EppMember K₂)
    (K₁ : Type u) [Field K₁] [Algebra d.K K₁] [Algebra K₁ K₂]
    [IsScalarTower d.K K₁ K₂] [Module.Finite d.K K₁] [Module.Finite K₁ K₂]
    [IsGalois K₁ K₂] [Group.IsSolvable (K₂ ≃ₐ[K₁] K₂)] :
    ∃ (n : ℕ) (g : Fin n → EppMember K₂),
      (∀ j, (g j).deg = Module.finrank K₁ K₂) ∧
      ((∀ j, (g j).Solves) → d.Solves) := by
  classical
  let : Algebra d.A K₁ := ((algebraMap d.K K₁).comp (algebraMap d.A d.K)).toAlgebra
  let : IsScalarTower d.A d.K K₁ := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower d.A K₁ K₂ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply d.A d.K K₂, IsScalarTower.algebraMap_apply d.A d.K K₁,
      ← IsScalarTower.algebraMap_apply d.K K₁ K₂]
  let D₁ := canonicalBaseChange d.A d.B d.K d.L K₁
  let := D₁.commRingL₁
  let := D₁.algebraKL₁
  let := D₁.algebraLL₁
  let := D₁.algebraK₁L₁
  obtain ⟨n, E, hE, hLE, hKE, hBE, hAE, hBLE, hABE, hAKE, hfinE, -, e, he⟩ :=
    exists_finiteFieldFactors_of_package d.A d.B d.K d.L K₁ D₁
  let := hE
  let := hLE
  let := hKE
  let := hBE
  let := hAE
  let := hBLE
  let := hABE
  let := hAKE
  let := hfinE
  let R : Type u := integralClosure d.A K₁
  let S : Fin n → Type u := fun j => integralClosure d.B (E j)
  obtain ⟨hR, hAR, hRfin, hRc, hRf⟩ := integralClosure_isCompleteDVR d.A d.K K₁
  let := hR
  let := hAR
  let := hRfin
  let := hRc
  let := hRf
  have hSall := fun j => integralClosure_isCompleteDVR d.B d.L (E j)
  choose hS hBS hSfin hSc hSf using hSall
  let := hS
  let := hBS
  let := hSfin
  let := hSc
  let := hSf
  let : ∀ j, Algebra R (S j) := fun j =>
    (mapIntegralClosureOfTower d.A d.B K₁ (E j)).toRingHom.toAlgebra
  let : ∀ j, Algebra R (E j) := fun j =>
    ((algebraMap K₁ (E j)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ j, @IsScalarTower R K₁ (E j)
      (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ (E j)).toSMul
      (inferInstance : Algebra R (E j)).toSMul := fun j =>
    IsScalarTower.of_algebraMap_eq' (R := R) (S := K₁) (A := E j) rfl
  let : ∀ j, @IsScalarTower R (S j) (E j)
      (inferInstance : Algebra R (S j)).toSMul (inferInstance : Algebra (S j) (E j)).toSMul
      (inferInstance : Algebra R (E j)).toSMul := fun j =>
    IsScalarTower.of_algebraMap_eq (R := R) (S := S j) (A := E j) fun r =>
      (mapIntegralClosureOfTower_apply d.A d.B K₁ (E j) r).symm
  let : Algebra R K₂ := ((algebraMap K₁ K₂).comp (algebraMap R K₁)).toAlgebra
  let : @IsScalarTower R K₁ K₂
      (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ K₂).toSMul
      (inferInstance : Algebra R K₂).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := K₁) (A := K₂) rfl
  let : ∀ j, IsExtension R (S j) := fun j =>
    (integralClosure_factor_isExtension d.A d.B d.K d.L K₁ (E j)).choose_spec.choose_spec.1
  let : PerfectField (IsLocalRing.ResidueField R) := perfectField_residueField_of_finite d.A R
  let : ∀ j, Algebra d.K (E j) := fun j =>
    ((algebraMap K₁ (E j)).comp (algebraMap d.K K₁)).toAlgebra
  let : ∀ j, IsScalarTower d.K K₁ (E j) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨n, fun j => { A := R, B := S j, K := K₁, L := E j }, fun _ => rfl, ?_⟩
  intro hsol
  -- Retyping through `have` is what makes the members' bundled instances usable: the packages
  -- `hsol` supplies are typed by the record's *projections*, which are only definitionally the
  -- instances instance search finds here, and `apply` does not see through that.
  have hsol' : ∀ j, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} R (S j) K₁ (E j) K₂,
      D.IsWeakSolution := hsol
  choose D hD using hsol'
  refine ⟨canonicalBaseChange d.A d.B d.K d.L K₂, ?_⟩
  apply isWeakSolution_of_iterated_packages d.A d.B d.K d.L K₁ K₂ R
    (canonicalBaseChange d.A d.B d.K d.L K₂) E S
    ?_ ?_ ?_ D hD (reducedTensorFactorsEquiv d.K d.L K₁ D₁.L₁ E D₁.eL₁ e D₁.eL₁_right he)
    (fun j x => reducedTensorFactorsEquiv_left d.K d.L K₁ D₁.L₁ E
      D₁.eL₁ e D₁.eL₁_right he D₁.eL₁_left x j)
  · intro a
    change algebraMap d.A K₂ a = algebraMap K₁ K₂ (algebraMap d.A K₁ a)
    exact IsScalarTower.algebraMap_apply d.A K₁ K₂ a
  · intro j b
    rw [← IsScalarTower.algebraMap_apply d.B d.L (E j),
      ← IsScalarTower.algebraMap_apply d.B (S j) (E j)]
  · intro j a
    apply Subtype.ext
    change algebraMap d.B (E j) (algebraMap d.A d.B a) =
      ((mapIntegralClosureOfTower d.A d.B K₁ (E j)) (algebraMap d.A R a) : E j)
    rw [mapIntegralClosureOfTower_apply]
    change algebraMap d.B (E j) (algebraMap d.A d.B a) =
      algebraMap K₁ (E j) (algebraMap d.A K₁ a)
    rw [← IsScalarTower.algebraMap_apply d.A d.B (E j),
      ← IsScalarTower.algebraMap_apply d.A K₁ (E j)]

/-- **The step of the descent**: a member that has not absorbed all of `K₂` is replaced by finitely
many members of strictly smaller measure.

The prime-degree layer comes from `exists_intermediateField_prime_finrank_of_isSolvable`, which
also returns the strict decrease `[K₂ : K₁] < [K₂ : K]` — proved there by
`Module.finrank_mul_finrank` — and re-supplies `IsGalois K₁ K₂` and solvability of `Gal(K₂ / K₁)`,
which is what lets the new members be members. -/
private theorem exists_factorMembers (d : EppMember K₂) (h : 1 < d.deg) :
    ∃ (n : ℕ) (g : Fin n → EppMember K₂),
      (∀ j, (g j).deg < d.deg) ∧ ((∀ j, (g j).Solves) → d.Solves) := by
  obtain ⟨F, -, -, -, hdec, hgal, hsolv⟩ :=
    exists_intermediateField_prime_finrank_of_isSolvable d.K K₂ h
  let := hgal
  let := hsolv
  obtain ⟨n, g, hdeg, himp⟩ := exists_factorMembers_of_layer d F
  exact ⟨n, g, fun j => (hdeg j).trans_lt hdec, himp⟩

/-- **The reduction, with no hypothesis at all: a member is replaced by finitely many members whose
base field is already `K₂`.**

This is `exists_factorMembers_of_layer` at `K₁ := K₂`, and it is the unconditional content of this
section.  Read it as Epp's reduction made precise: to know that the prescribed `K₂` weakly resolves
`d`, it suffices to know that it leaves nothing ramified at each conjugate factor of
`(d.L ⊗[d.K] K₂) ⧸ nilradical` — where the base field is all of `K₂`, so the remaining base change
is the trivial one and `Solves` there is bare weak unramifiedness.

`forall_solves_of_prescribed_family` below routes the same content through the abstract outer
induction, which is worth having because it exhibits the package-level step as a step.  But its
`hterminal` is a *hypothesis* and this is a *theorem*, and the difference is the point: see the
section docstring. -/
theorem exists_terminalMembers (d : EppMember K₂) :
    ∃ (n : ℕ) (g : Fin n → EppMember K₂),
      (∀ j, (g j).deg = 1) ∧ ((∀ j, (g j).Solves) → d.Solves) := by
  have h1 : ∀ g : K₂ ≃ₐ[K₂] K₂, g = 1 := fun g =>
    AlgEquiv.ext fun x => by simpa using g.commutes x
  let : Group.IsSolvable (K₂ ≃ₐ[K₂] K₂) :=
    Group.isSolvable_of_comm fun a b => by rw [h1 a, h1 b]
  obtain ⟨n, g, hdeg, himp⟩ := exists_factorMembers_of_layer d K₂
  exact ⟨n, g, fun j => (hdeg j).trans (Module.finrank_self K₂), himp⟩

/-- The family form of `exists_terminalMembers`: one prescribed `K₂`, and the whole family reduced
at once to members based at `K₂`.  Pointwise, as usual — the resource is baked into `Solves`, so
there is nothing to reconcile between members. -/
theorem exists_forall_terminalMembers {ι : Type*} (f : ι → EppMember K₂) :
    ∃ (m : ι → ℕ) (g : (i : ι) → Fin (m i) → EppMember K₂),
      (∀ i j, (g i j).deg = 1) ∧ ((∀ i j, (g i j).Solves) → ∀ i, (f i).Solves) := by
  choose m g hdeg himp using fun i => exists_terminalMembers (f i)
  exact ⟨m, g, fun i => hdeg i, fun hall i => himp i fun j => hall i j⟩

/-- **The prescribed family theorem: one base change `K₂`, an arbitrary finite family of members,
and a single residual obligation.**

Every member of the family has a weak solution over the one prescribed `K₂`, provided `hterminal`
holds.  The existential over extensions is not here at all — `K₂` is a parameter, and `Solves`
speaks about that one field — which is what distinguishes this from the amalgamating route: nothing
in the proof ever combines two independently chosen extensions.

`hterminal` is the residual obligation, and it says exactly this: a member whose base field is
already `K₂` (that being what `Module.finrank d.K K₂ ≤ 1` means) is solved by the trivial base
change, i.e. its `A → B` is weakly unramified.  That is the shared solver, and it is not
discharged here — see the
section docstring, which also records why it is stronger than a bare degree-`p` solver.

The index type is in `Type u` for the caller's convenience; the descent runs at `Type (u + 1)`,
where the member structure lives, and `ULift` bridges the two. -/
theorem forall_solves_of_prescribed_family
    (hterminal : ∀ d : EppMember K₂, d.deg ≤ 1 → d.Solves)
    {ι : Type u} [Finite ι] (f : ι → EppMember K₂) : ∀ i, (f i).Solves := by
  have hstep : ∀ (κ : Type (u + 1)) [Finite κ] (F : κ → EppMember K₂),
      (∀ i, 1 < (F i).deg) →
      ∃ (m : κ → ℕ) (g : (i : κ) → Fin (m i) → EppMember K₂),
        (∀ i j, (g i j).deg < (F i).deg) ∧
        ((∀ i j, (g i j).Solves) → ∀ i, (F i).Solves) := by
    intro κ _ F hF
    choose m g hdeg himp using fun i => exists_factorMembers (F i) (hF i)
    exact ⟨m, g, fun i => hdeg i, fun hall i => himp i fun j => hall i j⟩
  let : Finite (ULift.{u + 1, u} ι) := Finite.of_equiv ι Equiv.ulift.symm
  exact fun i =>
    forall_solves_of_family_descent EppMember.deg EppMember.Solves hterminal hstep
      (ULift.{u + 1, u} ι) (fun x => f x.down) ⟨i⟩

end PrescribedFamily

/-! ### `FamilyTowerSolvable`: the base of the layer recursion

`Stacks.EppTheorem.FamilyTowerSolvable` (`EppPerfectResidueComplete.lean`) is the layer
recursion.  It is proved by
strong induction on the degree bound `n`; what is here is the **base**, `n = 1`, which needs no
recursion, no prescribed extension and no terminal solver, and which the induction's other branches
all reduce to.

Two things make it as short as it is, and both arrived with the perfect-residue complete case rather
than being built here:

* `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField` — at a member that is *already*
  weakly unramified, **every** finite base change is a weak solution, over a merely perfect residue
  field and with no completeness hypothesis.  This is the replacement of the
  `IsAlgClosed`-dependent `isWeakSolution_of_finite_extension` that §3 note (c) names, and it is
  why `K₂ := K` serves here.
* `canonicalBaseChange`, which supplies the package unconditionally.

So no extension is produced at all in this branch: the existential is discharged by `K` itself,
which is the degenerate case of the discipline that `∃ K₂` sits outside `∀ i` — one field, namely
the base, for every member at once. -/

section TowerFamily

open IsDiscreteValuationRing

/-- A DVR over a complete DVR, with finite fraction extension, is module-finite over it. -/
private theorem module_finite_of_isAdicComplete_of_finite_fractionRing
    (B C L M : Type*)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M] [Algebra B C] [Algebra B L] [Algebra C M]
    [Algebra L M] [Algebra B M] [IsScalarTower B L M] [IsScalarTower B C M]
    [IsFractionRing B L] [IsFractionRing C M] [IsDiscreteValuationRing.IsExtension B C]
    [Module.Finite L M] [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
    Module.Finite B C := by
  let : IsIntegralClosure C B M := isIntegralClosure_of_isAdicComplete B C L M
  let : Module.Finite B (integralClosure B M) :=
    (isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete B L M).2
  exact Module.Finite.equiv (IsIntegralClosure.equiv B (integralClosure B M) M C).toLinearEquiv

/-- **At a member whose upper layer is trivial, the whole tower is weakly unramified.**

Factored out because both the base of the recursion and its mixed levels need it: the degree-one
member is the one that can be *carried* against whatever extension the level produced, and this is
what makes that sound. The three lines establishing `Module.Finite B C` are the opening of Tag
09F8's own `normalTowerSolvable` — `C` is module-finite over `B` because, `B` being complete and
`M / L` finite, it *is* the integral closure. -/
theorem isWeaklyUnramified_of_finrank_eq_one
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower B C M] [IsScalarTower B L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing B L] [IsFractionRing C M]
    [Module.Finite L M] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hweak : IsWeaklyUnramified A B) (h1 : Module.finrank L M = 1) :
    IsWeaklyUnramified A C := by
  let : Module.Finite B C := module_finite_of_isAdicComplete_of_finite_fractionRing B C L M
  refine isWeaklyUnramified_trans A B C hweak ?_
  have hd := ramificationIdx_dvd_finrank_of_isLocalRing B C
  rw [← IsFractionRing.finrank_eq B L C M, h1] at hd
  exact (isWeaklyUnramified_iff_ramificationIdx_eq_one B C).mpr (Nat.dvd_one.mp hd)

/-- **The base case of the layer recursion: a family whose upper layers are all trivial is solved
by the base field itself.**

`Module.finrank (L i) (M i) ≤ 1` forces the ramification index of `B i → C i` to be one
(`ramificationIdx_dvd_finrank_of_isLocalRing`, via `IsFractionRing.finrank_eq`), which composes
with `hweak` to make `A → C i` weakly unramified (`isWeaklyUnramified_trans`), and then the trivial
base change `K₂ = K` is a weak solution because `κ_A` is perfect.

Nothing here uses `p`, Epp's condition, normality, or completeness of the `B i`; they are carried
because `FamilyTowerSolvable` carries them, and their being unused at `n = 1` is the honest reason
this branch is not where the mathematics is. -/
theorem familyTowerSolvable_one (p : ℕ) [Fact p.Prime] : FamilyTowerSolvable.{u} p 1 := by
  intro ι _ A K B C L M
  intros
  rename_i hweak _ _ _ hdegree
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  refine ⟨canonicalBaseChange A (C i) K (M i) K, ?_⟩
  refine isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField A (C i) K (M i) K _ ?_
  exact isWeaklyUnramified_of_finrank_eq_one A (B i) (C i) K (L i) (M i) (hweak i)
    (le_antisymm (hdegree i) Module.finrank_pos)

/-- **The shared prime-degree family solver, per layer, in the producer form the tower step
consumes.**

This interface is in the library because `familyTowerSolvable_of_forall_terminal` below is its
proved consumer.

It is `FamilyTowerSolvable` with two changes, each from that note's design table:

* the degree bound is replaced by the per-member alternative that
  `exists_finite_extension_isWeakSolution_of_prime_degree` takes verbatim — purely inseparable of
  degree exactly `p`, or Galois of prime degree;
* `Normal (L i) (M i)` is dropped, because that theorem does not assume it.

**It is a producer, not a predicate, and that is the whole point of the shape.** A prescribed
predicate — "if `K₂` has property `P` then every terminal member is solved" — does not close the
tower step: something must still produce a `K₂` that has `P` *and* serves the level's non-terminal
members, and combining two independently produced extensions is the amalgamation the route forbids.
So the existential sits outside `∀ i` here, exactly as in `FamilyTowerSolvable`, and O2 owes one
finite `K₂ / K` computed from bounds over the whole family before any member is examined. -/
abbrev FamilyPrimeDegreeSolvable (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (ι : Type u) [Finite ι]
    (A K : Type u) (B C L M : ι → Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, IsDiscreteValuationRing (B i)]
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)] [∀ i, IsDiscreteValuationRing (C i)]
    [∀ i, Field (L i)] [∀ i, Field (M i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (C i)] [∀ i, Algebra A (C i)]
    [∀ i, Algebra (B i) (L i)] [∀ i, Algebra (C i) (M i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (M i)] [∀ i, Algebra K (M i)]
    [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (M i)] [∀ i, Algebra A (M i)]
    [∀ i, IsScalarTower A (B i) (C i)] [∀ i, IsScalarTower A (B i) (L i)]
    [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower (B i) (C i) (M i)] [∀ i, IsScalarTower (B i) (L i) (M i)]
    [∀ i, IsScalarTower A (C i) (M i)] [∀ i, IsScalarTower A K (M i)]
    [∀ i, IsScalarTower K (L i) (M i)]
    [∀ i, IsExtension A (B i)] [∀ i, IsExtension (B i) (C i)] [∀ i, IsExtension A (C i)]
    [∀ i, IsFractionRing (B i) (L i)] [∀ i, IsFractionRing (C i) (M i)]
    [CharP (IsLocalRing.ResidueField A) p] [∀ i, ExpChar (IsLocalRing.ResidueField (B i)) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (_hweak : ∀ i, IsWeaklyUnramified A (B i))
    [∀ i, Module.Finite (L i) (M i)]
    (_hepp : ∀ i, EppCondition A (B i) p)
    (_hterminal : ∀ i,
      IsPurelyInseparable (L i) (M i) ∧ Module.finrank (L i) (M i) = p ∨
        IsGalois (L i) (M i) ∧ (Module.finrank (L i) (M i)).Prime),
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∀ i, ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A (C i) K (M i) K₂,
        D.IsWeakSolution

/-- The one-member prime-degree obligation underlying `FamilyPrimeDegreeSolvable`.

This interface deliberately has exactly the hypotheses of one member of the family statement.  It
is separated out because, over a perfect base residue field, weak solutions survive arbitrary
further finite extensions: finitely many independently obtained solution fields can therefore be
embedded in one finite overfield and all the solutions transported there. -/
abbrev PrimeDegreeSolvable (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A K]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing B L] [IsFractionRing C M] [IsFractionRing A K]
    [CharP (IsLocalRing.ResidueField A) p] [ExpChar (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B],
    IsWeaklyUnramified A B →
    ∀ [Module.Finite L M],
    EppCondition A B p →
    (IsPurelyInseparable L M ∧ Module.finrank L M = p ∨
      IsGalois L M ∧ (Module.finrank L M).Prime) →
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₂,
        D.IsWeakSolution

/-- The genuinely wild part of the one-member prime-degree obligation: a Galois layer whose
degree equals the residue characteristic. -/
abbrev WildPrimeDegreeSolvable (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (A B C K L M : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C] [Algebra A K]
    [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing B L] [IsFractionRing C M] [IsFractionRing A K]
    [CharP (IsLocalRing.ResidueField A) p] [ExpChar (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B],
    IsWeaklyUnramified A B →
    ∀ [Module.Finite L M] [IsGalois L M],
    EppCondition A B p →
    Module.finrank L M = p →
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra A K₂)
      (_ : IsScalarTower A K K₂) (_ : Module.Finite K K₂),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M K₂,
        D.IsWeakSolution

/-- Purely inseparable layers and Galois layers of degree prime to the residue characteristic are
already solved.  Consequently the only one-member input needed for Epp's prime-degree step is the
Galois degree-`p` case. -/
theorem primeDegreeSolvable_of_wildPrimeDegreeSolvable (p : ℕ) [Fact p.Prime]
    (hwild : WildPrimeDegreeSolvable.{u} p) : PrimeDegreeSolvable.{u} p := by
  intro A B C K L M
  intros
  rename_i hweak _ hepp hterminal
  rcases hterminal with ⟨hpure, hdegree⟩ | ⟨hgal, hdegreePrime⟩
  · let := hpure
    exact exists_finite_extension_isWeakSolution_of_isPurelyInseparable
      A B C K L M p hdegree hweak
  · let := hgal
    by_cases hdegree : Module.finrank L M = p
    · exact hwild A B C K L M hweak hepp hdegree
    · let : Module.Finite B C := module_finite_of_isAdicComplete_of_finite_fractionRing B C L M
      let : IsAdicComplete (IsLocalRing.maximalIdeal C) C := isAdicComplete_of_finite B C
      have htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
          Nat.Coprime (ringChar (IsLocalRing.ResidueField A))
              (IsDiscreteValuationRing.ramificationIndex A C) ∧
            Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
              (IsLocalRing.ResidueField C) := by
        refine Or.inr ⟨?_, Algebra.isSeparableExtension_of_perfectField _ _⟩
        rw [ringChar.eq (IsLocalRing.ResidueField A) p]
        have hd : IsDiscreteValuationRing.ramificationIndex B C ∣ Module.finrank L M := by
          rw [IsFractionRing.finrank_eq B L C M, ramificationIndex_eq_ramificationIdx B C]
          exact ramificationIdx_dvd_finrank_of_isLocalRing B C
        have he : IsDiscreteValuationRing.ramificationIndex A C =
            IsDiscreteValuationRing.ramificationIndex B C := by
          have h := Ideal.ramificationIdx_tower (R := A)
            (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal C)
          rw [← ramificationIndex_eq_ramificationIdx A C,
            ← ramificationIndex_eq_ramificationIdx A B,
            ← ramificationIndex_eq_ramificationIdx B C] at h
          simpa only [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hweak, one_mul]
            using h
        rw [he]
        exact ((Nat.coprime_primes (Fact.out : p.Prime) hdegreePrime).mpr
          (Ne.symm hdegree)).of_dvd_right hd
      obtain ⟨K₂, hK₂, hKK₂, hAK₂, htower, hfin, -, D, hD⟩ :=
        exists_finite_extension_isWeakSolution_of_tame_or_charZero A C K M htame
      exact ⟨K₂, hK₂, hKK₂, hAK₂, htower, hfin, D, hD⟩

/-- A one-member prime-degree solver automatically gives the synchronized finite-family solver
over a perfect residue field.

Apply the one-member solver independently, embed the finitely many resulting fields in one finite
overfield, and use
`exists_finite_extension_forall_isWeakSolution_of_perfect_residueField` to preserve every weak
solution.  Thus the synchronization once built into the degree induction is not additional
mathematics in the perfect-residue setting. -/
theorem familyPrimeDegreeSolvable_of_primeDegreeSolvable (p : ℕ) [Fact p.Prime]
    (hsingle : PrimeDegreeSolvable.{u} p) : FamilyPrimeDegreeSolvable.{u} p := by
  intro ι _ A K B C L M
  intros
  rename_i hweak _ hepp hterminal
  have hsol : ∀ i, ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
      (_ : IsScalarTower A K E) (_ : Module.Finite K E),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
        A (C i) K (M i) E, D.IsWeakSolution := fun i =>
    hsingle A (B i) (C i) K (L i) (M i) (hweak i) (hepp i) (hterminal i)
  choose E hE hKE hAE htower hfin D hD using hsol
  let := hE
  let := hKE
  let := hAE
  let := htower
  let := hfin
  let : ∀ i, Module.Finite (B i) (C i) := fun i =>
    module_finite_of_isAdicComplete_of_finite_fractionRing (B i) (C i) (L i) (M i)
  let : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (C i)) (C i) := fun i =>
    isAdicComplete_of_finite (B i) (C i)
  exact exists_finite_extension_forall_isWeakSolution_of_perfect_residueField
    A K C M E D hD

end TowerFamily

end Stacks.EppTheorem

end
