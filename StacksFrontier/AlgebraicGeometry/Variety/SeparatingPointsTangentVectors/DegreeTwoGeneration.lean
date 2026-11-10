module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.PinnedTwist
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwoClassification

/-!
# Generation of an invertible module from the degree-two hypothesis

Let `k` be an algebraically closed field, let `X` be proper over `k` through `p` and let `ℒ` be
an invertible module on `X`. If `H⁰(X, ℒ) ⟶ H⁰(Z, ℒ|_Z)` is surjective for every closed
subscheme `Z ⊆ X` which is zero-dimensional of degree two over `k`, then the global sections of
`ℒ` generate it.

This is the step of [Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T) that cannot be
routed through condition (1) of [Stacks, Tag
0E8S](https://stacks.math.columbia.edu/tag/0E8S): separation of closed points does not imply
generation when `X` has a single closed point, as
`StacksFrontier/AlgebraicGeometry/Variety/SeparatingPointsTangentVectors/Basic.lean` records with
two counterexamples. The degree-two hypothesis is therefore consumed directly, and the
one-point case is treated on its own, where an invertible module has a nonvanishing global
section outright.

## Main results

* `AlgebraicGeometry.exists_mem_nonvanishingLocus_of_isClosed`: at every closed point of `X`
  some global section of `ℒ` is nonvanishing. With a second closed point available this is the
  separating section of the degree-two subscheme carried by the pair; without one the space is a
  single point.
* `AlgebraicGeometry.generatesStalks_id_of_surjectsOnDegreeTwo`: **the complete linear system of
  `ℒ` generates it**, in the form `Stacks.ProjectiveFromSections.GeneratesStalks` that the
  morphism to projective space of [Stacks, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
  consumes. The nonvanishing opens cover the closed points, hence cover `X`, the closed points
  being dense in every closed subset of a scheme locally of finite type over a field.
* `AlgebraicGeometry.exists_fin_generatesStalks_of_surjectsOnDegreeTwo`: finitely many global
  sections already generate, `X` being quasi-compact over the field.
* `AlgebraicGeometry.exists_hom_projectiveSpaceOver_of_surjectsOnDegreeTwo`: **the morphism to
  projective space of [Stacks, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY) exists**
  under the degree-two hypothesis alone, together with an isomorphism of the pulled-back
  degree-one twist with `ℒ` carrying the homogeneous coordinates to the generating sections.

## Auxiliary results

* `AlgebraicGeometry.maximalIdeal_stalk_eq_bot_of_field` and
  `AlgebraicGeometry.mem_nonvanishingLocus_of_ne_zero_of_field`: on the spectrum of a field every
  nonzero global section of a module is nonvanishing.
* `AlgebraicGeometry.mem_nonvanishingLocus_of_not_vanishesAlong`: a global section which does not
  vanish at a point, in the sense that its pullback to the residue-field point is nonzero, is
  nonvanishing there. This is [Stacks, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
  together with the previous item.
* `AlgebraicGeometry.exists_mem_nonvanishingLocus_of_subsingleton`: on a one-point scheme an
  invertible module has a global section nonvanishing at that point.
* `AlgebraicGeometry.generatesStalks_of_forall_exists_mem_nonvanishingLocus`: a family of global
  sections of an invertible module which at every point has a nonvanishing member generates the
  stalks.

## What is not proved here

The morphism produced here realizes the linear system spanned by the finitely many generating
sections, and nothing below shows that system to be *complete*: the criterion of
[Stacks, Tag 0E8S](https://stacks.math.columbia.edu/tag/0E8S), as
`AlgebraicGeometry.isClosedImmersion_of_surjectsOnDegreeTwo` consumes it, asks the family of
sections to exhaust `H⁰(X, ℒ)`, because the separating section the degree-two hypothesis
produces is an arbitrary global section and must itself be pulled back from the target. Closing
that gap needs the finite-dimensionality of `H⁰(X, ℒ)` of
[Stacks, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6) — so that a `k`-basis can be taken
as the generating family — together with the `k`-linearity of the comparison
`H⁰(𝐏, 𝒪(1)) ⟶ H⁰(X, ℒ)` and of vanishing at a point, neither of which is available at the
spelling in which the pullback of sections is stated here. So
`AlgebraicGeometry.isRelativelyVeryAmple_of_surjectsOnDegreeTwo_of_complete` still takes its
morphism, its twist isomorphism and its completeness hypothesis.

## References

* [Stacks Project, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Ample (IsInvertibleModule)

universe u

namespace AlgebraicGeometry

/-! ### Nonvanishing at a point and vanishing along the residue-field point -/

/-- **The local ring of the spectrum of a field has zero maximal ideal**, being the field. -/
theorem maximalIdeal_stalk_eq_bot_of_field (K : Type u) [Field K] (z : Spec (.of K)) :
    IsLocalRing.maximalIdeal ((Spec (.of K)).presheaf.stalk z) = ⊥ := by
  let e : (Spec (.of K)).presheaf.stalk z ≅ CommRingCat.of K :=
    (Spec (.of K)).presheaf.stalkCongr
      (by rw [show z = IsLocalRing.closedPoint K from Subsingleton.elim _ _]; rfl) ≪≫
      stalkClosedPointIso (.of K)
  exact (Ideal.map_eq_bot_iff_of_injective (ConcreteCategory.bijective_of_isIso e.hom).1).mp
    ((IsLocalRing.map_maximalIdeal_of_surjective e.hom.hom
      (ConcreteCategory.bijective_of_isIso e.hom).2).trans IsLocalRing.maximalIdeal_eq_bot)

/-- **A nonzero global section of a module on the spectrum of a field is nonvanishing.** The
local ring is the field, so `𝔪 · M` is the zero submodule, and the germ of a nonzero global
section on a one-point space is nonzero. -/
theorem mem_nonvanishingLocus_of_ne_zero_of_field (K : Type u) [Field K]
    (M : (Spec (.of K)).Modules) (t : Γ(M, ⊤)) (ht : t ≠ 0) (z : Spec (.of K)) :
    z ∈ Stacks.Ample.nonvanishingLocus M t := by
  have hbot : Stacks.ModuleStalk.maximalSmul M z = ⊥ := by
    change IsLocalRing.maximalIdeal ((Spec (.of K)).presheaf.stalk z) • (⊤ : Submodule _ _) = ⊥
    rw [maximalIdeal_stalk_eq_bot_of_field, Submodule.bot_smul]
  intro hmem
  rw [hbot, Submodule.mem_bot] at hmem
  refine ht ?_
  let F : TopCat.Sheaf AddCommGrpCat.{u} (Spec (.of K)) := ⟨M.presheaf, M.isSheaf⟩
  refine TopCat.Presheaf.section_ext F ⊤ t 0 fun y _ => ?_
  rw [Subsingleton.elim y z, map_zero]
  exact hmem

/-- **A global section which does not vanish at a point is nonvanishing there.** Vanishing at `x`
means that the pullback of the section to `Spec κ(x)` is zero; the nonvanishing locus of that
pullback is the preimage of the nonvanishing locus by [Stacks, Tag
0H78](https://stacks.math.columbia.edu/tag/0H78), and over a field a nonzero section is
nonvanishing. -/
theorem mem_nonvanishingLocus_of_not_vanishesAlong {X : Scheme.{u}} (L : X.Modules) (x : X)
    (s : Γ(L, ⊤)) (hs : ¬ VanishesAlong (X.fromSpecResidueField x) s) :
    x ∈ Stacks.Ample.nonvanishingLocus L s := by
  have hz := mem_nonvanishingLocus_of_ne_zero_of_field (X.residueField x)
    ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj L)
    (Stacks.NonvanishingPullback.pullbackGlobalSection (X.fromSpecResidueField x) L s) hs
    (IsLocalRing.closedPoint (X.residueField x))
  have h := (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff
    (X.fromSpecResidueField x) L s
    (IsLocalRing.closedPoint (X.residueField x))).mp hz
  have heq : (X.fromSpecResidueField x) (IsLocalRing.closedPoint (X.residueField x)) = x :=
    X.fromSpecResidueField_apply x _
  rwa [heq] at h

/-! ### Generation from the degree-two hypothesis -/

/-- **A family of global sections of an invertible module, one of which is nonvanishing at every
point, generates the stalks.** At a point where `tᵢ` does not vanish its germ already spans the
stalk, by Nakayama at a rank-one stalk. -/
theorem generatesStalks_of_forall_exists_mem_nonvanishingLocus {X : Scheme.{u}} (M : X.Modules)
    [IsInvertibleModule X M] {ι : Type u} (t : ι → Γ(M, ⊤))
    (h : ∀ x : X, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus M (t i)) :
    Stacks.ProjectiveFromSections.GeneratesStalks t :=
  Stacks.StalkwiseGeneration.generatesStalks_of_span_eq_top t fun x =>
    (h x).elim fun _ hi => Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus M t hi

/-- **On a one-point scheme an invertible module has a global section nonvanishing at that
point.** Some element of the stalk avoids `𝔪 · M`, every stalk element is the germ of a section
over an open neighbourhood, and the only open neighbourhood is the whole space. -/
theorem exists_mem_nonvanishingLocus_of_subsingleton {X : Scheme.{u}} [Subsingleton X]
    (M : X.Modules) [IsInvertibleModule X M] (x : X) :
    ∃ s : Γ(M, ⊤), x ∈ Stacks.Ample.nonvanishingLocus M s := by
  obtain ⟨w, hw⟩ := Stacks.SectionProduct.exists_notMem_maximalSmul M x
  obtain ⟨U, hU, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) M.presheaf w
  have hUtop : U = ⊤ := top_unique fun z _ => by rwa [Subsingleton.elim z x]
  subst hUtop
  refine ⟨s₀, ?_⟩
  rwa [Stacks.Ample.mem_nonvanishingLocus_iff, show (M.presheaf.Γgerm x).hom s₀ = w from hs₀]

/-- A scheme which is not a single point has, beside any given closed point, another one: the
closed points are dense, so they cannot all equal one of them unless the space is a
subsingleton. -/
theorem exists_isClosed_singleton_ne {X : Scheme.{u}} [JacobsonSpace X] (hX : ¬ Subsingleton X)
    (y : X) (hy : IsClosed ({y} : Set X)) :
    ∃ x : X, IsClosed ({x} : Set X) ∧ x ≠ y := by
  by_contra! h
  have hc : closedPoints X ⊆ ({y} : Set X) := fun x hx => h x hx
  have hu : (Set.univ : Set X) ⊆ {y} := by
    rw [← closure_closedPoints]
    exact closure_minimal hc hy
  exact hX ⟨fun a b => (hu (Set.mem_univ a)).trans (hu (Set.mem_univ b)).symm⟩

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- **At a closed point some global section of `ℒ` is nonvanishing.** If `X` has another closed
point, the degree-two hypothesis separates the two and the separating section does not vanish at
the second; and if it has not, `X` is a single point and an invertible module there has a
nonvanishing global section outright. -/
theorem exists_mem_nonvanishingLocus_of_isClosed (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : X.Modules) [IsInvertibleModule X L] (hsurj : SurjectsOnDegreeTwo p L)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ s : Γ(L, ⊤), x ∈ Stacks.Ample.nonvanishingLocus L s := by
  by_cases hsub : Subsingleton X
  · exact exists_mem_nonvanishingLocus_of_subsingleton L x
  · let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
    obtain ⟨y, hy, hyx⟩ := exists_isClosed_singleton_ne hsub x hx
    obtain ⟨s, -, hns⟩ := separatesClosedPoints_of_surjectsOnDegreeTwo p hsurj
      (hasDegreeTwoPointPairs p L) (ψ := id) Function.surjective_id y x hy hx hyx
    exact ⟨s, mem_nonvanishingLocus_of_not_vanishesAlong L x s hns⟩

/-- **The complete linear system of `ℒ` generates it.** The nonvanishing opens of the global
sections cover the closed points by the degree-two hypothesis, hence cover `X`, the closed points
being dense in every closed subset of a scheme locally of finite type over a field.

This is the step of [Stacks, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T) which cannot be
routed through separation of closed points alone: on a scheme with a single closed point
separation is vacuous and generation can fail, so the hypothesis is consumed directly. -/
theorem generatesStalks_id_of_surjectsOnDegreeTwo (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : X.Modules) [IsInvertibleModule X L] (hsurj : SurjectsOnDegreeTwo p L) :
    Stacks.ProjectiveFromSections.GeneratesStalks (id : Γ(L, ⊤) → Γ(L, ⊤)) := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  refine generatesStalks_of_forall_exists_mem_nonvanishingLocus L id fun z => ?_
  by_contra hz
  push Not at hz
  set Z : Set X := {w : X | ∀ s : Γ(L, ⊤), w ∉ Stacks.Ample.nonvanishingLocus L s} with hZ
  have hZclosed : IsClosed Z := by
    rw [hZ, show {w : X | ∀ s : Γ(L, ⊤), w ∉ Stacks.Ample.nonvanishingLocus L s} =
      (⋃ s : Γ(L, ⊤), Stacks.Ample.nonvanishingLocus L s)ᶜ by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]]
    exact isClosed_compl_iff.mpr (isOpen_iUnion fun s =>
      Stacks.NonvanishingOpen.isOpen_nonvanishingLocus X L s)
  have hempty : Z ∩ closedPoints X = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
    obtain ⟨s, hs⟩ := exists_mem_nonvanishingLocus_of_isClosed p L hsurj w hw.2
    exact hw.1 s hs
  have hclosure := JacobsonSpace.closure_inter_closedPoints hZclosed
  rw [hempty, closure_empty] at hclosure
  exact (hclosure ▸ hz : z ∈ (∅ : Set X))

/-- **At every point some global section of `ℒ` is nonvanishing**, the degree-two hypothesis
holding. This is `AlgebraicGeometry.generatesStalks_id_of_surjectsOnDegreeTwo` read pointwise. -/
theorem exists_mem_nonvanishingLocus_of_surjectsOnDegreeTwo (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : X.Modules) [IsInvertibleModule X L] (hsurj : SurjectsOnDegreeTwo p L) (z : X) :
    ∃ s : Γ(L, ⊤), z ∈ Stacks.Ample.nonvanishingLocus L s :=
  Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks _
    (generatesStalks_id_of_surjectsOnDegreeTwo p L hsurj) z

/-- **Finitely many global sections of `ℒ` already generate it.** The nonvanishing opens of the
complete linear system cover `X`, which is quasi-compact over the field, so finitely many of
them do; the family is indexed by `Fin (n + 1)` with the zero section in the last slot, which is
the shape the morphism to `ℙⁿ` of [Stacks, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
consumes. -/
theorem exists_fin_generatesStalks_of_surjectsOnDegreeTwo (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : X.Modules) [IsInvertibleModule X L] (hsurj : SurjectsOnDegreeTwo p L) :
    ∃ (n : ℕ) (t : Fin (n + 1) → Γ(L, ⊤)), Stacks.ProjectiveFromSections.GeneratesStalks t := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hcov : (Set.univ : Set X) ⊆
      ⋃ s : Γ(L, ⊤), (Stacks.NonvanishingOpen.nonvanishingOpen X L s : Set X) := by
    intro z _
    obtain ⟨s, hs⟩ := exists_mem_nonvanishingLocus_of_surjectsOnDegreeTwo p L hsurj z
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun s : Γ(L, ⊤) => (Stacks.NonvanishingOpen.nonvanishingOpen X L s : Set X))
    (fun s => (Stacks.NonvanishingOpen.nonvanishingOpen X L s).isOpen) hcov
  refine ⟨T.card, Fin.lastCases 0 fun j => (T.equivFin.symm j : Γ(L, ⊤)), ?_⟩
  rw [← Stacks.ProjectiveFromSections.generatesStalks_ulift_iff]
  refine generatesStalks_of_forall_exists_mem_nonvanishingLocus L _ fun z => ?_
  obtain ⟨s, hsT, hz⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ z))
  refine ⟨ULift.up (Fin.castSucc (T.equivFin ⟨s, hsT⟩)), ?_⟩
  change z ∈ Stacks.Ample.nonvanishingLocus L
    (Fin.lastCases 0 (fun j => (T.equivFin.symm j : Γ(L, ⊤)))
      (Fin.castSucc (T.equivFin ⟨s, hsT⟩)))
  rw [Fin.lastCases_castSucc]
  simpa using hz

/-- **The degree-two hypothesis produces the morphism to projective space of [Stacks, Tag
0FCY](https://stacks.math.columbia.edu/tag/0FCY), with its identification of the pulled-back
twist.** Finitely many global sections of `ℒ` generate it, and a generating family gives a
morphism `φ : X ⟶ ℙⁿ_k` over `k` and an isomorphism `φ^* 𝒪(1) ≅ ℒ` carrying the `i`-th
homogeneous coordinate to the `i`-th section.

The twist is pulled back along the morphism to the integral model underlying `φ`, which is the
shape `Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse`
provides. -/
theorem exists_hom_projectiveSpaceOver_of_surjectsOnDegreeTwo (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : X.Modules) [IsInvertibleModule X L] (hsurj : SurjectsOnDegreeTwo p L) :
    ∃ (n : ℕ) (φ : X ⟶ projectiveSpaceOver n (Spec (.of k)))
      (t : Fin (n + 1) → Γ(L, ⊤)),
      φ ≫ Limits.pullback.fst (Limits.terminal.from (Spec (.of k)))
          (Limits.terminal.from (projectiveSpaceAtUniverse.{u} n)) = p ∧
      ∃ α : (Scheme.Modules.pullback (φ ≫
          projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
            (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ⟶ L,
        IsIso α ∧ ∀ i, α.app ⊤ (Stacks.TwistPullbackPinned.pullbackCoordSection.{u}
          (φ ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) = t i := by
  obtain ⟨n, t, ht⟩ := exists_fin_generatesStalks_of_surjectsOnDegreeTwo p L hsurj
  obtain ⟨φ, hφ, α, hiso, hα⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse t ht p
  exact ⟨n, φ, t, hφ, α, hiso, hα⟩

end AlgebraicGeometry

end
