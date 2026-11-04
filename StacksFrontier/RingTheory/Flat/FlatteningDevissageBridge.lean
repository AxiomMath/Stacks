module

public import StacksFrontier.RingTheory.Flat.FlatteningProjectiveCriterion

/-!
# From the dévissage criterion to the local flattening ideal

In the situation of Stacks Tag 05MK — a local homomorphism `A → B` of local rings and a
`B`-module `M` — the source's proof of Stacks Tag 05PG ends by recognizing the flatness
condition of Stacks Tag 05ML as a condition on one map `α₁ : B₁^{⊕ r₁} → M₁` coming out of a
complete dévissage. The two statements it uses about that map are of different shapes:

* Stacks Tag 05I3 (`Module.flat_localizedModule_tfae`) delivers *injectivity* of `α₁` after base
  change, and
* Stacks Tag 05PE (`Module.exists_ideal_bijective_rTensor_iff_map_eq_bot`) consumes
  *bijectivity* of a surjection out of a projective module after base change.

The source closes that gap in its last paragraph: with `N₁ = Im(α₁)` the sequence
`0 → N₁ → M₁ → Coker(α₁) → 0` is universally exact because `Coker(α₁)` is flat over `A`, so
`α₁ ⊗ 1_{A'}` is injective exactly when `B₁^{⊕ r₁} ⊗_A A' → N₁ ⊗_A A'` is an isomorphism. This
file proves that step and feeds it into
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff`, so that the
remaining obligation of Stacks Tag 05PG is stated in the shape Stacks Tag 05I3 produces rather
than in the shape Stacks Tag 05PE consumes.

The step is proved under projectivity of `Coker(α₁)` rather than flatness. That is what the
source has available: Stacks Tag 05I4
(`Module.CompleteDevissage.nonempty_linearEquiv_directSum`) makes `Coker(α₁)` a direct sum of the
smooth lower algebras of the tail of the dévissage, each of which is projective over `A`. With a
projective cokernel the quotient map `M₁ → Coker(α₁)` splits, so `N₁ → M₁` is a split injection
and stays injective after *any* base change, with no appeal to universal exactness. The flat case
would go through `Module.Flat.iff_forall_rTensor_injective_of_exact` (Stacks Tag 058M) instead,
at the cost of its universe restrictions.

## Main results

* `LinearMap.exists_leftInverse_subtype_range_of_projective_quotient`: if the cokernel of `α` is
  projective then the inclusion of `Im(α)` into the target has a left inverse.
* `LinearMap.injective_rTensor_subtype_range_of_projective_quotient`: consequently that inclusion
  is injective after an arbitrary base change.
* `LinearMap.bijective_rTensor_rangeRestrict_iff_injective_rTensor`: the corestriction of `α` to
  its image is bijective after base change exactly when `α` is injective after base change.
* `Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_injective`,
  `Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_map_eq_bot_of_injective` and
  `Module.FlatAtPointSituation.exists_fg_ideal_conditionOn_iff_map_eq_bot_of_injective`: the
  conclusions of Stacks Tag 05PG from the base-change injectivity of a map out of a projective
  `A`-module with projective cokernel.

## Implementation notes

Nothing here proves Stacks Tag 05PG, and nothing here carries its tag. The hypothesis `hinj`
below is still equivalent to the conclusion — apply the results to `α = I.mkQ`, whose image is
all of `A ⧸ I` and whose cokernel is zero — exactly as the hypothesis of
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff` is. What changes
is the shape: `hinj` is an injectivity statement about a map whose cokernel is projective, which
is what a complete dévissage together with Stacks Tags 05I3 and 05I4 produces, and no longer
mentions the image of that map.

## References

* [Stacks Project, Tag 058M](https://stacks.math.columbia.edu/tag/058M)
* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05PE](https://stacks.math.columbia.edu/tag/05PE)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

universe u v w x y z

namespace LinearMap

variable {A : Type u} [CommRing A] {P : Type y} {N : Type z} [AddCommGroup P] [Module A P]
  [AddCommGroup N] [Module A N]

/-- **The inclusion of the image of a map with projective cokernel splits.** If `N ⧸ Im(α)` is
projective over `A` then there is `ρ : N →ₗ[A] Im(α)` restricting to the identity on `Im(α)`.

The quotient map `N → N ⧸ Im(α)` admits a section `σ` because the quotient is projective, and
`1 - σ ∘ (N → N ⧸ Im(α))` lands in `Im(α)` and is the identity there. -/
theorem exists_leftInverse_subtype_range_of_projective_quotient (α : P →ₗ[A] N)
    [Module.Projective A (N ⧸ LinearMap.range α)] :
    ∃ ρ : N →ₗ[A] LinearMap.range α, ρ ∘ₗ (LinearMap.range α).subtype = LinearMap.id := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (LinearMap.range α).mkQ
    (LinearMap.id (R := A) (M := N ⧸ LinearMap.range α)) (Submodule.mkQ_surjective _)
  have hker : ∀ n : N, (LinearMap.range α).mkQ n = 0 ↔ n ∈ LinearMap.range α := fun n ↦ by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  let τ : N →ₗ[A] N := LinearMap.id - σ ∘ₗ (LinearMap.range α).mkQ
  have hmem : ∀ n : N, τ n ∈ LinearMap.range α := by
    intro n
    refine (hker _).mp ?_
    have hs : (LinearMap.range α).mkQ (σ ((LinearMap.range α).mkQ n)) =
        (LinearMap.range α).mkQ n := congrFun (congrArg DFunLike.coe hσ) _
    simp only [τ, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp,
      Function.comp_apply, map_sub, hs, sub_self]
  refine ⟨LinearMap.codRestrict _ τ hmem, LinearMap.ext fun n ↦ Subtype.ext ?_⟩
  have hn : (LinearMap.range α).mkQ (n : N) = 0 := (hker _).mpr n.2
  simp [τ, hn]

/-- **The inclusion of the image of a map with projective cokernel is universally injective.**
It has a left inverse by `LinearMap.exists_leftInverse_subtype_range_of_projective_quotient`, and
a left inverse survives tensoring. -/
theorem injective_rTensor_subtype_range_of_projective_quotient (α : P →ₗ[A] N)
    [Module.Projective A (N ⧸ LinearMap.range α)] (Q : Type x) [AddCommGroup Q] [Module A Q] :
    Function.Injective (((LinearMap.range α).subtype).rTensor Q) := by
  obtain ⟨ρ, hρ⟩ := exists_leftInverse_subtype_range_of_projective_quotient α
  have h : (ρ.rTensor Q) ∘ₗ (((LinearMap.range α).subtype).rTensor Q) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hρ, LinearMap.rTensor_id]
  intro s t hst
  have := congrArg (ρ.rTensor Q) hst
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, h] at this
  simpa using this

/-- **The universal-exactness step of the source's proof of Stacks Tag 05PG.** If the cokernel of
`α : P → N` is projective over `A` then for every `A`-module `Q` the corestriction
`P → Im(α)` is bijective after tensoring with `Q` exactly when `α` itself is injective after
tensoring with `Q`.

Tensoring the factorization `α = (Im α ↪ N) ∘ (P ↠ Im α)` with `Q` keeps the second factor
surjective, and the first factor stays injective by
`LinearMap.injective_rTensor_subtype_range_of_projective_quotient`. So the composite is injective
exactly when the surjection is, and for a surjection injectivity is bijectivity.

In the source `α` is the map `α₁ : B₁^{⊕ r₁} → M₁` of a complete dévissage, `Im(α) = N₁`, and the
projectivity of `Coker(α₁)` comes from Stacks Tag 05I4. The source argues instead from flatness
of `Coker(α₁)` and the universal exactness of Stacks Tag 058M. -/
theorem bijective_rTensor_rangeRestrict_iff_injective_rTensor (α : P →ₗ[A] N)
    [Module.Projective A (N ⧸ LinearMap.range α)] (Q : Type x) [AddCommGroup Q] [Module A Q] :
    Function.Bijective (α.rangeRestrict.rTensor Q) ↔ Function.Injective (α.rTensor Q) := by
  have hsplit : ((LinearMap.range α).subtype).comp α.rangeRestrict = α := rfl
  have hcomp : α.rTensor Q =
      ((LinearMap.range α).subtype).rTensor Q ∘ₗ α.rangeRestrict.rTensor Q := by
    rw [← LinearMap.rTensor_comp, hsplit]
  have hsub := injective_rTensor_subtype_range_of_projective_quotient α Q
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, LinearMap.rTensor_surjective Q α.surjective_rangeRestrict⟩⟩
  · rw [hcomp]
    simpa only [LinearMap.coe_comp] using hsub.comp h.1
  · rw [hcomp] at h
    simp only [LinearMap.coe_comp] at h
    exact h.of_comp

end LinearMap

/-- The cokernel of a quotient map `M → M ⧸ p`, read as a map of `A`-modules, is zero, hence
projective. This is what makes
`Module.FlatAtPointSituation.conditionOn_iff_injective_rTensor_mkQ` an instance of the theorems
below. -/
instance Submodule.projective_quotient_range_mkQ {A : Type u} [CommRing A] {M : Type z}
    [AddCommGroup M] [Module A M] (p : Submodule A M) :
    Module.Projective A ((M ⧸ p) ⧸ LinearMap.range p.mkQ) := by
  have hrange : LinearMap.range p.mkQ = ⊤ :=
    LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective p)
  rw [hrange]
  have hsub : Subsingleton ((M ⧸ p) ⧸ (⊤ : Submodule A (M ⧸ p))) := by
    refine ⟨fun y z ↦ ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (⊤ : Submodule A (M ⧸ p)) y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (⊤ : Submodule A (M ⧸ p)) z
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact Submodule.mem_top
  have _ : Module.Free A ((M ⧸ p) ⧸ (⊤ : Submodule A (M ⧸ p))) :=
    Module.Free.of_subsingleton _ _
  exact Module.Projective.of_free

namespace Module.FlatAtPointSituation

/-- **The endgame of the source's proof of Stacks Tag 05PG, in the shape Stacks Tag 05I3
produces.** Suppose the flatness condition of Stacks Tag 05ML over a local `A`-algebra `R` is
equivalent to the *injectivity* of `α ⊗ R` for one fixed map `α : P → N` of `A`-modules with `P`
projective and `N ⧸ Im(α)` projective over `A`. Then there is an ideal `I ⊆ A` which
simultaneously corepresents the condition on the category `C` of Stacks Tag 05MK and
characterizes the flattening ideals as the ideals containing it.

This is `Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff` applied to
the corestriction `P → Im(α)`, whose base-change bijectivity is the base-change injectivity of
`α` by `LinearMap.bijective_rTensor_rangeRestrict_iff_injective_rTensor`.

In the source `α` is the map `α₁ : B₁^{⊕ r₁} → M₁` of a complete dévissage: `P` is projective
over `A` because the lower algebras of a dévissage are (Stacks Tag 05FT), and `Coker(α₁)` is
projective over `A` by Stacks Tag 05I4. Nothing here discharges `hinj`, which is still equivalent
to the conclusion, so nothing here carries the tag of Stacks Tag 05PG. -/
theorem exists_ideal_flattens_iff_le_and_conditionOn_iff_of_injective
    (S : FlatAtPointSituation.{u, v, w})
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective S.A (N ⧸ LinearMap.range α)]
    (hinj : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔ Function.Injective (α.rTensor R)) :
    ∃ I : Ideal S.A, (∀ J : Ideal S.A, S.Flattens J ↔ I ≤ J) ∧
      ∀ R : LocalAlgCat.{u, x} S.A,
        S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
  S.exists_ideal_flattens_iff_le_and_conditionOn_iff α.rangeRestrict α.surjective_rangeRestrict
    fun R _ _ _ _ ↦ (hinj R).trans
      (LinearMap.bijective_rTensor_rangeRestrict_iff_injective_rTensor α R).symm

/-- **Stacks Project, Tag 05PG**, granting that the flatness condition of Stacks Tag 05ML is the
base-change injectivity of a map out of a projective `A`-module with projective cokernel. There is
an ideal `I ⊆ A` such that for every local `A`-algebra `R` with local structure map the condition
over `R` holds exactly when `I` dies in `R`; that is, `A ⧸ I` corepresents the functor `F_lf` of
Stacks Tag 05MK.

The henselian, essentially-finite-type and finiteness hypotheses of the source are carried because
they are what the dévissage producing `α` needs; they are not used here. Nothing in this file
proves Stacks Tag 05PG, so the result is untagged. -/
theorem exists_ideal_conditionOn_iff_map_eq_bot_of_injective
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    [Algebra.EssFiniteType S.A S.B] [Module.Finite S.B S.M]
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective S.A (N ⧸ LinearMap.range α)]
    (hinj : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔ Function.Injective (α.rTensor R)) :
    ∃ I : Ideal S.A, ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨I, -, hcore⟩ := S.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_injective α hinj
  exact ⟨I, hcore⟩

/-- **Stacks Project, Tag 05PG**, finite generation, granting the same single hypothesis. Under
the finite-presentation hypotheses of the source the corepresenting ideal may be taken finitely
generated.

The ideal produced by
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_injective`
flattens the situation, so `Module.FlatAtPointSituation.flattensFGApprox` — the limit preservation
of Stacks Tag 05MN, already proved — returns a finitely generated flattening ideal below it, which
the characterization of the flattening ideals forces to be the ideal itself.

Nothing here proves Stacks Tag 05PG, so the result is untagged. -/
theorem exists_fg_ideal_conditionOn_iff_map_eq_bot_of_injective
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    (hB : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M]
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective S.A (N ⧸ LinearMap.range α)]
    (hinj : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔ Function.Injective (α.rTensor R)) :
    ∃ I : Ideal S.A, I.FG ∧ ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨I, hchar, hcore⟩ := S.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_injective α hinj
  obtain ⟨J, hJle, hJfg, hJflat⟩ := S.flattensFGApprox hB I ((hchar I).mpr le_rfl)
  exact ⟨I, le_antisymm ((hchar J).mp hJflat) hJle ▸ hJfg, hcore⟩

/-- **The hypothesis of the three theorems above is their conclusion.** If an ideal `I` of `A`
corepresents the flatness condition of Stacks Tag 05ML, then the condition is the base-change
*injectivity* of the quotient map `A → A ⧸ I`, which is a map out of the free, hence projective,
`A`-module `A` whose cokernel is zero.

So the hypothesis `hinj` is not weaker than the conclusion of Stacks Tag 05PG, and none of the
theorems above is a proof of it. What the hypothesis provides is a *shape*: the obligation becomes
the injectivity of one linear map after base change, with a projective cokernel — which is what a
complete dévissage, Stacks Tag 05I3 and Stacks Tag 05I4 produce. -/
theorem conditionOn_iff_injective_rTensor_mkQ (S : FlatAtPointSituation.{u, v, w})
    {I : Ideal S.A}
    (hI : ∀ R : LocalAlgCat.{u, max u x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥)
    (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
    [IsLocalHom (algebraMap S.A R)] :
    S.ConditionOn R ↔ Function.Injective (I.mkQ.rTensor R) := by
  rw [S.conditionOn_iff_bijective_rTensor_mkQ hI R]
  exact ⟨And.left, fun h ↦ ⟨h, LinearMap.rTensor_surjective R (Submodule.mkQ_surjective I)⟩⟩

end Module.FlatAtPointSituation

end
