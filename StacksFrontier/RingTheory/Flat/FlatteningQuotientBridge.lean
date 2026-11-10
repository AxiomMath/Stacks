module

public import StacksFrontier.RingTheory.Flat.FlatteningDevissageBridge
public import StacksFrontier.RingTheory.Flat.FlatteningStageStep

/-!
# The induction step of the local flattening theorem

`StacksFrontier.RingTheory.Flat.FlatteningDevissageBridge` reduces Stacks Tag 05PG to the
base-change injectivity of one map `α : P → N` of `A`-modules with `P` projective over `A` *and*
`N ⧸ Im(α)` projective over `A`. The second half of that hypothesis is not what a complete
dévissage supplies: Stacks Tag 05I4 makes `Coker(α₁)` free over the base only once
`Coker(α₁)_{𝔮₁}` is already flat over the base, which is exactly what the source arranges by the
sentence *"hence we may replace `A` by `A/J`"* — `J` being the ideal the induction hypothesis
produces for the cokernel. Over the original `A` the cokernel is not projective, and the flatness
condition of Stacks Tag 05ML is not the base-change injectivity of `α₁` alone; it is the
*conjunction* of that injectivity with the vanishing of `J`.

This file proves the step in that shape. The data is an ideal `J ⊆ A` and a map `α : P → N` of
`A`-modules with `P` projective over `A` whose cokernel becomes projective **after reduction
modulo `J`**, and the hypothesis is that the flatness condition over a local `A`-algebra `R` is
the conjunction of `J R = 0` with injectivity of `α ⊗ R`. The conclusion is the full conclusion of
Stacks Tag 05PG: an ideal `I ⊇ J` which corepresents the condition and cuts out the flattening
ideals.

The ideal is produced by Stacks Tag 05PE over `A ⧸ J` rather than over `A`: the reduced source
`(A ⧸ J) ⊗_A P` is projective over `A ⧸ J` but not over `A`, so the flattening ideal of the
reduced map lives in `A ⧸ J`, and `I` is its preimage. A local `A`-algebra in which `J` dies is
an `A ⧸ J`-algebra, and `LinearMap.baseChange_baseChange` identifies the two base changes of `α`
to it, which is what makes the two readings of the injectivity agree.

## Main definitions

There are no new definitions.

## Main results

* `LinearMap.injective_baseChange_baseChange_iff`: for a test algebra over an intermediate
  algebra, base changing in one step or in two gives the same injectivity.
* `LinearMap.quotRangeBaseChangeEquiv` and `Module.Projective.quotient_range_baseChange`: the
  cokernel of a base change is the base change of the cokernel.
* `Module.FlatAtPointSituation.exists_ideal_le_ker_iff_injective_rTensor_of_quotient`: the
  flattening ideal of `α` modulo `J`, pulled back to `A`.
* `Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_quotient`,
  `Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_map_eq_bot_of_quotient` and
  `Module.FlatAtPointSituation.exists_fg_ideal_conditionOn_iff_map_eq_bot_of_quotient`: the
  conclusions of Stacks Tag 05PG from that single hypothesis.
* `Module.FlatAtPointSituation.exists_fg_smallest_flattens_of_quotient` and
  `Module.FlatAtPointSituation.exists_fg_smallest_flattens_of_injective`: the smallest flattening
  ideal, finitely generated, in the shape a consumer of the flattening theorem wants.

## Implementation notes

Nothing here proves Stacks Tag 05PG, and nothing here carries its tag: taking `J = ⊥` and
`α = I.mkQ` recovers the hypothesis from the conclusion exactly as in
`StacksFrontier.RingTheory.Flat.FlatteningProjectiveCriterion`. What the statements below change is
the *shape* of the remaining obligation, and the change is not cosmetic — the hypothesis of
`Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_map_eq_bot_of_injective` demands a
projective cokernel over `A`, which the source's dévissage does not provide and which is false in
general, while the hypothesis below demands it only over `A ⧸ J`, which is what Stacks Tag 05I4
gives once `J` is the ideal of the dévissage tail.

The hypothesis is stated with the test algebras in `Type (max u x)`, as in
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff`, because the
characterization of the flattening ideals has to test the quotients `A ⧸ K`, which live in
`Type u`, while the conclusion ranges over `LocalAlgCat.{u, x} A`.

The projectivity hypothesis is stated as `(A ⧸ J) ⊗_A (N ⧸ Im α)`, the reduction of the
cokernel, which is the module Stacks Tag 05I4 makes free. The form
`LinearMap.bijective_rTensor_rangeRestrict_iff_injective_rTensor` consumes is the cokernel of the
reduced map, `((A ⧸ J) ⊗_A N) ⧸ Im((A ⧸ J) ⊗_A α)`; the two agree by right exactness of the
tensor product, which is `LinearMap.quotRangeBaseChangeEquiv`.

## References

* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05MN](https://stacks.math.columbia.edu/tag/05MN)
* [Stacks Project, Tag 05PE](https://stacks.math.columbia.edu/tag/05PE)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w x y z

namespace LinearMap

/-- **Base changing in one step or in two gives the same injectivity.** For an `A`-algebra `A'`
and an `A'`-algebra `R`, a map `α` of `A`-modules is injective after tensoring with `R` over `A`
exactly when its base change to `A'` is injective after tensoring with `R` over `A'`.

The two composites differ by the canonical identifications
`R ⊗_{A'} (A' ⊗_A P) ≃ R ⊗_A P` of `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which
`LinearMap.baseChange_baseChange` records. -/
theorem injective_baseChange_baseChange_iff {A : Type u} [CommRing A] (A' : Type v) [CommRing A']
    [Algebra A A'] (R : Type w) [CommRing R] [Algebra A R] [Algebra A' R] [IsScalarTower A A' R]
    {P : Type y} [AddCommGroup P] [Module A P] {N : Type z} [AddCommGroup N] [Module A N]
    (α : P →ₗ[A] N) :
    Function.Injective ((α.baseChange A').baseChange R) ↔
      Function.Injective (α.baseChange R) := by
  rw [LinearMap.baseChange_baseChange (A := A') (B := R) α]
  change Function.Injective
    (⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A A' R R N).symm ∘
      ⇑(α.baseChange R) ∘ ⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A A' R R P)) ↔ _
  rw [EquivLike.comp_injective _ (TensorProduct.AlgebraTensorModule.cancelBaseChange
      A A' R R N).symm,
    EquivLike.injective_comp (TensorProduct.AlgebraTensorModule.cancelBaseChange A A' R R P)]

/-- **Base changing in one step or in two gives the same injectivity**, for `rTensor` rather than
`baseChange`. This is the reading
`Module.FlatAtPointSituation.exists_ideal_le_ker_iff_injective_rTensor_of_quotient` needs, the
flattening ideal of Stacks Tag 05PE being stated for `rTensor`. -/
theorem injective_rTensor_baseChange_iff {A : Type u} [CommRing A] (A' : Type v) [CommRing A']
    [Algebra A A'] (R : Type w) [CommRing R] [Algebra A R] [Algebra A' R] [IsScalarTower A A' R]
    {P : Type y} [AddCommGroup P] [Module A P] {N : Type z} [AddCommGroup N] [Module A N]
    (α : P →ₗ[A] N) :
    Function.Injective ((α.baseChange A').rTensor R) ↔ Function.Injective (α.rTensor R) := by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, ← LinearMap.lTensor_inj_iff_rTensor_inj,
    ← LinearMap.baseChange_eq_lTensor, ← LinearMap.baseChange_eq_lTensor]
  exact injective_baseChange_baseChange_iff A' R α

end LinearMap

/-- The cokernel of the base change of `α` is projective as soon as the base change of the
cokernel of `α` is. This is `LinearMap.quotRangeBaseChangeEquiv` read on projectivity, and it is
what lets the induction step of Stacks Tag 05PG be stated with the hypothesis Stacks Tag 05I4
supplies. -/
theorem Module.Projective.quotient_range_baseChange {A : Type u} [CommRing A] (A' : Type v)
    [CommRing A'] [Algebra A A'] {P : Type y} [AddCommGroup P] [Module A P]
    {N : Type z} [AddCommGroup N] [Module A N] (α : P →ₗ[A] N)
    [Module.Projective A' (A' ⊗[A] (N ⧸ LinearMap.range α))] :
    Module.Projective A' ((A' ⊗[A] N) ⧸ LinearMap.range (α.baseChange A')) :=
  Module.Projective.of_equiv (LinearMap.quotRangeBaseChangeEquiv A' α).symm

namespace Module.FlatAtPointSituation

/-- A flattening ideal characterized as the smallest one is finitely generated when `A → B` is
essentially of finite presentation and `M` is finitely presented. -/
private theorem fg_of_flattens_iff (S : FlatAtPointSituation.{u, v, w})
    (hB : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M] {I : Ideal S.A}
    (hchar : ∀ K : Ideal S.A, S.Flattens K ↔ I ≤ K) : I.FG := by
  obtain ⟨K, hKle, hKfg, hKflat⟩ := S.flattensFGApprox hB I ((hchar I).mpr le_rfl)
  exact le_antisymm ((hchar K).mp hKflat) hKle ▸ hKfg

/-- **The flattening ideal of a map whose cokernel is projective only after reduction.** Let
`J ⊆ A` be an ideal and let `α : P → N` be a map of `A`-modules with `P` projective over `A`
whose base change to `A ⧸ J` has projective cokernel. There is an ideal `I ⊇ J` of `A` such that
for every `A`-algebra `R` killing `J`, the map `α ⊗ R` is injective exactly when `I` dies in `R`.

Stacks Tag 05PE over `A ⧸ J` gives the flattening ideal of the corestriction of
`(A ⧸ J) ⊗_A α` to its image, whose base-change bijectivity is the base-change injectivity of
`(A ⧸ J) ⊗_A α` by `LinearMap.bijective_rTensor_rangeRestrict_iff_injective_rTensor`; `I` is its
preimage in `A`, and `LinearMap.injective_rTensor_baseChange_iff` identifies the base change of
the reduced map with the base change of `α`. -/
theorem exists_ideal_le_ker_iff_injective_rTensor_of_quotient {A : Type u} [CommRing A]
    (J : Ideal A) {P : Type y} [AddCommGroup P] [Module A P] [Module.Projective A P]
    {N : Type z} [AddCommGroup N] [Module A N] (α : P →ₗ[A] N)
    [Module.Projective (A ⧸ J) ((A ⧸ J) ⊗[A] (N ⧸ LinearMap.range α))] :
    ∃ I : Ideal A, J ≤ I ∧ ∀ (R : Type w) [CommRing R] [Algebra A R],
      J ≤ RingHom.ker (algebraMap A R) →
        (Function.Injective (α.rTensor R) ↔ I ≤ RingHom.ker (algebraMap A R)) := by
  have : Module.Projective (A ⧸ J)
      (((A ⧸ J) ⊗[A] N) ⧸ LinearMap.range (α.baseChange (A ⧸ J))) :=
    Module.Projective.quotient_range_baseChange (A ⧸ J) α
  obtain ⟨K, hK⟩ := Module.exists_ideal_bijective_rTensor_iff_map_eq_bot (A ⧸ J)
    ((A ⧸ J) ⊗[A] P) (LinearMap.range (α.baseChange (A ⧸ J)))
    (α.baseChange (A ⧸ J)).rangeRestrict (α.baseChange (A ⧸ J)).surjective_rangeRestrict
  refine ⟨K.comap (algebraMap A (A ⧸ J)), fun a ha ↦ ?_, ?_⟩
  · rw [Ideal.mem_comap, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact K.zero_mem
  intro R _ _ hJ
  let : Algebra (A ⧸ J) R :=
    (Ideal.Quotient.lift J (algebraMap A R) fun a ha ↦ hJ ha).toAlgebra
  have hmap : ∀ a : A, algebraMap (A ⧸ J) R (algebraMap A (A ⧸ J) a) = algebraMap A R a :=
    fun _ ↦ rfl
  have : IsScalarTower A (A ⧸ J) R := IsScalarTower.of_algebraMap_eq fun a ↦ (hmap a).symm
  rw [← LinearMap.injective_rTensor_baseChange_iff (A ⧸ J) R α,
    ← LinearMap.bijective_rTensor_rangeRestrict_iff_injective_rTensor
      (α.baseChange (A ⧸ J)) R,
    hK R, Ideal.map_eq_bot_iff_le_ker]
  refine ⟨fun h a ha ↦ ?_, fun h a ha ↦ ?_⟩
  · rw [RingHom.mem_ker, ← hmap a]
    exact RingHom.mem_ker.mp (h (Ideal.mem_comap.mp ha))
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.mem_ker, ← Ideal.Quotient.algebraMap_eq, hmap b]
    exact h (show b ∈ _ by rwa [Ideal.mem_comap, Ideal.Quotient.algebraMap_eq])

/-- **The flatness condition is corepresented, given the induction step of Stacks Tag 05PG.**
Suppose the flatness condition of Stacks Tag 05ML over a local `A`-algebra `R` is the conjunction
of the vanishing of an ideal `J ⊆ A` in `R` with the injectivity of `α ⊗ R`, for a map
`α : P → N` of `A`-modules with `P` projective over `A` whose cokernel is projective after
reduction modulo `J`. Then the condition is corepresented by an ideal `I ⊇ J`.

This is `Module.FlatAtPointSituation.exists_ideal_le_ker_iff_injective_rTensor_of_quotient`
rewritten through `Ideal.map_eq_bot_iff_le_ker`. -/
theorem exists_ideal_conditionOn_iff_le_ker_of_quotient (S : FlatAtPointSituation.{u, v, w})
    (J : Ideal S.A) {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective (S.A ⧸ J) ((S.A ⧸ J) ⊗[S.A] (N ⧸ LinearMap.range α))]
    (hcond : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔
        (Ideal.map (algebraMap S.A R) J = ⊥ ∧ Function.Injective (α.rTensor R))) :
    ∃ I : Ideal S.A, J ≤ I ∧ ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)],
        S.ConditionOn R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨I, hJI, hI⟩ :
      ∃ I : Ideal S.A, J ≤ I ∧ ∀ (R : Type max u x) [CommRing R] [Algebra S.A R],
        J ≤ RingHom.ker (algebraMap S.A R) →
          (Function.Injective (α.rTensor R) ↔ I ≤ RingHom.ker (algebraMap S.A R)) :=
    exists_ideal_le_ker_iff_injective_rTensor_of_quotient J α
  refine ⟨I, hJI, fun R _ _ _ _ ↦ ?_⟩
  rw [hcond R, Ideal.map_eq_bot_iff_le_ker, Ideal.map_eq_bot_iff_le_ker]
  exact ⟨fun h ↦ (hI R h.1).mp h.2, fun h ↦ ⟨hJI.trans h, (hI R (hJI.trans h)).mpr h⟩⟩

/-- **The induction step of Stacks Tag 05PG, in full.** Under the hypothesis of
`Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_le_ker_of_quotient` there is an ideal
`I ⊆ A` which simultaneously corepresents the flatness condition on the category `C` of
Stacks Tag 05MK and characterizes the flattening ideals as the ideals containing it.

The corepresenting ideal is fed back into
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff` through the
quotient map `A → A ⧸ I`, a surjection out of the free module `A` whose base-change bijectivity
is the vanishing of `I` (`Ideal.bijective_rTensor_mkQ_iff`). -/
theorem exists_ideal_flattens_iff_le_and_conditionOn_iff_of_quotient
    (S : FlatAtPointSituation.{u, v, w}) (J : Ideal S.A)
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective (S.A ⧸ J) ((S.A ⧸ J) ⊗[S.A] (N ⧸ LinearMap.range α))]
    (hcond : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔
        (Ideal.map (algebraMap S.A R) J = ⊥ ∧ Function.Injective (α.rTensor R))) :
    ∃ I : Ideal S.A, (∀ K : Ideal S.A, S.Flattens K ↔ I ≤ K) ∧
      ∀ R : LocalAlgCat.{u, x} S.A,
        S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨I₀, -, hI₀⟩ :
      ∃ I : Ideal S.A, J ≤ I ∧ ∀ (R : Type max u x) [CommRing R] [IsLocalRing R]
        [Algebra S.A R] [IsLocalHom (algebraMap S.A R)],
          S.ConditionOn R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
    S.exists_ideal_conditionOn_iff_le_ker_of_quotient J α hcond
  exact S.exists_ideal_flattens_iff_le_and_conditionOn_iff I₀.mkQ (Submodule.mkQ_surjective I₀)
    fun R _ _ _ _ ↦ (hI₀ R).trans (Ideal.bijective_rTensor_mkQ_iff I₀ R).symm

/-- **Stacks Project, Tag 05PG**, granting the induction step in the shape the source's dévissage
produces it. There is an ideal `I ⊆ A` such that the flatness condition of Stacks Tag 05ML over a
local `A`-algebra `R` holds exactly when `I` dies in `R`.

The henselian, essentially-finite-type and finiteness hypotheses of the source are carried
because they are what the dévissage producing `α` and `J` needs; they are not used here. Nothing
in this file proves Stacks Tag 05PG, so the result is untagged. -/
theorem exists_ideal_conditionOn_iff_map_eq_bot_of_quotient
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    [Algebra.EssFiniteType S.A S.B] [Module.Finite S.B S.M] (J : Ideal S.A)
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective (S.A ⧸ J) ((S.A ⧸ J) ⊗[S.A] (N ⧸ LinearMap.range α))]
    (hcond : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔
        (Ideal.map (algebraMap S.A R) J = ⊥ ∧ Function.Injective (α.rTensor R))) :
    ∃ I : Ideal S.A, ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
  (S.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_quotient J α hcond).imp
    fun _ ↦ And.right

/-- **Stacks Project, Tag 05PG**, finite generation, granting the same single hypothesis. Under
the finite-presentation hypotheses of the source the corepresenting ideal may be taken finitely
generated.

The ideal produced by
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_quotient`
flattens the situation, so `Module.FlatAtPointSituation.flattensFGApprox` — the limit preservation
of Stacks Tag 05MN — returns a finitely generated flattening ideal below it, which the
characterization of the flattening ideals forces to be the ideal itself. -/
theorem exists_fg_ideal_conditionOn_iff_map_eq_bot_of_quotient
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    (hB : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M] (J : Ideal S.A)
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective (S.A ⧸ J) ((S.A ⧸ J) ⊗[S.A] (N ⧸ LinearMap.range α))]
    (hcond : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔
        (Ideal.map (algebraMap S.A R) J = ⊥ ∧ Function.Injective (α.rTensor R))) :
    ∃ I : Ideal S.A, I.FG ∧ ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨I, hchar, hcore⟩ :
      ∃ I : Ideal S.A, (∀ K : Ideal S.A, S.Flattens K ↔ I ≤ K) ∧
        ∀ R : LocalAlgCat.{u, x} S.A,
          S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
    S.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_quotient J α hcond
  exact ⟨I, fg_of_flattens_iff S hB hchar, hcore⟩

/-- **The smallest flattening ideal, finitely generated**, granting the induction step of
Stacks Tag 05PG. This is the shape in which a consumer of the local flattening theorem uses it:
the flattening ideals of the situation are exactly the ideals containing one finitely generated
ideal. -/
theorem exists_fg_smallest_flattens_of_quotient (S : FlatAtPointSituation.{u, v, w})
    [HenselianLocalRing S.A] (hB : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M] (J : Ideal S.A)
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective (S.A ⧸ J) ((S.A ⧸ J) ⊗[S.A] (N ⧸ LinearMap.range α))]
    (hcond : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔
        (Ideal.map (algebraMap S.A R) J = ⊥ ∧ Function.Injective (α.rTensor R))) :
    ∃ I : Ideal S.A, I.FG ∧ ∀ K : Ideal S.A, S.Flattens K ↔ I ≤ K := by
  obtain ⟨I, hchar, -⟩ :
      ∃ I : Ideal S.A, (∀ K : Ideal S.A, S.Flattens K ↔ I ≤ K) ∧
        ∀ R : LocalAlgCat.{u, x} S.A,
          S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
    S.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_quotient J α hcond
  exact ⟨I, fg_of_flattens_iff S hB hchar, hchar⟩

/-- **The smallest flattening ideal, finitely generated**, granting the base-change injectivity
of a map out of a projective `A`-module with projective cokernel — the hypothesis of
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_injective`.

This is the `J = ⊥` reading of
`Module.FlatAtPointSituation.exists_fg_smallest_flattens_of_quotient`, stated separately because
the cokernel hypothesis is then about `N ⧸ Im(α)` itself and needs no reduction. -/
theorem exists_fg_smallest_flattens_of_injective (S : FlatAtPointSituation.{u, v, w})
    [HenselianLocalRing S.A] (hB : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M]
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {N : Type z} [AddCommGroup N] [Module S.A N] (α : P →ₗ[S.A] N)
    [Module.Projective S.A (N ⧸ LinearMap.range α)]
    (hinj : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔ Function.Injective (α.rTensor R)) :
    ∃ I : Ideal S.A, I.FG ∧ ∀ K : Ideal S.A, S.Flattens K ↔ I ≤ K := by
  obtain ⟨I, hchar, -⟩ :
      ∃ I : Ideal S.A, (∀ K : Ideal S.A, S.Flattens K ↔ I ≤ K) ∧
        ∀ R : LocalAlgCat.{u, x} S.A,
          S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
    S.exists_ideal_flattens_iff_le_and_conditionOn_iff_of_injective α hinj
  exact ⟨I, fg_of_flattens_iff S hB hchar, hchar⟩

end Module.FlatAtPointSituation

end
