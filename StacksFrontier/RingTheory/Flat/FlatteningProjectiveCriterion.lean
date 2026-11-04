module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.VanishingAfterBaseChange
public import StacksFrontier.RingTheory.Flat.FlatteningBridge
public import StacksFrontier.RingTheory.Flat.FlatteningEquivalence
public import StacksFrontier.RingTheory.Flat.FlatteningFGApprox
public import StacksFrontier.RingTheory.Flat.NoetherianSpreadout

/-!
# The local flattening theorem from a single map out of a projective module

In the situation of Stacks Tag 05MK — a local homomorphism `A → B` of local rings and a
`B`-module `M`, tested against the category `C` of local `A`-algebras with local structure map —
`StacksFrontier.RingTheory.Flat.HenselianFlattening` reduces Stacks Tag 05PG to the two statements
`Module.FlatAtPointSituation.FlattensSInf` and `Module.FlatAtPointSituation.FlattensKer`, and
`StacksFrontier.RingTheory.Flat.FlatteningEquivalence` shows those two are *together* equivalent to
the conclusion. This file replaces that pair by a single hypothesis in the shape the source's
dévissage argument actually produces, and proves one genuinely unconditional statement about
flattening ideals.

The source finishes its proof of Stacks Tag 05PG by exhibiting the flatness condition as the
condition that one fixed surjection `α : B₁^{⊕ r₁} → N₁` of `A`-modules stay an isomorphism after
base change, `B₁^{⊕ r₁}` being projective over `A`, and then quoting the flattening ideal of such
a surjection (Stacks Tag 05PE, available as
`Module.exists_ideal_bijective_rTensor_iff_map_eq_bot`). That last step is what
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff` carries out: from a
surjection `f : P → Q` of `A`-modules with `P` projective over `A` whose base-change bijectivity
is the flatness condition, it produces an ideal `I ⊆ A` which both corepresents the condition and
cuts out the flattening ideals, and the two conclusions of Stacks Tag 05PG follow — the finitely
generated one by feeding the already-proved
`Module.FlatAtPointSituation.flattensFGApprox` the ideal `I` itself.

Like the pair it replaces, the hypothesis `hcond` below is equivalent to the conclusion of
Stacks Tag 05PG and not weaker than it: given a corepresenting ideal `I`, the surjection
`Ideal.Quotient.mk I : A → A ⧸ I` out of the free module `A` has exactly `I` as its flattening
ideal. So nothing here proves Stacks Tag 05PG, and nothing here carries its tag. What the
reduction buys is that the remaining obligation is a statement about *one linear map*, which is
the object the complete dévissage of Stacks Tags 05I1, 05I3, 05I4, 05P4 and 05P5 constructs,
rather than a statement quantified over all ideals and all local algebras.

The unconditional statement is
`Module.FlatAtPointSituation.exists_fg_ideal_le_maximalIdeal_flattens`: when `A → B` is of finite
presentation and `M` is a finitely presented `B`-module there is a *finitely generated* ideal
inside `𝔪_A` which flattens the situation. This strengthens
`Module.FlatAtPointSituation.flattens_maximalIdeal`, the maximal ideal itself being finitely
generated only under a Noetherian hypothesis, and it bounds the smallest flattening ideal by a
finitely generated one without any appeal to Stacks Tag 05MN.

## Main definitions

There are no new definitions.

## Main results

* `Module.FlatAtPointSituation.exists_fg_ideal_le_maximalIdeal_flattens`: a finitely generated
  ideal inside the maximal ideal flattens the situation, unconditionally, as soon as `A → B` is
  of finite presentation and `M` is finitely presented over `B`.
* `Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff`: a surjection
  out of a projective `A`-module whose base-change bijectivity is the flatness condition produces
  an ideal which corepresents the condition and whose containment characterizes the flattening
  ideals.
* `Module.FlatAtPointSituation.exists_ideal_flatAtClosedFiberPrimes_iff_map_eq_bot` and
  `Module.FlatAtPointSituation.exists_fg_ideal_flatAtClosedFiberPrimes_iff_map_eq_bot`: the two
  conclusions of Stacks Tag 05PG, granting that single hypothesis.

## Implementation notes

The hypothesis `hcond` is taken at the universe `max u x`, where `u` is the universe of `A` and
`x` that of the test algebras: the characterization of the flattening ideals has to test the
quotients `A ⧸ J`, which live in `Type u`, while the conclusion ranges over
`LocalAlgCat.{u, x} A`, and `max u x` is the one universe above both. Nothing is lost, since the
dévissage produces the hypothesis in every universe. The two universe crossings are
`Module.FlatAtPointSituation.conditionOn_ulift_iff` and `ULift.ker_algebraMap`, both from
`StacksFrontier.RingTheory.Flat.FlatteningEquivalence`; the first is applied through
`Module.FlatAtPointSituation.flattens_iff_le_of_condition_iff` for the quotients and by hand for
a test algebra in `Type x`.

Stacks Tag 05PE is stated with the universe of the base-changed ring fixed by the application, so
a single appeal to it cannot serve both `Type u` and `Type x`. This is why the ideal is extracted
once, at `Type (max u x)`, with an explicit type ascription, and both readings are obtained from
that one ideal by a universe lift.

## References

* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05PE](https://stacks.math.columbia.edu/tag/05PE)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w x y z

namespace Ideal

/-- The base change of the quotient map `A → A ⧸ I` along `A → R` is bijective exactly when `I`
dies in `R`: the identification `TensorProduct.quotTensorEquivQuotSMul` turns `I.mkQ ⊗ R` into the
quotient map `R → R ⧸ I • R`, whose injectivity is the vanishing of `I • R`, and `I • R` is the
extension `Ideal.map (algebraMap A R) I` by `Ideal.smul_top_eq_map`.

This is the flattening ideal of Stacks Tag 05PE for the quotient map out of the free module `A`,
computed. It is what makes the hypothesis of
`Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff` no weaker than its
conclusion. -/
theorem bijective_rTensor_mkQ_iff {A : Type u} [CommRing A] (I : Ideal A) (R : Type v)
    [CommRing R] [Algebra A R] :
    Function.Bijective (I.mkQ.rTensor R) ↔ Ideal.map (algebraMap A R) I = ⊥ := by
  have hsq := TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor (R := A) (M := R) I
  have hb : Function.Bijective (I.mkQ.rTensor R) ↔
      Function.Bijective ((I • (⊤ : Submodule A R)).mkQ) := by
    constructor
    · intro h
      have hc : Function.Bijective
          ((TensorProduct.quotTensorEquivQuotSMul R I).toLinearMap ∘ₗ I.mkQ.rTensor R) :=
        (TensorProduct.quotTensorEquivQuotSMul R I).bijective.comp h
      rw [hsq] at hc
      simpa using hc.comp (TensorProduct.lid A R).symm.bijective
    · intro h
      have hc : Function.Bijective
          ((I • (⊤ : Submodule A R)).mkQ ∘ₗ (TensorProduct.lid A R).toLinearMap) :=
        h.comp (TensorProduct.lid A R).bijective
      rw [← hsq] at hc
      simpa using (TensorProduct.quotTensorEquivQuotSMul R I).symm.bijective.comp hc
  rw [hb, show Function.Bijective ((I • (⊤ : Submodule A R)).mkQ) ↔
      Function.Injective ((I • (⊤ : Submodule A R)).mkQ) from
    and_iff_left (Submodule.mkQ_surjective _), ← LinearMap.ker_eq_bot, Submodule.ker_mkQ,
    Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_bot_iff]

end Ideal

namespace Module.FlatAtPointSituation

/-- **A finitely generated flattening ideal inside the maximal ideal, unconditionally.** If
`A → B` is of finite presentation and `M` is a finitely presented `B`-module, there is a finitely
generated ideal `I ⊆ 𝔪_A` such that the flatness condition of Stacks Tag 05ML holds over
`A ⧸ I`.

This is the Noetherian spreadout step of Stacks Tag 0AT8
(`Stacks.Flatness.exists_fg_ideal_le_maximalIdeal_free_tensorProduct_of_universe`), which makes
`(A ⧸ I) ⊗_A M` free over `A ⧸ I`, read through
`Module.FlatAtPointSituation.flattens_iff_flat_quotient`: flattening the situation is exactly
flatness of `M ⧸ I M` over `A ⧸ I`, and `TensorProduct.quotTensorEquivQuotSMulₐ` identifies that
module with the base change.

It strengthens `Module.FlatAtPointSituation.flattens_maximalIdeal`, and bounds the smallest
flattening ideal by a finitely generated one with no appeal to the limit preservation of
Stacks Tag 05MN. -/
theorem exists_fg_ideal_le_maximalIdeal_flattens (S : FlatAtPointSituation.{u, v, w})
    [Algebra.FinitePresentation S.A S.B] [Module.FinitePresentation S.B S.M] :
    ∃ I : Ideal S.A, I.FG ∧ I ≤ maximalIdeal S.A ∧ S.Flattens I := by
  obtain ⟨I, hfg, hle, hfree⟩ :=
    Stacks.Flatness.exists_fg_ideal_le_maximalIdeal_free_tensorProduct_of_universe
      (A := S.A) S.B S.M
  refine ⟨I, hfg, hle, ?_⟩
  rw [S.flattens_iff_flat_quotient I]
  have _ : Module.Free (S.A ⧸ I) ((S.A ⧸ I) ⊗[S.A] S.M) := hfree
  exact Module.Flat.of_linearEquiv (TensorProduct.quotTensorEquivQuotSMulₐ S.M I).symm

/-- **The endgame of the source's proof of Stacks Tag 05PG.** Suppose the flatness condition of
Stacks Tag 05ML over a local `A`-algebra `R` is equivalent to the bijectivity of `f ⊗ R` for one
fixed surjection `f : P → Q` of `A`-modules with `P` projective over `A`. Then there is an ideal
`I ⊆ A` which simultaneously

* corepresents the condition on the category `C` of Stacks Tag 05MK, and
* characterizes the flattening ideals as the ideals containing it.

The ideal is the flattening ideal of `f` supplied by Stacks Tag 05PE
(`Module.exists_ideal_bijective_rTensor_iff_map_eq_bot`); the second clause is then
`Module.FlatAtPointSituation.flattens_iff_le_of_condition_iff`.

In the source `f` is the map `α₁ : B₁^{⊕ r₁} → N₁` of a complete dévissage, whose source is
projective over `A` because the lower algebras of a dévissage are. -/
theorem exists_ideal_flattens_iff_le_and_conditionOn_iff (S : FlatAtPointSituation.{u, v, w})
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {Q : Type z} [AddCommGroup Q] [Module S.A Q] (f : P →ₗ[S.A] Q)
    (hf : Function.Surjective f)
    (hcond : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔ Function.Bijective (f.rTensor R)) :
    ∃ I : Ideal S.A, (∀ J : Ideal S.A, S.Flattens J ↔ I ≤ J) ∧
      ∀ R : LocalAlgCat.{u, x} S.A,
        S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨I, hI⟩ : ∃ I : Ideal S.A, ∀ (B : Type max u x) [CommRing B] [Algebra S.A B],
      Function.Bijective (f.rTensor B) ↔ Ideal.map (algebraMap S.A B) I = ⊥ :=
    Module.exists_ideal_bijective_rTensor_iff_map_eq_bot S.A P Q f hf
  have key : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)],
      S.ConditionOn R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
    fun R _ _ _ _ ↦ (hcond R).trans (hI R)
  have hquot : ∀ R : LocalAlgCat.{u, max u x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := fun R ↦ key (R : Type max u x)
  refine ⟨I, fun J ↦ flattens_iff_le_of_condition_iff hquot J, fun R ↦ ?_⟩
  have hfin : S.ConditionOn (R : Type x) ↔
      Ideal.map (algebraMap S.A (R : Type x)) I = ⊥ := by
    rw [← S.conditionOn_ulift_iff (R : Type x), key (ULift.{u} (R : Type x) : Type max u x),
      Ideal.map_eq_bot_iff_le_ker, Ideal.map_eq_bot_iff_le_ker, ULift.ker_algebraMap (R : Type x)]
  exact hfin

/-- **Stacks Project, Tag 05PG**, granting that the flatness condition is the base-change
bijectivity of one surjection out of a projective `A`-module. There is an ideal `I ⊆ A` such that
for every local `A`-algebra `R` with local structure map the flatness condition of Stacks Tag
05ML over `R` holds exactly when `I` dies in `R`; that is, `A ⧸ I` corepresents the functor
`F_lf` of Stacks Tag 05MK.

The henselian, essentially-finite-type and finiteness hypotheses of the source are carried
because they are what the dévissage producing `f` needs; they are not used in this derivation.
Nothing here proves Stacks Tag 05PG — the hypothesis `hcond` is equivalent to the conclusion, as
the module docstring explains — so the result is untagged. -/
theorem exists_ideal_flatAtClosedFiberPrimes_iff_map_eq_bot
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    [Algebra.EssFiniteType S.A S.B] [Module.Finite S.B S.M]
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {Q : Type z} [AddCommGroup Q] [Module S.A Q] (f : P →ₗ[S.A] Q)
    (hf : Function.Surjective f)
    (hcond : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔ Function.Bijective (f.rTensor R)) :
    ∃ I : Ideal S.A, ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨I, -, hcore⟩ := S.exists_ideal_flattens_iff_le_and_conditionOn_iff f hf hcond
  exact ⟨I, hcore⟩

/-- Let `A` be a henselian local ring, `A → B` essentially of finite presentation and `M` a
finitely presented `B`-module. Suppose that for every local `A`-algebra `R` the condition on `R`
holds if and only if `f ⊗ R` is bijective, where `f : P → Q` is a surjection from a projective
`A`-module. Then there is a finitely generated ideal `I` of `A` such that for every local
`A`-algebra `R` the condition holds if and only if `I R = 0`. -/
theorem exists_fg_ideal_flatAtClosedFiberPrimes_iff_map_eq_bot
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    (hB : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M]
    {P : Type y} [AddCommGroup P] [Module S.A P] [Module.Projective S.A P]
    {Q : Type z} [AddCommGroup Q] [Module S.A Q] (f : P →ₗ[S.A] Q)
    (hf : Function.Surjective f)
    (hcond : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
      [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔ Function.Bijective (f.rTensor R)) :
    ∃ I : Ideal S.A, I.FG ∧ ∀ R : LocalAlgCat.{u, x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  obtain ⟨I, hchar, hcore⟩ := S.exists_ideal_flattens_iff_le_and_conditionOn_iff f hf hcond
  obtain ⟨J, hJle, hJfg, hJflat⟩ := S.flattensFGApprox hB I ((hchar I).mpr le_rfl)
  obtain rfl : I = J := le_antisymm ((hchar J).mp hJflat) hJle
  exact ⟨I, hJfg, hcore⟩

/-- **The hypothesis of the three theorems above is their conclusion.** If an ideal `I` of `A`
corepresents the flatness condition of Stacks Tag 05ML, then the condition is the base-change
bijectivity of the quotient map `A → A ⧸ I`, which is a surjection out of the free, hence
projective, `A`-module `A`.

So the hypothesis `hcond` is not weaker than the conclusion of Stacks Tag 05PG, and
`Module.FlatAtPointSituation.exists_ideal_flatAtClosedFiberPrimes_iff_map_eq_bot` is not a proof
of it. What the hypothesis provides is a *shape*: the obligation becomes a statement about one
linear map, which is the object the complete dévissage of the source constructs. -/
theorem conditionOn_iff_bijective_rTensor_mkQ (S : FlatAtPointSituation.{u, v, w})
    {I : Ideal S.A}
    (hI : ∀ R : LocalAlgCat.{u, max u x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥)
    (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
    [IsLocalHom (algebraMap S.A R)] :
    S.ConditionOn R ↔ Function.Bijective (I.mkQ.rTensor R) := by
  rw [Ideal.bijective_rTensor_mkQ_iff]
  exact hI { carrier := R }

/-- **The two readings of Stacks Tag 05PG are equivalent.** An ideal corepresenting the flatness
condition of Stacks Tag 05ML on the category `C` of Stacks Tag 05MK exists exactly when the
condition is the base-change bijectivity of a quotient map `A → A ⧸ I`.

The forward implication is `Module.FlatAtPointSituation.conditionOn_iff_bijective_rTensor_mkQ`;
the reverse is `Module.FlatAtPointSituation.exists_ideal_flattens_iff_le_and_conditionOn_iff`
applied to the surjection `I.mkQ` out of the free module `A`. This is the precise sense in which
the reduction performed in this file is a restatement of Stacks Tag 05PG and not a proof of
it. -/
theorem exists_ideal_condition_iff_exists_bijective_rTensor_mkQ
    (S : FlatAtPointSituation.{u, v, w}) :
    (∃ I : Ideal S.A, ∀ R : LocalAlgCat.{u, max u x} S.A,
        S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥) ↔
      ∃ I : Ideal S.A, ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
        [IsLocalHom (algebraMap S.A R)],
        S.ConditionOn R ↔ Function.Bijective (I.mkQ.rTensor R) := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨I, fun R _ _ _ _ ↦ S.conditionOn_iff_bijective_rTensor_mkQ hI R⟩
  · rintro ⟨I, hI⟩
    obtain ⟨I', -, hcore⟩ :
        ∃ I' : Ideal S.A, (∀ J : Ideal S.A, S.Flattens J ↔ I' ≤ J) ∧
          ∀ R : LocalAlgCat.{u, max u x} S.A,
            S.Condition R ↔ Ideal.map (algebraMap S.A R) I' = ⊥ :=
      S.exists_ideal_flattens_iff_le_and_conditionOn_iff I.mkQ (Submodule.mkQ_surjective I)
        (fun R _ _ _ _ ↦ hI R)
    exact ⟨I', hcore⟩

end Module.FlatAtPointSituation

end
