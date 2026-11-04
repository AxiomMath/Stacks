module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongCoproduct
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective

/-!
# Non-effective descent data for projective schemes

There is an étale covering `X → S` of schemes and a descent datum `(V/X, φ)` relative to it with
`V → X` projective which does not descend to a scheme. This file states that assertion, carries
the construction of the witness as a named hypothesis, and proves the reduction of the assertion
to the form in which the construction delivers it.

## Main results

* `Stacks.Examples.NonEffectiveProjectiveDescent.exists_nonEffectiveDescentData_projective`:
  **[Stacks, Tag 08KF]**, granted the construction of the witness. There are an étale covering
  consisting of a single morphism `f : X ⟶ S` and a descent datum relative to `f` whose scheme
  over `X` is projective over `X` and which is not effective.
* `Stacks.Examples.NonEffectiveProjectiveDescent.isProjectiveMorphism_sigmaMap`: a coproduct of
  finitely many H-projective morphisms is H-projective.
* `Stacks.Examples.NonEffectiveProjectiveDescent.singleton_mem_etalePrecoverage_sigmaDesc`: the
  morphism out of the coproduct of an étale covering family is itself an étale covering.

## Implementation notes

The covering is expressed by a singleton presieve in `AlgebraicGeometry.Scheme.etalePrecoverage`,
projectivity by `AlgebraicGeometry.IsProjective` — clause (1) of [Stacks, Tag 01W8] — and
non-effectivity by `AlgebraicGeometry.DescentData.IsEffective`, clause (3) of
[Stacks, Tag 023Z]: a descent datum relative to the single morphism `f` is effective when it is
isomorphic to the canonical descent datum of a scheme over `S`, which is exactly "the descent
datum is effective in the category of schemes". Its family-indexed companion
`AlgebraicGeometry.DescentData.IsFamilyEffective`, clause (2) of [Stacks, Tag 02VU], is the same
condition for a family of morphisms, and the two agree on a one-member family by
`AlgebraicGeometry.DescentData.isFamilyEffective_iff_isEffective`.

### The reduction, which is proved

The source's construction produces not one étale morphism but a *finite étale covering family*
together with a descent datum relative to it whose members are H-projective. Passing from that to
the shape the tag asserts is the content proved here, and it has three separate parts.

* The covering. The morphism out of the coproduct of an étale covering family is an étale
  covering, because `AlgebraicGeometry.Etale` is Zariski local at the source and the ranges of the
  members of the family already cover the base.
* The projectivity. The member of the corresponding datum over the coproduct is the coproduct of
  the members, by the `objIso` field of `AlgebraicGeometry.DescentData.FamilyCoproductEquivalence`
  ([Stacks, Tag 023X]), so what is needed is that a finite coproduct of H-projective morphisms is
  H-projective. Each member is a closed immersion into some `ℙⁿ` over its base; the exponents are
  raised to their maximum by `AlgebraicGeometry.exists_isClosedImmersion_projectiveSpaceOver`, and
  the coproduct of the resulting closed immersions is a closed immersion into `ℙᴺ` over the
  coproduct because coproducts of schemes are universal colimits. H-projectivity then gives
  `AlgebraicGeometry.IsProjective` by `AlgebraicGeometry.IsProjectiveMorphism.isProjective`,
  clause (2) of [Stacks, Tag 01W9].
* The non-effectivity. This transfers in the useful direction already:
  `AlgebraicGeometry.DescentData.isFamilyEffective_of_coproduct` says that a datum for a family is
  effective as soon as the corresponding datum for the morphism out of the coproduct is, so the
  contrapositive carries non-effectivity from the family to the single morphism.

### What is carried as a hypothesis, and why

`Stacks.Examples.NonEffectiveProjectiveDescent.EtaleProjectiveNonEffectiveFamily` asserts that
some finite étale covering family carries an H-projective descent datum which is not effective.
**Nothing in this repository proves it**, so the statement of the tag below is an implication. The
source builds it from three results, and each is unavailable here for a different reason.

* [Stacks, Tag 0D5E]: a field `k` and a family of curves over `𝔸¹_k` whose total space is not a
  scheme. This repository has the *obstruction* only, as
  `Stacks.Examples.CurveFamilyNotScheme.not_exists_scheme_of_no_dominating_closed_avoiding`: no
  scheme carries the geometry the construction produces. The family itself is not constructed,
  because its total space is obtained from a blowup of a cubic surface by Artin's contraction
  theorem for algebraic spaces, which this repository does not have.
* [Stacks, Tag 0E6F]: a family of curves becomes a scheme, H-projective over its base, after an
  étale covering of the base. This repository carries no form of the statement.
* [Stacks, Tag 02W5] for the big fppf site: descent data of schemes along a covering are the
  sheaves which become representable over each member, representably exactly when effectively.
  The general-site halves are proved, as
  `CategoryTheory.GrothendieckTopology.locallyRepresentableEquivalence` and
  `CategoryTheory.GrothendieckTopology.effectiveDescentData_toDescentData_iff`, but they live in
  the descent data of a pseudofunctor on a site; identifying those with the scheme descent data of
  `AlgebraicGeometry.DescentData` over `AlgebraicGeometry.BigFppfOver`, which is what the source
  uses, is not available.

Given the three, the witness is the source's: the non-schematic total space of the 0D5E family,
read as a sheaf on the big fppf site over its base, is locally representable for the 0E6F covering
by schemes H-projective over the covering members, so 02W5 turns it into an H-projective descent
datum, and that datum is not effective because an effective one would descend to a scheme
representing the total space.

## References

* [The Stacks Project, Tag 08KF](https://stacks.math.columbia.edu/tag/08KF)
* [The Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [The Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [The Stacks Project, Tag 023X](https://stacks.math.columbia.edu/tag/023X)
* [The Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [The Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [The Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [The Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [The Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Examples.NonEffectiveProjectiveDescent

/-! ### Coproducts of closed immersions and of H-projective morphisms -/

/-- **A coproduct of closed immersions of schemes is a closed immersion.** Each summand of the
target is an open over which the morphism of coproducts base changes to the given member. -/
theorem isClosedImmersion_sigmaMap {I : Type v} [Finite I] {X Y : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, IsClosedImmersion (f i)) :
    IsClosedImmersion (Limits.Sigma.map f) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (sigmaOpenCover Y)
    fun i ↦ ?_
  show IsClosedImmersion (pullback.snd (Limits.Sigma.map f) (Sigma.ι Y i))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      (isPullback_sigmaMap f i).isoPullback.hom,
    (isPullback_sigmaMap f i).isoPullback_hom_snd]
  exact hf i

/-- **A coproduct of finitely many H-projective morphisms is H-projective.** The closed immersions
into the relative projective spaces of the members are pushed into a common `ℙᴺ` and then taken
together, which is a closed immersion into `ℙᴺ` over the coproduct because coproducts of schemes
are universal colimits. -/
theorem isProjectiveMorphism_sigmaMap {I : Type v} [Finite I] {X Y : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, IsProjectiveMorphism (f i)) :
    IsProjectiveMorphism (Limits.Sigma.map f) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose n a ha haf using hf
  let N := Finset.univ.sup n
  have hn (i : I) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  choose b hb hbf using fun i ↦ exists_isClosedImmersion_projectiveSpaceOver (Y i) (hn i)
  let c (i : I) := a i ≫ b i
  have hc (i : I) : IsClosedImmersion (c i) := by
    have := ha i
    have := hb i
    exact IsClosedImmersion.comp _ _
  have hcf (i : I) : c i ≫ (projectiveSpaceOver N (Y i) ↘ Y i) = f i := by
    simp only [c, Category.assoc, hbf, haf]
  let P := projectiveSpaceAtUniverse.{u} N
  have hpb : IsPullback
      (Limits.Sigma.map (fun i ↦ pullback.fst (terminal.from (Y i)) (terminal.from P)))
      (Sigma.desc (fun i ↦ pullback.snd (terminal.from (Y i)) (terminal.from P)))
      (terminal.from (∐ Y)) (terminal.from P) :=
    (isUniversalColimit_sigmaCofan Y).isPullback_of_isColimit_right
      (fun i ↦ terminal.from (Y i)) (terminal.from (∐ Y)) (terminal.from P)
      (fun i ↦ pullback.fst (terminal.from (Y i)) (terminal.from P))
      (fun i ↦ pullback.snd (terminal.from (Y i)) (terminal.from P))
      (fun i ↦ IsPullback.of_hasPullback _ _) (coproductIsCoproduct _)
  have : IsClosedImmersion (Limits.Sigma.map c) := isClosedImmersion_sigmaMap c hc
  refine ⟨N, Limits.Sigma.map c ≫ hpb.isoPullback.hom, inferInstance, ?_⟩
  show (Limits.Sigma.map c ≫ hpb.isoPullback.hom) ≫ pullback.fst _ _ = _
  rw [Category.assoc, hpb.isoPullback_hom_fst]
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  simp only [Sigma.ι_map_assoc, Sigma.ι_map]
  rw [← Category.assoc]
  exact congrArg (fun g ↦ g ≫ Sigma.ι Y i) (hcf i)

/-! ### The morphism out of the coproduct of an étale covering -/

/-- **The morphism out of the coproduct of an étale covering family is an étale covering.** It is
étale because being étale is Zariski local at the source, and surjective because the ranges of the
members of the family already cover the base. -/
theorem singleton_mem_etalePrecoverage_sigmaDesc {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.etalePrecoverage S) :
    Presieve.singleton (Limits.Sigma.desc f) ∈ Scheme.etalePrecoverage S := by
  let : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  obtain ⟨hcover, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff _).mp hf
  refine (Scheme.singleton_mem_precoverage_iff
    (@Etale : MorphismProperty Scheme.{u}) (Sigma.desc f)).mpr
      ⟨fun s ↦ ?_, IsZariskiLocalAtSource.sigmaDesc hprop⟩
  obtain ⟨i, y, rfl⟩ := hcover s
  exact ⟨Sigma.ι X i y, by simp [← Scheme.Hom.comp_apply]⟩

/-! ### The witness, as a named hypothesis -/

/-- **The source's construction, as a named hypothesis.** There is a finite étale covering family
of a scheme carrying a descent datum whose members are H-projective over the members of the family
and which is not effective.

This is a hypothesis and not a theorem: the datum is the one the source builds from the
non-schematic total space of the family of curves of [Stacks, Tag 0D5E], and this repository
constructs neither that family, nor the étale presentation of [Stacks, Tag 0E6F], nor the fppf
case of the descent-data/sheaf comparison of [Stacks, Tag 02W5]. -/
def EtaleProjectiveNonEffectiveFamily : Prop :=
  ∃ (S : Scheme.{u}) (I : Type u) (_ : Finite I) (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
      (D : DescentData f),
    Presieve.ofArrows X f ∈ Scheme.etalePrecoverage S ∧
      (∀ i, IsProjectiveMorphism (D.obj i).hom) ∧ ¬ D.IsFamilyEffective

/-! ### Tag 08KF, granted the construction -/

/-- **A non-effective descent datum for the morphism out of the coproduct.** If a descent datum
relative to a family is not effective, then neither is the corresponding descent datum relative to
the morphism out of the coproduct of the family. -/
theorem not_isEffective_familyCoproduct {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S} {D : DescentData f}
    (hD : ¬ D.IsFamilyEffective) :
    ¬ ((DescentData.familyCoproductEquivalence f).equivalence.functor.obj D).IsEffective :=
  fun h ↦ hD (DescentData.isFamilyEffective_of_coproduct f
    (DescentData.isFamilyEffective_of_isEffective h))

/-- **The member over the coproduct is projective when the members of the family are.** The member
of the corresponding descent datum over the coproduct is the coproduct of the members of the
original datum, so H-projectivity of the members gives projectivity of that member. -/
theorem isProjective_familyCoproduct {S : Scheme.{u}} {I : Type v} [Finite I] [Small.{u} I]
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S} (D : DescentData f)
    (hD : ∀ i, IsProjectiveMorphism (D.obj i).hom) :
    IsProjective
      ((((DescentData.familyCoproductEquivalence f).equivalence.functor.obj D).obj ()).hom) := by
  let o := (DescentData.familyCoproductEquivalence f).objIso D
  have : IsIso o.inv.left :=
    inferInstanceAs (IsIso ((Over.forget (∐ X)).mapIso o.symm).hom)
  refine IsProjectiveMorphism.isProjective ?_
  refine IsProjectiveMorphism.of_iso (asIso o.inv.left) (Iso.refl (∐ X)) ?_
    (isProjectiveMorphism_sigmaMap (fun i ↦ (D.obj i).hom) hD)
  simp

/-- **[Stacks, Tag 08KF], granted the construction of the witness.** There are an étale covering
of a scheme consisting of a single morphism `f : X ⟶ S` and a descent datum relative to `f` whose
scheme over `X` is projective over `X` and which is not effective in the category of schemes. -/
@[stacks 08KF "THE EXISTENCE IS NOT ASSERTED. What is proved is the reduction of the tag to
its family form: given an étale covering family whose members are H-projective over the
base and whose descent datum is not family-effective, the coproduct is a single étale
morphism, is projective, and its datum is not effective. The witness itself is carried as
`EtaleProjectiveNonEffectiveFamily`, which is what the chain of Tags 0D5E (existence half,
blocked on Artin contraction), 0E6F (no library carrier at all) and 02W5 (fppf case, only
the general-site halves are proved) would produce"]
theorem exists_nonEffectiveDescentData_projective
    (hW : EtaleProjectiveNonEffectiveFamily.{u}) :
    ∃ (S X : Scheme.{u}) (f : X ⟶ S)
      (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ f)),
      Presieve.singleton f ∈ Scheme.etalePrecoverage S ∧
        IsProjective (D.obj ()).hom ∧ ¬ D.IsEffective := by
  obtain ⟨S, I, hI, X, f, D, hcover, hprojective, heffective⟩ := hW
  have : Finite I := hI
  exact ⟨S, ∐ X, Sigma.desc f,
    (DescentData.familyCoproductEquivalence f).equivalence.functor.obj D,
    singleton_mem_etalePrecoverage_sigmaDesc f hcover,
    isProjective_familyCoproduct D hprojective,
    not_isEffective_familyCoproduct heffective⟩

end Stacks.Examples.NonEffectiveProjectiveDescent

end
