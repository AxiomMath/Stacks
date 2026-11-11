module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongCoproduct
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective

/-!
# Non-effective descent data for projective schemes

[Stacks, Tag 08KF] says: there is an étale covering `X → S` of schemes and a descent datum
`(V/X, φ)` relative to it with `V → X` projective which does not descend to a scheme. The tag is
proved, with no hypothesis, by
`Stacks.Examples.NonEffectiveProjectiveDescent.exists_etale_descentData_projective_not_isEffective`
in `StacksFrontier/AlgebraicGeometry/Examples/HironakaInvolution/NonEffectiveDescent.lean`, which
formalizes the source's Hironaka-type construction on `ℙ³`. This file proves a different,
independent statement: the passage from a non-effective H-projective descent datum along a finite
étale covering *family* to one along a single étale morphism.

## Main results

* `Stacks.Examples.NonEffectiveProjectiveDescent.exists_nonEffectiveDescentData_projective`:
  from a finite étale covering family with an H-projective, non-effective descent datum
  (`EtaleProjectiveNonEffectiveFamily`), a single étale covering morphism with a projective,
  non-effective descent datum.
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

A finite étale covering family together with a descent datum relative to it whose members are
H-projective is turned into one étale morphism with a projective descent datum. This has three
separate parts.

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

### The family form, and the source

`Stacks.Examples.NonEffectiveProjectiveDescent.EtaleProjectiveNonEffectiveFamily` asserts that
some finite étale covering family carries an H-projective descent datum which is not effective;
`exists_nonEffectiveDescentData_projective` takes it as a hypothesis. It is not how the source
proves [Stacks, Tag 08KF]. The source's proof (Examples, Section 08KE) is a Hironaka-type
construction: the involution `[x : y : z : w] ↦ [y : x : w : z]` of `ℙ³` acts freely off two lines,
the conics `C`, `D` are exchanged, the two orders of blowing up `C` and `D` glue to Hironaka's
threefold, and the involution gives a descent datum along the étale quotient map which cannot be
effective because of the rational equivalence `L₀ + g(L₀) ∼ 0`. It does not use the family of
curves of [Stacks, Tag 0D5E] (proved in this repository, with `k = ℂ`, as
`Stacks.Examples.CurveFamilyNotScheme.exists_curveFamily_total_not_scheme`); that route appears
only in a comment of the source, through [Stacks, Tag 0E6F] (proved in this repository as
`AlgebraicGeometry.CurveFamily.exists_etaleCovering_isPullback_isProjectiveMorphism`) and
[Stacks, Tag 02W5]. The source's construction is the one formalized in
`StacksFrontier/AlgebraicGeometry/Examples/HironakaInvolution/NonEffectiveDescent.lean`.

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
  change IsClosedImmersion (pullback.snd (Limits.Sigma.map f) (Sigma.ι Y i))
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
  change (Limits.Sigma.map c ≫ hpb.isoPullback.hom) ≫ pullback.fst _ _ = _
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

/-! ### The family form -/

/-- **A non-effective H-projective descent datum along a finite étale covering family.** There is
a finite étale covering family of a scheme carrying a descent datum whose members are H-projective
over the members of the family and which is not effective.

This is the input of `exists_nonEffectiveDescentData_projective`, not a statement of the source:
[Stacks, Tag 08KF] is proved by a different construction, see the module docstring. -/
def EtaleProjectiveNonEffectiveFamily : Prop :=
  ∃ (S : Scheme.{u}) (I : Type u) (_ : Finite I) (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
      (D : DescentData f),
    Presieve.ofArrows X f ∈ Scheme.etalePrecoverage S ∧
      (∀ i, IsProjectiveMorphism (D.obj i).hom) ∧ ¬ D.IsFamilyEffective

/-! ### From a family to a single morphism -/

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

/-- **From a non-effective H-projective datum along a finite étale family to one along a single
étale morphism.** Given `EtaleProjectiveNonEffectiveFamily`, the morphism out of the coproduct of
the family is an étale covering carrying a descent datum whose scheme is projective over it and
which is not effective in the category of schemes. [Stacks, Tag 08KF] itself is proved without
hypothesis by
`Stacks.Examples.NonEffectiveProjectiveDescent.exists_etale_descentData_projective_not_isEffective`.
-/
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
