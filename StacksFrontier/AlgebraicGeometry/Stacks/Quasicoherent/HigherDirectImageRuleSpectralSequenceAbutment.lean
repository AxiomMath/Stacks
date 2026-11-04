module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion

/-!
# The homological half of Stacks 076Z: a rule containing a page contains the abutment

**Stacks 076Z** is the criterion
`AlgebraicGeometry.Stack.SmoothLocalHigherDirectImageCriterion`: if a rule `M` assigning to an
algebraic stack a subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` cuts out a weak Serre subcategory
everywhere (hypothesis (1)), is stable under inverse image along a smooth 1-morphism
(hypothesis (2)), is local for a jointly surjective family of smooth 1-morphisms
(hypothesis (3)) and is preserved by the higher direct images between stacks representable by
affine schemes (hypothesis (4)), then it is preserved by the higher direct images along every
quasi-compact (**Stacks 050U**) quasi-separated (**Stacks 04YW**) 1-morphism of algebraic stacks,
in every degree.

The source's proof has two halves. The *geometric* half produces, for a quasi-compact
quasi-separated `f : 𝒳 ⟶ 𝒴` and a member `ℱ` of the rule, the first-quadrant spectral sequence
of **Stacks 072G** along a smooth surjective chart of the source, and shows -- by iterating the
device four times, improving the representability of the source from a stack to an algebraic
space, a scheme, a separated scheme and finally an affine one, and using hypotheses (2), (3) and
(4) -- that every term of its first page is again a member of the rule. The *homological* half
then concludes: the spectral sequence is first quadrant, so part (4) of **Stacks 0132** applies
and the abutment `Rⁿf_*ℱ` is a member too, since hypothesis (1) makes the rule a weak Serre
subcategory.

This file states the outcome of the geometric half as a property of a rule,
`AlgebraicGeometry.Stack.StackEtaleModuleRule.HasCechSpectralSequenceWithPageInRule`, and proves
the homological half from it, by `CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page`.

## Main definitions

* `AlgebraicGeometry.Stack.StackEtaleModuleRule.toObjectProperty`: the rule at an algebraic
  stack, read as a property of the objects of `Mod(𝒳_étale, 𝒪_𝒳)`. This is the form hypothesis
  (1) of **Stacks 076Z** is stated in and the form the weak Serre argument consumes.
* `AlgebraicGeometry.Stack.StackEtaleModuleRule.HasCechSpectralSequenceWithPageInRule`: the
  outcome of the geometric half of the proof of **Stacks 076Z**, as a statement about a rule.

## Main results

* `AlgebraicGeometry.Stack.preservesHigherDirectImages_of_hasCechSpectralSequenceWithPageInRule`:
  a rule satisfying hypothesis (1) and admitting the spectral sequence of the geometric half is
  preserved by the higher direct images along every quasi-compact quasi-separated 1-morphism, in
  every degree.

## Implementation notes

`HasCechSpectralSequenceWithPageInRule` asks, for every quasi-compact quasi-separated
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` and every member `ℱ` of the rule on `𝒳_étale`, for a
cohomological spectral sequence of sheaves of modules on `𝒴_étale` starting at the page `1`,
every term of one of whose pages is a member of the rule on `𝒴_étale`, and which abuts to the
higher direct images `Rⁿf_*ℱ` of **Stacks 06WE** in the sense of
`CategoryTheory.SpectralSequence.AbutsTo`. Three remarks on the shape.

*It is not the conclusion.* The conclusion of the criterion is a statement about `Rⁿf_*ℱ`; the
property is a statement about the existence of a spectral sequence with members of the rule on
one of its pages. Nothing in it says that the abutment is a member, and the step from the one to
the other is exactly part (4) of **Stacks 0132**, which is what is proved here. Nor can the
property be had for free: `AbutsTo` asks for an infinity page at every bidegree and a *finite*
filtration of each `Rⁿf_*ℱ` whose graded pieces are the terms of that infinity page, so a
spectral sequence with a page in the rule which did not converge, or whose terms were unrelated
to `Rⁿf_*ℱ`, does not satisfy it.

*The abutment is indexed by `ℤ`, with the negative degrees zero*, which is the indexing
`Stacks.RelativeCech.PushforwardSpectralSequenceData` (**Stacks 072D**) uses for the abutment of
the relative Čech-to-cohomology spectral sequence.

*Membership is asked of some page, not of the first one.* **Stacks 072G** produces a spectral
sequence whose *first* page is `Rᵠ(f ∘ gₚ)_* gₚ^*ℱ` for the terms `gₚ` of the relative Čech nerve
of the chart, and that is the page the source's induction puts in the rule; but a weak Serre
subcategory containing one page contains every later one, so "some page lies in the rule" is
strictly weaker than "the first page does", and it is the weaker form that is asked.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 072D](https://stacks.math.columbia.edu/tag/072D)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

universe u t

namespace AlgebraicGeometry.Stack

namespace StackEtaleModuleRule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A rule at an algebraic stack, as a property of objects.** The rule `M` evaluated on the
sheaves of modules on `𝒴_étale`, which is the ambient category `Mod(𝒴_étale, 𝒪_𝒴)` of
**Stacks 076Z**.

This is the predicate hypothesis (1),
`AlgebraicGeometry.Stack.StackEtaleModuleRule.IsWeakSerre`, asserts to be a weak Serre
subcategory, and it is the shape the weak Serre argument of part (4) of **Stacks 0132** consumes.
No sheafification hypothesis is needed to *state* it: the category of sheaves of modules exists
without one, and only the abelian structure the weak Serre condition refers to needs them. -/
abbrev toObjectProperty (M : StackEtaleModuleRule B S hS) (𝒴 : AlgebraicStacks.{u, t} B S hS) :
    ObjectProperty (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) :=
  fun F => M 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids F.val

/-- **The geometric half of the proof of Stacks 076Z.** For every quasi-compact
(**Stacks 050U**) and quasi-separated (**Stacks 04YW**) 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` and every member `ℱ` of the rule on `𝒳_étale`, there is a cohomological spectral
sequence of sheaves of modules on `𝒴_étale`, starting at the page `1`, which abuts to the higher
direct images `Rⁿf_*ℱ` of **Stacks 06WE** and every term of one of whose pages is a member of the
rule on `𝒴_étale`.

This is what the source produces from the spectral sequence of **Stacks 072G** along a smooth
surjective chart of the source of `f`, after iterating the device four times to improve the
representability of that source down to the affine case; hypotheses (2), (3) and (4) of
**Stacks 076Z** are what the iteration consumes. It is *not* the conclusion of **Stacks 076Z**:
nothing here says that the abutment belongs to the rule, and the passage from a page to
the abutment is part (4) of **Stacks 0132**, which
`AlgebraicGeometry.Stack.preservesHigherDirectImages_of_hasCechSpectralSequenceWithPageInRule`
supplies from hypothesis (1).

The abutment is indexed by `ℤ` with the negative degrees zero, which is how
`Stacks.RelativeCech.PushforwardSpectralSequenceData` (**Stacks 072D**) indexes the abutment of
the relative Čech-to-cohomology spectral sequence. -/
noncomputable abbrev HasCechSpectralSequenceWithPageInRule (M : StackEtaleModuleRule B S hS) :
    Prop :=
  ∀ {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴), IsQuasiCompactMorphism B S hS f →
    AlgebraicStacks.IsQuasiSeparated B S hS f →
    letI := hasSheafify_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    letI := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    letI := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
    ∀ F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
        (etaleTopology B) (etaleTopology_le_topology B)),
      M (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) F.val →
        ∃ E : CohomologicalSpectralSequence
          (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒴.val.val.p
            𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) 1,
          (∃ (r : ℤ) (hr : (1 : ℤ) ≤ r), ∀ pq : ℤ × ℤ,
              toObjectProperty.{u, t} B S hS M 𝒴 ((E.page r hr).X pq)) ∧
            CategoryTheory.SpectralSequence.AbutsTo E (fun n : ℤ => if n < 0 then 0 else
              (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
                (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
                (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
                (CatFiberedInGroupoids.homFunctor f.hom) rfl (etaleTopology B)
                (etaleTopology_le_topology B) n.toNat).obj F)

end StackEtaleModuleRule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The homological half of the proof of Stacks 076Z.** Let `M` be a rule which cuts out a weak
Serre subcategory of `Mod(𝒴_étale, 𝒪_𝒴)` at every algebraic stack `𝒴` -- hypothesis (1) of
**Stacks 076Z** -- and which admits, along every quasi-compact quasi-separated 1-morphism and at
every member of the rule, a spectral sequence with a page in the rule abutting to the higher
direct images. Then the higher direct images carry the rule into the rule along every
quasi-compact quasi-separated 1-morphism, in every degree.

The abutment of a spectral sequence one of whose pages lies in a weak Serre subcategory lies in it
too, by part (4) of **Stacks 0132**
(`CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page`), and the abutment in degree `i ≥ 0`
is `Rⁱf_*ℱ`. -/
theorem preservesHigherDirectImages_of_hasCechSpectralSequenceWithPageInRule
    (M : StackEtaleModuleRule B S hS)
    (hserre : StackEtaleModuleRule.IsWeakSerre.{u, t} B S hS M)
    (hss : StackEtaleModuleRule.HasCechSpectralSequenceWithPageInRule.{u, t} B S hS M) :
    StackEtaleModuleRule.PreservesHigherDirectImages.{u, t} B S hS M := by
  intro 𝒳 𝒴 f hqc hqs i F hF
  let := hasSheafify_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  let := wEqualsLocallyBijective_associatedTopology_of_category_succ B S hS 𝒴.val.val.p
  let : (StackEtaleModuleRule.toObjectProperty.{u, t} B S hS M 𝒴).IsWeakSerreClass := hserre 𝒴
  obtain ⟨E, ⟨r, hr, hpage⟩, habuts⟩ := hss f hqc hqs F hF
  have key := habuts.prop_of_prop_page
    (StackEtaleModuleRule.toObjectProperty.{u, t} B S hS M 𝒴) hr hpage (i : ℤ)
  rw [show ((i : ℤ)).toNat = i from by omega] at key
  split_ifs at key with hneg
  · exact absurd hneg (by omega)
  · exact key

end AlgebraicGeometry.Stack

end
