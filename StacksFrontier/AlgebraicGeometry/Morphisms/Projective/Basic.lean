module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionClosedImmersion
public import StacksFrontier.Examples.GroupSchemes.NonSeparated

/-!
# Projective morphisms

A morphism of schemes `f : X ⟶ S` is *projective* when `X` is, as an `S`-scheme, a closed
subscheme of the projective bundle `𝐏(ℰ) = Proj_S(Sym(ℰ))` of some quasi-coherent `𝒪_S`-module
`ℰ` of finite type, and *locally projective* when `S` is covered by opens over which the
restriction of `f` is projective. These are the first and the third of the three conditions the
Stacks project defines in Tag 01W8, following EGA; the second, H-projectivity, is
`AlgebraicGeometry.IsProjectiveMorphism`.

The projective bundle entering the definition is neither a parameter nor an axiomatized
interface: it is the term `Stacks.SymGraded.schemeProjectiveBundle`, the relative homogeneous
spectrum of the sheaf symmetric algebra of `ℰ`, whose quasi-coherence hypothesis is discharged
for a quasi-coherent `ℰ` by `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`. So
`𝐏(ℰ)` is a closed term built from `ℰ` and nothing is existentially quantified except `ℰ` and the
closed immersion, which is what the source quantifies over too.

## Main definitions

* `AlgebraicGeometry.IsProjective`: the first condition of Tag 01W8, a closed immersion into a
  projective bundle over the base.
* `AlgebraicGeometry.IsLocallyProjective`: the third condition of Tag 01W8, the first one
  holding over the members of an open covering of the base.

## Main results

* `AlgebraicGeometry.isProjective_schemeProjectiveBundleToBase`: the projection of a projective
  bundle is projective, so the condition is satisfiable.
* `AlgebraicGeometry.IsProjective.isSeparated`: a projective morphism is separated.
* `AlgebraicGeometry.exists_not_isProjective`: over the affine line above any field there is a
  morphism which is **not** projective, so the condition is not satisfied by every morphism.

## Why the two non-vacuity statements are here

A definition of projectivity which quantified over an *arbitrary* `S`-scheme carrying some
structure, rather than over the projective bundle itself, would be satisfied by the datum
`𝐏 = X`, `i = 𝟙`, hence by every morphism; the resulting predicate would be vacuous, and every
lemma taking it as a hypothesis would be a theorem about nothing. That degenerate datum is not
available here, because `𝐏(ℰ)` is a term in `ℰ` and the identity of `X` is a morphism
`X ⟶ 𝐏(ℰ)` only when `X` *is* `Proj_S(Sym(ℰ))`.

That argument is recorded as mathematics rather than as prose by the two results above.
`AlgebraicGeometry.isProjective_schemeProjectiveBundleToBase` shows the predicate is inhabited —
the degenerate datum is exactly the legitimate one for the bundle's own projection — and
`AlgebraicGeometry.exists_not_isProjective` shows it is not everywhere true, which is what a
vacuous definition could never give. The second goes through separatedness: the projection of a
projective bundle is separated
(`Stacks.SymGraded.isSeparated_projectiveBundleToBase`, Tag 01OD) and a closed immersion is a
monomorphism, hence separated, so a projective morphism is separated, while the affine line with
its origin doubled is not separated over the affine line
(`Stacks.Examples.exists_flat_finiteType_groupScheme_not_isSeparated`, Tag 06E8).

## Implementation notes

`Stacks.SymGraded.schemeProjectiveBundle` takes the quasi-coherence of the homogeneous pieces of
`Sym(ℰ)` as an explicit argument, so the existential quantifies over it as well. That costs
nothing: it is a `Prop`, so by definitional proof irrelevance any two proofs of it give the same
bundle, and `AlgebraicGeometry.isProjective_of_isClosedImmersion` supplies the canonical one, so
a consumer never has to produce it. The alternative — fixing it to the canonical proof inside
the definition — would need the quasi-coherence instance in scope *before* `ℰ` is introduced,
which an existential cannot provide.

`AlgebraicGeometry.IsLocallyProjective` is stated with the restrictions
`AlgebraicGeometry.morphismRestrict`, which are the morphisms `f⁻¹(U) → U` the source writes,
rather than with base changes along the inclusions of the members of a covering. The two agree,
`f ∣_ U` being the base change of `f` along `U.ι`, but only the first is literally the source's
condition and only the first needs no pullback comparison.

## What is not done

The lemmas *about* projectivity are not proved here, and each is blocked on one missing
comparison rather than on the definition.

* Tag 01W9's second assertion, that an H-projective morphism is projective, needs the
  identification of `ℙⁿ_S` with `𝐏(𝒪_S^{⊕ n + 1})` — Tag 01OE — which would follow from a
  uniqueness statement for the relative homogeneous spectrum, and that is not available.
* Tag 0C4Q for this notion of projectivity, and the implication from
  `AlgebraicGeometry.IsProjective` to `AlgebraicGeometry.IsLocallyProjective`, are **no longer**
  missing. Both need `𝐏(ℰ) ×_S S' ≅ 𝐏(g^* ℰ)`, Tag 01O3, and that is available:
  `AlgebraicGeometry.projectiveBundleBaseChangeComparison` in
  `StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange` proves it for this bundle, by
  comparing the two presentations of the projective bundle that the trees carry rather than
  through the chart-level route recorded in
  `StacksFrontier.AlgebraicGeometry.RelativeProjBaseChange.Charts`. The three consequences are
  `AlgebraicGeometry.IsProjective.of_comp` (Tag 0C4Q, unconditional beyond the separatedness of
  `g` the source states), `AlgebraicGeometry.IsProjective.isLocallyProjective`, and stability
  under base change — `AlgebraicGeometry.IsProjective.pullback_fst`, together with
  `AlgebraicGeometry.IsLocallyProjective.pullback_fst` and
  `AlgebraicGeometry.isStableUnderBaseChange_isProjective`, all unconditional, in that same file
  (Tag 02V6).

  The implication to `AlgebraicGeometry.IsLocallyProjective` has a second, independent route
  that does not pass through Tag 01O3 at all:
  `Stacks.LocallyProjectiveHProjective.isProjectiveMorphism_morphismRestrict_of_isProjective` of
  `StacksFrontier.AlgebraicGeometry.LocallyProjectiveHProjective.Sym` makes a projective morphism
  H-projective over every affine open of the base, and the second clause of Tag 01W9,
  `Stacks.IsProjectiveMorphism.isProjective`, turns that back into projectivity. Tag 01WB —
  `Stacks.LocallyProjectiveHProjective.isLocallyProjective_iff_isLocallyProjectiveMorphism`, in
  that same file — is the resulting equivalence of clause (3) with its H-projective form.
* Tag 0BCL's first assertion, for *this* notion of projectivity, is **no longer** missing: it
  is `AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper` in
  `StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition`, from Tag 07RL
  (`AlgebraicGeometry.IsProjective.isQuasiProjective`), Tag 01WC
  (`AlgebraicGeometry.IsProjective.isProper`), Tag 07RM
  (`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`) and
  Tag 01W6.

The twist `𝒪_{𝐏(ℰ)}(1)` is **not** among the missing pieces: it is
`Stacks.AlgebraicGeometry.ChartCocycleRigidity.symGluedTwistOne`, the glued sheaf
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist` in degree one, whose cocycle
hypothesis `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle (Sym ℰ) 1` is
discharged unconditionally for quasi-coherent `ℰ` by
`Stacks.AlgebraicGeometry.ChartCocycleRigidity.isNestedCocycle_one_sym`. Tag 01VM is accordingly
available, as `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`, stated over the same bundle —
`Stacks.Tag01VMVeryAmple.schemeProjectiveBundle_eq` records that
`Stacks.SymGraded.schemeProjectiveBundle ℰ _` and the `relativeProj` of
`Stacks.Tag01VMRelativeVeryAmple.symAlgebra ℰ` are the same term. What remains missing of Tag
01NR is the twist in the *other* degrees and the graded algebra `⨁ₙ 𝒪(n)` with its `ψ`, since
`IsNestedCocycle (Sym ℰ) n` is proved only at `n = 1`: degree-one rigidity is the only rigidity
statement available without
`Stacks.AlgebraicGeometry.ChartCocycleRigidity.IsLegMultiplicative` for Tag 01NO's comparison.

Properness of `𝐏(ℰ) ⟶ S` is not drawn here for this bundle. It is proved in
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionRings.lean` for a relative homogeneous
spectrum whose affine section rings are of finite type over their degree-zero parts, but that is
stated for `Stacks.RelativeProj.Situation`, a different presentation of the same construction.
The comparison of the two presentations is no longer missing —
`AlgebraicGeometry.projectiveBundlePresentationsAgree` is proved in
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange` — so what remains is to transport
the properness statement along it, which no result here does.

## References

* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01OD](https://stacks.math.columbia.edu/tag/01OD)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 06E8](https://stacks.math.columbia.edu/tag/06E8)
-/

@[expose] public section

open CategoryTheory
open Stacks.SymGraded

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **Stacks Project, Tag 01W8, first condition.** A morphism `f : X ⟶ S` is *projective* if
`X` is isomorphic, as a scheme over `S`, to a closed subscheme of the projective bundle
`𝐏(ℰ) = Proj_S(Sym(ℰ))` of some quasi-coherent `𝒪_S`-module `ℰ` of finite type — equivalently,
if there is a closed immersion `i : X ⟶ 𝐏(ℰ)` with `i` followed by the projection equal to
`f`. -/
@[stacks 01W8 "projective", ega "II 5.5.2"]
def IsProjective (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType)
      (hqc : IsQuasicoherentPieces E) (i : X ⟶ (schemeProjectiveBundle E hqc).scheme),
    IsClosedImmersion i ∧ i ≫ (schemeProjectiveBundle E hqc).toBase = f

/-- A closed immersion into the projective bundle of a quasi-coherent module of finite type,
over the base, exhibits its target's projection as a projective morphism. This is the way to
produce a `AlgebraicGeometry.IsProjective`: the quasi-coherence of the homogeneous pieces of
`Sym(ℰ)` is supplied here, from `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`, so
no consumer has to name it. -/
theorem isProjective_of_isClosedImmersion (E : S.Modules) [E.IsQuasicoherent] [E.IsFiniteType]
    (i : X ⟶ (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).scheme)
    [IsClosedImmersion i] {f : X ⟶ S}
    (hf : i ≫ (schemeProjectiveBundle E
      (isQuasicoherentPieces_of_isQuasicoherent E)).toBase = f) :
    IsProjective f :=
  ⟨E, ‹E.IsQuasicoherent›, ‹E.IsFiniteType›, isQuasicoherentPieces_of_isQuasicoherent E, i,
    ‹IsClosedImmersion i›, hf⟩

/-- **The projection of a projective bundle is projective.** The identity of `𝐏(ℰ)` is a closed
immersion over the base, so the condition of Tag 01W8 is satisfiable. -/
theorem isProjective_schemeProjectiveBundleToBase (E : S.Modules) [E.IsQuasicoherent]
    [E.IsFiniteType] :
    IsProjective (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).toBase :=
  isProjective_of_isClosedImmersion E (𝟙 _) (Category.id_comp _)

/-- **A projective morphism is separated.** The projection of a projective bundle is separated
and a closed immersion is a monomorphism, hence separated, so the composite is. -/
theorem IsProjective.isSeparated {f : X ⟶ S} (hf : IsProjective f) : IsSeparated f := by
  obtain ⟨E, hq, hft, hqc, i, hi, rfl⟩ := hf
  have hsep : IsSeparated (schemeProjectiveBundle E hqc).toBase :=
    isSeparated_projectiveBundleToBase E
  infer_instance

/-- **Not every morphism of schemes is projective.** Over the affine line above a field, the
affine line with its origin doubled is not separated, hence not projective.

Together with `AlgebraicGeometry.isProjective_schemeProjectiveBundleToBase` this is the
non-vacuity of `AlgebraicGeometry.IsProjective`: the condition holds of something and fails of
something, which a definition made vacuous by an unconstrained projective bundle could not
do. -/
theorem exists_not_isProjective (k : Type u) [Field k] :
    ∃ (G : Scheme.{u}) (f : G ⟶ Spec (.of (Polynomial k))), ¬ IsProjective f := by
  obtain ⟨G, -, -, -, -, hns⟩ :=
    Stacks.Examples.exists_flat_finiteType_groupScheme_not_isSeparated k
  exact ⟨G.left, G.hom, fun h => hns h.isSeparated⟩

/-- **Stacks Project, Tag 01W8, third condition.** A morphism `f : X ⟶ S` is *locally
projective* if the base is covered by opens over each of which the restriction of `f` is
projective. -/
@[stacks 01W8 "locally projective"]
def IsLocallyProjective (f : X ⟶ S) : Prop :=
  ∃ (ι : Type u) (U : ι → S.Opens), (⨆ i, U i) = ⊤ ∧ ∀ i, IsProjective (f ∣_ U i)

end AlgebraicGeometry

end
