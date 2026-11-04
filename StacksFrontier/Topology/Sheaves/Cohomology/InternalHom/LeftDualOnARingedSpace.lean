module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualIsTheDerivedDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# A left dual in `D(O_X)` on a ringed space is the derived dual of Example 0FPC

Let `(X, O_X)` be a ringed space and let `M` be an object of the derived category `D(O_X)` of
sheaves of `O_X`-modules, carrying the symmetric monoidal structure of Stacks 0FPB — the derived
tensor product, with the structure sheaf in degree zero as unit. Suppose `M` has a **left dual**
in the sense of Categories, Definition 0FFP: an object `N` together with a coevaluation
`η : O_X ⟶ M ⊗^L_{O_X} N` and an evaluation `ε : N ⊗^L_{O_X} M ⟶ O_X` satisfying the two
triangle identities, which is Mathlib's `CategoryTheory.ExactPairing M N`. Then

`M^∨ = RSheafHom(M, O_X) ≅ N`,

so the left dual is the dual object constructed in Example 0FPC; the identification is the
transpose, under the pairing, of the evaluation `ε' : M^∨ ⊗^L_{O_X} M ⟶ O_X` of Example 0FPC, and
it carries `ε'` to `ε`.

This is the second assertion of Stacks 0FPD. The ringed space is read as the ringed site of its
opens with the open-cover topology, exactly as Stacks 0FPB is Stacks 0FPT read there and as
Stacks 0FPC is Stacks 0FPU read there, and the content is then the ringed-site statement
Stacks 0FPV of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualIsTheDerivedDual`.

## Main results

* `Stacks.SheafOfModules.isIso_derivedDualToLeftDualMonoidal`: Stacks 0FPD, second assertion.
  The canonical morphism `M^∨ ⟶ N` which the exact pairing matches with the evaluation of
  Example 0FPC is an isomorphism.
* `Stacks.SheafOfModules.derivedDualIsoLeftDual` and
  `Stacks.SheafOfModules.leftDualIsoDerivedDual`: that isomorphism, as the identification
  `M^∨ ≅ N` and its inverse `N ≅ M^∨`.
* `Stacks.SheafOfModules.whiskerRight_derivedDualToLeftDualMonoidal`: the identification carries
  the evaluation `ε` of the pairing back to the evaluation of Example 0FPC. This pins it down —
  it is not an unconstrained morphism of its type.
* `Stacks.SheafOfModules.derivedDualEvaluation_eq_ringedSite`: the evaluation the previous item
  compares against **is** the evaluation `Stacks.SheafOfModules.derivedDualEvaluation` of
  Example 0FPC (`Stacks.SheafOfModules.derivedDual_isLeftDual`). This is
  what makes "the left dual is the one constructed in Example 0FPC" a statement about that
  construction rather than about a fresh one.
* `Stacks.SheafOfModules.derivedMonoidalStructure_eq_monoidalDerivedSite`: the monoidal structure
  in which the left dual is taken is the one of Stacks 0FPB.
* `Stacks.SheafOfModules.exactPairingUnitDerived`: the pairing hypothesis of the statements below
  has an inhabitant in `D(O_X)` over every ringed space, so none of them is vacuous. Not a clause
  of the tag; it carries no tag.

## The two conclusions of Stacks 0FPD

Stacks 0FPD has two conclusions for an object `M` of `D(O_X)` admitting a left dual: (a) `M` is
perfect, and (b) the left dual is the one constructed in Example 0FPC. This file proves (b).
Conclusion (a) is `Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualIsPerfect`, and the two are
stated together, for one and the same pairing, by
`Stacks.Cohomology.LeftDualPerfect.isPerfect_and_isIso_derivedDualToLeftDual`, which carries the
tag. The pairing hypothesis is inhabited over every ringed space, by `exactPairingUnitDerived`
below.

**Where the pairing hypothesis comes from.** The consumer of this tag inside the chapter is
Stacks 0FPG, whose clause (1) — invertibility of `M` for `⊗^L` — produces one:
`Stacks.Cohomology.InvertibleDerived.exists_exactPairing_of_isInvertibleObject` of
`StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects`, off the monoidal-category
statement `CategoryTheory.MonoidalCategory.IsInvertible.exists_exactPairing` of
`StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual`. So the hypothesis below is reachable
from the invertibility hypothesis the chapter actually hands it, and conclusion (a) turns it into
perfectness.

The one input the argument needs beyond the pairing is the naturality, in the source variable,
of the tensor–internal-Hom bijection of Stacks 08J8, proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality` as
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`.

**No instance side conditions either.** The files of this cluster usually carry a block of five
instance hypotheses — `HasSheafify` and `WEqualsLocallyBijective` for the open-cover topology,
additivity of `⊗_{O_X}` in each variable, and the existence of the total tensor complex. None of
them is a hypothesis of Stacks 0FPD, and none is needed: the first two are instances already,
and the other three are the library's own
`Stacks.SheafOfModules.Tensor.sheafTensor_additive`,
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` and
`Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor`, pinned below as file-local instances
at the site of opens of `X` because they are stated with the sections universe tied to the site
universes as `max u v`, which synthesis cannot solve against this cluster's diagonal `u` while
those universes are metavariables. So the statements below quantify over every ringed space,
with the exact pairing as their only hypothesis.

## Implementation notes

The left dual is taken in the monoidal structure `DerivedMonoidal.derivedMonoidal Rc` of
Stacks 0FPT, which is the structure Stacks 0FPB records for a ringed space:
`derivedMonoidalStructure_eq_monoidalDerivedSite` below is that identification, by `rfl`. It is
accessed through `AlgebraicGeometry.RingedSite.derivedMonoidalStructure` at `ringedSite Rc`, the
spelling in which the ringed-site statement is proved, so that the pairing hypothesis and the
site-level declarations match without a transport. The structure is not an instance, so every
statement below introduces it with a `let` in its own type, as the companion file
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualPairing` does.

**Every such `let` carries its type.** The objects below live in
`DerivedCategory (StructureSheafModules Rc)`, whose ring sheaf is `structureSheaf Rc`, i.e.
`CategoryTheory.sheafCompose` applied to `Rc`; the site-level structure and the site-level
declarations are stated at `(Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O)`, i.e. at
`Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which writes that composite presheaf out. The two
sheaves of rings are the same sheaf —
`SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O)` and
`StructureSheafModules Rc` are equal by `rfl` — but seeing it needs `sheafCompose`, a plain
`def`, unfolded, which *elaboration* does and *instance synthesis* does not. Marking
`CategoryTheory.sheafCompose` `implicit_reducible`, or even `reducible`, does not help here:
the two `DerivedCategory` applications also carry their `Category`, `Abelian` and
`HasDerivedCategory` arguments, synthesized separately at each spelling, so the crossing is past
any transparency setting. So the monoidal structure and the exact pairing are each *named as a
term at the spelling the surrounding expression needs* — `letI : <type> := <the existing
structure>` — instead of being left to search: nothing new is registered, and the single
definitional unification happens at the ascription, where the elaborator checks it at default
transparency. `whiskerRight_derivedDualToLeftDualMonoidal` needs both seatings at once, because
`▷` reads its category off the site-level morphism while `ε_ M N` reads it off `M`. Where even a
named-and-typed `let` is not enough — the `IsIso` that `asIso` wants in `derivedDualIsoLeftDual`,
whose statement is itself one of these crossings — the witness is handed to `asIso` as an
explicit argument, so that no synthesis is asked to cross anything at all.

Note that `Stacks.SheafOfModules.derivedDualEvaluation` of Example 0FPC is *typed* against a
second, `CategoryTheory.MonoidalCategory.reseat`-ed spelling
`Stacks.SheafOfModules.derivedMonoidalStructure` of the same monoidal structure, whose tensor
product is `Stacks.SheafOfModules.derivedTensor` on the nose. The two spellings have the same
tensor product and the same unit definitionally but different associator and unitors, and nothing
in this library transports an exact pairing between them, so the pairing hypothesis below is
stated for the un-reseated structure. This costs nothing in content: the *morphism*
`derivedDualEvaluation Rc M` of Example 0FPC is, by definition, the ringed-site evaluation
`AlgebraicGeometry.RingedSite.derivedDualEvaluation` from which the comparison morphism of this
file is built, and `derivedDualEvaluation_eq_ringedSite` below records that equation. The
composite form of the same fact — `derivedDualEvaluation Rc M` written out as the ringed-site
monoidal evaluation conjugated by the tensor comparison and the unit isomorphism, which is
`AlgebraicGeometry.RingedSite.derivedDualEvaluationMonoidal_eq` — is *not* restated here: the
`whnf` it requires of the re-seated tensor product does not finish within the elaborator's
budget, and raising the limit with an option is a workaround this development does not accept.
Composing `derivedDualEvaluation_eq_ringedSite` with that site-level lemma gives it.

The universes are the diagonal of the derived-internal-Hom cluster, with the derived category the
**standard** model: `attribute [local instance] HasDerivedCategory.standard` is in force below,
as it is in every file of this cluster.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 0FPA](https://stacks.math.columbia.edu/tag/0FPA)
* [Stacks Project, Tag 0FPS](https://stacks.math.columbia.edu/tag/0FPS)
* [Stacks Project, Tag 0FNS](https://stacks.math.columbia.edu/tag/0FNS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The monoidal structure in which the left dual is taken is the one of Stacks 0FPB.** Left
duals below are taken for `AlgebraicGeometry.RingedSite.derivedMonoidalStructure` at the ringed
site of opens of `X`, and that is the monoidal structure of
`Stacks.Cohomology.MonoidalDerived.symmetricMonoidalDerivedSite`, the one Stacks 0FPB records
for a ringed space. -/
theorem derivedMonoidalStructure_eq_monoidalDerivedSite :
    RingedSite.derivedMonoidalStructure (ringedSite Rc) =
      (Stacks.Cohomology.MonoidalDerived.symmetricMonoidalDerivedSite Rc).monoidal :=
  rfl

section Pairing

variable (M N : DerivedCategory (StructureSheafModules Rc))

/-- **The evaluation of Example 0FPC, read back across the two identifications.** The evaluation
`ε' : M^∨ ⊗ M ⟶ 𝟙` used by the comparison morphism of this file, read back across the comparison
of the two spellings of the derived tensor product and the identification of the unit with the
structure sheaf in degree zero, is the evaluation `Stacks.SheafOfModules.derivedDualEvaluation`
of Example 0FPC. So the object and the evaluation this file compares a left dual with are the
ones Example 0FPC constructs, not fresh ones. -/
theorem derivedDualEvaluation_eq_ringedSite :
    letI := derivedMonoidalStructure Rc
    derivedDualEvaluation Rc M = RingedSite.derivedDualEvaluation (ringedSite Rc) M :=
  rfl

/-- **Stacks 0FPD, second assertion: a left dual of `M` in `D(O_X)` is the dual object of
Example 0FPC.** The morphism `M^∨ = RSheafHom(M, O_X) ⟶ N` which the exact pairing matches with
the evaluation of Example 0FPC is an isomorphism; its inverse is the morphism which the
tensor–internal-Hom bijection of Stacks 08DK matches with the evaluation of the pairing. -/
@[stacks 0FPD "conclusion (b) only: that the left dual of M is the object constructed in \
Example 0FPC, namely the derived dual RSheafHom(M, O_X), the identification being the morphism \
matched with the evaluation of Example 0FPC by the pairing — see \
`Stacks.SheafOfModules.whiskerRight_derivedDualToLeftDualMonoidal` for the compatibility of the \
two evaluations and `Stacks.SheafOfModules.derivedDualEvaluation_eq_ringedSite` for the \
identification of that evaluation with the one Example 0FPC constructs. The monoidal structure \
on D(O_X) is the one of Tag 0FPB and a left dual is Mathlib's `CategoryTheory.ExactPairing`, \
which is Definition 0FFP. Conclusion (a) of the tag — that M is PERFECT — is NOT proved here and \
NOT assumed here: it needs the pairing to restrict to the slices D(O_X|_U), for which the \
derived restriction functor would have to be monoidal, and nothing in this library makes it so. \
The naturality of the bijection of Tag 08DK/08JA in its source variable, which the argument \
uses, is the theorem \
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, so the exact pairing \
itself is the one remaining input"]
theorem isIso_derivedDualToLeftDualMonoidal
    (pair : letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
        RingedSite.derivedMonoidalStructure (ringedSite Rc)
      ExactPairing M N) :
    letI : @ExactPairing
        (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O)))
        inferInstance (RingedSite.derivedMonoidalStructure (ringedSite Rc)) M N := pair
    IsIso (RingedSite.derivedDualToLeftDual (X := ringedSite Rc) M N) := by
  exact @RingedSite.isIso_derivedDualToLeftDual (ringedSite Rc) _ _ _ _ _ M N pair

/-- **The identification `M^∨ ≅ N` of Stacks 0FPD.** The dual object `M^∨ = RSheafHom(M, O_X)`
of Example 0FPC is a left dual `N` of `M`, by the morphism that the pairing matches with the
evaluation of Example 0FPC. -/
def derivedDualIsoLeftDual
    (pair : letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
        RingedSite.derivedMonoidalStructure (ringedSite Rc)
      ExactPairing M N) :
    derivedDual Rc M ≅ N :=
  letI : @ExactPairing
      (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O)))
      inferInstance (RingedSite.derivedMonoidalStructure (ringedSite Rc)) M N := pair
  @asIso _ _ _ _ (RingedSite.derivedDualToLeftDual (X := ringedSite Rc) M N)
    (isIso_derivedDualToLeftDualMonoidal Rc M N pair)

/-- **Stacks 0FPD, second assertion, in the direction the source states it**: a left dual `N` of
`M` in `D(O_X)` is the dual object `M^∨ = RSheafHom(M, O_X)` of Example 0FPC. -/
def leftDualIsoDerivedDual
    (pair : letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
        RingedSite.derivedMonoidalStructure (ringedSite Rc)
      ExactPairing M N) :
    N ≅ derivedDual Rc M :=
  (derivedDualIsoLeftDual Rc M N pair).symm

/-- **The identification `M^∨ ⟶ N` carries the evaluation of the pairing to the evaluation of
Example 0FPC.** This pins the comparison morphism down — it is not an unconstrained morphism of
its type — and it is the compatibility of the two duality data on the evaluation side. -/
theorem whiskerRight_derivedDualToLeftDualMonoidal
    (pair : letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
        RingedSite.derivedMonoidalStructure (ringedSite Rc)
      ExactPairing M N) :
    letI := RingedSite.derivedMonoidalStructure (ringedSite Rc)
    letI : @ExactPairing
        (DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O)))
        inferInstance (RingedSite.derivedMonoidalStructure (ringedSite Rc)) M N := pair
    letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
      RingedSite.derivedMonoidalStructure (ringedSite Rc)
    letI : ExactPairing M N := pair
    RingedSite.derivedDualToLeftDual (X := ringedSite Rc) M N ▷ M ≫ ε_ M N =
      RingedSite.derivedDualEvaluationMonoidal (X := ringedSite Rc) M := by
  exact @RingedSite.whiskerRight_derivedDualToLeftDual (ringedSite Rc) _ _ _ _ _ M N pair

/-! ### Non-vacuity of the pairing hypothesis

The statements above take an exact pairing as their hypothesis, so their content depends on that
datum having an inhabitant in `D(O_X)` itself. It does, assuming nothing: the monoidal unit — the
structure sheaf in degree zero — is its own two-sided tensor inverse, hence its own left dual by
`CategoryTheory.MonoidalCategory.HasInverse.exactPairing`. These are not clauses of the tag and
carry no tag.
-/

/-- **The pairing hypothesis of Stacks 0FPD has an inhabitant over every ringed space.** The unit
of the derived tensor product is its own left dual, so `isIso_derivedDualToLeftDualMonoidal` is
not vacuous. -/
@[instance_reducible]
def exactPairingUnitDerived :
    letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
      RingedSite.derivedMonoidalStructure (ringedSite Rc)
    ExactPairing (𝟙_ (DerivedCategory (StructureSheafModules Rc)))
      (MonoidalCategory.hasInverseUnit
        (C := DerivedCategory (StructureSheafModules Rc))).inv :=
  letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
    RingedSite.derivedMonoidalStructure (ringedSite Rc)
  MonoidalCategory.exactPairingUnitOfHasInverse

end Pairing

end Stacks.SheafOfModules

end
