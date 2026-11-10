module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.RelativeProjFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.RelativeProjQuasiCompact

/-!
# The finite type conditions for the relative homogeneous spectrum

Let `S` be a scheme carrying a quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra
`𝒜`. Stacks 084I compares two ways of asking that `𝒜` be finitely generated over the base:

1. `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite type as an `𝒜_0`-algebra;
2. `𝒜_0` is a finite type `𝒪_S`-module and `𝒜` is of finite type as an `𝒪_S`-algebra.

These are equivalent, and under either one the structure morphism of the relative homogeneous
spectrum is proper.

Affine-locally the equivalence is the transitivity of finite type algebras along the tower
`Γ(S, U) ⟶ 𝒜_0(U) ⟶ 𝒜(U)`: given the first two steps finite type the composite is, by
`Algebra.FiniteType.trans`, and conversely a finite type composite makes the second step finite
type, by `Algebra.FiniteType.of_restrictScalars_finiteType`. The tower commutes because the
structure sheaf maps into degree zero.

## Main definitions

* `Stacks.RelativeProj.Situation.IsDegreeZeroFiniteType` — the degree-zero part of the graded
  algebra is a finite type module over the structure sheaf: over every affine open of the base,
  the degree-zero piece of the graded ring of sections is a finite module over the sections of
  the structure sheaf. This is the first conjunct of both conditions of Stacks 084I.
* `Stacks.RelativeProj.Situation.IsFiniteTypeOverBase` — over every affine open of the base the
  graded ring of sections is a finite type algebra over the sections of the structure sheaf.
  This is the second conjunct of condition (2).

## Main results

* `Stacks.RelativeProj.Situation.properFiniteType_tfae` — the two finite type conditions of
  Stacks 084I are equivalent.
* `Stacks.RelativeProj.Situation.isFiniteType_of_isFiniteTypeOverBase` — either condition
  implies the finite type hypothesis `Stacks.RelativeProj.Situation.IsFiniteType` used by
  Stacks 07ZY, so the consequences drawn there are available from Stacks 084I's hypotheses.

## Implementation notes

**Only the finite type clause of Stacks 084I is proved here.** The source's other assertion, that
the structure morphism is proper under either condition, is not available in this library: it
rests on Stacks 0800 (`divisors-lemma-relative-proj-proper`), whose scheme-level form is absent,
as is Stacks 07ZZ (`divisors-lemma-relative-proj-universally-closed`). Supplying them means
generalizing the degree-zero hypothesis of
`Stacks.RelativeProj.Data.prop_toBase_of_toSpecZero` and its consequences from an isomorphism
`𝒪_S ≅ 𝒜_0` to an integral ring map, which is a separate development. In particular
`Stacks.RelativeProj.Situation.isProper_relativeProjToBase` does *not* prove the properness
clause: its hypothesis is that every `Stacks.RelativeProj.Situation.sectionRingZeroMap` is an
isomorphism, which is the special case `𝒜_0 = 𝒪_S` of `𝒜_0` being of finite type, and no
declaration here claims that clause.

The statement is at the level of schemes rather than algebraic spaces, which is where the source
places it, because relative `Proj` is not constructed for algebraic spaces in this library —
Stacks 084A, 084B and 084C are absent and
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProj.lean` takes the chart square as a hypothesis
instead of building it. Without that construction there is no space-level graded algebra whose
finite type conditions could be stated.

The two conditions are both quantified over all affine opens of the base. The sibling predicate
`Stacks.RelativeProj.Situation.IsFiniteType` instead asks for one affine neighbourhood of each
point; it is implied by `IsFiniteTypeOverBase`, which is
`Stacks.RelativeProj.Situation.isFiniteType_of_isFiniteTypeOverBase`, but the converse needs the
compatibility of the graded rings of sections with localization, so the equivalence is stated in
the uniform shape that `Stacks.RelativeProj.Situation.IsFiniteTypeOverDegreeZero` already uses.
For the same reason the degree-zero condition is spelled affine-locally with `RingHom.Finite`
rather than through `SheafOfModules.IsFiniteTypeOnSite`: that is the form the tower argument
consumes, and it matches the sibling predicates.

The source's proof of the properness clause cites
`divisors-lemma-relative-proj-universally-closed` (Stacks 07ZZ); the intended citation is
Stacks 0800, `divisors-lemma-relative-proj-proper`, which is the properness statement rather
than the universal closedness one.

## References

* [Stacks Project, Tag 084I](https://stacks.math.columbia.edu/tag/084I)
* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-! ### The two conditions -/

/-- The degree-zero part of the graded algebra of a relative `Proj` situation is a finite type
module over the structure sheaf: over every affine open `U` of the base, the degree-zero piece
of the graded ring of sections is a finite `Γ(S, U)`-module, the module structure being the one
given by `Stacks.RelativeProj.Situation.sectionRingZeroMap`. This is the condition on `𝒜_0`
common to both parts of Stacks 084I. -/
def IsDegreeZeroFiniteType : Prop :=
  ∀ U : s.base.Opens, IsAffineOpen U →
    (show Γ(s.base, U) →+* s.sectionRingGrading U 0 from (s.sectionRingZeroMap U).hom).Finite

/-- The graded algebra of a relative `Proj` situation is of finite type over the structure
sheaf: over every affine open `U` of the base, the graded ring of sections is a finite type
algebra over `Γ(S, U)`. This is the second condition of Stacks 084I; it differs from
`Stacks.RelativeProj.Situation.IsFiniteType` only in asking for every affine open rather than
for one affine neighbourhood of each point. -/
def IsFiniteTypeOverBase : Prop :=
  ∀ U : s.base.Opens, IsAffineOpen U →
    (show Γ(s.base, U) →+* s.sectionRing U from s.sectionRingBaseMap U).FiniteType

/-! ### The tower over an affine open -/

/-- The structure sheaf maps into degree zero: the map from the sections of the structure sheaf
to the graded ring of sections factors through the degree-zero piece, through the map
`Stacks.RelativeProj.Situation.sectionRingZeroMap`. This is what makes `Γ(S, U) ⟶ 𝒜_0(U) ⟶ 𝒜(U)`
a tower of algebras. -/
private theorem algebraMap_comp_sectionRingZeroMap (U : s.base.Opens) :
    (algebraMap (s.sectionRingGrading U 0) (s.sectionRing U)).comp
        (show Γ(s.base, U) →+* s.sectionRingGrading U 0 from (s.sectionRingZeroMap U).hom) =
      (show Γ(s.base, U) →+* s.sectionRing U from s.sectionRingBaseMap U) := by
  ext r i
  have hmem : s.sectionRingBaseMap U r ∈ s.sectionRingGrading U 0 := by
    change s.sectionRingBaseMap U r ∈ (DirectSum.of (s.sectionPieces U) 0).range
    let r' : (forget₂ CommRingCat RingCat).obj Γ(s.base, U) := r
    change (s.sectionRingStructure).baseMap U r' ∈ _
    rw [(s.sectionRingStructure).baseMap_apply U r']
    exact ⟨_, rfl⟩
  have hproj : (s.sectionRingZeroMap U).hom r = ⟨s.sectionRingBaseMap U r, hmem⟩ := by
    refine Subtype.ext ?_
    change GradedRing.projZeroRingHom (s.sectionRingGrading U)
      (s.sectionRingBaseMap U r) = s.sectionRingBaseMap U r
    rw [GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_same (s.sectionRingGrading U) hmem]
  change (((s.sectionRingZeroMap U).hom r : s.sectionRingGrading U 0) : s.sectionRing U) i =
    (s.sectionRingBaseMap U r) i
  rw [hproj]

/-- Over an affine open on which the degree-zero piece is a finite module and the graded ring of
sections is a finite type algebra over it, the graded ring of sections is a finite type algebra
over the structure sheaf. This is the forward implication of Stacks 084I over a single affine
open, and it is `Algebra.FiniteType.trans` along the tower. -/
private theorem finiteType_sectionRingBaseMap (U : s.base.Opens)
    (hzero : (show Γ(s.base, U) →+* s.sectionRingGrading U 0 from
      (s.sectionRingZeroMap U).hom).Finite)
    (hdeg : Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U)) :
    (show Γ(s.base, U) →+* s.sectionRing U from s.sectionRingBaseMap U).FiniteType := by
  rw [← algebraMap_comp_sectionRingZeroMap]
  exact (RingHom.finiteType_algebraMap.mpr hdeg).comp hzero.to_finiteType

/-- Over an affine open on which the graded ring of sections is a finite type algebra over the
structure sheaf, it is a finite type algebra over its degree-zero piece. This is the reverse
implication of Stacks 084I over a single affine open; it uses only the tower, not the finiteness
of the degree-zero piece. -/
private theorem finiteType_overDegreeZero (U : s.base.Opens)
    (hft : (show Γ(s.base, U) →+* s.sectionRing U from s.sectionRingBaseMap U).FiniteType) :
    Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U) := by
  rw [← RingHom.finiteType_algebraMap]
  rw [← algebraMap_comp_sectionRingZeroMap] at hft
  exact hft.of_comp_finiteType

/-! ### Stacks 084I, the finite type conditions -/

/-- **Stacks 084I.** For a relative `Proj` situation the two finite type conditions are
equivalent: that the degree-zero part of the graded algebra is a finite type module over the
structure sheaf and the graded algebra is of finite type over its degree-zero part, and that the
degree-zero part is a finite type module over the structure sheaf and the graded algebra is of
finite type over the structure sheaf. -/
@[stacks 084I "the equivalence of the two finite-type conditions, both read over every \
affine open of the base"]
theorem properFiniteType_tfae :
    List.TFAE
      [s.IsDegreeZeroFiniteType ∧ s.IsFiniteTypeOverDegreeZero,
        s.IsDegreeZeroFiniteType ∧ s.IsFiniteTypeOverBase] := by
  tfae_have 1 → 2 := fun ⟨hzero, hdeg⟩ =>
    ⟨hzero, fun U hU => finiteType_sectionRingBaseMap s U (hzero U hU) (hdeg U hU)⟩
  tfae_have 2 → 1 := fun ⟨hzero, hft⟩ =>
    ⟨hzero, fun U hU => finiteType_overDegreeZero s U (hft U hU)⟩
  tfae_finish

/-! ### Comparison with the finite type hypothesis of Stacks 07ZY -/

/-- Every point of a scheme has an affine open neighbourhood, the affine opens being a basis of
the topology. -/
private theorem exists_isAffineOpen_mem (X : Scheme.{u}) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
  obtain ⟨V, hV, hxV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨V, hV, hxV⟩

/-- Finite type over the structure sheaf on every affine open implies the finite type hypothesis
`Stacks.RelativeProj.Situation.IsFiniteType` of Stacks 07ZY, which asks only for one affine
neighbourhood of each point. So the conclusions of Stacks 07ZY follow from either condition of
Stacks 084I. -/
theorem isFiniteType_of_isFiniteTypeOverBase (h : s.IsFiniteTypeOverBase) : s.IsFiniteType := by
  intro x
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem s.base x
  exact ⟨U, hU, hxU, h U hU⟩

end Stacks.RelativeProj.Situation

end
