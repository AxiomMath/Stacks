module

public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Basic

/-!
# Stacks Tag 07RM at the axiom-clean projectivity predicate, and what it does to Tag 087S

`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Basic.lean` proves Stacks Tag 07RM
with projectivity as a parameter. This file instantiates that parameter at
`Stacks.HProjective.IsHProjective`, discharging both of the parameter's side conditions, and then
measures what remains.

Tag 07RM itself, at Definition 01W8's projectivity `AlgebraicGeometry.IsProjective`, is proved
with no hypothesis beyond the source's:
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs` in
`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Projective.lean`. Everything below
is about the H-projective reading, which is a different statement: `𝐏(ℰ) ⟶ S` need not be
H-projective over a base carrying no ample invertible module.

## The measurement: Tag 07RM at H-projectivity and part (2) of Tag 087S are the same theorem

`Stacks.HProjective.ProjectiveCompactification` is the hypothesis the sibling file
`StacksFrontier/AlgebraicGeometry/HProjective/QuasiProjective.lean` introduced in order to prove
part (2) of Tag 087S, and its docstring records it as "Tag 07RM composed with part (1) of Tag
087S". `Stacks.QuasiProjectiveCompactification.projectiveCompactification_iff` shows that
hypothesis is **equivalent** to the conclusion it was introduced to prove:

* forward is the sibling's `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective`;
* backward is
  `exists_isOpenImmersion_isHProjective_of_isHQuasiProjective`, which is half 2 of Tag 07RM's own
  proof — Mathlib's Tag 01RG applied to the quasi-compact immersion that H-quasi-projectivity
  already supplies, with `ℙⁿ_S` playing the role of `𝐏(E)`.

So naming `Stacks.HProjective.ProjectiveCompactification` bought nothing beyond part (2) itself,
and **one** theorem is missing here rather than two: either Tag 07RM at H-projectivity or part (2)
of Tag 087S, from which the other follows. The one remaining input is
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at
`Stacks.HProjective.IsHProjective` (at `AlgebraicGeometry.IsProjective` it is the theorem
`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`), which
`immersionIntoProjective_isHProjective_of_hQuasiProjectiveOfQuasiProjective`
shows is itself no stronger than part (2).

## Main definitions

* `Stacks.QuasiProjectiveCompactification.HQuasiProjectiveOfQuasiProjective`: part (2) of Stacks
  Tag 087S, packaged as a proposition so that it can be compared with
  `Stacks.HProjective.ProjectiveCompactification`.

## Main results

* `exists_isOpenImmersion_isHProjective_of_isHQuasiProjective`: **Tag 07RM's
  conclusion for an H-quasi-projective morphism, with no hypothesis at all.**
* `isHQuasiProjective_iff_exists_isOpenImmersion_isHProjective`: for a
  quasi-compact morphism, Tag 07RM's conclusion at `Stacks.HProjective.IsHProjective` is equivalent
  to H-quasi-projectivity.
* `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective`: Tag 07RM's
  conclusion at `Stacks.HProjective.IsHProjective`, from
  `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at that predicate alone — both
  side conditions on the projectivity predicate are discharged here.
* `Stacks.QuasiProjectiveCompactification.projectiveCompactification_iff`: the equivalence
  described above.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.QuasiProjectiveCompactification

/-! ### The two side conditions, at `Stacks.HProjective.IsHProjective` -/

/-- An H-projective morphism is separated: this is the hypothesis `hsep` of
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective`, i.e. the use the
source makes of [Stacks, Tag 03GI]. -/
theorem isSeparated_of_isHProjective {Y S : Scheme.{u}} (q : Y ⟶ S)
    (hq : Stacks.HProjective.IsHProjective q) : IsSeparated q :=
  hq.isSeparated

/-- A closed immersion into an H-projective `S`-scheme is H-projective over `S`: this is the
hypothesis `hcomp` of `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective`,
i.e. the source's "and `X' ⟶ S` is projective by definition". -/
theorem isHProjective_comp_of_isClosedImmersion {X' Y S : Scheme.{u}} (c : X' ⟶ Y) (q : Y ⟶ S)
    (hc : IsClosedImmersion c) (hq : Stacks.HProjective.IsHProjective q) :
    Stacks.HProjective.IsHProjective (c ≫ q) := by
  have := hc
  exact hq.comp_isClosedImmersion c

/-! ### Half 2 of Tag 07RM, unconditionally -/

/-- **Tag 07RM's conclusion for an H-quasi-projective morphism, with no hypothesis.** An
H-quasi-projective morphism factors as an open immersion followed by an H-projective morphism.

This is exactly half 2 of the source's proof of Tag 07RM: H-quasi-projectivity already supplies
a quasi-compact immersion over the base into `ℙⁿ_S`, which plays the role of `𝐏(E)`, so Tag 01RG
— Mathlib's `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact` — factors it
through a closed subscheme of `ℙⁿ_S`, and that subscheme is H-projective over the base. No
quasi-compactness or quasi-separatedness of the base is needed, and no ample module appears. -/
theorem exists_isOpenImmersion_isHProjective_of_isHQuasiProjective {X S : Scheme.{u}}
    {f : X ⟶ S} (hf : Stacks.HProjective.IsHQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.HProjective.IsHProjective p ∧ i ≫ p = f := by
  obtain ⟨n, i, hi, hic, hif⟩ := hf
  obtain ⟨X', j, c, hj, hc, hjc⟩ := exists_isOpenImmersion_isClosedImmersion i hi hic
  refine ⟨X', j, c ≫ (projectiveSpaceOver n S ↘ S), hj,
    isHProjective_comp_of_isClosedImmersion c _ hc (Stacks.HProjective.isHProjective_over n S), ?_⟩
  rw [← Category.assoc, hjc, hif]

/-- The converse: a quasi-compact morphism factoring as an open immersion followed by an
H-projective morphism is H-quasi-projective. This is the sibling file's
`Stacks.HProjective.isHQuasiProjective_comp_of_isHProjective` with the factorisation taken out of
an existential. -/
theorem isHQuasiProjective_of_exists_isOpenImmersion_isHProjective {X S : Scheme.{u}}
    {f : X ⟶ S} (hf : QuasiCompact f)
    (h : ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.HProjective.IsHProjective p ∧ i ≫ p = f) :
    Stacks.HProjective.IsHQuasiProjective f := by
  obtain ⟨X', i, p, hi, hp, rfl⟩ := h
  have := hi
  exact Stacks.HProjective.isHQuasiProjective_comp_of_isHProjective i hp hf

/-- **For a quasi-compact morphism, Tag 07RM's conclusion at `Stacks.HProjective.IsHProjective` is
equivalent to H-quasi-projectivity.** Quasi-compactness is needed only for the backward
direction, and it is a consequence of quasi-projectivity, which is Tag 07RM's hypothesis. -/
theorem isHQuasiProjective_iff_exists_isOpenImmersion_isHProjective {X S : Scheme.{u}}
    {f : X ⟶ S} (hf : QuasiCompact f) :
    Stacks.HProjective.IsHQuasiProjective f ↔
      ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
        IsOpenImmersion i ∧ Stacks.HProjective.IsHProjective p ∧ i ≫ p = f :=
  ⟨exists_isOpenImmersion_isHProjective_of_isHQuasiProjective,
    isHQuasiProjective_of_exists_isOpenImmersion_isHProjective hf⟩

/-! ### Tag 07RM at the axiom-clean predicate -/

/-- **Stacks Tag 07RM** with projectivity read as `Stacks.HProjective.IsHProjective`: a
quasi-projective morphism over a quasi-compact quasi-separated base factors as an open immersion
followed by an H-projective morphism.

Both side conditions of
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective` are discharged, so
the only hypothesis left is `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at
H-projectivity, which is not proved. The tag itself, at Definition 01W8's projectivity, is
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`. -/
theorem exists_isOpenImmersion_isHProjective
    (hgap : ImmersionIntoProjective @Stacks.HProjective.IsHProjective.{u}) {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    (hf : Stacks.HProjective.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.HProjective.IsHProjective p ∧ i ≫ p = f :=
  exists_isOpenImmersion_isProjective (P := @Stacks.HProjective.IsHProjective.{u})
    isSeparated_of_isHProjective isHProjective_comp_of_isClosedImmersion hgap f hf

/-! ### What this does to Tag 087S -/

/-- **Part (2) of Stacks Tag 087S, packaged as a proposition.** Every quasi-projective morphism
is H-quasi-projective. Packaged so that it can be compared with
`Stacks.HProjective.ProjectiveCompactification`, which is likewise a closed proposition. -/
def HQuasiProjectiveOfQuasiProjective : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), Stacks.HProjective.IsQuasiProjective f →
    Stacks.HProjective.IsHQuasiProjective f

/-- **The hypothesis Tag 087S part (2) was proved from is equivalent to part (2) itself.**

`Stacks.HProjective.ProjectiveCompactification` is "Tag 07RM composed with part (1) of Tag 087S".
The forward implication is the sibling file's proof of part (2); the backward implication is
`exists_isOpenImmersion_isHProjective_of_isHQuasiProjective`, half 2 of Tag
07RM's own proof. So exactly one of the two is needed, not both. -/
theorem projectiveCompactification_iff :
    Stacks.HProjective.ProjectiveCompactification.{u} ↔ HQuasiProjectiveOfQuasiProjective.{u} := by
  refine ⟨fun h _ _ f hf ↦ Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective h f hf,
    fun h X S f hf ↦ ?_⟩
  obtain ⟨X', i, p, hi, hp, hip⟩ :=
    exists_isOpenImmersion_isHProjective_of_isHQuasiProjective (h X S f hf)
  exact ⟨X', i, p, hi, hip, hp⟩

/-- Half 1 of Tag 07RM, at `Stacks.HProjective.IsHProjective`, is no stronger than part (2)
of Tag 087S: H-quasi-projectivity supplies the immersion into `ℙⁿ_S`, which is H-projective over
the base. So this gap is not a new hypothesis beyond part (2). -/
theorem immersionIntoProjective_isHProjective_of_hQuasiProjectiveOfQuasiProjective
    (h : HQuasiProjectiveOfQuasiProjective.{u}) :
    ImmersionIntoProjective @Stacks.HProjective.IsHProjective.{u} := by
  intro X S f _ _ hf
  obtain ⟨n, i, hi, -, hif⟩ := h X S f hf
  exact ⟨projectiveSpaceOver n S, i, _, hi, Stacks.HProjective.isHProjective_over n S, hif⟩

end Stacks.QuasiProjectiveCompactification

end
