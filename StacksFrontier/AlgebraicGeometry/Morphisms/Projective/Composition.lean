module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Composite
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Projective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projective morphisms over a quasi-compact quasi-separated base

Over a quasi-compact quasi-separated base, a morphism is projective — in the sense of
`AlgebraicGeometry.IsProjective`, the predicate of clause (1) of Definition 01W8 that
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic` defines: a closed immersion over the
base into the projective bundle `𝐏(ℰ)` of a quasi-coherent module of finite type — if and only if
it is quasi-projective and proper (clause (1) of Tag 0BCL), and a composition of projective
morphisms is projective (Tag 0C4P).

## Main results

* `AlgebraicGeometry.isProjective_comp_of_isOpenImmersion_of_isProper`: an open immersion
  followed by a projective morphism is projective as soon as the composite is proper.
* `AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper`: **Tag 0BCL, clause (1)**.
* `AlgebraicGeometry.compactSpace_of_isProper` and
  `AlgebraicGeometry.quasiSeparatedSpace_of_isProper`: the source of a proper morphism whose
  target is quasi-compact, respectively quasi-separated, is again such. These supply the
  hypotheses of Tag 0BCL at the intermediate base of Tag 0C4P.
* `AlgebraicGeometry.IsProjective.comp`: **Tag 0C4P**, a composition of projective morphisms
  over a quasi-compact quasi-separated base is projective.

## Implementation notes

Clause (1) of Tag 0BCL is proved as the source proves it. Forwards, a projective morphism is
quasi-projective (Tag 07RL, `AlgebraicGeometry.IsProjective.isQuasiProjective`) and proper
(Tag 01WC, `AlgebraicGeometry.IsProjective.isProper`); neither uses the hypothesis on the base.
Backwards, Tag 07RM factors a quasi-projective morphism over a quasi-compact quasi-separated base
as an open immersion `X ⟶ X'` followed by a projective `X' ⟶ S`; properness of the composite and
separatedness of `X' ⟶ S` make the open immersion proper (Tag 01W6), hence with closed image,
hence a closed immersion, and a closed immersion into a projective `S`-scheme is projective.
Clause (2) of the tag, for H-projectivity, is
`AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper` of
`StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective`, where it is proved over an arbitrary
base.

For H-projectivity, stability under composition is Tag 01WE and holds over an arbitrary base,
through the Segre embedding; it is `AlgebraicGeometry.IsProjectiveMorphism.comp`. That result is
not Tag 0C4P: for projectivity in the sense of clause (1) the projective bundles of the two
morphisms live over different bases, and the source instead passes through quasi-projectivity and
properness by clause (1) of Tag 0BCL, applied at the base `S` and at the intermediate base `Y`.
The quasi-compactness and quasi-separatedness of `Y`, which the source leaves implicit, is
derived from the properness of `g`.

## References

* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 0C4P](https://stacks.math.columbia.edu/tag/0C4P)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 0C4M](https://stacks.math.columbia.edu/tag/0C4M)
* [Stacks Project, Tag 01W3](https://stacks.math.columbia.edu/tag/01W3)
* [Stacks Project, Tag 01WE](https://stacks.math.columbia.edu/tag/01WE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### Clause (1) of Tag 0BCL -/

/-- **An open immersion followed by a projective morphism, with proper composite, is
projective.** Let `j : X ⟶ X'` be an open immersion and `p : X' ⟶ S` projective. If `j ≫ p` is
proper, then `j` is proper because `p` is separated ([Stacks, Tag 01W6]); so `j` has closed
image, and an open immersion with closed image is a closed immersion. A closed immersion into a
projective `S`-scheme is projective over `S`. -/
@[ega "II 5.5.3" "(ii), special case"]
theorem isProjective_comp_of_isOpenImmersion_of_isProper {X X' S : Scheme.{u}} (j : X ⟶ X')
    (p : X' ⟶ S) [IsOpenImmersion j] (hp : IsProjective p) [IsProper (j ≫ p)] :
    IsProjective (j ≫ p) := by
  have := hp.isSeparated
  have := IsProper.of_comp j p
  exact Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion j p
    (IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range) hp

/-- **Stacks Project, Tag 0BCL, clause (1).** A morphism of schemes `f : X ⟶ S` to a
quasi-compact quasi-separated scheme is projective — in the sense of
`AlgebraicGeometry.IsProjective`, a closed immersion over `S` into the projective bundle of a
quasi-coherent module of finite type — if and only if it is quasi-projective and proper.

Forwards this is Tags 07RL and 01WC, which need no hypothesis on `S`. Backwards, Tag 07RM factors
`f` as an open immersion followed by a projective morphism, and
`AlgebraicGeometry.isProjective_comp_of_isOpenImmersion_of_isProper` concludes. -/
@[stacks 0BCL "(1)", ega "II 5.5.3" "more general"]
theorem isProjective_iff_isQuasiProjective_and_isProper {X S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] (f : X ⟶ S) :
    IsProjective f ↔ IsQuasiProjective f ∧ IsProper f := by
  refine ⟨fun hf => ⟨hf.isQuasiProjective, hf.isProper⟩, fun ⟨hqp, hpr⟩ => ?_⟩
  obtain ⟨X', j, p, hj, hp, rfl⟩ :=
    Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs f hqp
  exact isProjective_comp_of_isOpenImmersion_of_isProper j p hp

/-- **Stacks Project, Tag 07RL over a quasi-compact quasi-separated base. A projective morphism
is quasi-projective.** This is the forward half of clause (1) of Tag 0BCL, which
`AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper` proves over such a base. -/
@[stacks 07RL "over a quasi-compact quasi-separated base, the forward half of clause (1) of \
Tag 0BCL; the source states the tag over an arbitrary base"]
theorem isQuasiProjective_of_isProjective
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {f : X ⟶ S}
    (hf : IsProjective f) : IsQuasiProjective f :=
  ((isProjective_iff_isQuasiProjective_and_isProper f).mp hf).1

/-! ### The intermediate base -/

/-- **A proper morphism to a quasi-compact scheme has quasi-compact source.** A proper morphism is
universally closed, hence quasi-compact, and a quasi-compact morphism to a quasi-compact scheme
has quasi-compact source. -/
theorem compactSpace_of_isProper {Y S : Scheme.{u}} (g : Y ⟶ S) [CompactSpace S] [IsProper g] :
    CompactSpace Y :=
  QuasiCompact.compactSpace_of_compactSpace g

/-- **A proper morphism to a quasi-separated scheme has quasi-separated source.** A proper
morphism is separated, hence quasi-separated, and a quasi-separated morphism to a quasi-separated
scheme has quasi-separated source. -/
theorem quasiSeparatedSpace_of_isProper {Y S : Scheme.{u}} (g : Y ⟶ S) [QuasiSeparatedSpace S]
    [IsProper g] : QuasiSeparatedSpace Y :=
  quasiSeparatedSpace_of_quasiSeparated g

/-! ### Composition of projective morphisms -/

/-- **Stacks Project, Tag 0C4P. A composition of projective morphisms over a quasi-compact
quasi-separated base is projective.** For `f : X ⟶ Y` and `g : Y ⟶ S` projective and `S`
quasi-compact and quasi-separated, the composition `f ≫ g` is projective.

The proof is the source's. A projective morphism is quasi-projective and proper (Tags 07RL and
01WC), so `f` and `g` are; a composition of proper morphisms is proper, and a composition of
quasi-projective morphisms with quasi-compact target is quasi-projective (Tag 0C4M); clause (1)
of Tag 0BCL, `AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper`, at the base `S`
returns projectivity of `f ≫ g`. -/
@[stacks 0C4P]
theorem IsProjective.comp {X Y S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    {f : X ⟶ Y} {g : Y ⟶ S} (hf : IsProjective f) (hg : IsProjective g) :
    IsProjective (f ≫ g) := by
  have := hf.isProper
  have := hg.isProper
  exact (isProjective_iff_isQuasiProjective_and_isProper (f ≫ g)).mpr
    ⟨IsQuasiProjective.comp f g hf.isQuasiProjective hg.isQuasiProjective, inferInstance⟩

end AlgebraicGeometry

end
