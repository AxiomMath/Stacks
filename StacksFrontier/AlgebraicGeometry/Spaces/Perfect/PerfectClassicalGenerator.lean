module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallClassicalGenerator
public import StacksCore.Tactic.StacksAttribute

/-!
# A perfect generator classically generates the perfect objects of an algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, and let `G` be a
perfect object of `D(𝒪_X)` which is a generator of `D_QCoh(𝒪_X)`. Then `G` is a *classical*
generator of `D_perf(𝒪_X)`: the smallest strictly full saturated triangulated subcategory of
`D_QCoh(𝒪_X)` containing `G` is exactly the subcategory of perfect objects. Such a `G` exists
by [Stacks, Tag 09IY]. This is [Stacks, Tag 0GFC].

## Main results

* `AlgebraicGeometry.Space.triangEnvelope_eq_isPerfect_of_isWeakTriangulatedGenerator`:
  **Stacks 0GFC**, the triangulated envelope of a perfect generator `G` of `D_QCoh(𝒪_X)` is the
  property of being perfect.
* `AlgebraicGeometry.Space.exists_isPerfect_isWeakTriangulatedGenerator_triangEnvelope_eq`:
  **Stacks 0GFC**, the existence clause: there is such a `G` ([Stacks, Tag 09IY]).

## Implementation notes

*The reading.* A perfect object of `D(𝒪_X)` has quasi-coherent cohomology sheaves, so `D_perf(𝒪_X)`
is a full subcategory of `D_QCoh(𝒪_X)` and `G` is an object of `D_QCoh(𝒪_X)`
(`AlgebraicGeometry.Space.qcohDerived_of_isPerfect`). *Generator* is Definition
[Stacks, Tag 09SJ] in the triangulated category `D_QCoh(𝒪_X)`,
`ObjectProperty.IsWeakTriangulatedGenerator`: an object of `D_QCoh(𝒪_X)` receiving only zero maps
from the shifts of `G` is zero. *Classical generator of `D_perf(𝒪_X)`* is the equality of the
triangulated envelope `⟨G⟩` (`ObjectProperty.triangEnvelope`, the closure under shifts, finite
sums, extensions and direct summands) with perfectness. As `D_perf(𝒪_X)` is closed in
`D_QCoh(𝒪_X)` under all four operations, the envelope taken in `D_QCoh(𝒪_X)` and the one taken in
`D_perf(𝒪_X)` agree.

*The proof* is the source's: `D_QCoh(𝒪_X)` has direct sums ([Stacks, Tag 08F3],
`AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory_ringUniverse`), its compact
objects are its perfect objects ([Stacks, Tag 09M8],
`AlgebraicGeometry.Space.isCompactObject_iff_isPerfect`), and a compact generator classically
generates the compact objects ([Stacks, Tag 09SR]). The last is applied in the form
`CategoryTheory.ObjectProperty.triangEnvelope_singleton_eq_of_isCompactObject_iff_of_locallySmall`,
because the morphisms of `D_QCoh(𝒪_X)` live one universe above its direct sums.

*The model.* `D_QCoh(𝒪_X)` ([Stacks, Tag 071X],
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`) and both of [Stacks, Tags 09M8 and 09IY]
are stated at `CategoryTheory.HasDerivedCategory.standard`, so the perfectness predicate is read
at that model too.

## References

* [Stacks Project, Tag 0GFC](https://stacks.math.columbia.edu/tag/0GFC)
* [Stacks Project, Tag 09IY](https://stacks.math.columbia.edu/tag/09IY)
* [Stacks Project, Tag 09M8](https://stacks.math.columbia.edu/tag/09M8)
* [Stacks Project, Tag 08F3](https://stacks.math.columbia.edu/tag/08F3)
* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GFC.** Let `X` be a quasi-compact and quasi-separated algebraic space over `S`, and
let `G` be a perfect object of `D(𝒪_X)` which is a generator of `D_QCoh(𝒪_X)`. Then `G` is a
classical generator of `D_perf(𝒪_X)`: the triangulated envelope of `G` in `D_QCoh(𝒪_X)` — its
closure under shifts, finite direct sums, extensions and direct summands — is exactly the property
of being perfect.

The source combines [Stacks, Tag 08F3] (direct sums in `D_QCoh(𝒪_X)`), [Stacks, Tag 09M8]
(compact equals perfect) and [Stacks, Tag 09SR] (a compact generator classically generates the
compact objects). Such a `G` exists by [Stacks, Tag 09IY]; see
`AlgebraicGeometry.Space.exists_isPerfect_isWeakTriangulatedGenerator_triangEnvelope_eq`. -/
@[stacks 0GFC]
theorem triangEnvelope_eq_isPerfect_of_isWeakTriangulatedGenerator (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (G : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hG : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect G.obj)
    (hgen : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton G).triangEnvelope =
      fun E => (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E.obj := by
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have := enoughInjectives_modules_ringUniverse B S hS X.1 X.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  have : IsCompactObject.{u} G := (isCompactObject_iff_isPerfect X hqc hqs G).2 hG
  exact ObjectProperty.triangEnvelope_singleton_eq_of_isCompactObject_iff_of_locallySmall G hgen _
    (isCompactObject_iff_isPerfect X hqc hqs)

/-- **Stacks 0GFC, the existence clause.** On a quasi-compact and quasi-separated algebraic space
`X` over `S` there is a perfect object `G` of `D(𝒪_X)` which is a generator of `D_QCoh(𝒪_X)`
([Stacks, Tag 09IY]), and every such `G` is a classical generator of `D_perf(𝒪_X)`: its
triangulated envelope in `D_QCoh(𝒪_X)` is the property of being perfect. The generator is the
compact generator of `exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs`, perfect by
[Stacks, Tag 09M8], exactly as in the proof of `exists_isPerfect_generator`. -/
@[stacks 0GFC "the existence of a perfect generator G of D_QCoh(O_X), by 09IY"]
theorem exists_isPerfect_isWeakTriangulatedGenerator_triangEnvelope_eq
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ G : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect G.obj ∧
        (ObjectProperty.singleton G).IsWeakTriangulatedGenerator ∧
          (ObjectProperty.singleton G).triangEnvelope =
            fun E => (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E.obj := by
  obtain ⟨G, hGc, hgen⟩ := exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs B S hS
    B.contains_terminal X hqc hqs
  have hG := (isCompactObject_iff_isPerfect X hqc hqs G).1 hGc
  exact ⟨G, hG, hgen,
    triangEnvelope_eq_isPerfect_of_isWeakTriangulatedGenerator X hqc hqs G hG hgen⟩

end AlgebraicGeometry.Space

end
