module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierNormalTensorIso
public import StacksCore.Tactic.StacksAttribute

/-!
# A duality theory: the upper shriek of an effective Cartier divisor

Clause (7) of [Stacks, Section 0AU3] reads:

> if `f : X ⟶ Y` is the inclusion of an effective Cartier divisor into an object of `FTS_S`,
> then `f^!(-) = Lf^*(-) ⊗_{𝒪_X} f^*𝒪_Y(X)[-1]`.

Both inputs of that clause are available in this repository, at the same model of the derived
category, and this file composes them.

* `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion` is clause (5) of the same
  section, [Stacks, Tag 0AA2]: for a closed immersion of `FTS S`, any right adjoint of `Ri_*` on
  the quasi-coherent derived categories is, on bounded-below complexes, derived sheaf Hom out of
  the structure sheaf of the closed subscheme, `i^!(-) = R𝓗om_{𝒪_Y}(𝒪_X, -)`.
* `Stacks.Divisors.normalTensorDerivedSheafHomIso` is [Stacks, Tag 0AA4]: for an effective
  Cartier divisor `D ⊆ X` with normal sheaf `𝒩 = i^*𝒪_X(D)`, the canonical map
  `Li^*K ⊗^L_{𝒪_D} 𝒩[-1] ⟶ R𝓗om_{𝒪_X}(𝒪_D, K)` is an isomorphism, functorially in `K`.

Composing them gives the clause: on `D⁺_QCoh(𝒪_X)` the twisted inverse image of the inclusion of
an effective Cartier divisor is `Li^*(-) ⊗^L_{𝒪_D} 𝒩[-1]`.

## Main definitions

* `Stacks.Duality.IsNormalTensorPullbackRightAdjoint` — the conclusion of clause (7) for one
  effective Cartier divisor and one candidate right adjoint of `Ri_*`: on the bounded-below part
  of `D_QCoh(𝒪_X)` the functor agrees with `Li^*(-) ⊗^L_{𝒪_D} 𝒩[-1]`. This is the shape in
  which `Stacks.Duality.IsDerivedSheafHomRightAdjoint` states clause (5), with the target functor
  replaced by the one clause (7) names.

## Main results

* `Stacks.Duality.isNormalTensorPullbackRightAdjoint_of_isDerivedSheafHomRightAdjoint` — the
  composition of the two inputs, for an arbitrary scheme.
* `Stacks.Duality.isNormalTensorPullbackRightAdjoint_of_fts` — **[Stacks, Section 0AU3], clause
  (7)**.

## Implementation notes

*`𝒩` and `f^*𝒪_Y(X)`.* The clause writes the tensor factor as `f^*𝒪_Y(X)`, the pullback to the
divisor of the invertible sheaf it defines. That is how
`Stacks.Divisors.normalSheafShiftToDerivedSheafHomExactSupport` reads it: the map of
[Stacks, Tag 0AA4] is formed after
`Stacks.Divisors.normalSheafIsoInvertibleSheaf`, the normal-sheaf clause of [Stacks, Tag 0B3P],
which identifies `𝒩_{D/X}` with `i^*𝒪_X(D)`. So no further identification is needed and the two
spellings are the same sheaf.

*What `f^!` is.* As in clause (5), the twisted inverse image enters as a functor `a` together
with the adjunction `Ri_* ⊣ a` characterising it, not as a constructed functor; a right adjoint
being unique up to canonical isomorphism, the statement about an arbitrary one says the same
thing as the statement about any particular one. That `a` exists is [Stacks, Tag 0A9E], proved
unconditionally for a morphism of quasi-compact quasi-separated schemes as
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs` and,
for a closed immersion with no hypothesis on the target, as
`Stacks.Duality.LocallySmall.isLeftAdjoint_affineHomQuasiCoherentDerivedPushforward`.

*The divisor as an object of `FTS S`.* The clause takes the divisor inside an object `Y` of
`FTS S`; the divisor is then itself an object of `FTS S`, since a closed immersion is separated,
locally of finite type and quasi-compact, and those three properties are stable under
composition. `Stacks.Duality.divisorFTS` and `Stacks.Duality.divisorFTSHom` record that object
and the inclusion as a morphism of `FTS S`, which is what clause (5) consumes.

*The model.* Everything is read at `HasDerivedCategory.standard`, which is the instance both inputs
are stated at — `StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointPredicate.lean`
for the first and `StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierNormalTensorIso.lean` for
the second. The local attribute carries priority `10000` for the same reason it does there: the
import closure reaches `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose
`HasDerivedCategory` instances are global and would otherwise displace the choice.

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

section Divisor

variable {X : Scheme.{u}} (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **The conclusion of clause (7) of [Stacks, Section 0AU3] for one effective Cartier divisor
`D ⊆ X` and one candidate right adjoint `a` of `Ri_*`:** on the bounded-below part of
`D_QCoh(𝒪_X)` the functor `a` agrees with `Li^*(-) ⊗^L_{𝒪_D} 𝒩[-1]`, where `𝒩 = i^*𝒪_X(D)` is
the normal sheaf of the divisor.

This is `Stacks.Duality.IsDerivedSheafHomRightAdjoint` with the functor `a` is compared to
replaced by the one clause (7) names; both sides are compared after the inclusion into the
ambient `D(𝒪_D)`, which is fully faithful. -/
def IsNormalTensorPullbackRightAdjoint
    (a : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory D.subscheme) : Prop :=
  Nonempty
    ((ObjectProperty.ι (isBoundedBelowQuasiCoherent X) ⋙ a ⋙
        (DerivedCategoryB.derivedCategoryB (A := D.subscheme.Modules)
          (SheafOfModules.isQuasicoherent D.subscheme.ringCatSheaf)).ι) ≅
      (ObjectProperty.ι (isBoundedBelowQuasiCoherent X) ⋙
        (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
        Stacks.Divisors.normalTensorDerivedPullback D))

/-- **Clause (5) of [Stacks, Section 0AU3] plus [Stacks, Tag 0AA4] give clause (7).** If a
candidate right adjoint `a` of `Ri_*` is derived sheaf Hom out of `𝒪_D` on bounded-below
complexes, then it is `Li^*(-) ⊗^L_{𝒪_D} 𝒩[-1]` there, because the canonical map from the latter
to the former is an isomorphism of functors by [Stacks, Tag 0AA4]. -/
theorem isNormalTensorPullbackRightAdjoint_of_isDerivedSheafHomRightAdjoint
    (a : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory D.subscheme)
    (h : IsDerivedSheafHomRightAdjoint D.subschemeι a) :
    IsNormalTensorPullbackRightAdjoint D a :=
  ⟨h.some ≪≫ Functor.isoWhiskerLeft _
    (Functor.isoWhiskerLeft _ (Stacks.Divisors.normalTensorDerivedSheafHomIso D).symm)⟩

end Divisor

section FTS

variable {S : Scheme.{u}} [IsNoetherian S] (Y : AlgebraicGeometry.FTS S)
  (D : Y.left.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **An effective Cartier divisor in an object of `FTS S` is an object of `FTS S`.** Its
structure morphism is the closed immersion of the divisor followed by that of the ambient
scheme; a closed immersion is separated, locally of finite type and quasi-compact, and all three
properties are stable under composition. -/
abbrev divisorFTS : AlgebraicGeometry.FTS S :=
  AlgebraicGeometry.FTS.mk (D.subschemeι ≫ Y.hom)

/-- The inclusion of an effective Cartier divisor, as a morphism of `FTS S`. -/
abbrev divisorFTSHom : divisorFTS Y D ⟶ Y :=
  CategoryTheory.MorphismProperty.Over.homMk D.subschemeι rfl trivial

/-- The underlying morphism of schemes of `Stacks.Duality.divisorFTSHom` is the closed immersion
of the divisor, so it is a closed immersion. This is what clause (5) of the section consumes. -/
instance isClosedImmersion_divisorFTSHom_left :
    IsClosedImmersion (divisorFTSHom Y D).left :=
  inferInstanceAs (IsClosedImmersion D.subschemeι)

/-- **Stacks Project, Section 0AU3, clause (7).** Let `S` be a Noetherian scheme, let `Y` be an
object of `AlgebraicGeometry.FTS S` — a scheme separated and of finite type over `S` — and let
`D ⊆ Y` be an effective Cartier divisor, with closed immersion `i : D ⟶ Y` and normal sheaf
`𝒩 = i^*𝒪_Y(D)`. Let `a` be a right adjoint of `Ri_* : D_QCoh(𝒪_D) ⥤ D_QCoh(𝒪_Y)`. Then `a`,
which is `i^!`, is `Li^*(-) ⊗^L_{𝒪_D} 𝒩[-1]` on bounded-below complexes with quasi-coherent
cohomology:

`i^!(-) = Li^*(-) ⊗_{𝒪_D} i^*𝒪_Y(D)[-1]`.

The proof is the section's own: clause (5) of the section, which is [Stacks, Tag 0AA2] and is
formalized as `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion`, identifies
`i^!` with `R𝓗om_{𝒪_Y}(𝒪_D, -)`; and [Stacks, Tag 0AA4],
`Stacks.Divisors.normalTensorDerivedSheafHomIso`, identifies that with
`Li^*(-) ⊗^L_{𝒪_D} 𝒩[-1]`. -/
@[stacks 0AU3 "clause (7) of Section 48.19: for the inclusion of an effective Cartier divisor \
  into an object of FTS S, f^! is derived pullback tensored with the shifted normal sheaf \
  i^*O_Y(D)[-1]. Both inputs are proved unconditionally: clause (5) of the same section \
  (Tag 0AA2) as Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion, and \
  Tag 0AA4 as Stacks.Divisors.normalTensorDerivedSheafHomIso. As in clause (5), i^! is the \
  explicit parameter a with its adjunction, the existence statement being Tag 0A9E"]
theorem isNormalTensorPullbackRightAdjoint_of_fts
    (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory D.subscheme)
    (adj : affineHomQuasiCoherentDerivedPushforward D.subschemeι ⊣ a) :
    IsNormalTensorPullbackRightAdjoint D a :=
  isNormalTensorPullbackRightAdjoint_of_isDerivedSheafHomRightAdjoint D a
    (isDerivedSheafHomRightAdjoint_of_fts_closedImmersion (divisorFTSHom Y D) a adj)

end FTS

end Stacks.Duality

end
