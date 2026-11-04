module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Proper
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Unconditional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 0BDG: projectivity descends along any field extension

Let `k` be a field, `X` a scheme over `k` and `K/k` a field extension. [Stacks Project, Tag 0BDG]
says that `X` is projective over `k` as soon as its base change `X_K` is projective over `K`.

The source proof is two lines: a scheme over a field is projective over that field exactly when it
is quasi-projective and proper over it ([Stacks Project, Tag 0BCL], clause (1)), and both
quasi-projectivity and properness descend along an arbitrary field extension —
[Stacks Project, Tag 0BDE] and [Stacks Project, Tag 0BDF], available here as
`AlgebraicGeometry.isQuasiProjective_of_fieldExtension` and
`AlgebraicGeometry.isProper_of_fieldExtension`.

All three inputs are unconditional in this repository, so Tag 0BDG is proved here under the
source's hypotheses and nothing else: the two descents were already unconditional, and clause (1)
of Tag 0BCL at the only bases at which the proof applies it — the affine bases `Spec k` and
`Spec K` — is proved below as
`AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper_of_isAffine`.

## Main results

* `AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper_of_isAffine`: clause (1) of
  [Stacks Project, Tag 0BCL] over an affine base — a morphism to an affine scheme is projective
  if and only if it is quasi-projective and proper.
* `AlgebraicGeometry.ProjectiveIffQuasiProjectiveAndProperOverAffine` and
  `AlgebraicGeometry.projectiveIffQuasiProjectiveAndProperOverAffine`: the same statement
  quantified over all morphisms to all affine bases, and its proof.
* `AlgebraicGeometry.isQuasiProjective_and_isProper_of_fieldExtension`: quasi-projectivity
  together with properness descends along an arbitrary field extension.
* `AlgebraicGeometry.isProjective_of_fieldExtension`: **[Stacks Project, Tag 0BDG]**.

## Implementation notes

**How clause (1) of Tag 0BCL is obtained over an affine base.** The source states it over a
quasi-compact quasi-separated base, and in that generality it is
`AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition`, which goes through Tag 07RM.
Over an **affine** base no such input is needed, because there projectivity and H-projectivity
simply agree, and this file does not import that one. The chain is three unconditional
equivalences:

* `AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine` — Tag 01WB over an
  affine base: projective and H-projective agree there;
* `AlgebraicGeometry.isProjectiveMorphism_iff_isHQuasiProjective_and_isProper` — clause (2) of
  Tag 0BCL, over a base with no hypothesis at all;
* `AlgebraicGeometry.isQuasiProjective_iff_isHQuasiProjective_of_isAffine` — Tag 01VZ over an
  affine base: quasi-projective and H-quasi-projective agree there.

An affine scheme is quasi-compact and quasi-separated, so the result below is a special case of
the source's clause (1) and not a strengthening of it. It is exactly the form the proof of Tag
0BDG consumes: the two bases at which that proof applies the equivalence are `Spec k` and
`Spec K`, both affine.

**The quantified form.** `AlgebraicGeometry.ProjectiveIffQuasiProjectiveAndProperOverAffine`
bundles the equivalence as a single `Prop` quantified over all schemes and all morphisms to an
affine base, and `AlgebraicGeometry.projectiveIffQuasiProjectiveAndProperOverAffine` proves it.

**The shape of the base change.** The base change is
`pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))`, so that its target is literally
the structure morphism's base `Spec K` and the statement is at the order the two descents
`AlgebraicGeometry.isQuasiProjective_of_fieldExtension` and
`AlgebraicGeometry.isProper_of_fieldExtension` are stated at; no comparison of the two orders of
the fibre product appears.

## References

* [Stacks Project, Tag 0BDG](https://stacks.math.columbia.edu/tag/0BDG)
* [Stacks Project, Tag 0BDE](https://stacks.math.columbia.edu/tag/0BDE)
* [Stacks Project, Tag 0BDF](https://stacks.math.columbia.edu/tag/0BDF)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
* [Stacks Project, Tag 01VZ](https://stacks.math.columbia.edu/tag/01VZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Clause (1) of Tag 0BCL over an affine base -/

/-- **Clause (1) of [Stacks Project, Tag 0BCL] over an affine base.** A morphism of schemes to an
affine base is projective — in the sense of `AlgebraicGeometry.IsProjective`, a closed immersion
over the base into the projective bundle of a quasi-coherent module of finite type — if and only
if it is quasi-projective and proper.

Over an affine base projectivity agrees with H-projectivity and quasi-projectivity with
H-quasi-projectivity, by Tags 01WB and 01VZ, and the equivalence in the H-forms is clause (2) of
the same tag. The source states clause (1) over a quasi-compact quasi-separated base; an affine
scheme is both, so this is a special case of it. -/
@[ega "II 5.5.3" "special case"]
public theorem isProjective_iff_isQuasiProjective_and_isProper_of_isAffine {Y S : Scheme.{u}}
    (g : Y ⟶ S) [IsAffine S] : IsProjective g ↔ IsQuasiProjective g ∧ IsProper g := by
  rw [isProjective_iff_isProjectiveMorphism_of_isAffine,
    isProjectiveMorphism_iff_isHQuasiProjective_and_isProper,
    isQuasiProjective_iff_isHQuasiProjective_of_isAffine]

/-- **Clause (1) of [Stacks Project, Tag 0BCL] over an affine base, quantified over all
morphisms.** A morphism of schemes to an affine base is projective if and only if it is
quasi-projective and proper.

This bundles `AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper_of_isAffine` as a
single `Prop`, which is how the proof of [Stacks Project, Tag 0BDG] below carried it while it was
unavailable. It is proved by
`AlgebraicGeometry.projectiveIffQuasiProjectiveAndProperOverAffine`; the quasi-compact
quasi-separated form is `AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper`. -/
public def ProjectiveIffQuasiProjectiveAndProperOverAffine : Prop :=
  ∀ (Y S : Scheme.{u}) (_ : IsAffine S) (g : Y ⟶ S),
    IsProjective g ↔ IsQuasiProjective g ∧ IsProper g

/-- **Clause (1) of [Stacks Project, Tag 0BCL] holds over every affine base.** -/
public theorem projectiveIffQuasiProjectiveAndProperOverAffine :
    ProjectiveIffQuasiProjectiveAndProperOverAffine.{u} := by
  intro Y S hS g
  have := hS
  exact isProjective_iff_isQuasiProjective_and_isProper_of_isAffine g

/-! ### Descent along a field extension -/

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- **The descent half of [Stacks Project, Tag 0BDG].** Let `k` be a field and `X` a scheme over
`k`. If the base change `X_K` is quasi-projective and proper over `K` for some field extension
`K/k`, then `X` is quasi-projective and proper over `k`.

The two halves are [Stacks Project, Tag 0BDE] and [Stacks Project, Tag 0BDF], namely
`AlgebraicGeometry.isQuasiProjective_of_fieldExtension` and
`AlgebraicGeometry.isProper_of_fieldExtension`. -/
public theorem isQuasiProjective_and_isProper_of_fieldExtension
    (h : IsQuasiProjective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    IsQuasiProjective f ∧ IsProper f :=
  ⟨isQuasiProjective_of_fieldExtension k K f h.1, isProper_of_fieldExtension k K f h.2⟩

/-- **[Stacks Project, Tag 0BDG].** Let `k` be a field and `X` a scheme over `k`. If `X_K` is
projective over `K` for some field extension `K/k`, then `X` is projective over `k`.

This is the source proof verbatim: projectivity over a field is quasi-projectivity together with
properness, and each of those descends along an arbitrary field extension by
[Stacks Project, Tag 0BDE] and [Stacks Project, Tag 0BDF]. The identification of projectivity
with the conjunction is clause (1) of [Stacks Project, Tag 0BCL], applied at the two affine bases
`Spec K` and `Spec k`, where it is
`AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper_of_isAffine`. -/
@[stacks 0BDG]
public theorem isProjective_of_fieldExtension
    (h : IsProjective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    IsProjective f :=
  (isProjective_iff_isQuasiProjective_and_isProper_of_isAffine f).mpr
    (isQuasiProjective_and_isProper_of_fieldExtension k K f
      ((isProjective_iff_isQuasiProjective_and_isProper_of_isAffine _).mp h))

add_to_ega "II 6.6.5" "projective descent" isProjective_of_fieldExtension
add_to_ega "IV 9.1.5" "projective case" isProjective_of_fieldExtension

end AlgebraicGeometry

end
