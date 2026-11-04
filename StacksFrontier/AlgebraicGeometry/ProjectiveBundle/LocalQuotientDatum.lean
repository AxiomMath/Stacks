module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TrivializingAffineCover
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.QuotientGradedMap

/-!
# The local datum of an invertible quotient

The inverse direction of Tag 0B3V's bijection builds a section of `𝐏(ℰ) ⟶ X` from an invertible
quotient `q : ℰ ↠ ℒ` by working over a cover of `X`. **On each member of that cover three things
must hold at once**: it is affine, `ℒ` is trivial on it, and `q` is *actually surjective on
sections* over it — not merely an epimorphism of sheaves. This file supplies a cover with all
three, for any scheme, any quasi-coherent `ℰ` and any invertible `ℒ`.

The third is the one that is not formal. An epimorphism of sheaves of modules is only locally
surjective on sections, so on a general open there need be no `s` with `q(s) = t`. Over an
*affine* open and for *quasi-coherent* modules it is genuinely surjective, because the obstruction
lies in the first cohomology of the kernel and that vanishes;
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` is that statement, and it is why the
cover has to be affine rather than merely trivializing.

Nothing here is new mathematics. The content is that the two known covers can be taken to be the
*same* cover, together with the observation that `ℒ` being invertible makes it quasi-coherent and
so eligible for the surjectivity theorem.

## Main results

* `Stacks.RelativeProj.exists_affineOpen_trivializing_surjective`: **every point has an affine
  open neighbourhood on which `ℒ` is trivial and `q` is surjective on sections.**
* `Stacks.RelativeProj.exists_lift_of_trivializing`: the same, stated as the lift that the
  construction actually consumes — a section of `ℰ` mapping to a prescribed section of `ℒ`.

## Implementation notes

**Why `ℒ` is quasi-coherent for free.** `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`
requires both modules to be quasi-coherent, and only `ℰ` is assumed so. An invertible module is
locally isomorphic to the structure sheaf, hence quasi-coherent:
`Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule` supplies the instance, so no
hypothesis is added to the statements below. It is stated for `Stacks.Ample.IsInvertibleModule`,
the `Stacks.SheafOfModules` spelling of invertibility, so
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` converts the instance this file
carries.

**The trivialization is reported as `Nonempty`, not as a chosen isomorphism.** That is the form
`Stacks.LineBundle.Situation.exists_trivializing_affineOpen` produces, and the construction
downstream chooses one per cover member anyway; carrying an unchosen one here would force every
consumer to transport along a choice it did not make.

**The line bundle situation is the identity one.** The trivializing cover is stated for a
`Stacks.LineBundle.Situation`, whose base morphism plays no part in it;
`Stacks.RelativeProj.invertibleSituation` supplies the identity, exactly as for the graded map.

No `@[stacks]` attribute is attached. Tag 0B3V is the bijection and Tag 01CS the local triviality
of an invertible module; collecting two known covers into one asserts neither.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F L : X.Modules} [F.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Every point has an affine open neighbourhood on which `ℒ` is trivial and `q` is surjective
on sections.** The three conditions the inverse direction of Tag 0B3V's bijection needs of a
cover member, on one cover. -/
theorem exists_affineOpen_trivializing_surjective (q : F ⟶ L) [Epi q] (p : X) :
    ∃ V : X.affineOpens, p ∈ V.1 ∧
      Nonempty (L.over V.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over V.1)) ∧
      Function.Surjective (q.val.app (op V.1)) := by
  obtain ⟨V, hpV, hV⟩ := (invertibleSituation L).exists_trivializing_affineOpen p
  have : L.IsQuasicoherent :=
    have : Stacks.Ample.IsInvertibleModule X L :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr ‹_›
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  exact ⟨V, hpV, hV, Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X q V.1 V.2⟩

/-- **The lift, in the form the construction consumes.** Given a section `t` of `ℒ` over an
affine open trivializing it — in practice the generator the trivialization provides — there is a
section of `ℰ` over that open mapping to it. This is the degree-one element whose image is a unit,
which is what `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit` is applied
to. -/
theorem exists_lift_of_trivializing (q : F ⟶ L) [Epi q] (p : X) :
    ∃ V : X.affineOpens, p ∈ V.1 ∧
      Nonempty (L.over V.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over V.1)) ∧
      ∀ t : L.val.obj (op V.1), ∃ s : F.val.obj (op V.1), q.val.app (op V.1) s = t := by
  obtain ⟨V, hpV, hV, hsurj⟩ := exists_affineOpen_trivializing_surjective q p
  exact ⟨V, hpV, hV, fun t => hsurj t⟩

end Stacks.RelativeProj

end
