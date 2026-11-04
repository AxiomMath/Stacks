module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-projective morphisms

A morphism of schemes `f : X ⟶ S` is *quasi-projective* when it is of finite type and `X` carries
an invertible sheaf that is ample relative to `f`. This is the first of the three notions of
[Stacks, Tag 01VW]; the other two — H-quasi-projectivity, a quasi-compact immersion into relative
projective space, and local quasi-projectivity, quasi-projectivity after an open cover of the base
— are not defined here. See the implementation notes.

## Main definitions

* `AlgebraicGeometry.IsQuasiProjective`: finite type together with a relatively ample invertible
  sheaf.

## Main results

* `AlgebraicGeometry.IsQuasiProjective.locallyOfFiniteType`,
  `AlgebraicGeometry.IsQuasiProjective.quasiCompact` and
  `AlgebraicGeometry.IsQuasiProjective.exists_isRelativelyAmple`: the three components of the
  predicate, so that it can be consumed without unfolding the conjunction. The first two are the
  quasi-projective case of the finite-type half of [Stacks, Tag 01VX], which for this spelling of
  the definition is immediate; the separated half is discussed in
  `StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType`.
* `AlgebraicGeometry.isQuasiProjective_iff`: the predicate unfolded, and
  `AlgebraicGeometry.IsQuasiProjective.mk'`: its introduction rule from an explicit sheaf.

## Implementation notes

Finite type is spelled as the conjunction of `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact`, which is the characterization of [Stacks, Tag 01T1] and the
spelling every finite-type statement in this repository uses; there is no single named predicate
for it.

Relative ampleness is `Stacks.RelativeAmple.IsRelativelyAmple` of [Stacks, Tag 01VH],
whose invertibility binder is `AlgebraicGeometry.SheafOfModules.IsInvertible` of
[Stacks, Tag 01CS]. Invertibility of the chosen sheaf is therefore existentially bound as data and
then supplied as a local instance, rather than being an instance binder of the predicate: the
sheaf is being quantified over, so there is nothing for instance synthesis to key on. Since
`AlgebraicGeometry.SheafOfModules.IsInvertible` is `Prop`-valued, proof irrelevance makes the
predicate independent of which witness is produced.

**The other two notions of the tag are deliberately absent, and this file carries only the
`"quasi-projective"` clause of the attribute.** H-quasi-projectivity is a quasi-compact immersion
into `ℙⁿ_S`; the closed-immersion variant of that notion is already taken as explicit witness data
rather than as a predicate in
`StacksFrontier/AlgebraicGeometry/HProjectiveProper/Basic.lean`, and introducing a predicate for
the quasi-compact variant alone would leave the two spellings of one idea side by side. Local
quasi-projectivity is quasi-projectivity of `pullback.snd f (𝒰.f i)` for an open cover `𝒰` of `S`,
which this file's definition makes expressible immediately. Neither is used by anything yet.

## References

* [EGA II, Definition 5.3.1]
* [H, page 103]
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01T1](https://stacks.math.columbia.edu/tag/01T1)
* [Stacks Project, Tag 01VX](https://stacks.math.columbia.edu/tag/01VX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is *quasi-projective* when it is of finite type — locally of finite type
and quasi-compact — and the source carries an invertible sheaf that is ample relative to it. -/
@[stacks 01VW "quasi-projective", ega "II 5.3.1"]
public abbrev IsQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  (LocallyOfFiniteType f ∧ QuasiCompact f) ∧
    ∃ L : X.Modules, ∃ hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        X.ringCatSheaf.2 L,
      letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
      Stacks.RelativeAmple.IsRelativelyAmple f L

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- A morphism is quasi-projective precisely when it is locally of finite type, quasi-compact, and
admits an invertible sheaf that is ample relative to it. -/
public theorem isQuasiProjective_iff :
    IsQuasiProjective f ↔ ((LocallyOfFiniteType f ∧ QuasiCompact f) ∧
      ∃ L : X.Modules, ∃ hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
          X.ringCatSheaf.2 L,
        letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
        Stacks.RelativeAmple.IsRelativelyAmple f L) :=
  Iff.rfl

namespace IsQuasiProjective

/-- **Stacks Project, Tag 01VX, quasi-projective case.** A quasi-projective morphism is locally
of finite type; here this is part of the definition. -/
@[stacks 01VX "finite_type"]
public theorem locallyOfFiniteType (h : IsQuasiProjective f) : LocallyOfFiniteType f := h.1.1

/-- **Stacks Project, Tag 01VX, quasi-projective case.** A quasi-projective morphism is
quasi-compact; here this is part of the definition. -/
@[stacks 01VX "finite_type"]
public theorem quasiCompact (h : IsQuasiProjective f) : QuasiCompact f := h.1.2

/-- A quasi-projective morphism admits an invertible sheaf that is ample relative to it. -/
public theorem exists_isRelativelyAmple (h : IsQuasiProjective f) :
    ∃ L : X.Modules, ∃ hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        X.ringCatSheaf.2 L,
      letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
      Stacks.RelativeAmple.IsRelativelyAmple f L :=
  h.2

/-- A morphism locally of finite type that admits a relatively ample invertible sheaf is
quasi-projective; quasi-compactness comes from the relatively ample sheaf. -/
public theorem mk' (hft : LocallyOfFiniteType f) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL' : Stacks.RelativeAmple.IsRelativelyAmple f L) : IsQuasiProjective f :=
  ⟨⟨hft, hL'.1⟩, L, hL, hL'⟩

end IsQuasiProjective

end AlgebraicGeometry

end
