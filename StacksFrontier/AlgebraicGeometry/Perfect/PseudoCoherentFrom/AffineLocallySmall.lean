module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Pseudo-coherence on an affine scheme, at the locally small derived category

Let `A` be a commutative ring and let `M` be a cochain complex of `A`-modules. Tag 08E7 compares
`m`-pseudo-coherence of `M` with `m`-pseudo-coherence of the complex of `𝒪`-modules it determines
on `Spec A`. The sheaf-level side of that comparison speaks of an object of the derived category
of `𝒪_{Spec A}`-modules, and that derived category is data: `HasDerivedCategory.{d}` fixes the
universe `d` in which the morphisms live. The two choices in use for a scheme are the standard
one, whose morphisms are in `Type (u + 1)`, and the locally small one, whose morphisms are again
in `Type u`; the latter is the only one at which the quasi-coherent derived category has the
direct sums Brown representability needs, so it is the one at which derived sheafification
`M ↦ M̃` (Tag 06Z0) and the affine base-change comparison (Tag 08DW) are stated. This file states
Tag 08E7 there.

No new mathematics is involved. Sheaf-level `m`-pseudo-coherence of the *object* `Q(𝒦)` is
equivalent, at every choice of derived category, to `m`-pseudo-coherence of the *complex* `𝒦`, a
condition which mentions no derived category at all: one direction is Tag 08CC part (2), and the
other takes `𝒦` itself as the representative. So the statement of Tag 08E7 whose sheaf-level side
is the complex-level condition on the sheafification of `M` implies the statement at any choice of
derived category, and it is proved from the existing one at the standard choice.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_obj_iff` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherent_Q_obj_iff` — pseudo-coherence of the object
  `Q(𝒦)` is pseudo-coherence of the complex `𝒦`, for any choice of derived category.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_tilde_iff` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplex_tilde_iff` — Tag 08E7 with its
  sheaf-level side phrased for the complex, mentioning no derived category of
  `𝒪_{Spec A}`-modules.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_tilde_iff_locallySmall` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherent_tilde_iff_locallySmall` — Tag 08E7 with its
  sheaf-level side read in the derived category of `𝒪_{Spec A}`-modules whose morphisms are in
  `Type u`.

## Implementation notes

The module-level predicate `StacksDraft.PseudoCoherence.IsPseudoCoherentFrom` carries no
`HasDerivedCategory` binder: the derived category of `A`-modules in its type is the one built by
`HasDerivedCategory.standard`, with morphisms in `Type (u + 1)`. The module side of every
statement below is therefore at that derived category, and only the sheaf side moves. `A`-modules
and `𝒪_{Spec A}`-modules have separate `HasDerivedCategory` instances, so this is consistent;
nothing identifies the two universes.

`HasDerivedCategory.standard` is activated at a raised priority, because at the default priority
the locally small `ModuleCat.hasDerivedCategory` is selected first and the goal
`HasDerivedCategory.{u + 1} (ModuleCat.{u} A)` is then reported unsolvable. The locally small
instances for sheaves of modules are raised above it in turn, which is what fixes the sheaf side
of the last two statements while leaving the module side standard.

No statement here mentions two derived categories of the *same* category: the comparison between
the two choices on the sheaf side is routed through the complex-level condition, which mentions
none. That is not only cleaner but necessary. An instance hypothesis
`[HasDerivedCategory.{d} (OXMod.{u, u} X)]` makes the goal
`HasDerivedCategory.{u + 1} (OXMod.{u, u} X)` unsolvable even where it is solvable without that
hypothesis, so a single declaration cannot hold a free choice of derived category on the sheaf
side and still appeal to the standard one.

## References

* [Stacks Project, Lemma 36.61.4 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Lemma 20.46.9 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

/-! ### Pseudo-coherence of an object presented by a complex -/

/-- **A complex whose image in the derived category is `m`-pseudo-coherent is itself
`m`-pseudo-coherent.** This is Tag 08CC part (2) applied to the presentation of `Q(𝒦)` by `𝒦`
itself. -/
public theorem isPseudoCoherentComplexFrom_of_Q_obj {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] {K : CochainComplex (OXMod.{u, u} X) ℤ} {m : ℤ}
    (h : IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m) : IsPseudoCoherentComplexFrom K m :=
  isPseudoCoherentComplexFrom_of_iso _ m h K (Iso.refl _)

/-- **A complex whose image in the derived category is pseudo-coherent is itself
pseudo-coherent.** Each degree is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_Q_obj` applied to the single
representative furnished by pseudo-coherence of `Q(𝒦)`. -/
public theorem isPseudoCoherentComplex_of_Q_obj {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] {K : CochainComplex (OXMod.{u, u} X) ℤ}
    (h : IsPseudoCoherent (DerivedCategory.Q.obj K)) : IsPseudoCoherentComplex K := by
  obtain ⟨K', hK', ⟨e⟩⟩ := h
  exact fun m => isPseudoCoherentComplexFrom_of_Q_obj (K := K) ⟨K', hK' m, ⟨e⟩⟩

/-- **`m`-pseudo-coherence of `Q(𝒦)` is `m`-pseudo-coherence of `𝒦`.** A complex which is
`m`-pseudo-coherent represents its own image in the derived category, and conversely Tag 08CC
part (2) makes every complex representing an `m`-pseudo-coherent object `m`-pseudo-coherent.

The right-hand side mentions no derived category, so the left-hand side holds at one choice of
derived category exactly when it holds at every other. -/
public theorem isPseudoCoherentFrom_Q_obj_iff {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (K : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m ↔ IsPseudoCoherentComplexFrom K m :=
  ⟨isPseudoCoherentComplexFrom_of_Q_obj, fun h => ⟨K, h, ⟨Iso.refl _⟩⟩⟩

/-- **Pseudo-coherence of `Q(𝒦)` is pseudo-coherence of `𝒦`.** As for a single degree, and for
the same reason. -/
public theorem isPseudoCoherent_Q_obj_iff {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (K : CochainComplex (OXMod.{u, u} X) ℤ) :
    IsPseudoCoherent (DerivedCategory.Q.obj K) ↔ IsPseudoCoherentComplex K :=
  ⟨isPseudoCoherentComplex_of_Q_obj, fun h => ⟨K, h, ⟨Iso.refl _⟩⟩⟩

/-! ### Tag 08E7 with its sheaf-level side read on complexes -/

section Complexes

attribute [local instance 2000] _root_.HasDerivedCategory.standard

/-- **Tag 08E7 for `m`-pseudo-coherence, with the sheaf-level side read on complexes.** A complex
`M` of `A`-modules is `m`-pseudo-coherent exactly when the complex of `𝒪`-modules it determines
on `Spec A` is an `m`-pseudo-coherent complex. No derived category of `𝒪_{Spec A}`-modules occurs
in the statement, so it is the form of Tag 08E7 from which the statement at any choice of derived
category follows. -/
public theorem isPseudoCoherentComplexFrom_tilde_iff {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (m : ℤ) :
    IsPseudoCoherentComplexFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (((tilde.functor (CommRingCat.of A) :
          ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m :=
  (isPseudoCoherentFrom_Q_obj_iff (X := (Spec (CommRingCat.of A)).toRingedSpace) _
    m).symm.trans (isPseudoCoherentFrom_tilde_iff M m)

/-- **Tag 08E7 for pseudo-coherence, with the sheaf-level side read on complexes.** A complex `M`
of `A`-modules is pseudo-coherent exactly when the complex of `𝒪`-modules it determines on
`Spec A` is a pseudo-coherent complex. -/
public theorem isPseudoCoherentComplex_tilde_iff {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsPseudoCoherentComplex (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (((tilde.functor (CommRingCat.of A) :
          ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
  (isPseudoCoherent_Q_obj_iff (X := (Spec (CommRingCat.of A)).toRingedSpace)
    _).symm.trans (isPseudoCoherent_tilde_iff M)

end Complexes

/-! ### Tag 08E7 at the locally small derived category -/

section LocallySmall

attribute [local instance 2000] _root_.HasDerivedCategory.standard
attribute [local instance 3000] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

/-- **Tag 08E7 for `m`-pseudo-coherence, at the locally small derived category.** A complex of
`A`-modules is `m`-pseudo-coherent exactly when the complex of `𝒪`-modules it determines on
`Spec A` is `m`-pseudo-coherent as an object of the derived category of `𝒪_{Spec A}`-modules
whose morphisms are in `Type u`. That is the derived category at which derived sheafification and
the affine base-change comparison are stated. -/
@[stacks 08E7 "m-pseudo-coherent, at the locally small derived category"]
public theorem isPseudoCoherentFrom_tilde_iff_locallySmall {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (m : ℤ) :
    IsPseudoCoherentFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (DerivedCategory.Q.obj
          (((tilde.functor (CommRingCat.of A) :
            ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
            ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m :=
  (isPseudoCoherentFrom_Q_obj_iff _ m).trans (isPseudoCoherentComplexFrom_tilde_iff M m)

/-- **Tag 08E7 for pseudo-coherence, at the locally small derived category.** A complex of
`A`-modules is pseudo-coherent exactly when the complex of `𝒪`-modules it determines on `Spec A`
is pseudo-coherent as an object of the derived category of `𝒪_{Spec A}`-modules whose morphisms
are in `Type u`. -/
@[stacks 08E7 "pseudo-coherent, at the locally small derived category"]
public theorem isPseudoCoherent_tilde_iff_locallySmall {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsPseudoCoherent (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (DerivedCategory.Q.obj
          (((tilde.functor (CommRingCat.of A) :
            ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
            ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
  (isPseudoCoherent_Q_obj_iff _).trans (isPseudoCoherentComplex_tilde_iff M)

end LocallySmall

end AlgebraicGeometry.RingedSpace

end
