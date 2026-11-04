module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt

/-!
# Pseudo-coherence of a derived pushforward

Let `i : X ⟶ Y` be a morphism of schemes — in the intended application a closed immersion of an
affine scheme into an affine space over an affine base. For an object `E` of the derived category
of `𝒪_X`-modules, this file states that the derived pushforward `Ri_*E` is `m`-pseudo-coherent as
an object of the derived category of `𝒪_Y`-modules, in the sheaf-level sense of Stacks 08CB.

This is the local condition out of which relative pseudo-coherence (Stacks 09UI) is built, and it
is the condition whose independence of the chosen closed immersion is Stacks 09VC.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward`.

## Implementation notes

The unbounded derived pushforward need not be given by a functor on the whole derived category, so
instead of choosing a resolution the statement asks for a complex `K` representing `E` together
with a value of the right derived functor of
`K ↦ Q((i_*)K)`
at `K`, in the sense of `CategoryTheory.Functor.IsRightDerivedValueAt` (Stacks 05S9): a cocone on
the ind-object indexed by quasi-isomorphisms out of `K` which exhibits that ind-object as
essentially constant. Its vertex is `Ri_*E`, and that is the object required to be
`m`-pseudo-coherent. Carrying the cocone in the statement means definedness of the derived functor
is asserted rather than silently assumed.

Pseudo-coherence of the vertex is `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom` at the
ringed space `Y.toRingedSpace`, whose category of modules is `Y.Modules`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these definitions makes
the same declaration.

## References

* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Definition 13.14.2 (05S9)](https://stacks.math.columbia.edu/tag/05S9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The derived pushforward of `E` along `i` is `m`-pseudo-coherent: there are a complex `K`
representing `E` and a cocone `c` exhibiting the value at `K` of the right derived functor of
`K ↦ Q(i_*K)` with respect to the quasi-isomorphisms, whose vertex `c.pt` — that is, `Ri_*E` — is
`m`-pseudo-coherent on `Y` in the sense of Stacks 08CB. -/
public abbrev IsPseudoCoherentFromAfterPushforward
    {X Y : Scheme.{u}} (i : X ⟶ Y) (E : DerivedCategory X.Modules) (m : ℤ) : Prop :=
  let F : CochainComplex X.Modules ℤ ⥤ DerivedCategory Y.Modules :=
    ((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Q
  let W : MorphismProperty (CochainComplex X.Modules ℤ) :=
    HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)
  ∃ K : CochainComplex X.Modules ℤ,
    Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
      ∃ c : Cocone (MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ F),
        F.IsRightDerivedValueAt W K c ∧
          RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) c.pt m

end AlgebraicGeometry.Scheme.Modules

end
