module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport

/-!
# Coherence of the module on the scheme-theoretic support

Let `X` be a locally Noetherian algebraic space over a scheme `S`, let `F` be a coherent
`𝒪_X`-module and let `i : Z → X` be the scheme-theoretic support of `F`, with `G` the
quasi-coherent `𝒪_Z`-module whose direct image along `i` is `F`.  Stacks 07UG asserts that `G`
is a coherent `𝒪_Z`-module.

The scheme-theoretic support enters only through the fact that it is a closed subspace, so the
statement is proved here for an arbitrary closed subspace `Z` of `X` and then specialized.  The
inclusion of a closed subspace is a closed immersion, hence locally of finite type, so `Z` is
again locally Noetherian; `F` is of finite type because it is coherent, hence so is `G` by
Stacks 07U0 part (3); and on a locally Noetherian algebraic space a quasi-coherent module of
finite type is coherent by Stacks 07UB (1) ⇔ (2).

## Main results

* `AlgebraicGeometry.Space.isCoherent_of_modulePushforward_closedSubspace`: a quasi-coherent
  module on a closed subspace of a locally Noetherian algebraic space whose direct image is
  coherent is itself coherent.
* `AlgebraicGeometry.Space.isClosedSubspace_schemeTheoreticSupport_of_isCoherent` and
  `AlgebraicGeometry.Space.coherentSchemeTheoreticSupport`: the scheme-theoretic support of a
  coherent module is a closed subspace of `X`, and is read as one.
* `AlgebraicGeometry.Space.isCoherent_module_on_coherentSchemeTheoreticSupport`: **Stacks 07UG**,
  the same statement at the scheme-theoretic support of the coherent module;
  `AlgebraicGeometry.Space.isCoherent_module_on_schemeTheoreticSupport` is the same statement
  with the (always available) closedness witness passed as an argument.

## Implementation notes

Local Noetherianity of an algebraic space is the étale-local scheme property of Stacks 03E6
attached to `AlgebraicGeometry.IsLocallyNoetherian`, and the coherence criterion of Stacks 07UB
consumes it as a `Fact` instance on the space in question, so the criterion is applied to the
closed subspace only after its local Noetherianity has been established and registered.

Finite type appears in two equivalent forms, the categorical
`SheafOfModules.IsFiniteTypeOnSite` of Stacks 03DL(5) and the sectionwise
`CategoryTheory.PresheafOfModules.IsFiniteType`; Stacks 07U0 part (3) produces the first and
the criterion of Stacks 07UB consumes the second, and the two are exchanged by
`Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite`.

The witness that the scheme-theoretic support is a closed subspace has to be named before the
module on the support can be spoken of, so it is produced first, by
`AlgebraicGeometry.Space.isClosedSubspace_schemeTheoreticSupport_of_isCoherent`, and bundled
into `AlgebraicGeometry.Space.coherentSchemeTheoreticSupport`; it is not a hypothesis of
`AlgebraicGeometry.Space.isCoherent_module_on_coherentSchemeTheoreticSupport`. The module `G` and
the identification of its direct image with `F` are hypotheses, exactly as in the source's
phrasing, where they come from the definition of the
scheme-theoretic support, so nothing here depends on the essential-image input carried by
`AlgebraicGeometry.Space.exists_module_on_schemeTheoreticSupport`.

## References

* [Stacks Project, Lemma 69.12.7 (Tag 07UG)](https://stacks.math.columbia.edu/tag/07UG)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **A quasi-coherent module on a closed subspace of a locally Noetherian algebraic space
whose direct image is coherent is itself coherent.**

The closed subspace is locally Noetherian because its inclusion is a closed immersion, hence
locally of finite type; the module on it is of finite type by Stacks 07U0 part (3); and over a
locally Noetherian space quasi-coherent plus finite type is coherent, by Stacks 07UB. -/
theorem isCoherent_of_modulePushforward_closedSubspace
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F]
    (Z : ClosedSubspaces B S hS X.1)
    (G : Modules.{u, u} B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2)
    (hG : G.IsQuasicoherentOnSite)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS X Z)).obj G ≅ F) :
    IsCoherent B S hS (closedSubspaceToSpace B S hS X Z).1
      (closedSubspaceToSpace B S hS X Z).2 G := by
  have hZnoeth : HasEtaleLocalProperty B S hS (closedSubspaceToSpace B S hS X Z).1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z.2.1 X.2 Z.1.ι
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS Z.1.ι Z.2.2) hX
  have : Fact (HasEtaleLocalProperty B S hS (closedSubspaceToSpace B S hS X Z).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hZnoeth⟩
  have hGft : SheafOfModules.IsFiniteTypeOnSite G :=
    isFiniteTypeOnSite_module_on_closedSubspace B S hS X F
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F) Z G e
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS
    (closedSubspaceToSpace B S hS X Z).1 (closedSubspaceToSpace B S hS X Z).2 G).2
    ⟨hG, Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite G hGft⟩

/-- **The scheme-theoretic support of a coherent module is a closed subspace.**

A coherent module is quasi-coherent and, being coherent on the small étale site, of finite
type there, so this is `AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`
for `F`. -/
theorem isClosedSubspace_schemeTheoreticSupport_of_isCoherent
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F] :
    IsClosedSubspace B S hS (schemeTheoreticSupport B S hS X F) :=
  (exists_isClosedSubspace_schemeTheoreticSupport B S hS X F
    ‹IsCoherent B S hS X.1 X.2 F›.toIsQuasicoherentOnSite
    ‹IsCoherent B S hS X.1 X.2 F›.toIsCoherentOnSite.isFiniteType).elim fun hZ _ => hZ

/-- The scheme-theoretic support of a coherent module, read as a closed subspace of `X`. -/
def coherentSchemeTheoreticSupport (F : Modules.{u, u} B S hS X.1 X.2)
    [IsCoherent B S hS X.1 X.2 F] : ClosedSubspaces B S hS X.1 :=
  ⟨schemeTheoreticSupport B S hS X F,
    isClosedSubspace_schemeTheoreticSupport_of_isCoherent B S hS X F⟩

/-- **Stacks 07UG.**  Let `X` be a locally Noetherian algebraic space over `S`, let `F` be a
coherent `𝒪_X`-module, let `i : Z → X` be the scheme-theoretic support of `F` and let `G` be
the quasi-coherent `𝒪_Z`-module with `i_*G ≅ F`.  Then `G` is a coherent `𝒪_Z`-module.

Here the witness `hZ` that the support is a closed subspace is an argument; it is a
proposition that always holds, by
`AlgebraicGeometry.Space.isClosedSubspace_schemeTheoreticSupport_of_isCoherent`, and the form
with no such argument is
`AlgebraicGeometry.Space.isCoherent_module_on_coherentSchemeTheoreticSupport`. -/
@[stacks 07UG]
theorem isCoherent_module_on_schemeTheoreticSupport
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F]
    (hZ : IsClosedSubspace B S hS (schemeTheoreticSupport B S hS X F))
    (G : Modules.{u, u} B S hS
      (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).1
      (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).2)
    (hG : G.IsQuasicoherentOnSite)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS X
      ⟨schemeTheoreticSupport B S hS X F, hZ⟩)).obj G ≅ F) :
    IsCoherent B S hS
      (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).1
      (closedSubspaceToSpace B S hS X ⟨schemeTheoreticSupport B S hS X F, hZ⟩).2 G :=
  isCoherent_of_modulePushforward_closedSubspace B S hS X hX F
    ⟨schemeTheoreticSupport B S hS X F, hZ⟩ G hG e

/-- **Stacks 07UG.**  Let `X` be a locally Noetherian algebraic space over `S`, let `F` be a
coherent `𝒪_X`-module, let `i : Z → X` be the scheme-theoretic support of `F` and let `G` be
the quasi-coherent `𝒪_Z`-module with `i_*G ≅ F`.  Then `G` is a coherent `𝒪_Z`-module.

The scheme-theoretic support is read as the closed subspace
`AlgebraicGeometry.Space.coherentSchemeTheoreticSupport`, so no witness of closedness is
assumed. -/
@[stacks 07UG]
theorem isCoherent_module_on_coherentSchemeTheoreticSupport
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F]
    (G : Modules.{u, u} B S hS
      (closedSubspaceToSpace B S hS X (coherentSchemeTheoreticSupport B S hS X F)).1
      (closedSubspaceToSpace B S hS X (coherentSchemeTheoreticSupport B S hS X F)).2)
    (hG : G.IsQuasicoherentOnSite)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS X
      (coherentSchemeTheoreticSupport B S hS X F))).obj G ≅ F) :
    IsCoherent B S hS
      (closedSubspaceToSpace B S hS X (coherentSchemeTheoreticSupport B S hS X F)).1
      (closedSubspaceToSpace B S hS X (coherentSchemeTheoreticSupport B S hS X F)).2 G :=
  isCoherent_module_on_schemeTheoreticSupport B S hS X hX F
    (isClosedSubspace_schemeTheoreticSupport_of_isCoherent B S hS X F) G hG e

end AlgebraicGeometry.Space

end
