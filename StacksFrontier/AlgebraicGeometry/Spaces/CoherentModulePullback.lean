module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport

/-!
# Coherence of the pullback of a coherent module

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `G` be a coherent `𝒪_Y`-module and assume `X` is locally Noetherian.  Then the
pullback `f^*G` of Stacks 03LU is a coherent `𝒪_X`-module.

This is the step the source performs inside the proof of Stacks 0EPB, part (2), where it is the
reason the cycle `[f^*ℱ]_{k+r}` can be written down at all: "Since `X` and `Y` are locally
Noetherian we may apply Cohomology of Spaces, Lemma 69.12.2 to see that `ℱ` is a finite type
`𝒪_Y`-module, that `f^*ℱ` is a finite type `𝒪_X`-module by Modules on Sites, Lemma 18.23.4, and
then another application of Cohomology of Spaces, Lemma 69.12.2 shows that `f^*ℱ` is a coherent
`𝒪_X`-module."  Each of the three citations is available in this library, and the proof below is
exactly that chain:

* Cohomology of Spaces, Lemma 69.12.2 is Stacks 07UB, conditions (1) and (2), proved as
  `AlgebraicGeometry.Space.isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType`;
* Modules on Sites, Lemma 18.23.4 is Stacks 03DO at clause 03DL (5), proved as
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`;
* and quasi-coherence of the pullback, which the source does not need to mention because for it
  coherence contains quasi-coherence, is Stacks 03GA, proved as
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.

Local Noetherianity is needed only on `X`; the source's hypothesis on `Y` is not used, because
finite type of `G` is read off its coherence directly rather than through Stacks 07UB.

## Main results

* `AlgebraicGeometry.Space.isCoherent_modulePullback`: **the pullback of a coherent module along
  an arbitrary morphism of algebraic spaces is coherent, on a locally Noetherian target of the
  pullback.**
* `AlgebraicGeometry.Space.isCoherent_modulePullback_instance`: the same as an instance, for the
  declarations which take coherence as an instance argument — among them
  `AlgebraicGeometry.Space.associatedCycle`, the `k`-cycle `[ℱ]_k` of Stacks 0EEB.

## Implementation notes

**No tag attribute is claimed.**  The statement is a composite of Stacks 07UB, Stacks 03DO and
Stacks 03GA, all three of which carry their attributes where they are proved; it is a step of
the proof of Stacks 0EPB, part (2), and not a clause of any tag of its own.  What it unblocks is
the *statement* of that part: `AlgebraicGeometry.Space.associatedCycle` requires
`AlgebraicGeometry.Space.IsCoherent` as an instance, so without this result `[f^*ℱ]_{k+r}` could
not be written down.  The cycle *identity* of Stacks 0EPB, part (2) needs in addition the base
change `i'_*𝒪_{f^{-1}(Z)} ≅ f^*(i_*𝒪_Z)` of the structure sheaf of a closed subspace along a
morphism which is not étale; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackClosedSubspaceMultiplicity`.

**Local Noetherianity is spelled as the étale-local property of schemes.**  There is no separate
predicate for a locally Noetherian algebraic space in this library; local Noetherianity of `X`
is `AlgebraicGeometry.Space.HasEtaleLocalProperty` at `AlgebraicGeometry.IsLocallyNoetherian`,
carried as a `Fact` instance in the style of
`AlgebraicGeometry.Space.isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType`.  For an étale
chart of a locally Noetherian space the hypothesis is supplied by
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_chart`.

## References

* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The pullback of a coherent module is coherent.**  For a morphism `f : X ⟶ Y` of algebraic
spaces with `X` locally Noetherian and a coherent `𝒪_Y`-module `G`, the pullback `f^*G` of
Stacks 03LU is a coherent `𝒪_X`-module.

By Stacks 07UB, conditions (1) and (2), coherence on a locally Noetherian algebraic space is
quasi-coherence together with finite type.  The pullback is quasi-coherent by Stacks 03GA, and
of finite type by Stacks 03DO at clause 03DL (5), `G` itself being of finite type because it is
coherent.  This is the step the source performs inside the proof of Stacks 0EPB, part (2). -/
theorem isCoherent_modulePullback
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G) :
    IsCoherent B S hS X.1 X.2 ((modulePullback B S hS f).obj G) := by
  have hcoh : SheafOfModules.IsCoherentOnSite G := hG.toIsCoherentOnSite
  have hft : SheafOfModules.IsFiniteTypeOnSite G :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS Y G
  refine (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X.1 X.2
    ((modulePullback B S hS f).obj G)).2 ⟨?_, ?_⟩
  · exact isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G
      hG.toIsQuasicoherentOnSite
  · exact Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _
      (isFiniteTypeOnSite_modulePullback B S hS f G hft)

/-- `AlgebraicGeometry.Space.isCoherent_modulePullback` as an instance, so that the pullback of
a coherent module may be fed to the declarations taking coherence as an instance argument. -/
instance isCoherent_modulePullback_instance
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (f : X ⟶ Y) (G : Modules.{u, u} B S hS Y.1 Y.2) [hG : IsCoherent B S hS Y.1 Y.2 G] :
    IsCoherent B S hS X.1 X.2 ((modulePullback B S hS f).obj G) :=
  isCoherent_modulePullback B S hS f G hG

/-- `AlgebraicGeometry.Space.isCoherent_modulePullback` with the locally Noetherian condition on
the source carried as an explicit hypothesis rather than as a `Fact` instance.

A one-line wrapper, with no proof of its own: the consumers which obtain that condition as the
third component of an `AlgebraicGeometry.Space.IsNoetherian` -- rather than from an instance in
scope -- need it in a term that appears inside a *statement*, where no `haveI` is available, and
supplying the `Fact` as a binder instead would add a hypothesis those statements do not have. -/
theorem isCoherent_modulePullback_of_hasEtaleLocalProperty (f : X ⟶ Y)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G) :
    IsCoherent B S hS X.1 X.2 ((modulePullback B S hS f).obj G) :=
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hLN⟩
  isCoherent_modulePullback B S hS f G hG

end AlgebraicGeometry.Space

end
