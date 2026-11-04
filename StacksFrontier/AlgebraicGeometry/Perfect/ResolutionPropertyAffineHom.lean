module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Coherent.FiniteTypeSubobjectLimits.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineFaithful
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty

/-!
# The resolution property along an affine morphism

The affine half of [Stacks, Tag 0F88]: if `f : X ⟶ Y` is an affine morphism onto a
quasi-compact, quasi-separated scheme with the resolution property, then `X` has the resolution
property.

## Main results

* `AlgebraicGeometry.hasResolutionProperty_of_isAffineHom`: the statement.

## Implementation notes

Let `F` be a finite type quasi-coherent `𝒪_X`-module.
`Stacks.AlgebraicGeometry.ModuleLimits.exists_finitePresentation_epi_pullback` produces an
`𝒪_Y`-module `G` of finite presentation and an epimorphism `f^*G ⟶ F`: it writes `f_*F` as a
directed colimit of finitely presented modules, pulls that colimit back along `f` — a left
adjoint, so the result is again a colimit — composes with the counit, and finds a single stage
of the colimit that already surjects. A module of finite presentation is quasi-coherent and of
finite type, so the resolution property of `Y` gives a finite locally free `E` with `E ⟶ G`
epi. Pulling back preserves epimorphisms, the pullback of a finite locally free module is
finite locally free, and the composite `f^*E ⟶ f^*G ⟶ F` is the required presentation of `F`.

`exists_finitePresentation_epi_pullback` is stated with two hypotheses that it does not prove,
and both are discharged here rather than passed on.

* Its `hepi` asks that the counit of `pullback f ⊣ pushforward f` be epi at quasi-coherent
  modules for an affine `f`, which is the half of [Stacks, Tag 01SB] the colimit argument needs.
  That is `Stacks.AlgebraicGeometry.ModuleLimits.affineCounitEpi`, proved from faithfulness of
  the pushforward in
  `StacksFrontier/AlgebraicGeometry/ModuleLimits/AffineFaithful.lean`.
* Its `hcolim` asks for the presentation of a quasi-coherent module on a quasi-compact
  quasi-separated scheme as a directed colimit of finitely presented ones. That is
  [Stacks, Tag 01PK], proved as
  `AlgebraicGeometry.exists_directed_system_of_isFinitePresentation`, with exactly the shape the
  hypothesis asks for.

Neither hypothesis is therefore open; `StacksFrontier/AlgebraicGeometry/ModuleLimits/Descend.lean`
carries both as hypotheses, and the two
files above discharge them.

`exists_finitePresentation_epi_pullback` also asks for `[CompactSpace X]`, which is not an
assumption of [Stacks, Tag 0F88]. It is implied: an affine morphism is quasi-compact and the
target is quasi-compact, so `QuasiCompact.compactSpace_of_compactSpace` supplies it, and the
hypotheses below are those of the source statement.

[Stacks, Tag 0F88] is stated for a morphism that is affine **or** quasi-affine, so this
declaration covers only the affine branch and its tag carries that clause string. The
quasi-affine branch is a different argument, routing through [Stacks, Tag 0891] and
[Stacks, Tag 0FDD]; **both are proved** — as
`Stacks.AmplePullback.isRelativelyAmple_iff_isQuasiAffineHom_of_iso_unitModule` and
`AlgebraicGeometry.hasResolutionProperty_of_isRelativelyAmple`. The quasi-affine case, and the full disjunction of the
source, are
`AlgebraicGeometry.hasResolutionProperty_of_isQuasiAffineHom` and
`AlgebraicGeometry.hasResolutionProperty_of_isAffineHom_or_isQuasiAffineHom` in
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyQuasiAffineHom.lean`. The proof below
is kept because it is independent of relative ampleness.

## References

* [Stacks Project, Tag 0F88](https://stacks.math.columbia.edu/tag/0F88)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace AlgebraicGeometry

/-- **The affine case of [Stacks, Tag 0F88].** The source of an affine morphism onto a
quasi-compact, quasi-separated scheme with the resolution property has the resolution property.

The quasi-affine case is
`AlgebraicGeometry.hasResolutionProperty_of_isQuasiAffineHom`, by way of [Stacks, Tag 0FDD] — so
the tag below carries the clause string naming the case that is. -/
@[stacks 0F88 "the affine case"]
theorem hasResolutionProperty_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [HasResolutionProperty Y] :
    HasResolutionProperty X := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  constructor
  intro F _ _
  obtain ⟨G, hGfp, p, hp⟩ :=
    exists_finitePresentation_epi_pullback affineCounitEpi.{u} f F
  obtain ⟨hGqc, hGft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation
      G hGfp
  have := hGqc
  have := hGft
  obtain ⟨E, hE, u, hu⟩ := HasResolutionProperty.exists_finiteLocallyFree_quotient G
  have : Epi u := hu
  have : Epi ((Scheme.Modules.pullback f).map u) :=
    preserves_epi_of_preservesColimit (Scheme.Modules.pullback f) u
  have : Epi p := hp
  exact ⟨(Scheme.Modules.pullback f).obj E,
    SheafOfModules.IsFiniteLocallyFree.pullback_scheme f E hE,
    (Scheme.Modules.pullback f).map u ≫ p, inferInstance⟩

end AlgebraicGeometry

end
