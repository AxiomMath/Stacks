module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningTowerStructureSheafGlobalSections

/-!
# Stacks 0DEL: the structure sheaf of a countably indexed affine formal algebraic space has no
higher cohomology

Let `X` be a countably indexed affine formal algebraic space over `S`. Stacks 0DEL asserts
`Hⁿ(X_étale, 𝒪_X) = 0` for `n > 0`. Here `X_étale` is the small étale site of Stacks 0DEA — the
small étale site of the reduction `X_red` — and `𝒪_X` is the structure sheaf of Stacks 0DEJ,
whose sections over an affine object `U_red` of `X_étale` are `lim Γ(U_λ, 𝒪)` for a presentation
`U = colim U_λ` of the affine formal algebraic space `U` étale over `X` with reduction `U_red`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.countablyIndexedStructureSheaf`: the structure sheaf `𝒪_X` of a
  countably indexed affine formal algebraic space `X`, a sheaf of topological rings on `X_étale`
  read at a reduction of `X`, built from a chosen sequential presentation `X = colim Xₙ`: its
  sections over an affine object `W` of `X_étale` are `lim Γ(Wₙ, 𝒪)`, `Wₙ` the étale lift of `W`
  to `Xₙ`, which is the stage `U ×_X Xₙ` of the affine formal algebraic space `U` étale over `X`
  with `U_red = W`.

## Main results

* `AlgebraicGeometry.FormalSpace.CountablePresentation.structureSheafGlobalSectionsIso`: the
  sections of `𝒪_X` over the final object `X_red` of `X_étale` are `lim Γ(Xₙ, 𝒪)`, the case
  `U = X` of the defining property of Stacks 0DEJ.
* `AlgebraicGeometry.FormalSpace.subsingleton_sheafH_countablyIndexedStructureSheaf`:
  **Stacks 0DEL** at an arbitrary reduction of `X`.
* `AlgebraicGeometry.FormalSpace.subsingleton_sheafH_canonicalStructureSheaf`: **Stacks 0DEL** at
  the reduction of Stacks 0AIN, that is on the site `X_étale` of Stacks 0DEA as the library
  states it.

## Implementation notes

The proof is the one of the source, carried out in
`StacksFrontier.AlgebraicGeometry.Spaces.ThickeningTowerStructureSheafCohomology`. By Stacks 0DEB
(here Stacks 04JS for `X_red`) the cohomology may be computed on `X_affine,étale`. There,
Stacks 03F9 reduces the vanishing to the Čech cohomology of finite coverings
`{Wᵢ ⟶ W}` of affine objects. The Čech complex of `𝒪_X` on such a covering is the inverse limit of
the Čech complexes of `W ↦ Γ(Wₙ, 𝒪)`, which are the Čech complexes of the structure sheaf of the
affine scheme `Wₙ` for the lifted covering, a standard étale covering — the complexes
`B ⊗ … ⊗ B / Jₙ` of the source — and these are acyclic in positive degrees by Stacks 03FJ, which
is the faithfully flat descent of Stacks 023M. The transition maps are surjective, being
restrictions along the closed immersions `Wₙ ⟶ Wₙ₊₁` of affine schemes, so the countability of
the presentation lets the Mittag-Leffler argument pass the vanishing to the limit — the role
Stacks 0AS0 plays in the source.

The cohomology is that of the abelian sheaf underlying `𝒪_X`, with coefficients in the universe
of the objects of `X_étale`; the universe of the `Ext` groups is left free.

The structure sheaf is built from a chosen sequential presentation of `X`; Stacks 0AIC shows that
the rings `lim Γ(Xₙ, 𝒪)` do not depend on the presentation
(`AlgebraicGeometry.FormalSpace.sectionsRingEquivOfPresentations`), and the same holds for the
sections over every affine object of `X_étale`.

## References

* [Stacks Project, Tag 0DEL](https://stacks.math.columbia.edu/tag/0DEL)
* [Stacks Project, Tag 0DEJ](https://stacks.math.columbia.edu/tag/0DEJ)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0DEB](https://stacks.math.columbia.edu/tag/0DEB)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe x u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : FppfSheaf B S hS}

/-- **The structure sheaf `𝒪_X` of a countably indexed affine formal algebraic space `X`**
(Stacks 0DEJ), a sheaf of topological rings on the small étale site `X_étale` of Stacks 0DEA read
at a reduction `R` of `X`. It is built from a chosen sequential presentation `X = colim Xₙ` by
affine schemes along thickenings: its sections over an affine object `W` of `X_étale` are
`lim Γ(Wₙ, 𝒪)` with the inverse-limit topology, where `Wₙ` is the étale lift of `W` to the stage
`Xₙ`. -/
noncomputable def countablyIndexedStructureSheaf (hc : IsCountablyIndexed B S hS X)
    (R : Reduction B S hS X) : Sheaf R.smallEtaleTopology TopCommRingCat.{u + 1} :=
  (nonempty_countablePresentation hc).some.structureSheaf R

/-- **The global sections of the structure sheaf.** For a presentation `X = colim Xₙ`, the
sections of `𝒪_X` over the final object `X_red` of `X_étale` are `lim Γ(Xₙ, 𝒪)` with its
inverse-limit topology: this is the defining property of the structure sheaf in Stacks 0DEJ for
the chart `U = X` and its presentation by the `Xₙ`. -/
noncomputable def CountablePresentation.structureSheafGlobalSectionsIso
    (P : CountablePresentation X) (R : Reduction B S hS X) :
    (P.structureSheaf R).obj.obj
        (Opposite.op (Space.representedTerminalChart (P.reductionIso R))) ≅
      limit ((P.diagram ⋙ BigAffineFppf.toScheme B S hS).op ⋙ Scheme.Γ ⋙
        TopCommRingCat.discreteULiftFunctor.{u + 1}) :=
  Space.towerStructureSheafGlobalSectionsIso (P.reductionIso R) P.tower R.space.property
    P.isAffine_reductionObj

/-- The final object of `X_étale` used in `CountablePresentation.structureSheafGlobalSectionsIso`
is a final object. -/
noncomputable def CountablePresentation.isTerminalReductionChart
    (P : CountablePresentation X) (R : Reduction B S hS X) :
    IsTerminal (Space.representedTerminalChart (P.reductionIso R)) :=
  Space.isTerminalRepresentedTerminalChart (P.reductionIso R)

/-- **Stacks 0DEL.** Let `X` be a countably indexed affine formal algebraic space over `S`, and
let `X_red` be a reduction of `X`. Then the structure sheaf `𝒪_X` has no higher cohomology on
`X_étale`: `Hⁿ(X_étale, 𝒪_X) = 0` for `n > 0`.

Only the countable presentation of `X` is used, not the set-theoretic condition which makes `X`
an affine formal algebraic space, so the statement is given for a countably indexed sheaf. -/
@[stacks 0DEL "at an arbitrary reduction `X_red` of `X`, which Stacks 0DEA reads `X_étale` \
against"]
theorem subsingleton_sheafH_countablyIndexedStructureSheaf (hc : IsCountablyIndexed B S hS X)
    (R : Reduction B S hS X) [HasExt.{x} (Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ Space.topCommRingToAddCommGrp).obj
        (countablyIndexedStructureSheaf hc R)) n) :=
  (nonempty_countablePresentation hc).some.subsingleton_sheafH_structureSheaf R n hn

/-- **Stacks 0DEL.** If `X` is a countably indexed affine formal algebraic space over `S`, then
`Hⁿ(X_étale, 𝒪_X) = 0` for `n > 0`, where `X_étale` is the small étale site of Stacks 0DEA at the
reduction of `X` given by Stacks 0AIN, and `𝒪_X` is the structure sheaf of `X` on it. -/
@[stacks 0DEL]
theorem subsingleton_sheafH_canonicalStructureSheaf (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hc : IsCountablyIndexed B S hS X)
    [HasExt.{x} (Sheaf (canonicalSmallEtaleTopology
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hX)) AddCommGrpCat.{u + 1})]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ Space.topCommRingToAddCommGrp).obj
        (countablyIndexedStructureSheaf hc
          (canonicalReduction
            (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hX)))) n) :=
  subsingleton_sheafH_countablyIndexedStructureSheaf hc _ n hn

end AlgebraicGeometry.FormalSpace

end
