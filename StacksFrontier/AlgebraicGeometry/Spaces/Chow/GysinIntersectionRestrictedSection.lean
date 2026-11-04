module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemePreimageModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeEffectiveCartier

/-!
# The intersection with the vanishing locus is the vanishing locus of the restricted section

In the situation of Stacks 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` be a triple as in
Definition 0ER1, so `ℒ` is invertible, `s` is a global section of it and `E = Z(s)` is its
vanishing locus of Stacks 0845.  For a closed subspace `Z ⊆ X` this file identifies the
intersection `E ∩ Z`, read as a closed subspace of `Z`, with the vanishing locus of the
restricted section:

  `E ∩ Z = Z(s|_Z)`,

and deduces that the effective Cartier hypothesis of Stacks 0ER7 — that `E ∩ Z` is an effective
Cartier divisor on `Z` — is equivalent to the regularity of `s|_Z` as a section of `ℒ|_Z`.

These are the first two sentences of the source's proof of Stacks 0ER7: *"the hypothesis is
equivalent to saying that `s|_Z` is a regular section of `ℒ|_Z`; consequently `D ∩ Z = Z(s|_Z)`"*.

## Main results

* `AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme`: `E ∩ Z = Z(s|_Z)` as closed
  subspaces of `Z`.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_interOnClosedSubspace_iff_isRegularSection`:
  **the first sentence of the proof of Stacks 0ER7**, `E ∩ Z` is an effective Cartier divisor on
  `Z` if and only if `s|_Z` is a regular section of `ℒ|_Z`.

## Implementation notes

### Nothing beyond the hypotheses of Stacks 0ER7 is assumed

`Z` is **not** assumed good over `B`, only to be a closed subspace, which is all Stacks 0ER7
asks of it; in particular no structure morphism `Z → B` and no δ-dimension bound enters.  That is
why the identification is taken from
`AlgebraicGeometry.Space.zeroScheme_modulePullback_eq_preimage` directly, rather than from its
reading in the dimension situation
`AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`
(`StacksFrontier/AlgebraicGeometry/Spaces/Chow/EffectiveCartierPullback.lean`), which carries
goodness of the source of the morphism.  Invertibility of `ℒ` is a hypothesis of Stacks 0ER1 and
so of Stacks 0ER7, and is the only hypothesis either result here carries.

### The two readings of the intersection, and which one this is

`AlgebraicGeometry.Space.interOnClosedSubspace` is `E ∩ Z` read as a closed subspace of `Z`: it
is the inverse image of `E` along `Z → X` in the sense of Stacks 083Q, and it is the object
Stacks 0ER7 asks to be an effective Cartier divisor.  Its sibling
`AlgebraicGeometry.Space.interOnVanishingLocus` reads the same intersection inside `E`, and is
*not* a vanishing locus of a restricted section: it is the inverse image of `Z` along
`i : E → X`.  So only the first reading is identified here, and that is the one the source's
first two sentences are about.

### What this does not do: the note it corrects

The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspace` used to record this
identification as unavailable, for want of the surjectivity half of Stacks 03MB in the form
Stacks 0846 needs; so did those of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinCompatibility`.  That is false:
`AlgebraicGeometry.Space.exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible`
(`StacksFrontier/AlgebraicGeometry/Spaces/ZeroSchemeIdealSheaf.lean`) supplies exactly that input
for an invertible `ℒ`, and
`AlgebraicGeometry.Space.zeroScheme_modulePullback_eq_preimage` is the identification built from
it.  Both notes now say so.

Correcting them does not close Stacks 0ER7.  What the source's proof needs after these two
sentences is Stacks 0EQL for the triple `(Z, ℒ|_Z, s|_Z)`, the identity
`[Z(s|_Z)]_k = ∑ n_W [Z(s|_W)]_k` over the irreducible components `W ⊆ Z` of δ-dimension
`k + 1`, and that identity is not proved in this library; it remains the one carried hypothesis
of `AlgebraicGeometry.Space.gysinCycleMap_closedSubspaceCycle_eq`
(`StacksFrontier/AlgebraicGeometry/Spaces/Chow/GysinOfClosedSubspaceNonContainment.lean`).

## References

* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

section Restriction

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)

/-- The restriction `ℒ|_Z` of a sheaf of modules on `X` to a closed subspace `Z ⊆ X`: its
inverse image of Stacks 03LU along the inclusion `Z → X`. -/
abbrev closedSubspaceRestrictSheaf :
    Modules.{u, u} D.site D.base D.base_mem Z.1.toFunctor Z.2.1 :=
  (modulePullback D.site D.base D.base_mem
    (closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hp.1⟩ Z)).obj L

/-- The restriction `s|_Z` of a global section of `ℒ` to a closed subspace `Z ⊆ X`: its inverse
image along the inclusion `Z → X`, a global section of `ℒ|_Z`. -/
abbrev closedSubspaceRestrictSection : (closedSubspaceRestrictSheaf D p hp L Z).sections :=
  modulePullbackSections D.site D.base D.base_mem
    (closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hp.1⟩ Z) L s

/-- **Stacks 0B8P.** The restriction `ℒ|_Z` of an invertible sheaf to a closed subspace is again
invertible, so `(ℒ|_Z, s|_Z)` is again a pair as in Stacks 0ER1 on `Z`.

This is `AlgebraicGeometry.Space.isInvertibleSheaf_pullbackSheaf` without the goodness of the
source, which Stacks 0ER7 does not assume of `Z`; it is therefore stated in the spelling by
which `AlgebraicGeometry.Space.IsEffectiveCartierDivisor` and the parts of Stacks 0846 index
`𝒪`-modules, rather than as `AlgebraicGeometry.Space.IsInvertibleSheaf`. -/
theorem isInvertible_closedSubspaceRestrictSheaf (hL : IsInvertibleSheaf D p hp L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings D.site D.base D.base_mem
        (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z))
      (structureRingSheaf D.site D.base D.base_mem
        (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z)).property
      (closedSubspaceRestrictSheaf D p hp L Z) :=
  let : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedTopos D.site D.base D.base_mem
        (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos D.site D.base D.base_mem ⟨X, hp.1⟩).O).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  (Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (smallEtaleRingedToposModulesHom D.site D.base D.base_mem
      (closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hp.1⟩ Z)) L).toAlgebraicGeometry _ _ _

/-- **The intersection `E ∩ Z` is the vanishing locus of the restricted section.**  For the
vanishing locus `E = Z(s)` of a global section of an invertible sheaf `ℒ` on `X` and a closed
subspace `Z ⊆ X`, the intersection `E ∩ Z` read as a closed subspace of `Z` is the vanishing
locus `Z(s|_Z)` of Stacks 0845 of the restricted section.

This is the second sentence of the proof of Stacks 0ER7.  Both sides are closed subspaces of
`Z`: the left is the inverse image of `E` along `Z → X` in the sense of Stacks 083Q, and the
identification is `AlgebraicGeometry.Space.zeroScheme_modulePullback_eq_preimage`, whose input is
the surjectivity half of Stacks 03MB for the quasi-coherent ideal of Stacks 0845, available for
an invertible `ℒ` as
`AlgebraicGeometry.Space.exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible`. -/
theorem interOnClosedSubspace_eq_zeroScheme (hL : IsInvertibleSheaf D p hp L) :
    interOnClosedSubspace D p hp L s Z =
      zeroScheme D.site D.base D.base_mem
        (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z)
        (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) :=
  (zeroScheme_modulePullback_eq_preimage D.site D.base D.base_mem
    (closedSubspaceInclusion D.site D.base D.base_mem ⟨X, hp.1⟩ Z) L s hL).symm

/-- **The first sentence of the proof of Stacks 0ER7.**  The hypothesis of Stacks 0ER7 that the
intersection `E ∩ Z` is an effective Cartier divisor on the closed subspace `Z ⊆ X` is
equivalent to saying that the restriction `s|_Z` is a regular section of `ℒ|_Z`.

The intersection is the vanishing locus of `s|_Z` by
`AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme`, and for the vanishing locus of a
section of an invertible sheaf the equivalence with regularity is part (4) of Stacks 0846,
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection`; `ℒ|_Z` is
invertible by Stacks 0B8P. -/
theorem isEffectiveCartierDivisor_interOnClosedSubspace_iff_isRegularSection
    (hL : IsInvertibleSheaf D p hp L) :
    IsEffectiveCartierDivisor D.site D.base D.base_mem
        (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z)
        (interOnClosedSubspace D p hp L s Z) ↔
      AlgebraicGeometry.IsRegularSection
        (structurePresheaf D.site D.base D.base_mem Z.1.toFunctor)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite D.site D.base D.base_mem Z.1.toFunctor Z.2.1).O).property
        (closedSubspaceRestrictSection D p hp L s Z) := by
  rw [interOnClosedSubspace_eq_zeroScheme D p hp L s Z hL]
  exact isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection D.site D.base D.base_mem
    (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z)
    (closedSubspaceRestrictSheaf D p hp L Z) (closedSubspaceRestrictSection D p hp L s Z)
    (isInvertible_closedSubspaceRestrictSheaf D p hp L Z hL)

end Restriction

end AlgebraicGeometry.Space

end
