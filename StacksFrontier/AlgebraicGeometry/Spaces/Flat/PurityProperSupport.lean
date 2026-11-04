module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityProper

/-!
# Purity when the support is proper, unconditionally

Part (1) of Stacks 0CVI says that in the situation of Stacks 0CV6, if the support of `ℱ` is
proper over `Y`, then `ℱ` is universally pure relative to `Y`. The source reduces it to part (2)
at the scheme-theoretic support `i : Z ⟶ X` of `ℱ` (Stacks 07U1), writing `ℱ = i_*𝒢` for a
finite type quasi-coherent `𝒪_Z`-module `𝒢` (Stacks 07U0), and transferring universal purity
of `𝒢` to `ℱ` by Stacks 0CVH.

`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityProper.lean` carries out that reduction, with
the input of Stacks 0CVH supplied by
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityClosedImmersionBaseChange.lean`, and names the
closed-subspace data of the support as arguments. Here that data is supplied by Stacks 07U0
itself: the support of a quasi-coherent module of finite type is a closed subspace cut out by the
annihilator ideal, `AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`.

## Main definitions

* `AlgebraicGeometry.Space.PrePureSituation.supportSubspace`: the scheme-theoretic support of
  the module of a situation, as a closed subspace of its source.

## Main results

* `AlgebraicGeometry.Space.ClosedSubspaceModule.isUniversallyPureAbove_of_isProper_comp`:
  **Stacks 0CVI, part (1)** for an arbitrary closed-immersion presentation `ℱ = i_*𝒢` with
  `Z ⟶ Y` proper.
* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isProper_supportSubspace`:
  **Stacks 0CVI, part (1)**, with the hypothesis on the scheme-theoretic support.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityProper`, the point `y` is a field of the
situation and the statements hold for an arbitrary situation, so they are the statements
relative to `Y`. The finite type of the module of a situation is the categorical
`SheafOfModules.IsFiniteTypeOnSite` of Stacks 03DL(5); it is passed to the sectionwise form
that `AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport` consumes by
`Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite`.

## References

* [Stacks Project, Tag 0CVI](https://stacks.math.columbia.edu/tag/0CVI)
* [Stacks Project, Tag 0CVH](https://stacks.math.columbia.edu/tag/0CVH)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0CVI, part (1), for a closed-immersion presentation of the module.** In the
situation of Stacks 0CV6, let `i : Z ⟶ X` be a closed immersion and suppose `ℱ = i_*𝒢` for a
finite type quasi-coherent `𝒪_Z`-module `𝒢`. If the composite `Z ⟶ Y` is proper, then `ℱ` is
universally pure above `y`.

This is part (2) applied to the situation on `Z`, transferred to `ℱ` by Stacks 0CVH; it is
`AlgebraicGeometry.Space.ClosedSubspaceModule.isUniversallyPureAbove_of_isProper`. -/
@[stacks 0CVI "part (1), for any presentation of the module as the direct image along a \
closed immersion whose composite to the target is proper"]
alias ClosedSubspaceModule.isUniversallyPureAbove_of_isProper_comp :=
  ClosedSubspaceModule.isUniversallyPureAbove_of_isProper

/-- The scheme-theoretic support of the module of a situation is a closed subspace of the
source, cut out by the annihilator ideal of the module: Stacks 07U0, for a quasi-coherent module
of finite type. -/
theorem PrePureSituation.exists_isClosedSubspace_schemeTheoreticSupport
    (P : PrePureSituation.{u, u} B S hS) :
    ∃ hZ : IsClosedSubspace B S hS (schemeTheoreticSupport B S hS P.sourceSpace P.F),
      definingIdealSheaf B S hS P.sourceSpace
          ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩ =
        annihilatorIdealSheaf B S hS P.sourceSpace P.F :=
  _root_.AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport B S hS
    P.sourceSpace P.F P.moduleQuasicoherent
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite P.F P.moduleFiniteType)

/-- **The scheme-theoretic support of the module of a situation**, Stacks 07U1, as a closed
subspace of the source of the situation. -/
def PrePureSituation.supportSubspace (P : PrePureSituation.{u, u} B S hS) :
    ClosedSubspaces B S hS P.X :=
  ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F,
    P.exists_isClosedSubspace_schemeTheoreticSupport.fst⟩

/-- **Stacks 0CVI, part (1).** In the situation of Stacks 0CV6, if the support of `ℱ` is proper
over `Y`, then `ℱ` is universally pure above `y`; the point `y` being arbitrary, `ℱ` is
universally pure relative to `Y`.

The support is the scheme-theoretic support `Z` of Stacks 07U1, and properness over `Y` is
properness of the composite `Z ⟶ X ⟶ Y`. The proof is the source's: by Stacks 07U0 the module
is `i_*𝒢` for a finite type quasi-coherent `𝒪_Z`-module `𝒢`, and the closed-immersion form
above applies. -/
@[stacks 0CVI "part (1): a finite type quasi-coherent module whose scheme-theoretic support is \
proper over the target is universally pure above every point of the target"]
theorem isUniversallyPureAbove_of_isProper_supportSubspace
    (P : PrePureSituation.{u, u} B S hS)
    (hZY : IsProper B S hS
      ((closedSubspaceInclusion B S hS P.sourceSpace P.supportSubspace).hom ≫ P.f)) :
    IsUniversallyPureAbove P := by
  obtain ⟨hZ, G, hG, ⟨e⟩⟩ := exists_module_on_schemeTheoreticSupport B S hS P.sourceSpace P.F
    P.moduleQuasicoherent
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite P.F P.moduleFiniteType)
  exact (ClosedSubspaceModule.ofSchemeTheoreticSupport hZ G hG
    e).isUniversallyPureAbove_of_isProper_comp hZY

end AlgebraicGeometry.Space

end
