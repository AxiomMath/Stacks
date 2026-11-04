module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupport

/-!
# A right adjoint to direct image along a closed immersion, on quasi-coherent modules

Let `i : Z ⟶ X` be a closed immersion of schemes. Direct image of quasi-coherent modules
`i_* : QCoh(𝒪_Z) ⟶ QCoh(𝒪_X)` has a right adjoint `i^!`.

On *all* modules the right adjoint is sheaf Hom from `𝒪_Z` with exact support, the functor
sending an `𝒪_X`-module `𝒢` to the `𝒪_Z`-module of sections of `𝒢` annihilated by the ideal
cutting out `Z`. That functor does not preserve quasi-coherence, so on quasi-coherent modules
it is followed by the coherator, the right adjoint of the inclusion of quasi-coherent modules.

## Main definitions

* `Stacks.ClosedImmersion.moduleUpperShriek`: the right adjoint on all modules.
* `Stacks.ClosedImmersion.quasicoherentUpperShriek`: the functor `i^!` on quasi-coherent
  modules, namely the composite of the inclusion, the right adjoint on all modules, and the
  coherator.

## Main results

* `Stacks.ClosedImmersion.pushforwardModuleUpperShriekAdjunction`: the adjunction on all
  modules.
* `Stacks.ClosedImmersion.pushforwardQcohUpperShriekAdjunction`: `i_* ⊣ i^!` on quasi-coherent
  modules.
* `Stacks.ClosedImmersion.pushforwardQcoh_isLeftAdjoint`: the same statement read as the mere
  existence of a right adjoint.

## Implementation notes

The adjunction is assembled from two adjunctions and then restricted. Composing

  `ι : QCoh(𝒪_Z) ⟶ Mod(𝒪_Z)`  with its right adjoint the coherator,

and

  `i_* : Mod(𝒪_Z) ⟶ Mod(𝒪_X)`  with its right adjoint sheaf Hom with exact support,

gives `ι ⋙ i_* ⊣ i^! ⋙ coherator`. Since `i_*` on quasi-coherent modules is by definition the
lift of `i_*` along quasi-coherence, `i_*^{qc} ⋙ ι = ι ⋙ i_*` holds by definition, so the
composite adjunction is already an adjunction out of `QCoh(𝒪_Z)`; restricting it along the
fully faithful inclusion of `QCoh(𝒪_X)` into `Mod(𝒪_X)` — and along the identity on
`QCoh(𝒪_Z)` — moves the target into `QCoh(𝒪_X)` and replaces the right adjoint by its
composite with the inclusion. This is why `quasicoherentUpperShriek` has the inclusion on the
left: the two commutation isomorphisms required by the restriction are then identities.

What is *not* claimed is that the right adjoint on all modules preserves quasi-coherence; it
does not in general, and the coherator is exactly what repairs this.

## References

* [Stacks Project, Tag 01R0](https://stacks.math.columbia.edu/tag/01R0)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ClosedImmersion

attribute [local instance] AlgebraicGeometry.quasicoherentInclusion_isLeftAdjoint

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

/-- The right adjoint of direct image along a closed immersion of schemes, on all modules: the
sheaf Hom from `𝒪_Z` with exact support, whose sections over an open of `Z` are the sections of
the given module annihilated by the ideal cutting out `Z`. -/
def moduleUpperShriek : X.Modules ⥤ Z.Modules :=
  (closedQuotientOfClosedImmersion i).sheafHomExactSupport

/-- Direct image along a closed immersion of schemes is left adjoint to sheaf Hom from `𝒪_Z`
with exact support, on all modules. -/
def pushforwardModuleUpperShriekAdjunction :
    Scheme.Modules.pushforward i ⊣ moduleUpperShriek i :=
  (closedQuotientOfClosedImmersion i).modulePushforwardSheafHomExactSupportAdjunction

/-- **`i^!` for a closed immersion, on quasi-coherent modules.** It is the composite of the
inclusion of quasi-coherent `𝒪_X`-modules, the right adjoint of direct image on all modules,
and the coherator on `Z`. -/
@[stacks 01R0 "the functor"]
def quasicoherentUpperShriek :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ moduleUpperShriek i ⋙
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι.rightAdjoint

/-- **[Stacks, Tag 01R0].** Direct image of quasi-coherent modules along a closed immersion of
schemes is left adjoint to `i^!`. -/
@[stacks 01R0 "the adjunction"]
def pushforwardQcohUpperShriekAdjunction :
    Stacks.Modules.pushforwardQcoh i ⊣ quasicoherentUpperShriek i :=
  Adjunction.restrictFullyFaithful
    ((Adjunction.ofIsLeftAdjoint (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι).comp
      (pushforwardModuleUpperShriekAdjunction i))
    (Functor.FullyFaithful.id _)
    (Functor.FullyFaithful.ofFullyFaithful (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)
    (Iso.refl _) (Iso.refl _)

/-- **[Stacks, Tag 01R0], as an existence statement.** Direct image of quasi-coherent modules
along a closed immersion of schemes has a right adjoint. -/
@[stacks 01R0 "existence of the right adjoint"]
theorem pushforwardQcoh_isLeftAdjoint :
    (Stacks.Modules.pushforwardQcoh i).IsLeftAdjoint :=
  (pushforwardQcohUpperShriekAdjunction i).isLeftAdjoint

end Stacks.ClosedImmersion

end
