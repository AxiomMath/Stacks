module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic

/-!
# Restriction to a closed subscheme is surjective on sections over an affine open

Let `i : Z ⟶ X` be a closed immersion and `F` a quasi-coherent `𝒪_X`-module. The unit
`F ⟶ i_*i^*F` of `i^* ⊣ i_*` is only *locally* surjective, so a section of `i^*F` over an
arbitrary open of `Z` need not be the restriction of a section of `F`. Over the preimage of an
**affine** open `U` of `X` it is: on sections the unit is

`Γ(F, U) ⟶ Γ(i^*F, i⁻¹U)`,

and this map is surjective.

Both halves are already in the repository and the file only joins them.

* `Stacks.ClosedImmersion.epi_unit_app` is [Stacks, Tag 08KS]: along a closed immersion the unit
  is an epimorphism at every `𝒪_X`-module, with no hypothesis on the module.
* `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` is the `H¹`-vanishing half of
  [Stacks, Tag 01XB]: an epimorphism of quasi-coherent modules is surjective on sections over an
  affine open.

The target `i_*i^*F` is quasi-coherent because `i^*` preserves quasi-coherence
(`Stacks.Modules.instIsQuasicoherentPullbackObj`) and a closed immersion is an affine morphism,
so `i_*` does too.

## Main results

* `Stacks.ClosedImmersion.surjective_unit_app_of_isAffineOpen` — **the unit of `i^* ⊣ i_*` is
  surjective on sections over an affine open of the target.**

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.ClosedImmersion

/-- **The unit of `i^* ⊣ i_*` along a closed immersion is surjective on sections over an affine
open of the target.** For `U` affine the map `Γ(F, U) ⟶ Γ(i^*F, i⁻¹U)` is onto: the unit is an
epimorphism by `Stacks.ClosedImmersion.epi_unit_app`, both of its terms are quasi-coherent, and
`Γ(U, -)` is exact on quasi-coherent modules over an affine open.

Over a general open the statement is false — the failure that makes the local generation of
`Stacks.PullbackUnitGenerators.exists_mem_span` necessary elsewhere. -/
theorem surjective_unit_app_of_isAffineOpen {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : IsAffineOpen U) :
    Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).val.app (op U)) := by
  have := epi_unit_app i F
  have : ((𝟭 X.Modules).obj F).IsQuasicoherent := inferInstanceAs F.IsQuasicoherent
  have : ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).obj F).IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj F)).IsQuasicoherent
  exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F) U hU

end Stacks.ClosedImmersion

end
