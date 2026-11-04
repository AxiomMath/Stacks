module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NagataFormalism
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedCohenMacaulay

/-!
# The normalized dualizing complex along a flat proper morphism, for Nagata compactifications

In Situation [Stacks, Tag 0AU4], for the upper shriek functors of Nagata compactifications
(`Stacks.Duality.UpperShriek.nagata`), let `f : X ⟶ Y` be a flat proper morphism of schemes of
finite type over `S`, `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•`, `a`
the right adjoint of `Rf_*` and `ω_{X/Y}^• = a(𝒪_Y)` the relative dualizing complex. Then
`ω_X^• ≅ a(ω_Y^•) ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}^•` ([Stacks, Tag 0B6W]).

## Main results

* `Stacks.Duality.NormalizedOnOpens.nonempty_iso_pullback_tensor_of_flat_nagata`:
  [Stacks, Tag 0B6W].

## References

* [Stacks Project, Tag 0B6W](https://stacks.math.columbia.edu/tag/0B6W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

include hpe in
/-- **[Stacks, Tag 0B6W]** Let `f : X ⟶ Y` be a flat proper morphism of schemes of finite type over
`S`, where `S` is Noetherian with a dualizing complex `ω_S^•`, and `ω_X^•`, `ω_Y^•` the dualizing
complexes normalized relative to `ω_S^•`. With `a` the right adjoint of `Rf_*` and
`ω_{X/Y}^• = a(𝒪_Y)` the relative dualizing complex,
`ω_X^• ≅ a(ω_Y^•) ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}^•` in `D(𝒪_X)`. -/
@[stacks 0B6W]
theorem nonempty_iso_pullback_tensor_of_flat_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f] [Flat f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    Nonempty (𝒦X.complex.obj ≅ ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj 𝒦Y.complex.obj)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y))) :=
  nonempty_iso_pullback_tensor_of_flat nagataCompactification hpe hωS 𝒦X 𝒦Y

end NormalizedOnOpens

end Stacks.Duality
