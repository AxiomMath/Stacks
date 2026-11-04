module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.IdealSmul

/-!
# Quasi-coherent submodules of a coherent module on a Noetherian scheme

On a Noetherian scheme every quasi-coherent subsheaf of a coherent sheaf is coherent: over an
affine open the sections of the subsheaf are a submodule of a finite module over a Noetherian
ring, hence finite, and a quasi-coherent sheaf whose sections over every affine open form a
finite module is of finite type.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerSmul.isFiniteType_of_finite_sections`: a quasi-coherent
  module whose sections over every affine open form a finite module is of finite type.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_of_isQuasicoherent_submodule`: a
  quasi-coherent submodule of a coherent module on a Noetherian scheme is coherent.
* `Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_idealPowSmul`: `I ^ n • F` is coherent.

## Implementation notes

`isFiniteType_of_finite_sections` is the converse of [Stacks, Tag 01PB]
(`Stacks.AlgebraicGeometry.CoherentFinite.finite_sections`) and is assembled from the (5) ⇒ (2)
half of [Stacks, Tag 01XZ]: finiteness of the sections over `U` is condition (4) at `U` by
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_finite_specModule`, and the covering
taken is the family of *all* affine opens, whose supremum is `iSup_affineOpens_eq_top`.

The passage from finite type to coherent is
`Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType`, which is
(2) ⇒ (1) of the same tag and is where the Noetherian hypothesis is used a second time.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentFinite
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerSmul

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **A quasi-coherent module with finite sections over every affine open is of finite type.**
This is the converse of [Stacks, Tag 01PB]; it is the (5) ⇒ (2) half of [Stacks, Tag 01XZ]
applied to the covering of `X` by all of its affine opens. -/
theorem isFiniteType_of_finite_sections (G : X.Modules) [G.IsQuasicoherent]
    (h : ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(G, U.1)) : G.IsFiniteType :=
  isFiniteType_of_cover_isFiniteTildeOn G (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U ↦
      have := h U
      isFiniteTildeOn_of_finite_specModule G U.1 U.2
        (Module.Finite.equiv (specSectionsEquiv G U.2).symm)

/-- **A quasi-coherent submodule of a coherent module on a locally Noetherian scheme is
coherent.** Coherence is tested on affine opens, where the ring of sections is Noetherian and the
sections of the ambient module are finite, so a submodule of them is finite too; quasi-compactness
of the scheme plays no part. -/
theorem isCoherent_of_isQuasicoherent_submodule [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent]
    (G : F.Submodule) (hG : G.toSheafOfModules.IsQuasicoherent) :
    G.toSheafOfModules.IsCoherent := by
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hFft : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have := hG
  have hfin : ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(G.toSheafOfModules, U.1) := by
    intro U
    have h1 : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    have h2 : Module.Finite Γ(X, U.1) Γ(F, U.1) := finite_sections F U.2
    have h3 : Module.Finite Γ(X, U.1)
        ↥(show Submodule Γ(X, U.1) Γ(F, U.1) from G.toSubmodule.obj (op U.1)) := inferInstance
    exact h3
  have := isFiniteType_of_finite_sections G.toSheafOfModules hfin
  exact Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType
    (F := G.toSheafOfModules)

/-- **`I ^ n • F` is coherent**, for `F` coherent on a locally Noetherian scheme. -/
theorem isCoherent_idealPowSmul [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent] :
    (idealPowSmul I n F).toSheafOfModules.IsCoherent :=
  isCoherent_of_isQuasicoherent_submodule F (idealPowSmul I n F)
    (isQuasicoherent_idealPowSmul I n F)

end Stacks.AlgebraicGeometry.IdealPowerSmul

end
