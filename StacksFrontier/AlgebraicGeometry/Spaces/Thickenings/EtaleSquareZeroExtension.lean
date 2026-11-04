module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafSquareZeroExtension

/-!
# Square-zero extensions of the structure sheaf of an algebraic space, with implicit site data

For a morphism `f : X ⟶ Y` of algebraic spaces, a square-zero extension of `𝒪_X` along `f` is a
short exact sequence `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` of sheaves on the small étale site of `X`, with `𝒜`
an `f⁻¹𝒪_Y`-algebra and `ℐ` a quasi-coherent ideal of square zero. This module gives the type
`AlgebraicGeometry.Space.SquareZeroExtension B S hS f` of such data with the site, the base scheme
and its containment implicit, `AlgebraicGeometry.Space.EtaleSquareZeroExtension f`.

## Main definitions

* `AlgebraicGeometry.Space.EtaleSquareZeroExtension` — the data above, site data implicit.

## Main results

* `AlgebraicGeometry.Space.EtaleSquareZeroExtension.epi_π` — the surjection is an epimorphism of
  sheaves of commutative rings.
* `AlgebraicGeometry.Space.EtaleSquareZeroExtension.ι_injective` — the kernel inclusion is
  injective on sections over every étale chart.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A square-zero extension of the structure sheaf of `X` along `f`, that is
`AlgebraicGeometry.Space.SquareZeroExtension B S hS f` with the big fppf site `B`, the base scheme
`S` and `hS` implicit. -/
abbrev EtaleSquareZeroExtension {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :=
  SquareZeroExtension B S hS f

namespace EtaleSquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : EtaleSquareZeroExtension f)

/-- The surjection `𝒜 ⟶ 𝒪_X` of a square-zero extension is an epimorphism of sheaves of
commutative rings. -/
theorem epi_π : Epi E.π :=
  haveI := E.locallySurjective_π
  Sheaf.epi_of_isLocallySurjective E.π

/-- The inclusion `ℐ ⟶ 𝒜` of the kernel of a square-zero extension is injective on sections over
every object of the small étale site. -/
theorem ι_injective (E : EtaleSquareZeroExtension f) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective (E.ι U) := by
  intro x y hxy
  obtain ⟨_, -, huniq⟩ := E.exact_kernel U (E.ι U x) (E.mem_kernel U x)
  exact (huniq x rfl).trans (huniq y hxy.symm).symm

end EtaleSquareZeroExtension

end AlgebraicGeometry.Space

end
