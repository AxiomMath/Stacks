module

public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.Assembly
public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.Rigidity
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham cohomology sheaves of a proper smooth morphism over `ℚ` are finite locally free

For `f : X ⟶ Y` proper and smooth, with `Y` over a `ℚ`-scheme, every de Rham cohomology sheaf
`ℋ^q_dR(X/Y)` is a finite locally free `𝒪_Y`-module: the sentence of [Stacks, Tag 0FMN] that the
source defers to a future reference (Deligne's theorem). It is
`Stacks.DeRhamRigidity.isLocallyFree_deRhamCohomologySheaf_of_rigidity` with its rigidity
hypothesis discharged by `Stacks.DeRhamRigidity.nonempty_derivedDeRhamDirectImage_iso_trivialMap`.

## Main results

* `Stacks.DeRhamRigidity.isLocallyFree_deRhamCohomologySheaf_of_proper_smooth_rat`.

## Implementation notes

The theorem carries `@[stacks 0FMN]` for that sentence.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.DeRhamSmooth

universe u

namespace Stacks.DeRhamRigidity

/-- **The de Rham cohomology sheaves of a proper smooth morphism over `ℚ` are finite locally
free** ([Stacks, Tag 0FMN], the sentence the source defers to a future reference). Let
`f : X ⟶ Y` be proper and smooth, with `Y` over a scheme `S` over `Spec R` for a `ℚ`-algebra `R`.
Then every `ℋ^q_dR(X/Y)` is a finite locally free `𝒪_Y`-module. The proof reduces to an Artinian
local base (`Stacks.DeRhamSmooth.isLocallyFree_deRhamCohomologySheaf_of_artinian`), where the
de Rham complex is rigid (`nonempty_derivedDeRhamDirectImage_iso_trivialMap`) and the trivial
deformation has free cohomology (`free_moduleSpecΓ_deRhamCohomologySheaf_trivialMap`). -/
@[stacks 0FMN "if f is proper in addition to being smooth and S is a scheme over Q, then \
H^q_dR(X/Y) is finite locally free (the sentence the source defers to a future reference)"]
theorem isLocallyFree_deRhamCohomologySheaf_of_proper_smooth_rat {X Y S : Scheme.{u}}
    {R : CommRingCat.{u}} [Algebra ℚ R] (f : X ⟶ Y) (g : Y ⟶ S) (σ : S ⟶ Spec R) [IsProper f]
    [Smooth f] (q : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (deRhamCohomologySheaf f q) :=
  isLocallyFree_deRhamCohomologySheaf_of_rigidity
    (fun A _ _ _ σ hσ X f _ _ => nonempty_derivedDeRhamDirectImage_iso_trivialMap A σ hσ X f)
    f g σ q

end Stacks.DeRhamRigidity
