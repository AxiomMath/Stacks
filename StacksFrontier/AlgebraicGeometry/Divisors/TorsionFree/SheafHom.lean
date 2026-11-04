module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TorsionFree
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.Quasicoherent
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf-hom into a torsion free module is torsion free

Let `X` be an integral scheme, let `F` be an `𝒪_X`-module of finite presentation and let `G` be
a quasi-coherent torsion free `𝒪_X`-module. Then `SheafHom(F, G)` is torsion free.

Both inputs are already available. Torsion freeness of a quasi-coherent module on an integral
scheme is detected on stalks, `AlgebraicGeometry.isTorsionFree_iff_forall_stalk`; the stalk of
`SheafHom(F, G)` is the module of linear maps between the stalks because `F` is of finite
presentation, `Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearEquivOfFinitePresentation`;
and a module of linear maps into a torsion free module is torsion free, which is Mathlib's
instance on `LinearMap`. The quasi-coherence that the stalk criterion needs is
`AlgebraicGeometry.sheafHom_isQuasicoherent`.

## Main results

* `AlgebraicGeometry.isTorsionFree_sheafHom`: **the torsion freeness clause of
  [Stacks, Tag 0AXZ]**.

## Implementation notes

The source proves the statement by reducing to More on Algebra, [Stacks, Tag 0AUX], which is the
assertion that `Hom_R(M, N)` is torsion free over a domain `R` when `N` is. That ring-level
input is Mathlib's `Module.IsTorsionFree` instance on a space of linear maps, which needs no
hypothesis on the ring at all; the integrality of `X` is used only through the stalk criterion
for torsion freeness.

Quasi-coherence of `F` is not assumed separately: finite presentation implies it.

## References

* [Stacks Project, Tag 0AXZ](https://stacks.math.columbia.edu/tag/0AXZ)
* [Stacks Project, Tag 0AUX](https://stacks.math.columbia.edu/tag/0AUX)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.InternalHom
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry

/-- **The torsion freeness clause of [Stacks, Tag 0AXZ].** On an integral scheme, the sheaf-hom
`SheafHom(F, G)` from a module of finite presentation into a quasi-coherent torsion free module
is torsion free.

The proof is the one of the source: torsion freeness of a quasi-coherent module on an integral
scheme is a condition on the stalks, the stalk of `SheafHom(F, G)` at `x` is
`Hom_{𝒪_{X,x}}(F_x, G_x)` by [Stacks, Tag 01CP], and a module of linear maps into a torsion free
module is torsion free. -/
@[stacks 0AXZ "torsion freeness"]
theorem isTorsionFree_sheafHom {X : Scheme.{u}} [IsIntegral X] (F G : X.Modules)
    [F.IsFinitePresentation] [G.IsQuasicoherent] (hG : IsTorsionFree G) :
    IsTorsionFree (sheafInternalHom (spaceRingedSite X.sheaf) F G) := by
  let H : X.Modules := sheafInternalHom (spaceRingedSite X.sheaf) F G
  have : H.IsQuasicoherent := sheafHom_isQuasicoherent F G
  rw [isTorsionFree_iff_forall_stalk H]
  intro x
  have hGx : Module.IsTorsionFree ↑(X.presheaf.stalk x) ↑(G.presheaf.stalk x) :=
    (isTorsionFree_iff_forall_stalk G).mp hG x
  let e : (↑(F.presheaf.stalk x) →ₗ[↑(X.presheaf.stalk x)] ↑(G.presheaf.stalk x))
      ≃ₗ[↑(X.presheaf.stalk x)] ↑(H.presheaf.stalk x) :=
    (sheafHomStalkLinearEquivOfFinitePresentation
      (internalSheafHom X.toTopCat X.sheaf F G) x).equiv.symm
  exact e.symm.injective.moduleIsTorsionFree _ fun r m => e.symm.map_smul r m

end AlgebraicGeometry

end
