module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# Quasi-coherence across the slice site of an open

Let `X` be a scheme and `U` an open of `X`. A sheaf of modules for the localized sheaf of rings
`𝒪_X.over U` on the slice site `Opens(X)/U` is the same thing as an `𝒪_U`-module on the open
subscheme `U`, the identification being
`AlgebraicGeometry.Scheme.Modules.overEquiv`. This file transports quasi-coherence across that
identification, so that a module on `X` exhibited locally as a kernel or a coproduct *on the
slice site* can be recognized as quasi-coherent.

## Main results

* `Stacks.Modules.isQuasicoherent_restrict_of_slice`: if `M.over U` is isomorphic to a sheaf of
  modules on the slice site whose image under `overEquiv` is quasi-coherent, then the
  restriction `M|_U` is quasi-coherent.
* `Stacks.Modules.isQuasicoherent_overEquiv_kernel`: the image under `overEquiv` of a kernel on
  the slice site is quasi-coherent as soon as the images of its source and target are.
* `Stacks.Modules.isQuasicoherent_overEquiv_sigma`: the image under `overEquiv` of a finite
  coproduct of copies of `M.over U` is quasi-coherent, for `M` quasi-coherent.

## Implementation notes

Quasi-coherence of a kernel is available on `Scheme.Modules` only
(`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`), because its proof localizes the
sections at the sections of the structure sheaf of an affine open; there is no such statement
for `SheafOfModules (X.ringCatSheaf.over U)`, where no scheme is in sight. The route taken here
is therefore to push the slice-site kernel *forward* along `overEquiv` into
`(U : Scheme).Modules`, where that instance applies: the functor of an equivalence preserves
kernels and coproducts, so the image of a kernel is a kernel and the image of a coproduct is a
coproduct.

This is the direction opposite to the one `Stacks.Modules.presentationOver` goes, and it needs
none of the care that one does: `SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint`,
whose `IsIso` side condition is not synthesizable at reducible transparency, is never used, and
the instances required — `IsEquivalence` of the functor of an equivalence, and the limit and
colimit preservation that follows — are read off the equivalence itself rather than off a term
whose type mentions `Scheme.Modules`.

## References

* [Stacks Project, Tag 01LB](https://stacks.math.columbia.edu/tag/01LB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace Stacks.Modules

variable {X : Scheme.{u}}

/-- The image of `M.over U` under `AlgebraicGeometry.Scheme.Modules.overEquiv` is the
restriction `M|_U` of `M` to the open subscheme `U`.

This is `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` evaluated at `M`. -/
public def overEquivObjOverIso (U : X.Opens) (M : X.Modules) :
    (Scheme.Modules.overEquiv U).functor.obj (M.over U) ≅ M.restrict U.ι :=
  (Scheme.Modules.overFunctorEquiv U).app M

/-- If `M.over U` is isomorphic to a sheaf of modules `K` on the slice site over `U` whose
image under `AlgebraicGeometry.Scheme.Modules.overEquiv` is quasi-coherent, then the
restriction `M|_U` is quasi-coherent. -/
public theorem isQuasicoherent_restrict_of_slice (U : X.Opens) (M : X.Modules)
    {K : SheafOfModules.{u} (X.ringCatSheaf.over U)} (e : M.over U ≅ K)
    (h : ((Scheme.Modules.overEquiv U).functor.obj K).IsQuasicoherent) :
    (M.restrict U.ι).IsQuasicoherent :=
  Stacks.Descent.isQuasicoherent_of_iso
    (((Scheme.Modules.overEquiv U).functor.mapIso e).symm ≪≫ overEquivObjOverIso U M) h

/-- The image under `AlgebraicGeometry.Scheme.Modules.overEquiv` of the kernel of a morphism of
sheaves of modules on the slice site over `U` is quasi-coherent, provided the images of its
source and target are.

The functor of an equivalence preserves kernels, so the image of the kernel is the kernel of
the image, and a kernel of a morphism of quasi-coherent modules on a scheme is
quasi-coherent. -/
public theorem isQuasicoherent_overEquiv_kernel (U : X.Opens)
    {A B : SheafOfModules.{u} (X.ringCatSheaf.over U)} (f : A ⟶ B)
    (hA : ((Scheme.Modules.overEquiv U).functor.obj A).IsQuasicoherent)
    (hB : ((Scheme.Modules.overEquiv U).functor.obj B).IsQuasicoherent) :
    ((Scheme.Modules.overEquiv U).functor.obj (kernel f)).IsQuasicoherent := by
  have := hA
  have := hB
  exact Stacks.Descent.isQuasicoherent_of_iso
    (PreservesKernel.iso (Scheme.Modules.overEquiv U).functor f).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel
      ((Scheme.Modules.overEquiv U).functor.map f))

/-- A coproduct indexed by `Fin m` of quasi-coherent modules on a scheme is quasi-coherent.

This is `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma` at an index type
in `Type 0`, which that instance, stated for an index type in `Type u`, does not cover. -/
public theorem isQuasicoherent_sigma_fin {Y : Scheme.{u}} {m : ℕ} (N : Fin m → Y.Modules)
    (h : ∀ i, (N i).IsQuasicoherent) : (∐ N).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor N) fun i => h i.as

/-- The image under `AlgebraicGeometry.Scheme.Modules.overEquiv` of a finite coproduct of
copies of `M.over U` is quasi-coherent, for `M` a quasi-coherent `𝒪_X`-module.

The functor of an equivalence preserves coproducts, and each factor becomes the restriction
`M|_U`, which is quasi-coherent. -/
public theorem isQuasicoherent_overEquiv_sigma (U : X.Opens) (M : X.Modules)
    [M.IsQuasicoherent] (m : ℕ) :
    ((Scheme.Modules.overEquiv U).functor.obj (∐ fun _ : Fin m => M.over U)).IsQuasicoherent :=
  Stacks.Descent.isQuasicoherent_of_iso
    (PreservesCoproduct.iso (Scheme.Modules.overEquiv U).functor
      (fun _ : Fin m => M.over U)).symm <| isQuasicoherent_sigma_fin _ fun _ =>
    Stacks.Descent.isQuasicoherent_of_iso (overEquivObjOverIso U M).symm inferInstance

end Stacks.Modules

end

end
