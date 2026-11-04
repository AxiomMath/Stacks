module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent modules on a locally Noetherian scheme form an abelian category

Let `X` be a locally Noetherian scheme. The coherent `𝒪_X`-modules form an abelian subcategory
of `Mod(𝒪_X)`: the kernel and the cokernel of a map of coherent modules are coherent, and the
middle term of a short exact sequence whose outer terms are coherent is coherent.

## Main results

* `AlgebraicGeometry.isCoherent_kernel` and `AlgebraicGeometry.isCoherent_cokernel`: the kernel
  and the cokernel of a map of coherent modules are coherent.
* `AlgebraicGeometry.isCoherent_X₂_of_shortExact`: an extension of coherent modules is coherent.
* `AlgebraicGeometry.isWeakSerreClass_coherentModules` and
  `AlgebraicGeometry.nonempty_abelian_coherentModules`: coherent modules are a weak Serre
  subcategory of `X.Modules`, hence an abelian category.

## Implementation notes

This is the specialization to a locally Noetherian scheme of [Stacks, Tag 01BY], which holds
over an arbitrary ringed space; the Noetherian hypothesis is therefore not used in the proofs,
and is carried only because it is the hypothesis of the source lemma. The three closure
properties over a ringed space are `SheafOfModules.kernel_isCoherent`,
`SheafOfModules.cokernel_isCoherent` and the extension clause of
`SheafOfModules.coherentModules_isWeakSerreClass`, all of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/ImprovingCoherentModules/KernelCokernel.lean`.

What this file does is cross the one gap between those statements and their use on a scheme:
`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` carrying its
own `Category` and `Abelian` instances, so a class instance established for the latter is not
found by instance search for the former. The weak Serre property is therefore transported once,
in `isWeakSerreClass_coherentModules`, with the category of `X.Modules` pinned by `@`-notation,
and the extension and abelian statements are read off from it there. Kernels and cokernels need
no such transport, the ringed-space statements applying to a morphism of `X.Modules` directly.

An extension is represented by a short exact complex `S` of `X.Modules`, so the statement
quantifies over all extensions of `S.X₃` by `S.X₁` rather than over a choice of one.

## References

* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The coherent modules on a scheme are a weak Serre subcategory of `X.Modules`.** This is
`SheafOfModules.coherentModules_isWeakSerreClass` with the category of `X.Modules` pinned: the
two categories are definitionally equal but carry different instance paths, so the transport is
spelled out. -/
theorem isWeakSerreClass_coherentModules (X : Scheme.{u}) :
    @ObjectProperty.IsWeakSerreClass X.Modules _ _ (fun F => F.IsCoherent) :=
  SheafOfModules.coherentModules_isWeakSerreClass (R := X.ringCatSheaf)

/-- **[Stacks, Tag 01Y0].** The kernel of a map of coherent modules on a locally Noetherian
scheme is coherent. -/
@[stacks 01Y0 "kernel"]
theorem isCoherent_kernel {X : Scheme.{u}} [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsCoherent] [G.IsCoherent] (φ : F ⟶ G) : (kernel φ).IsCoherent :=
  SheafOfModules.kernel_isCoherent φ

/-- **[Stacks, Tag 01Y0].** The cokernel of a map of coherent modules on a locally Noetherian
scheme is coherent. -/
@[stacks 01Y0 "cokernel"]
theorem isCoherent_cokernel {X : Scheme.{u}} [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsCoherent] [G.IsCoherent] (φ : F ⟶ G) : (cokernel φ).IsCoherent :=
  SheafOfModules.cokernel_isCoherent φ

/-- **[Stacks, Tag 01Y0].** An extension of coherent modules on a locally Noetherian scheme is
coherent: the middle term of a short exact sequence of `𝒪_X`-modules whose outer terms are
coherent is coherent. -/
@[stacks 01Y0 "extensions"]
theorem isCoherent_X₂_of_shortExact {X : Scheme.{u}} [IsLocallyNoetherian X]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₃ : S.X₃.IsCoherent) : S.X₂.IsCoherent :=
  let := isWeakSerreClass_coherentModules X
  ObjectProperty.prop_X₂_of_shortExact (P := fun F : X.Modules => F.IsCoherent) hS h₁ h₃

/-- **[Stacks, Tag 01Y0].** The category of coherent `𝒪_X`-modules on a locally Noetherian
scheme is abelian. The abelian structure is the one a weak Serre subcategory of an abelian
category carries, by [Stacks, Tag 0754]. -/
@[stacks 01Y0 "abelian category"]
theorem nonempty_abelian_coherentModules (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Nonempty (Abelian (ObjectProperty.FullSubcategory (fun F : X.Modules => F.IsCoherent))) :=
  let := isWeakSerreClass_coherentModules X
  ObjectProperty.abelian_of_isWeakSerreClass _

end AlgebraicGeometry

end
