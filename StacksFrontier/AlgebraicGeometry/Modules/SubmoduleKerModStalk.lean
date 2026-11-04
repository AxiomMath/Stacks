module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKerStalk
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.ExactStalkCokernel

/-!
# The stalk of a kernel submodule, in the `modStalk` spelling

Let `P : A ⟶ B` be a morphism of sheaves of `𝒪_X`-modules on a scheme `X`. The kernel submodule
`SheafOfModules.Submodule.ker P`, whose sections over an open are by definition the sections
that `P` annihilates there, has a stalk at a point `x`; this file identifies that stalk with the
kernel of the stalk map of `P`.

`Stacks.SheafOfModules.TensorStalkRingedSpace.submoduleKerStalkLinearEquiv` already says this, in
the `grpStalk`/`stalkMapL` spelling of the stalk over the underlying ringed space. The statements
below say it in the `modStalk`/`stalkHom` spelling, whose scalars are
`Stacks.SheafOfModules.SheafHomStalk.ringStalk X.sheaf x`. That is the spelling in which
[Stacks, Tag 01CP] computes the stalk of an internal hom, so it is the one a consumer meeting a
kernel submodule inside a `SheafHom` must read the stalk in.

## Main results

* `Stacks.SheafOfModules.injective_stalkHom_submoduleKer_ι`: the stalk of the inclusion
  `ker P ⟶ A` is injective.
* `Stacks.SheafOfModules.range_stalkHom_submoduleKer_ι`: its range is the kernel of the stalk map
  of `P`, so a germ of a section of `A` is the germ of a section annihilated by `P` exactly when
  the stalk map of `P` annihilates it.
* `Stacks.SheafOfModules.submoduleKerModStalkLinearEquiv`: **the stalk of `ker P` is the kernel
  of the stalk map of `P`**, the two previous results packaged as an `𝒪_{X,x}`-linear
  equivalence.

## Implementation notes

Both halves transport results that already exist. Injectivity is
`Stacks.AlgebraicGeometry.ReflexiveModules.injective_stalkHom` at the monomorphism
`SheafOfModules.Submodule.ι`. The range computation is
`Stacks.SheafOfModules.range_stalkHom_eq_ker` applied to
`SheafOfModules.Submodule.exact_ker_shortComplex`, which is exactness of `ker P → A → B` at the
generality of an arbitrary site; nothing stalkwise is proved here.

**Why the sheaves are named at the `SheafOfModules` spelling.** The binders below are
`SheafOfModules.{u} (Stacks.SheafOfModules.SheafHomStalk.structureSheaf X.sheaf)` rather than
`AlgebraicGeometry.Scheme.Modules`. The two are the same type, but `AlgebraicGeometry.Scheme`
installs its own `Category` instance on the latter, whose `Hom` is the separate definition
`AlgebraicGeometry.Scheme.Modules.Hom`; with the sheaves named through it, instance search does
not produce `Mono (SheafOfModules.Submodule.ker P).ι`, the monomorphism instance of a submodule
inclusion off which injectivity on stalks is read. Named as below, that instance is found, and
`Stacks.SheafOfModules.mono_submoduleKer_ι` is where it is read; it is then passed to
`Stacks.AlgebraicGeometry.ReflexiveModules.injective_stalkHom`, whose own monomorphy argument is
phrased at the `AlgebraicGeometry.Scheme.Modules` spelling and accepts it because the two
categories are the same. Leaving that argument to instance search instead fails, since the goal
would then be generated at the spelling that does not resolve.

Nothing else moves: `Stacks.SheafOfModules.SheafHomStalk.modStalk` takes its argument at this
same spelling, and a consumer holding an object of `AlgebraicGeometry.Scheme.Modules` applies
these statements with no crossing, as
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogPolesFormsStalkKernel` does.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01AP](https://stacks.math.columbia.edu/tag/01AP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}
  {A B : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)} (P : A ⟶ B) (x : X)

/-- The inclusion `ker P ⟶ A` of the kernel submodule is a monomorphism. This is Mathlib's
instance for the inclusion of a submodule of a sheaf of modules, named here so that the goal it
answers is stated at the spelling of the sheaves given by the binders of this file; at the
`AlgebraicGeometry.Scheme.Modules` spelling instance search does not reach it. -/
theorem mono_submoduleKer_ι : Mono (_root_.SheafOfModules.Submodule.ker P).ι := inferInstance

/-- The stalk at `x` of the inclusion `ker P ⟶ A` of the kernel submodule is injective, the
inclusion of a submodule being a monomorphism. -/
theorem injective_stalkHom_submoduleKer_ι :
    Function.Injective (stalkHom (_root_.SheafOfModules.Submodule.ker P).ι x) :=
  injective_stalkHom _ (mono_submoduleKer_ι P) x

/-- **A germ of a section of `A` is the germ of a section annihilated by `P` exactly when the
stalk map of `P` annihilates it.** The range of the stalk of the inclusion `ker P ⟶ A` is the
kernel of the stalk map of `P`. -/
theorem range_stalkHom_submoduleKer_ι :
    LinearMap.range (stalkHom (_root_.SheafOfModules.Submodule.ker P).ι x)
      = LinearMap.ker (stalkHom P x) :=
  range_stalkHom_eq_ker (_root_.SheafOfModules.Submodule.exact_ker_shortComplex P) x

/-- **The stalk at `x` of the kernel submodule of `P` is the kernel of the stalk map of `P`**, as
`𝒪_{X,x}`-modules. The underlying map is the stalk of the inclusion `ker P ⟶ A`, by
`Stacks.SheafOfModules.coe_submoduleKerModStalkLinearEquiv_apply`. -/
def submoduleKerModStalkLinearEquiv :
    modStalk (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules x
      ≃ₗ[ringStalk X.sheaf x] LinearMap.ker (stalkHom P x) :=
  (LinearEquiv.ofInjective _ (injective_stalkHom_submoduleKer_ι P x)).trans
    (LinearEquiv.ofEq _ _ (range_stalkHom_submoduleKer_ι P x))

/-- `submoduleKerModStalkLinearEquiv` is the stalk of the inclusion `(ker P).ι`, read inside the
stalk of `A`. -/
@[simp]
lemma coe_submoduleKerModStalkLinearEquiv_apply
    (m : modStalk (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules x) :
    ((submoduleKerModStalkLinearEquiv P x m : LinearMap.ker (stalkHom P x)) : modStalk A x)
      = stalkHom (_root_.SheafOfModules.Submodule.ker P).ι x m := rfl

/-- Composing `submoduleKerModStalkLinearEquiv` with the inclusion of the kernel of the stalk map
of `P` into the stalk of `A` recovers the stalk of `(ker P).ι`. -/
lemma subtype_comp_submoduleKerModStalkLinearEquiv :
    (LinearMap.ker (stalkHom P x)).subtype ∘ₗ
        (submoduleKerModStalkLinearEquiv P x :
          modStalk (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules x
            →ₗ[ringStalk X.sheaf x] _)
      = stalkHom (_root_.SheafOfModules.Submodule.ker P).ι x :=
  LinearMap.ext fun _ => rfl

end Stacks.SheafOfModules

end
