module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogPolesFormsStalk
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKerModStalk

/-!
# The stalk of the sheaf of forms with a logarithmic pole, as maps into a kernel

Let `f : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an effective Cartier divisor with
ideal sheaf `ℐ`. Two identifications of the stalk at a point `x` are already available:

* `AlgebraicGeometry.Scheme.Hom.logPolesFormsStalkEquiv`, which is [Stacks, Tag 01CP] at
  `Ω^p_{X/S}(log Y) = SheafHom_{𝒪_X}(ℐ, 𝒦^p)`, reads the stalk as `Hom_{𝒪_{X,x}}(ℐ_x, 𝒦^p_x)`;
* `AlgebraicGeometry.Scheme.Hom.formRestrictionKernelStalkLinearEquiv` reads `𝒦^p_x` as the
  kernel of the stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`.

This file composes them, so that the stalk of `Ω^p_{X/S}(log Y)` becomes the module of
`𝒪_{X,x}`-linear maps from `ℐ_x` into that kernel. That is the shape the local description of
`Ω^p_{X/S}(log Y)` is to be read off in, the stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}` being the
exterior power `KaehlerDifferential.mapExteriorPower` by
`Stacks.GysinStalk.formsStalkMapEquation`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formRestrictionKernelModStalkLinearEquiv`: `𝒦^p_x` as the kernel
  of the stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`, in the `modStalk`/`stalkHom` spelling.
* `AlgebraicGeometry.Scheme.Hom.logPolesFormsStalkKerEquiv`: **the stalk at `x` of
  `Ω^p_{X/S}(log Y)` is the module of `𝒪_{X,x}`-linear maps from `ℐ_x` to the kernel of the
  stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`.**

## Main results

* `AlgebraicGeometry.Scheme.Hom.injective_stalkHom_formRestrictionKernel_ι` and
  `range_stalkHom_formRestrictionKernel_ι`: the two halves of the first equivalence.
* `AlgebraicGeometry.Scheme.Hom.coe_logPolesFormsStalkKerEquiv_apply`: the composite is Tag
  01CP's identification followed, in the target, by the stalk of the inclusion `𝒦^p ⟶ Ω^p_{X/S}`.
  This pins the composite down, Tag 01CP's own map being determined by its germ formula.

## Implementation notes

**Which spelling the stalk is read in, and why not the existing one.** `𝒦^p_x` as a kernel is
`AlgebraicGeometry.Scheme.Hom.formRestrictionKernelStalkLinearEquiv`, stated over
`Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x`, whereas Tag 01CP
delivers its answer over `Stacks.SheafOfModules.SheafHomStalk.ringStalk X.sheaf x`. The two
scalar rings are the same term, and so are the two spellings of the stalk of a sheaf of modules;
but each vocabulary's `Module` instances are keyed to its own abbreviation for the scalars, so a
composite written through either one leaves the other side's module structure unfound. The
sibling below therefore restates the kernel comparison in Tag 01CP's vocabulary rather than
bridging between the two, from the same site-general input
`SheafOfModules.Submodule.exact_ker_shortComplex` that the existing version rests on, by way of
`Stacks.SheafOfModules.submoduleKerModStalkLinearEquiv`. The existing version is untouched and
keeps its consumers.

## What this does not do

The kernel is left as the kernel of a stalk map; it is not identified with
`Stacks.LogPoles.logSubmodule`, and nothing here reaches `Stacks.LogPoles.logFormsX`. The input
for that step is `Stacks.GysinStalk.formsStalkMapEquation`, which is stated in a third
vocabulary again: its stalks are `CategoryTheory.ToType (X.presheaf.stalk x)` and its stalk map
is `PresheafOfModules.stalkMapL (R := X.sheaf.presheaf)`. `ToType` is not the coercion that the
two vocabularies above produce, so that identification needs its own crossing and is not
performed here.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (p : ℕ) (x : X)

/-- The stalk at `x` of the inclusion `𝒦^p ⟶ Ω^p_{X/S}` is injective, in the
`modStalk`/`stalkHom` spelling. -/
theorem injective_stalkHom_formRestrictionKernel_ι :
    Function.Injective (Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom
      (formRestrictionKernel f I p).ι x) :=
  Stacks.SheafOfModules.injective_stalkHom_submoduleKer_ι
    (formRestriction I.subschemeι f (p : ℤ)) x

/-- **A germ of a relative `p`-form lies in the stalk of `𝒦^p` exactly when its restriction to
the divisor has vanishing germ**, in the `modStalk`/`stalkHom` spelling. -/
theorem range_stalkHom_formRestrictionKernel_ι :
    LinearMap.range (Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom
        (formRestrictionKernel f I p).ι x)
      = LinearMap.ker (Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom
        (formRestriction I.subschemeι f (p : ℤ)) x) :=
  Stacks.SheafOfModules.range_stalkHom_submoduleKer_ι
    (formRestriction I.subschemeι f (p : ℤ)) x

/-- **The stalk at `x` of the sheaf `𝒦^p` of relative `p`-forms vanishing on the divisor is the
kernel of the stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`**, as `𝒪_{X,x}`-modules, in the spelling of
the stalk that [Stacks, Tag 01CP] uses. The underlying map is the stalk of the inclusion
`𝒦^p ⟶ Ω^p_{X/S}`. -/
def formRestrictionKernelModStalkLinearEquiv :
    modStalk (Rc := X.sheaf) (formRestrictionKernelSheaf f I p) x
      ≃ₗ[ringStalk X.sheaf x]
      LinearMap.ker (Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom
        (formRestriction I.subschemeι f (p : ℤ)) x) :=
  Stacks.SheafOfModules.submoduleKerModStalkLinearEquiv
    (formRestriction I.subschemeι f (p : ℤ)) x

/-- **The stalk at `x` of the sheaf `Ω^p_{X/S}(log Y)` of relative `p`-forms with a logarithmic
pole along the divisor is the module of `𝒪_{X,x}`-linear maps from `ℐ_x` to the kernel of the
stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`.**

This is [Stacks, Tag 01CP] at `Ω^p_{X/S}(log Y)`, followed in the target by the identification
of `𝒦^p_x` with that kernel. -/
def logPolesFormsStalkKerEquiv [Stacks.Divisors.IsEffectiveCartierDivisor I] :
    modStalk (Rc := X.sheaf) (logPolesForms f I p) x
      ≃ₗ[ringStalk X.sheaf x]
      (modStalk (Rc := X.sheaf) (Stacks.Divisors.negativeTwist I) x →ₗ[ringStalk X.sheaf x]
        LinearMap.ker (Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom
          (formRestriction I.subschemeι f (p : ℤ)) x)) :=
  (logPolesFormsStalkEquiv f I p x).equiv.trans
    (LinearEquiv.congrRight (formRestrictionKernelModStalkLinearEquiv f I p x))

/-- The composite is [Stacks, Tag 01CP]'s identification followed, in the target, by the stalk of
the inclusion `𝒦^p ⟶ Ω^p_{X/S}`: the value of the linear map it produces, read inside the stalk
of `Ω^p_{X/S}`, is the image of Tag 01CP's value under that stalk map. Together with the germ
formula characterising `AlgebraicGeometry.Scheme.Hom.logPolesFormsStalkEquiv`, this determines
the composite. -/
lemma coe_logPolesFormsStalkKerEquiv_apply [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (m : modStalk (Rc := X.sheaf) (logPolesForms f I p) x)
    (n : modStalk (Rc := X.sheaf) (Stacks.Divisors.negativeTwist I) x) :
    ((logPolesFormsStalkKerEquiv f I p x m n :
          LinearMap.ker (Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom
            (formRestriction I.subschemeι f (p : ℤ)) x)) :
        modStalk (Rc := X.sheaf) (relativeDifferentialForms f (p : ℤ)) x)
      = Stacks.AlgebraicGeometry.ReflexiveModules.stalkHom (formRestrictionKernel f I p).ι x
          ((logPolesFormsStalkEquiv f I p x).equiv m n) := rfl

end AlgebraicGeometry.Scheme.Hom

end
