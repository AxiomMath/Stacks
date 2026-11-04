module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKerStalk
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormsSheaf
public import StacksFrontier.AlgebraicGeometry.SchemeModulesSpelling.Basic

/-!
# The stalk of the sheaf of forms vanishing on a divisor

Let `f : X ⟶ S` be a morphism of schemes and let `I` record a closed subscheme of `X`. The
subsheaf `𝒦^p ⊆ Ω^p_{X/S}` of relative `p`-forms restricting to zero on that subscheme,
`AlgebraicGeometry.Scheme.Hom.formRestrictionKernel`, is the `SheafOfModules.Submodule.ker` of
`AlgebraicGeometry.Scheme.Hom.formRestriction`. This file identifies its stalk at a point with
the kernel of the stalk of `formRestriction`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.injective_stalkMapL_formRestrictionKernel_ι`: the stalk of the
  inclusion `𝒦^p ⟶ Ω^p_{X/S}` is injective.
* `AlgebraicGeometry.Scheme.Hom.range_stalkMapL_formRestrictionKernel_ι`: its range is the kernel
  of the stalk of `formRestriction`, so a germ of a `p`-form lies in `𝒦^p_x` exactly when its
  image in the stalk of `i_*Ω^p_{Y/S}` vanishes.
* `AlgebraicGeometry.Scheme.Hom.formRestrictionKernelStalkLinearEquiv`: **the stalk of `𝒦^p` is
  the kernel of the stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`**, the two previous results packaged as
  an `𝒪_{X,x}`-linear equivalence.

## Implementation notes

**Which spelling the stalk is read in.** The sheaves here are objects of
`AlgebraicGeometry.Scheme.Modules`, that is `SheafOfModules X.ringCatSheaf`, while the stalk
statements of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKerStalk` are over
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing` of the underlying ringed space.
`Stacks.SchemeModulesSpelling.modules_eq` records that the two categories are the same type, and
`Stacks.SchemeModulesSpelling.ofModules` is the identity between them; since
`AlgebraicGeometry.Scheme.Modules` is a `def`, instance search does not cross on its own, so the
statements below name the ringed-space spelling explicitly and the terms cross by that identity.
With the sheaves so named, the `𝒪_{X,x}`-module structures on the three stalks are found by
instance search as `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` and nothing has to
be supplied by hand.

**Reading the result back in the scheme spelling.** The underlying types do not move:
`Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x` is `X.presheaf.stalk x`
and `grpStalk X.toRingedSpace (Stacks.SchemeModulesSpelling.ofModules X M).val x` is the stalk of
the underlying presheaf of abelian groups of `M`. Only the `Module` instance differs from
`Stacks.ModuleStalk.stalkModule`, which is Mathlib's instance named at the scheme spelling, and
the two are equal by `Stacks.SchemeModulesSpelling.stalkModule_eq`. A consumer working in the
scheme spelling — `AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex` and
`Stacks.RelativeDifferentialStalkMap.moduleStalkRelativeDifferentialForms` do — substitutes that
equality rather than restating the results below.

**What determined the shape.** An instance for the `𝒪_{X,x}`-module structure on the stalk of an
object of `X.Modules` already exists: `Stacks.ModuleStalk.stalkModule`, at the scalar spelling
`X.presheaf.stalk x`. What it does not reach is `PresheafOfModules.stalkMapL`, whose presheaf of
commutative rings is inferred from the type of the morphism and so comes out as
`(sheafToPresheaf _ CommRingCat).obj X.sheaf ⋙ forget₂ _ _`, a term no `letI` in a proof body can
affect because the failure is in the elaboration of the statement. Naming the sheaves at the
ringed-space spelling avoids the question: there the presheaf of rings is
`X.presheaf ⋙ forget₂ _ _` already.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (p : ℕ) (x : X)

/-- The sheaf `i_*Ω^p_{Y/S}` of relative `p`-forms of the closed subscheme, pushed forward to
`X`: the target of `AlgebraicGeometry.Scheme.Hom.formRestriction`. -/
abbrev formRestrictionTarget : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj
    (relativeDifferentialForms (I.subschemeι ≫ f) (p : ℤ))

/-- The stalk at `x` of the inclusion `𝒦^p ⟶ Ω^p_{X/S}` is injective, the inclusion of a
subsheaf being a monomorphism. -/
theorem injective_stalkMapL_formRestrictionKernel_ι :
    Function.Injective (stalkMapL X.toRingedSpace
      (Stacks.SchemeModulesSpelling.ofModules X (formRestrictionKernelSheaf f I p)).val
      (Stacks.SchemeModulesSpelling.ofModules X (relativeDifferentialForms f (p : ℤ))).val
      (formRestrictionKernel f I p).ι.val x) :=
  injective_stalkMapL_submoduleKer_ι X.toRingedSpace
    (formRestriction I.subschemeι f (p : ℤ)) x

/-- **A germ of a relative `p`-form lies in the stalk of `𝒦^p` exactly when its restriction to
the divisor has vanishing germ.** The range of the stalk of the inclusion `𝒦^p ⟶ Ω^p_{X/S}` is
the kernel of the stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`. -/
theorem range_stalkMapL_formRestrictionKernel_ι :
    LinearMap.range (stalkMapL X.toRingedSpace
        (Stacks.SchemeModulesSpelling.ofModules X (formRestrictionKernelSheaf f I p)).val
        (Stacks.SchemeModulesSpelling.ofModules X (relativeDifferentialForms f (p : ℤ))).val
        (formRestrictionKernel f I p).ι.val x) =
      LinearMap.ker (stalkMapL X.toRingedSpace
        (Stacks.SchemeModulesSpelling.ofModules X (relativeDifferentialForms f (p : ℤ))).val
        (Stacks.SchemeModulesSpelling.ofModules X (formRestrictionTarget f I p)).val
        (formRestriction I.subschemeι f (p : ℤ)).val x) :=
  range_stalkMapL_submoduleKer_ι X.toRingedSpace
    (formRestriction I.subschemeι f (p : ℤ)) x

/-- **The stalk at `x` of the sheaf `𝒦^p` of relative `p`-forms vanishing on the divisor is the
kernel of the stalk of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`**, as `𝒪_{X,x}`-modules. The underlying map is
the stalk of the inclusion `𝒦^p ⟶ Ω^p_{X/S}`, by
`Stacks.SheafOfModules.TensorStalkRingedSpace.coe_submoduleKerStalkLinearEquiv_apply`. -/
def formRestrictionKernelStalkLinearEquiv :
    grpStalk X.toRingedSpace
        (Stacks.SchemeModulesSpelling.ofModules X (formRestrictionKernelSheaf f I p)).val x
      ≃ₗ[ringStalk X.toRingedSpace x]
      LinearMap.ker (stalkMapL X.toRingedSpace
        (Stacks.SchemeModulesSpelling.ofModules X (relativeDifferentialForms f (p : ℤ))).val
        (Stacks.SchemeModulesSpelling.ofModules X (formRestrictionTarget f I p)).val
        (formRestriction I.subschemeι f (p : ℤ)).val x) :=
  submoduleKerStalkLinearEquiv X.toRingedSpace
    (formRestriction I.subschemeι f (p : ℤ)) x

end AlgebraicGeometry.Scheme.Hom

end
