module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer

/-!
# The kernel submodule as an exact short complex, and its stalk

Let `f : M ⟶ N` be a morphism of sheaves of modules. Its kernel has two spellings: the
categorical `CategoryTheory.Limits.kernel f`, and the submodule `SheafOfModules.Submodule.ker f`
of `M` whose sections over an object are *by definition* the sections annihilated by `f` there.
`SheafOfModules.Submodule.kerIsoKernel` identifies the two, but only as objects with a map to
`M`; the statements that read a kernel on a stalk, or test exactness, are all phrased for a
short complex.

This file supplies the missing link: the short complex `ker f → M → N` built from the inclusion
of the kernel submodule is exact. That is proved at the generality of an arbitrary site, where
it needs no stalks at all, and it is what makes every existing stalkwise statement apply to the
submodule spelling of the kernel — among them
`Stacks.Duality.range_stalkMapL_eq_ker_stalkMapL`, which turns an exact short complex into an
equality of a range and a kernel of stalk maps.

Over a ringed space the file then records the resulting identification of the stalk of `ker f`
with the kernel of the stalk of `f`, in the `grpStalk`/`stalkMapL` spelling and with the same
shape as `Stacks.SheafOfModules.TensorStalkRingedSpace.kernelStalkLinearEquiv`, which says the
same thing for the categorical kernel.

## Main results

* `SheafOfModules.Submodule.exact_ker_shortComplex`: the short complex `ker f → M → N` is
  exact, for sheaves of modules on an arbitrary site.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.injective_stalkMapL_submoduleKer_ι`: over a
  ringed space, the stalk of the inclusion of `ker f` is injective.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.range_stalkMapL_submoduleKer_ι`: its range is
  the kernel of the stalk of `f`.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.submoduleKerStalkLinearEquiv`: the two previous
  results packaged as a linear equivalence.

## Implementation notes

Exactness is transported from the kernel fork along an isomorphism of short complexes whose
middle and right components are the identity and whose left component is `kerIsoKernel`; the
two commuting squares are `SheafOfModules.Submodule.kerIsoKernel_inv_comp_ι` and reflexivity.
Nothing is recomputed: `CategoryTheory.ShortComplex.exact_kernel` already gives exactness of
`kernel f → M → N`, and `CategoryTheory.ShortComplex.exact_of_iso` moves it across.

Stating this for the submodule spelling is not a convenience. A sheaf built as a
`SheafOfModules.Submodule.ker` — for instance the sheaf of relative differential forms vanishing
on a divisor, `AlgebraicGeometry.Scheme.Hom.formRestrictionKernel` — has its sections over an
open given by a membership condition, which is what the constructions that consume it evaluate.
Its stalk, on the other hand, was reachable only through the categorical kernel, that being the
spelling in which exactness of the stalk functor is available. The exactness below is the bridge
between the two, and the stalk statements are phrased so that the underlying map is the stalk of
the inclusion `(ker f).ι`, which is the map such a construction actually meets.

The ringed-space statements below mirror `KernelStalk.lean` so that the two spellings of the
kernel are read on a stalk in the same shape. A consumer whose sheaf of modules is spelled over
a sheaf of rings obtained differently — `AlgebraicGeometry.Scheme.ringCatSheaf` rather than
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing` of the underlying ringed space,
say — can still use these. The two sheaves of rings are equal only by `rfl`, so instance search
does not cross on its own; but naming the sheaves through the identity
`Stacks.SchemeModulesSpelling.ofModules` puts them at the spelling below, after which the module
structure on each stalk is found. That is what
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.FormRestrictionKernelStalk` does for the sheaf of
relative differential forms vanishing on a divisor.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01AP](https://stacks.math.columbia.edu/tag/01AP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v₁ u₁ u

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The isomorphism of short complexes between `kernel f → M → N` and `ker f → M → N`: the
identity on the last two terms, and `SheafOfModules.Submodule.kerIsoKernel` backwards on the
first. -/
noncomputable def kerShortComplexIso {M N : SheafOfModules.{v} R} (f : M ⟶ N) :
    ShortComplex.mk (kernel.ι f) f (by simp) ≅
      ShortComplex.mk (ker f).ι f (ker_ι_comp f) :=
  ShortComplex.isoMk (kerIsoKernel f).symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp)

/-- **The short complex `ker f → M → N` is exact**, where the first map is the inclusion of the
kernel submodule of `f`. This is exactness of the kernel fork of `f`, read through the
identification of the two spellings of the kernel, and it is what lets a statement about an
exact short complex of sheaves of modules be applied to `SheafOfModules.Submodule.ker`. -/
theorem exact_ker_shortComplex {M N : SheafOfModules.{v} R} (f : M ⟶ N) :
    (ShortComplex.mk (ker f).ι f (ker_ι_comp f)).Exact :=
  ShortComplex.exact_of_iso (kerShortComplexIso f) (CategoryTheory.ShortComplex.exact_kernel f)

end SheafOfModules.Submodule

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The stalk of the inclusion of the kernel submodule is injective, the inclusion of a
submodule being a monomorphism. -/
theorem injective_stalkMapL_submoduleKer_ι
    {A B : _root_.SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier) :
    Function.Injective (stalkMapL X
      (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules.val A.val
      (_root_.SheafOfModules.Submodule.ker P).ι.val x) :=
  (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap
    (_root_.SheafOfModules.Submodule.ker P).ι).1 inferInstance x

/-- **The stalk of the kernel submodule is the kernel of the stalk.** The germs of sections of
`A` represented by a section that `P` annihilates are exactly the germs killed by the stalk of
`P`. -/
theorem range_stalkMapL_submoduleKer_ι
    {A B : _root_.SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier) :
    LinearMap.range (stalkMapL X
        (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules.val A.val
        (_root_.SheafOfModules.Submodule.ker P).ι.val x)
      = LinearMap.ker (stalkMapL X A.val B.val P.val x) := by
  have h := ((AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
    (ShortComplex.mk (_root_.SheafOfModules.Submodule.ker P).ι P
      (_root_.SheafOfModules.Submodule.ker_ι_comp P))).1
      (_root_.SheafOfModules.Submodule.exact_ker_shortComplex P) x).moduleCat_range_eq_ker
  have h' := SetLike.ext_iff.1 h
  simp only [LinearMap.mem_range, LinearMap.mem_ker] at h'
  refine SetLike.ext fun m => ?_
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  exact h' m

/-- The stalk of the kernel submodule of `P` as the kernel of the stalk of `P`. -/
noncomputable def submoduleKerStalkLinearEquiv
    {A B : _root_.SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier) :
    grpStalk X (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules.val x
      ≃ₗ[ringStalk X x] LinearMap.ker (stalkMapL X A.val B.val P.val x) :=
  (LinearEquiv.ofInjective _ (injective_stalkMapL_submoduleKer_ι X P x)).trans
    (LinearEquiv.ofEq _ _ (range_stalkMapL_submoduleKer_ι X P x))

/-- `submoduleKerStalkLinearEquiv` is the stalk of the inclusion `(ker P).ι`, read inside
`grpStalk X A.val x`. -/
@[simp]
lemma coe_submoduleKerStalkLinearEquiv_apply
    {A B : _root_.SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier)
    (m : grpStalk X (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules.val x) :
    ((submoduleKerStalkLinearEquiv X P x m :
          LinearMap.ker (stalkMapL X A.val B.val P.val x)) : grpStalk X A.val x)
      = stalkMapL X (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules.val A.val
          (_root_.SheafOfModules.Submodule.ker P).ι.val x m := rfl

/-- Composing `submoduleKerStalkLinearEquiv` with the inclusion of the kernel of the stalk of
`P` into the stalk of `A` recovers the stalk of `(ker P).ι`. -/
lemma subtype_comp_submoduleKerStalkLinearEquiv
    {A B : _root_.SheafOfModules.{u} (structureSheafRing X)} (P : A ⟶ B) (x : X.carrier) :
    (LinearMap.ker (stalkMapL X A.val B.val P.val x)).subtype ∘ₗ
        (submoduleKerStalkLinearEquiv X P x :
          grpStalk X (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules.val x
            →ₗ[ringStalk X x] _)
      = stalkMapL X (_root_.SheafOfModules.Submodule.ker P).toSheafOfModules.val A.val
          (_root_.SheafOfModules.Submodule.ker P).ι.val x :=
  LinearMap.ext fun _ => rfl

end Stacks.SheafOfModules.TensorStalkRingedSpace

end
