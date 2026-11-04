module

public import StacksFrontier.AlgebraicGeometry.SubmoduleRestrict.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal

/-!
# The locality theorems, applied to a concrete submodule

`StacksFrontier/AlgebraicGeometry/SubmoduleRestrict/Basic.lean` carries a submodule `N` of an
`𝒪_X`-module `F` across an open immersion, and proves that the `𝒪_Y`-module of the restricted
submodule *is* the restriction of the `𝒪_X`-module of `N`
(`Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_toSheafOfModules`, a `rfl`). This file is
the demonstration that the crossing is complete: the locality theorems stated over
`AlgebraicGeometry.Scheme.Modules.restrict` apply to `N.toSheafOfModules` with their hypotheses
read off the restricted submodules, and each proof is one application and one transport along that
equality.

The hypotheses are stated in the `restrictTo` spelling, which is the shape an affine induction on
a glued submodule produces — see
`StacksFrontier/AlgebraicGeometry/SubmoduleGlueOpens/Basic.lean`, whose
`finite_sections_glue_of_le` and `span_sections_glue_of_le` transfer their properties over the
opens inside a member of the covering, while the induction needs them at every affine open of `X`.

## Main results

* `isQuasicoherent_toSheafOfModules_of_isAffineOpen`: if the restriction of `N` to every affine
  open of `X` is quasi-coherent, then `N.toSheafOfModules` is quasi-coherent.
* `isFiniteType_toSheafOfModules_of_restrict`: if the restriction of `N` to each member of an open
  covering of `X` is of finite type, then `N.toSheafOfModules` is of finite type.
* `isCoherent_toSheafOfModules_of_restrict`: the same for coherence.

## Implementation notes

The transport is written as `▸` on that equality rather than left to unification:
asking the elaborator to unify `(restrictTo U.ι N).toSheafOfModules` with
`Scheme.Modules.restrict N.toSheafOfModules U.ι` *at `f = U.ι`* exhausts the heartbeat budget at
`whnf`, although the two are `rfl`-equal for a general open immersion `f` — the proof in
`Basic.lean` is cheap because `f` is a variable there, and instantiating it at `U.ι` is what makes
whnf unfold the open-immersion structure. So the equality must be applied, never relied on
implicitly. Every statement below passes through `restrictTo_toSheafOfModules` or its
`restrictFunctor`-spelled twin `restrictTo_toSheafOfModules'` explicitly — which of the two is
decided by the spelling of the locality theorem being applied, since `▸` matches syntactically —
and none of them needs a compiler option.

## What this does not do

No stacks attribute is attached. These are instances of existing locality theorems, not assertions
of a tag; the content they are a step of is the affine induction of [Stacks, Tag 01PF].

The locality theorems phrased over `SheafOfModules.over` rather than over
`AlgebraicGeometry.Scheme.Modules.restrict` are not reached — see the corresponding section of
`StacksFrontier/AlgebraicGeometry/SubmoduleRestrict/Basic.lean`. In particular
`Stacks.SheafOfModules.isFiniteType_of_coversTop`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`, which does exist, in the
`Stacks.SheafOfModules` namespace, as do its two namesakes in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactnessSheafify.lean` and
`StacksFrontier/AlgebraicGeometry/CoherentKernel/Basic.lean`) is not used here: all three take
`M.over (Xc i)`, so reaching them needs the independent `over`-versus-`restrict` bridge. The
finite-type statement used instead is `AlgebraicGeometry.Modules.isFiniteType_of_restrict`, which
is already in the `restrict` spelling.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.SubmoduleRestrict

variable {X : Scheme.{u}} {F : X.Modules}

/-- **Quasi-coherence of a concrete submodule is affine-local.** If the restriction of `N` to
every affine open of `X` is quasi-coherent, so is `N`.

This is `AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen` applied to
`N.toSheafOfModules`; the hypothesis is stated for the restricted submodules because
`restrictTo_toSheafOfModules` makes the two the same module. -/
theorem isQuasicoherent_toSheafOfModules_of_isAffineOpen (N : F.Submodule)
    (h : ∀ U : X.Opens, IsAffineOpen U →
      (restrictTo U.ι N).toSheafOfModules.IsQuasicoherent) :
    (N.toSheafOfModules).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen
    (N.toSheafOfModules : X.Modules)
    fun U hU ↦ restrictTo_toSheafOfModules U.ι N ▸ h U hU

/-- **Being of finite type is local for a concrete submodule.** If the restriction of `N` to each
member of an open covering of `X` is of finite type, so is `N`.

This is `AlgebraicGeometry.Modules.isFiniteType_of_restrict` applied to `N.toSheafOfModules`. -/
theorem isFiniteType_toSheafOfModules_of_restrict (N : F.Submodule) {I : Type u}
    (U : I → X.Opens) (hU : IsOpenCover U)
    (h : ∀ i, (restrictTo (U i).ι N).toSheafOfModules.IsFiniteType) :
    (N.toSheafOfModules).IsFiniteType :=
  AlgebraicGeometry.Modules.isFiniteType_of_restrict
    (N.toSheafOfModules : X.Modules) U hU
    fun i ↦ restrictTo_toSheafOfModules' (U i).ι N ▸ h i

/-- **Coherence is local for a concrete submodule.** If the restriction of `N` to each member of
an open covering of `X` is coherent, so is `N`.

This is `AlgebraicGeometry.Modules.isCoherent_of_restrict` applied to `N.toSheafOfModules`. -/
theorem isCoherent_toSheafOfModules_of_restrict (N : F.Submodule) {I : Type u}
    (U : I → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, (restrictTo (U i).ι N).toSheafOfModules.IsCoherent) :
    (N.toSheafOfModules).IsCoherent :=
  AlgebraicGeometry.Modules.isCoherent_of_restrict
    (N.toSheafOfModules : X.Modules) U hU
    fun i ↦ restrictTo_toSheafOfModules' (U i).ι N ▸ h i

end Stacks.AlgebraicGeometry.SubmoduleRestrict

end
