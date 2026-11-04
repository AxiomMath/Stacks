module

public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.GeneralModule
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.Constructions.PullbackSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic

/-!
# Multiplying by a nonvanishing section into a tensor factor, at the scheme spelling

`StacksFrontier/AlgebraicGeometry/TensorPowerTrivialize/GeneralModule.lean` proves that a global
section `s` of an invertible module `L` makes `t ↦ t ⊗ s|_W` a linear equivalence
`Γ(𝓕, W) ≃ₗ Γ(𝓕 ⊗ L, W)` for an **arbitrary** second module `𝓕` and every open `W ≤ X_s`. It is
stated for a **ringed space** `X` and modules over the
`Stacks.SheafOfModules.TensorSheafification` packaging of its structure sheaf. Every consumer in
this repository works with a **scheme** `X`, modules `F L : X.Modules` and a global section
`s : Γ(L, ⊤)`. This file transports the equivalence to that spelling, keeping the formula, and
adds the compatibility with restriction that the ringed-space file does not state.

## Main definitions

* `Stacks.TensorPowerTrivialize.schemeTensorSectionsEquiv`: **the equivalence at the scheme
  spelling**, `Γ(F, W) ≃ₗ[Γ(X, W)] Γ(F ⊗ L, W)`, for `F L : X.Modules` with `L` invertible, a
  global section `s : Γ(L, ⊤)` and any `W ≤ X_s`.

## Main results

* `Stacks.TensorPowerTrivialize.schemeTensorSectionsEquiv_apply`: the equivalence is
  `t ↦ t ⊗ s|_W`. Without it the statement says only that the two modules of sections are
  abstractly isomorphic.
* `Stacks.TensorPowerTrivialize.map_schemeTensorSectionsEquiv`: **compatibility with
  restriction.** Multiplying by `s` and then restricting to a smaller open is restricting and
  then multiplying by `s` there. The ringed-space file states no such naturality, and the
  `𝒪_X` case -- the one obtained from `Stacks.TensorPowerTrivialize.trivEquiv` -- has it only
  inside the `θ_naturality` field of
  `Stacks.TensorPowerTrivialize.trivializationOfSection`.
* `Stacks.TensorPowerTrivialize.schemeTensorSectionsEquiv_symm_map`: the same for the
  **division**. Dividing a section of `F ⊗ L` by `s` and then restricting is restricting and
  then dividing. This is the form a comparison of two charts needs, since it divides over two
  different opens `W' ≤ W`.

## Which monoidal structure `F ⊗ L` is

`X.Modules` carries two different monoidal structures and the statements below are about one of
them. `Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict` is the structure of
[Stacks, Tag 01CA], whose tensor product **is**
`Stacks.SheafOfModules.Tensor.sheafTensor` applied to the two modules, on the nose; it is a local
instance here, and a consumer of these statements must name it too.
`Stacks.SheafInternalHom.schemeMonoidalCategory` is the *localized* structure, whose tensor
product is a sheafification and is a different object, isomorphic to this one by
`Stacks.SheafOfModules.tensorObjIso`. Only the first one lets
`Stacks.SheafOfModules.tensorSectionsAt` be applied to a section of `F ⊗ L` at all, so it is the
one in which the formula `t ↦ t ⊗ s|_W` can be stated.

## The route

There is nothing to prove in the transport. `Stacks.NonvanishingSpelling` records that
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf hX` is `X.ringCatSheaf`, so
`SheafOfModules (structureSheaf X.presheaf hX)` is `X.Modules` and no coercion of the modules is
needed; the sheaf condition `hX` is
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X`, which is the one
`Stacks.SheafInternalHom.schemeMonoidalCategory` is also built from. A global section
`s : Γ(L, ⊤)` becomes the restriction-compatible family
`(Stacks.NonvanishingSpelling.sectionsEquiv X L).symm s`, whose value over `W` is `s|_W` by
`rfl`, and the hypothesis `W ≤ X_s` crosses the two spellings of the nonvanishing open by
`Stacks.NonvanishingSpelling.nonvanishingOpen_symm_eq` absorbed into `LE.le.trans_eq`, exactly as
in `StacksFrontier/AlgebraicGeometry/NonvanishingSpelling/Trivialize.lean`.

The restriction compatibility is likewise not new mathematics: it is
`Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality`, which already states
that `tensorSectionsAt` commutes with restriction in full generality, together with
`Stacks.TensorPowerTrivialize.res_resTop` for the denominator.

## Implementation notes

**The proofs are terms, not rewrites.** `F ⊗ L` of the local instance and the application of
`Stacks.SheafOfModules.Tensor.sheafTensor` that `tensorSectionsAt` is stated at are equal by
`rfl` but not syntactically, so a goal mixing them is not type-correct at `implicit`
transparency and `rw` refuses it -- reporting a missing pattern rather than the cause. Concretely,
the `rw` form of `map_schemeTensorSectionsEquiv` fails with exactly the diagnostic
recorded in the header of
`StacksFrontier/AlgebraicGeometry/Constructions/PullbackSectionMultiplication.lean`. Each crossing
is therefore made once inside a proof given by `:=`, which is defeq-tolerant.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY) -- a global section of an
  invertible module is a basis of it on its nonvanishing locus.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) -- the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) -- the graded module of
  twisted sections, whose pieces these divisions act on.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace Stacks.TensorPowerTrivialize

open Stacks.NonvanishingSpelling

attribute [local instance] Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict

variable {X : Scheme.{u}} (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The equivalence -/

/-- **Multiplying by a nonvanishing global section of an invertible module is a linear
equivalence on sections, for an arbitrary second module, at the scheme spelling.** On an open `W`
inside the nonvanishing open of a global section `s` of an invertible `𝒪_X`-module `L`, the
sections of `F` over `W` and the sections of `F ⊗ L` over `W` are isomorphic as
`Γ(X, W)`-modules, for every `F : X.Modules`.

The equivalence is `t ↦ t ⊗ s|_W` (`schemeTensorSectionsEquiv_apply`). Taking `F = 𝒪_X` recovers
the trivialization clause of Stacks Tag 01CY, which is
`Stacks.TensorPowerTrivialize.trivEquiv`. -/
noncomputable def schemeTensorSectionsEquiv (s : Γ(L, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X L s) :
    Γ(F, W) ≃ₗ[Γ(X, W)] Γ(F ⊗ L, W) :=
  tensorSectionsEquiv (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F L
    ((sectionsEquiv X L).symm s)
    (hW.trans_eq (nonvanishingOpen_symm_eq X L s).symm)

/-- **The equivalence is `t ↦ t ⊗ s|_W`.** -/
theorem schemeTensorSectionsEquiv_apply (s : Γ(L, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X L s) (t : Γ(F, W)) :
    schemeTensorSectionsEquiv F L s hW t =
      Stacks.SheafOfModules.tensorSectionsAt X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op W) F L t (resTop L s W) :=
  tensorSectionsEquiv_apply (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F L
    ((sectionsEquiv X L).symm s)
    (hW.trans_eq (nonvanishingOpen_symm_eq X L s).symm) t

/-! ### Compatibility with restriction -/

/-- **Multiplying by `s` commutes with restriction.** For `W' ≤ W` two opens inside the
nonvanishing open of `s`, multiplying a section of `F` over `W` by `s` and restricting to `W'` is
restricting first and multiplying there.

This is what lets a construction made through the equivalence be compared over two different
opens, which is what a comparison of two charts does. -/
theorem map_schemeTensorSectionsEquiv (s : Γ(L, ⊤)) {W W' : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X L s)
    (hW' : W' ≤ Stacks.NonvanishingOpen.nonvanishingOpen X L s) (h : W' ⟶ W) (t : Γ(F, W)) :
    (F ⊗ L).presheaf.map h.op (schemeTensorSectionsEquiv F L s hW t)
      = schemeTensorSectionsEquiv F L s hW' (F.presheaf.map h.op t) :=
  (congrArg (fun y => (F ⊗ L).presheaf.map h.op y)
      (schemeTensorSectionsEquiv_apply F L s hW t)).trans
    (((Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F L h.op t
          (resTop L s W)).trans
        (congrArg (fun y => Stacks.SheafOfModules.tensorSectionsAt X.presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op W') F L
            (F.presheaf.map h.op t) y)
          (res_resTop L s h))).trans
      (schemeTensorSectionsEquiv_apply F L s hW' (F.presheaf.map h.op t)).symm)

/-- **Dividing by `s` commutes with restriction.** For `W' ≤ W` two opens inside the nonvanishing
open of `s`, dividing a section of `F ⊗ L` over `W` by `s` and restricting to `W'` is restricting
first and dividing there.

This is `map_schemeTensorSectionsEquiv` read through the equivalence, and it is the form in which
a chart comparison uses it: the ratios it writes down live over two different opens `W' ≤ W` and
have to agree on the smaller one. -/
theorem schemeTensorSectionsEquiv_symm_map (s : Γ(L, ⊤)) {W W' : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X L s)
    (hW' : W' ≤ Stacks.NonvanishingOpen.nonvanishingOpen X L s) (h : W' ⟶ W)
    (m : Γ(F ⊗ L, W)) :
    (schemeTensorSectionsEquiv F L s hW').symm ((F ⊗ L).presheaf.map h.op m)
      = F.presheaf.map h.op ((schemeTensorSectionsEquiv F L s hW).symm m) :=
  (congrArg (fun y => (schemeTensorSectionsEquiv F L s hW').symm
      ((F ⊗ L).presheaf.map h.op y))
      ((schemeTensorSectionsEquiv F L s hW).apply_symm_apply m).symm).trans
    (((congrArg (schemeTensorSectionsEquiv F L s hW').symm
        (map_schemeTensorSectionsEquiv F L s hW hW' h
          ((schemeTensorSectionsEquiv F L s hW).symm m)))).trans
      ((schemeTensorSectionsEquiv F L s hW').symm_apply_apply _))

end Stacks.TensorPowerTrivialize

end
