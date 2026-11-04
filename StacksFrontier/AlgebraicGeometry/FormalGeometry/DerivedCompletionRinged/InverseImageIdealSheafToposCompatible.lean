module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafTopos
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCompletionTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# `f^♯` carries `f^{-1}ℐ` into `f^{-1}ℐ · 𝒪_X`, in direct-image form

`InverseImageIdealSheafTopos.lean` builds the ideal sheaf `ℐ' = f^{-1}ℐ · 𝒪_X` of Section 52.7 for
an arbitrary `AlgebraicGeometry.RingedToposHom`, and characterises it by a universal property in
sheaves of **modules**. This file proves, in sheaves of **sets**, that `f^♯` carries `ℐ` into the
direct image of that `ℐ'`:

`(ℐ ↪ 𝒪) ≫ f^♯ = ψ ≫ f_*(ℐ' ↪ 𝒪')`

for an explicit `ψ : ℐ ⟶ f_*ℐ'`. This is the relation of [Stacks, Tag 099J] between the two
sheaves of ideals, written with the **direct-image** form of the structure map.

## Why the direct-image form is the useful one

`AlgebraicGeometry.RingedToposHom.IdealCompatible`, which is how [Stacks, Tag 099J],
[Stacks, Tag 099K], the topos-level comparison map of [Stacks, Tag 0A0G] and its invertibility
criterion all phrase their hypothesis, is the *inverse-image* form: `f^{-1}ℐ ⟶ f^{-1}𝒪 ⟶ 𝒪'`
factors through `ℐ' ↪ 𝒪'`. The two are transposes of each other under `f^{-1} ⊣ f_*`, which is a
bijection, so they carry the same information; and the direct-image form is the one the consumers
actually work with. `AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete`, the
proof of [Stacks, Tag 099J], takes `IdealCompatible` and immediately converts it to exactly the
equation proved here before using it, and `AlgebraicGeometry.RingedToposHom.mem_of_square` — the
only place in that proof where the ideals are touched — consumes `ψ` and this equation directly.

## Why this is not immediate from the construction

`ℐ'` is an image in sheaves of modules, so `f^*ℐ ⟶ 𝒪'` factors through it **as modules**, by
`AlgebraicGeometry.RingedToposHom.idealMapFactorThru_ι`. What is wanted is a statement about
`f^{-1}` and about sheaves of sets. The two pullbacks differ by the extension of scalars along
`f^♯` that sits inside `f^*`, so neither statement is the other read through a forgetful functor.

## How it is proved: transpose, then forget

Write `ψ` for the transpose of the module factorisation under `f^* ⊣ f_*` ([Stacks, Tag 03D7],
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`), read on underlying sheaves of
sets. Then:

* the module factorisation, transposed along `f^* ⊣ f_*` by naturality in both variables and with
  `idealMapFactorThru_ι`, says that `ψ` followed by `f_*(ℐ' ↪ 𝒪')` is `ℐ ↪ 𝒪` followed by the
  transpose of the comparison `f^*𝒪 ⟶ 𝒪'`;
* that transpose is the unit-module structure map `𝒪 ⟶ f_*𝒪'`, by
  `AlgebraicGeometry.RingedToposHom.homEquiv_pullbackUnitStructureMap` — immediate, because
  `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap` is *defined* as its inverse
  transpose — and on underlying sheaves of sets the unit-module structure map is `f^♯` itself, by
  `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_unitStructureMap`;
* applying the forgetful functor to the first point and substituting the second gives the
  equation.

Choosing `pullbackUnitStructureMap` as the second factor of `inverseImageIdealMap` is what keeps
this inside one development. The modules development's
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` is the same morphism, but it lives
over the four-field `Stacks.Sheaves.RingedToposModules.RingedToposHom`, hence over a different
spelling of `f^*` and of the adjunction; a proof routed through it has to reconcile the two
spellings inside rewrite motives that are not type-correct at reducible transparency, and it has
to pass between `RingCat` and `CommRingCat` at the *inverse-image* form of the structure map — an
identification the library deliberately does not record (see the docstring of
`AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing`). The route above needs neither: only
the direct-image form appears, and the `RingCat`/`CommRingCat` passage that survives is on the
nose and happens on `Y` alone.

One coincidence carries the remaining bookkeeping, and it was checked rather than assumed: the
underlying sheaf of sets of a direct image of modules is the direct image of the underlying sheaf
of sets, on objects and on morphisms, **on the nose**.

## The transposition back, and where it is

`AlgebraicGeometry.RingedToposHom.IdealCompatible f ℐ (inverseImageIdealSheaf f ℐ)` — the
inverse-image form, the transpose of the theorem below — is proved in
`InverseImageIdealSheafToposIdealCompatible.lean`, by
`AlgebraicGeometry.RingedToposHom.idealCompatible_inverseImageIdealSheaf`. What separates the two
is only the transposition along `f^{-1} ⊣ f_*`: each equation is the image of the other under a
bijection of hom-sets, by `CategoryTheory.Adjunction.homEquiv_naturality_left` and
`..._naturality_right` together with
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`.

Two spellings of the underlying sheaf of sets of `f^{-1}𝒪` occur — `f^{-1}` of the underlying
sheaf of sets of `𝒪`, against the underlying sheaf of sets of `f^{-1}𝒪` — and, on the other side,
two spellings of the underlying sheaf of sets of `f_*𝒪'`; both pairs are definitionally equal
only at default transparency, so `rewrite` on them builds motives that fail to re-typecheck.
The transposition never has to rewrite across either spelling: composing `Eq.trans` and `congrArg` forms no motive, and `Equiv.injective` turns the
goal into an equation between the two adjuncts, which the three naturality lemmas discharge
directly. No new named isomorphism is needed.

## Main results

* `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_homEquiv_pullbackUnitStructureMap`: on
  underlying sheaves of sets, the transpose of the comparison `f^*𝒪 ⟶ 𝒪'` is `f^♯`.
* `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_homEquiv_idealMapFactorThru_comp`: the
  relation of [Stacks, Tag 099J] between `ℐ` and `ℐ' = f^{-1}ℐ · 𝒪_X`, in direct-image form, with
  no hypothesis on `ℐ` and none on the morphism.

## Deliberately untagged

Section 52.7 introduces `f^{-1}ℐ · 𝒪_X` and its compatibility in passing rather than as a numbered
statement, and the ringed-sites counterpart
`AlgebraicGeometry.RingedSite.pushforwardIdealCompatible_inverseImageIdealSheaf` carries no
attribute either.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- **The transpose of the comparison `f^*𝒪 ⟶ 𝒪'` is the structure map**, on underlying sheaves of
sets. The transpose is the unit-module structure map `𝒪 ⟶ f_*𝒪'` by
`AlgebraicGeometry.RingedToposHom.homEquiv_pullbackUnitStructureMap`, and on underlying sheaves of
sets that is `f^♯` by
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_unitStructureMap`. -/
theorem moduleSheafFunctor_map_homEquiv_pullbackUnitStructureMap :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).homEquiv _ _ (pullbackUnitStructureMap f)) =
      forgetFSharp f :=
  (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (homEquiv_pullbackUnitStructureMap f)).trans
    (moduleSheafFunctor_map_unitStructureMap f)

/-- **`f^♯` carries `ℐ` into the direct image of `ℐ' = f^{-1}ℐ · 𝒪_X`**, for an arbitrary morphism
of ringed topoi: the relation of [Stacks, Tag 099J] between `ℐ` and the `ℐ'` that
`InverseImageIdealSheafTopos.lean` constructs, written with the direct-image form of the structure
map, with no hypothesis on `ℐ` and none on the morphism.

This is the form of that relation which
`AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete` derives from its
`AlgebraicGeometry.RingedToposHom.IdealCompatible` hypothesis and then actually uses, and which
`AlgebraicGeometry.RingedToposHom.mem_of_square` consumes. `IdealCompatible` itself — the
inverse-image form, the transpose of this one — is proved from this theorem by
`AlgebraicGeometry.RingedToposHom.idealCompatible_inverseImageIdealSheaf` of
`InverseImageIdealSheafToposIdealCompatible.lean`; see "The transposition back, and where it is"
in the module documentation for what separates them.

The proof is the transposition described in the module documentation. -/
theorem moduleSheafFunctor_homEquiv_idealMapFactorThru_comp :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).homEquiv _ _ (idealMapFactorThru.{u} f I)) ≫
        f.toToposHom.pushforward.map
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
            (inverseImageIdealSheaf.{u} f I).ι) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map I.ι ≫
        forgetFSharp f := by
  have hι : idealMapFactorThru.{u} f I ≫ (inverseImageIdealSheaf.{u} f I).ι =
      (f.toModulesHom.pullbackModules).map I.ι ≫ pullbackUnitStructureMap f :=
    idealMapFactorThru_ι f I
  have hmod : (pullbackAdjPushforwardModules f).homEquiv _ _ (idealMapFactorThru.{u} f I) ≫
        (pushforwardModules f).map (inverseImageIdealSheaf.{u} f I).ι =
      I.ι ≫ (pullbackAdjPushforwardModules f).homEquiv _ _ (pullbackUnitStructureMap f) := by
    rw [← Adjunction.homEquiv_naturality_right, hι, Adjunction.homEquiv_naturality_left]
  have h :=
    congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map hmod
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleSheafFunctor_map_homEquiv_pullbackUnitStructureMap f] at h
  exact h

end AlgebraicGeometry.RingedToposHom

end
