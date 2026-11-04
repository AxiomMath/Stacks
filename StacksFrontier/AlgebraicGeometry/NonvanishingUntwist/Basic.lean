module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic

/-!
# Untwisting by a nowhere-vanishing section

[Stacks, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L) is not a lemma but a displayed
map: for a scheme `X`, an invertible sheaf `L`, a global section `s ∈ Γ(X, L)` and a sheaf of
`𝒪_X`-modules `F`, the comparison

  `Γ_*(X, L, F)_{(s)} ⟶ Γ(X_s, F|_{X_s})`,  `t / s^n ↦ t|_{X_s} ⊗ s|_{X_s}^{-n}`.

The clause `⊗ s|_{X_s}^{-n}` is the only geometric step in it, and this file is that step at a
single twist: a global section `s` of an invertible `L` which is invertible over an open `U`
identifies `(F ⊗_{𝒪_X} L)|_U` with `F|_U`, for *every* sheaf of modules `F`. The Stacks text
makes the same remark in the same place — "This makes sense because `X_s ⊂ X` is by definition
the open over which `s` has an inverse, see Modules, Lemma 01CY".

It is the composite of two existing results:

* `Stacks.SheafOfModules.isIso_over_nonvanishingOpen`, the trivialization clause of Tag 01CY
  (`StacksFrontier/AlgebraicGeometry/NonvanishingTrivialization/Basic.lean`), which says that
  multiplication by `s` is an isomorphism `𝒪_X|_{X_s} ⟶ L|_{X_s}`; and
* `Stacks.SheafOfModules.TensorOver.tensorOverIsoOfTrivial`
  (`StacksFrontier/AlgebraicGeometry/TensorCoherence/Basic.lean`), which says that tensoring
  by a module that restricts to the structure sheaf on `U` does nothing to the restriction
  to `U`.

## Main definitions

* `Stacks.SheafOfModules.trivializationOver`: the isomorphism `L|_U ≅ 𝒪_U` carried by a global
  section of `L` that is invertible over `U`.
* `Stacks.SheafOfModules.tensorOverIsoOfSection`: **the untwisting**, `(F ⊗ L)|_U ≅ F|_U`.
* `Stacks.SheafOfModules.tensorOverNonvanishingIso`: the same at `U = X_s`, where the
  hypothesis is discharged by Tag 01CY, so nothing is assumed beyond `L` being invertible and
  the stalks of `𝒪_X` being local rings.

## Implementation notes

**The hypothesis is the conclusion of Tag 01CY, taken as an instance.** `tensorOverIsoOfSection`
asks for `IsIso ((L.unitHomEquiv.symm s).over U)` rather than `U ≤ X_s`. The two are equivalent
for the opens that matter, but the instance form is what Tag 01CY produces —
`isIso_over_nonvanishingOpen` is declared `@[stacks 01CY "trivialization", instance]` — so at
`U = X_s` the hypothesis is found by instance search and `tensorOverNonvanishingIso` assumes
nothing extra. A consumer working over a smaller open supplies it from
`Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen` together with the restriction lemma
`StacksTag09NE.isIso_over_of_le`
(`StacksFrontier/AlgebraicGeometry/ClosedCoverGlue/Sections.lean`), which is stated for a
scheme.

**The invertibility hypothesis is `Stacks.SheafOfModules.IsInvertible`, not
`AlgebraicGeometry.SheafOfModules.IsInvertible`.** Two developments of Tag 01CS sit on top of
each other in this repository, with identical argument shapes, and the nonvanishing locus is
stated for the first. `AlgebraicGeometry.Scheme.Modules.isInvertible_tensorPower`
(`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean`) transports the second to the first, which is
how a consumer holding the tensor-power form gets here. Both classes are named `IsInvertible`,
and inside a namespace beginning `Stacks.SheafOfModules` the bare name resolves to the first
even under `open AlgebraicGeometry.SheafOfModules (IsInvertible)` — so every occurrence below is
written out in full.

**The tensor product is `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, not the
monoidal `⊗`.** That is the spelling `tensorOverIsoOfTrivial` is stated for, and the two are
identified by `Stacks.SheafOfModules.tensorObjIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean`); restating this file for `⊗`
would need that iso on the ambient site *and* on the slice site. The consumer of 0B5L reads
sections, and `tensorSheaf` is the spelling the restriction results are in.

The displayed map of 0B5L untwists by `s^{-n}` for every `n`, so it needs
`(F ⊗ L^{⊗ n})|_{X_s} ≅ F|_{X_s}`; that follows from the result here together with a
trivialization of `L^{⊗ n}` over `X_s`, equivalently `X_{s^n} = X_s`.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  (F L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L]
  (s : L.sections) (U : Opens X.carrier)

/-- The trivialization `L|_U ≅ 𝒪_U` carried by a global section `s` of `L` whose multiplication
morphism `𝒪_X ⟶ L` is an isomorphism over `U`. -/
noncomputable def trivializationOver [IsIso ((L.unitHomEquiv.symm s).over U)] :
    L.over U ≅ _root_.SheafOfModules.unit ((structureSheafRing X).over U) :=
  (asIso ((L.unitHomEquiv.symm s).over U)).symm ≪≫
    (FiniteTypeKernel.unitOverIso (R := structureSheafRing X) U).symm

/-- **Untwisting by a section that is invertible over `U`.** This is the step
`⊗ s|_{X_s}^{-1}` of the comparison map of [Stacks, Tag 0B5L]: over an open on which the global
section `s` of the invertible module `L` has an inverse, tensoring by `L` does nothing to the
restriction of any sheaf of modules `F`. -/
noncomputable def tensorOverIsoOfSection [IsIso ((L.unitHomEquiv.symm s).over U)] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (L))).over U ≅ F.over U :=
  TensorOver.tensorOverIsoOfTrivial U F L (trivializationOver L s U)

/-- **Untwisting over the nonvanishing locus**, with nothing assumed beyond invertibility of `L`
and locality of the stalks of `𝒪_X`: the hypothesis of `tensorOverIsoOfSection` at `U = X_s` is
the trivialization clause of [Stacks, Tag 01CY], which is available as an instance. -/
noncomputable def tensorOverNonvanishingIso
    [∀ x : X.carrier, IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x)] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (L))).over (nonvanishingOpen L s)
      ≅ F.over (nonvanishingOpen L s) :=
  tensorOverIsoOfSection F L s (nonvanishingOpen L s)

end Stacks.SheafOfModules

end
