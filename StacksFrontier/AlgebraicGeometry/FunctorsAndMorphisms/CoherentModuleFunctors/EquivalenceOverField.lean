module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceOverBase
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic

/-!
# Equivalences of categories of coherent modules over a field

Let `k` be a field and let `X` and `Y` be schemes of finite type over `k`. Tag 0FZR says that a
`k`-linear equivalence `F : Coh(𝒪_X) ⥤ Coh(𝒪_Y)` is `𝓕 ↦ f^*𝓕 ⊗ ℒ` for an isomorphism of
schemes `f : Y ⟶ X` over `k` and an invertible `𝒪_Y`-module `ℒ`. The Stacks proof is one
sentence: the lemma is a weak form of Tag 0GPK and Tag 0GPL.

This file supplies the two ingredients that separate Tag 0FZR from Tag 0GPL and assembles the
deduction.

## Finite type over a field is Noetherian

Tag 0GPL asks for `X` and `Y` *Noetherian*; Tag 0FZR gives them of *finite type over `k`*. A
morphism of finite type is one that is locally of finite type and quasi-compact, and
`Spec k` is a Noetherian scheme because a field is a Noetherian ring. So
the library's `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`
(`StacksFrontier/AlgebraicGeometry/SchemeTheoreticImage/Basic.lean`) — a scheme of finite type over
a Noetherian scheme is Noetherian — closes the gap. Both of its halves are Mathlib's:
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` for the local component and
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` for compactness.

## `k`-linearity gives `f` over `k`

This is not re-proved here: it is exactly the content of Tag 0GPL,
`AlgebraicGeometry.CoherentModuleFunctors.exists_iso_pullbackTensor_over_base`, whose last
conjunct is `f.hom ≫ X.hom = Y.hom`. A field is a commutative ring, so Tag 0GPL applies with
`R := k` with nothing to adapt.

## Nothing is carried

Tags 0GPL and 0GPK, and this file, rest on Tag 0GPJ, which is proved —
`AlgebraicGeometry.exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence`, restated
for this chain as
`AlgebraicGeometry.CoherentModuleFunctors.exists_iso_pullbackTensor_quasicoherent` — so no
hypothesis is carried, the result is unconditional, and it is registered as Tag 0FZR.

## Generality

The Stacks statement also assumes `X` separated and `Y` reduced. Those hypotheses belong to the
*second* proof given there, the one that avoids Gabriel–Rosenberg reconstruction and goes
through Tag 0FZN and Tag 0FZP. The first proof, which is the one followed here, deduces the
lemma from Tag 0GPK and Tag 0GPL alone and uses neither. They are therefore omitted, and the
statement below is more general than the source's; in particular it implies it.

## Main results

* `AlgebraicGeometry.CoherentModuleFunctors.isNoetherian_of_finiteType_over_field`: a scheme of
  finite type over a field is Noetherian.
* `AlgebraicGeometry.CoherentModuleFunctors.exists_iso_pullbackTensor_over_field`: **Tag
  0FZR**.

## References

* [Stacks Project, Tag 0FZR](https://stacks.math.columbia.edu/tag/0FZR)
* [Stacks Project, Tag 0GPL](https://stacks.math.columbia.edu/tag/0GPL)
* [Stacks Project, Tag 0GPK](https://stacks.math.columbia.edu/tag/0GPK)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.SheafOfModules (CoherentModules)

universe u

namespace AlgebraicGeometry

namespace CoherentModuleFunctors

/-- A scheme of finite type over a field is Noetherian: a field is a Noetherian ring, so
`Spec k` is a Noetherian scheme, and finite type over a Noetherian scheme is Noetherian. -/
lemma isNoetherian_of_finiteType_over_field (k : Type u) [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : IsNoetherian X.left :=
  isNoetherian_of_locallyOfFiniteType X.hom

/-- **Stacks Project, Tag 0FZR.** Let `k` be a field, let `X` and `Y` be schemes of finite type
over `k`, and let `F : Coh(𝒪_X) ⥤ Coh(𝒪_Y)` be an equivalence of categories which is `k`-linear.
Then there are an isomorphism of schemes `f : Y ≅ X` over `k`, that is with
`f ≫ (X → Spec k) = (Y → Spec k)`, and an invertible `𝒪_Y`-module `ℒ` with
`F(𝓕) = f^*𝓕 ⊗ ℒ`, naturally in the coherent `𝒪_X`-module `𝓕`.

Finite type is `LocallyOfFiniteType X.hom` together with `QuasiCompact X.hom`; this makes `X`
and `Y` Noetherian by `isNoetherian_of_finiteType_over_field`, which is what Tag 0GPL needs, and
`k`-linearity is what makes its `f` a morphism over `k`.

Nothing is hypothesised: Tag 0GPL is unconditional, so the content here is only the passage
from Noetherian to finite type over `k`.

The source states the lemma with `X` separated and `Y` reduced. Those hypotheses are used by its
second proof only; the deduction from Tag 0GPK and Tag 0GPL carried out here does not need them,
so they are absent and the statement is correspondingly more general. -/
@[stacks 0FZR "with `X` SEPARATED and `Y` REDUCED deleted: the source uses those two hypotheses \
in its second proof only, and the deduction carried out here — from Tag 0GPL, with finite type \
over the field giving Noetherian by `isNoetherian_of_finiteType_over_field` — does not need them, \
so the statement is more general than the source's and implies it.  Finite type is \
`LocallyOfFiniteType` together with `QuasiCompact`.  As in Tags 0GPK and 0GPL the prescribed form \
of the functor is stated after the fully faithful inclusions of the coherent modules into all \
`𝒪`-modules, where the inverse image and the tensor product live"]
theorem exists_iso_pullbackTensor_over_field (k : Type u) [Field k]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (F : CoherentModules X.left.ringCatSheaf ⥤ CoherentModules Y.left.ringCatSheaf)
    [F.IsEquivalence] :
    letI : Linear k (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear k X
    letI : Linear k (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear k Y
    F.Linear k →
      ∃ (f : Y.left ≅ X.left) (L : Y.left.Modules),
        Stacks.SheafOfModules.IsInvertible Y.left.presheaf Y.left.ringCatSheaf.2 L ∧
        Nonempty (coherentToModules X.left ⋙ pullbackTensor f.hom L ≅
          F ⋙ coherentToModules Y.left) ∧
        f.hom ≫ X.hom = Y.hom :=
  let := isNoetherian_of_finiteType_over_field k X
  let := isNoetherian_of_finiteType_over_field k Y
  exists_iso_pullbackTensor_over_base k X Y F

end CoherentModuleFunctors

end AlgebraicGeometry

end
