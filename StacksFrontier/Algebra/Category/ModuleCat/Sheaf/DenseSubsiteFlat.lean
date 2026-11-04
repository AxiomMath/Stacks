module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafTensor

/-!
# Flatness of a sheaf of modules is intrinsic to the ringed topos

Let `v : C ⥤ C'` exhibit `(C, J)` as a dense subsite of `(C', K)` and let `O` be a sheaf of
commutative rings on `(C', K)`. Restriction of sections along `v` is an equivalence from sheaves
of `O`-modules to sheaves of modules over the restricted ring sheaf as soon as the Comparison
Lemma holds for sheaves of abelian groups
(`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`), and it commutes with the tensor
product of sheaves of modules
(`Stacks.DenseSubsiteModules.moduleRestriction_sheafTensorRight`). This file draws the
consequence those two facts exist for:

`Stacks.DenseSubsiteModules.isFlat_moduleRestriction_iff`:
`Stacks.SheafOfModules.IsFlat N ↔ Stacks.SheafOfModules.IsFlat (N|_C)`.

Flatness of `N` (Stacks 03ER (3)) is exactness of `- ⊗_O N`, so it is a property of the
endofunctor `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj N`. Restriction
carries that endofunctor to `- ⊗_{O|_C} N|_C` up to natural isomorphism, and an equivalence of
categories neither creates nor destroys exactness, so the two flatness assertions agree. This is
Stacks 03DG method (2) for flatness, and it is the input that the proof of Stacks 05VD consumes
through Tag 03DG: it is what lets 05VD's statement be read on any site presenting the ringed
topos rather than only on a chosen one.

## Main results

* `Stacks.DenseSubsiteModules.isFlat_moduleRestriction_iff`: **flatness is invariant under
  restriction to a dense subsite**. This is the main result.

## Implementation notes

The statement is a biconditional, and both directions use the hypothesis
`[(v.sheafPushforwardContinuous AddCommGrpCat J K).IsEquivalence]`, i.e. the Comparison Lemma for
sheaves of abelian groups, which is what
`Stacks.DenseSubsiteModules.isEquivalence_moduleRestriction`
already asks for and is no smallness assumption on either site. The proof uses its preservation
and reflection of finite limits and colimits, and cancels its inverse on the left using
`CategoryTheory.Equivalence.invFunIdAssoc`. The restriction functor and its compatibility with
the native tensor product are used directly.

**No tag is placed.** Stacks 05VD asserts that *pullback along a morphism of ringed topoi or
ringed sites* preserves flatness, and that statement is where `@[stacks 05VD]` sits. This file
proves one of its inputs — the invariance of flatness under change of presenting site — and
nothing of the tagged statement itself, so tagging it `05VD` would overstate the tag's
coverage. Tag 03DG, the "method (2)" whose instance for flatness this is, is not formalized.

**Hypotheses and universes.** Beyond `v.IsDenseSubsite J K` and the Comparison Lemma for
`AddCommGrpCat.{w}`, these are exactly the hypotheses of `Stacks.SheafOfModules.IsFlat` on the
two sites: `HasWeakSheafify` and `WEqualsLocallyBijective` for `AddCommGrpCat.{w}` on `J` and on
`K`, and `HasSheafCompose` for `forget₂ CommRingCat RingCat` on `J` and on `K`. Nothing is
assumed about the sites: no finite limits, no products, no smallness. The single module universe
`w` is inherited from `Stacks.DenseSubsiteModules.moduleRestriction` and from
the two native tensor factors; the four universes of the two sites are free and independent.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD), whose proof consumes
  this through Tag 03DG
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER), part (3), the definition
  of flatness used here
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace Stacks.DenseSubsiteModules

section DenseSubsite

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence]

/-- **Flatness of a sheaf of modules is invariant under restriction to a dense subsite.**

A sheaf of `O`-modules on `(C', K)` is flat if and only if its restriction along `v` is flat as a
sheaf of modules over the restricted ring sheaf. Flatness is exactness of tensoring; restriction
is an equivalence carrying one tensor endofunctor to the other up to natural isomorphism
(`moduleRestriction_sheafTensorRight`), and an equivalence neither creates nor destroys
exactness. This is Stacks 03DG method (2) for flatness, and the form in which the proof of
Stacks 05VD consumes it. -/
theorem isFlat_moduleRestriction_iff (O : Sheaf K CommRingCat.{w})
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Stacks.SheafOfModules.IsFlat (O := O) N ↔
      Stacks.SheafOfModules.IsFlat (O := commRingRestriction J K v O)
        ((moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj N) := by
  let := isEquivalence_moduleRestriction
    (J := J) (K := K) (v := v) (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
  let sourceTensor := (Stacks.SheafOfModules.Tensor.sheafTensor.{u₂, v₂, w, w, w} O).flip.obj N
  let targetTensor :=
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u₁, v₁, w, w, w}
      (commRingRestriction J K v O)).flip.obj
        ((moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj N)
  constructor
  · intro hflat
    have hT : PreservesFiniteLimits sourceTensor := hflat.1
    have hTc : PreservesFiniteColimits sourceTensor := hflat.2
    have h1 : PreservesFiniteLimits
        (sourceTensor ⋙ moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
      comp_preservesFiniteLimits _ _
    have h1c : PreservesFiniteColimits
        (sourceTensor ⋙ moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
      comp_preservesFiniteColimits _ _
    have h2 : PreservesFiniteLimits
        (moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ targetTensor) :=
      @preservesFiniteLimits_of_natIso _ _ _ _ _ _
        (moduleRestriction_sheafTensorRight J K v O N) h1
    have h2c : PreservesFiniteColimits
        (moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ targetTensor) :=
      @preservesFiniteColimits_of_natIso _ _ _ _ _ _
        (moduleRestriction_sheafTensorRight J K v O N) h1c
    have h3 : PreservesFiniteLimits
        ((moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)).inv ⋙
          moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ targetTensor) :=
      comp_preservesFiniteLimits _ _
    have h3c : PreservesFiniteColimits
        ((moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)).inv ⋙
          moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ targetTensor) :=
      comp_preservesFiniteColimits _ _
    exact ⟨@preservesFiniteLimits_of_natIso _ _ _ _ _ _
        ((moduleRestrictionEquivalence J K v
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).invFunIdAssoc targetTensor) h3,
      @preservesFiniteColimits_of_natIso _ _ _ _ _ _
        ((moduleRestrictionEquivalence J K v
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).invFunIdAssoc targetTensor) h3c⟩
  · intro hflat
    have hT : PreservesFiniteLimits targetTensor := hflat.1
    have hTc : PreservesFiniteColimits targetTensor := hflat.2
    have h2 : PreservesFiniteLimits
        (moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ targetTensor) :=
      @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ inferInstance hT
    have h2c : PreservesFiniteColimits
        (moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ targetTensor) :=
      @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ inferInstance hTc
    have h1 : PreservesFiniteLimits
        (sourceTensor ⋙ moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
      @preservesFiniteLimits_of_natIso _ _ _ _ _ _
        (moduleRestriction_sheafTensorRight J K v O N).symm h2
    have h1c : PreservesFiniteColimits
        (sourceTensor ⋙ moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
      @preservesFiniteColimits_of_natIso _ _ _ _ _ _
        (moduleRestriction_sheafTensorRight J K v O N).symm h2c
    exact ⟨preservesFiniteLimits_of_reflects_of_preserves sourceTensor
        (moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O)),
      preservesFiniteColimits_of_reflects_of_preserves sourceTensor
        (moduleRestriction.{w} J K v (Stacks.SheafOfModules.Tensor.ringSheaf O))⟩

end DenseSubsite

end Stacks.DenseSubsiteModules

end
