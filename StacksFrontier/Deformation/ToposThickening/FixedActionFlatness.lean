module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MultiplicationIdealProduct
public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessEquivalence
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningBoundary

/-!
# The ideal-product sequence of an extension whose canonical action map is the identity

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I`, let `ℱ` be an `O`-module presented on the thickened topos as an `i_*O`-module, and
let

`0 ⟶ I ⊗_O ℱ ⟶ ℱ' ⟶ ℱ ⟶ 0`

be an extension of Stacks 08MB whose canonical action of the square-zero ideal
(`Deformation.ToposThickening.extensionActionMap`) is the **identity** of `I ⊗_O ℱ`. This file
reads such an extension as the ideal-product sequence of Stacks 08MP: the ideal product `I·ℱ'`
is the kernel term, the reduction `ℱ' ⟶ ℱ` is a cokernel of its inclusion, and the second
factor `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of Stacks 08MQ is an isomorphism.

This is the bookkeeping of Section 08MN that the source treats as implicit and that no tag
states on its own; it is the half of
`Deformation.ToposThickening.IsFlatLiftCorrespondence` which says that *the middle term of an
extension with action map the identity has `I·ℱ'` the image of `I ⊗_O ℱ`*, and it is what feeds
such an extension to the flatness criterion of Stacks 08MQ,
`Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`, whose hypotheses `q`, `hq` and
`hqex` are exactly the reduction, the vanishing and the short exactness proved here.

## Main results

* `Deformation.ToposThickening.multiplicationMap_eq_comp_f`: the multiplication map
  `I ⊗_{O'} ℱ' ⟶ ℱ'` of Stacks 08M4 is the reduction comparison `I ⊗_{O'} ℱ' ⟶ I ⊗_O ℱ`
  followed by the inclusion `I ⊗_O ℱ ⟶ ℱ'` of the extension. This is the whole content of the
  action map being the identity, read on pure tensors.
* `Deformation.ToposThickening.idealProduct_ι_comp_g_eq_zero` and
  `.isColimitCokernelCoforkIdealProduct`: the reduction kills the ideal product and is a
  cokernel of its inclusion.
* `Deformation.ToposThickening.shortExact_idealProduct`: **the ideal-product sequence
  `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ ℱ ⟶ 0` is short exact**, which is the datum `hqex` of Stacks 08MQ.
* `Deformation.ToposThickening.isIso_canonicalSecondFactor`: **the second factor
  `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of Stacks 08MQ is an isomorphism.**

## Implementation notes

The reduction comparison `I ⊗_{O'} ℱ' ⟶ I ⊗_O ℱ` is an epimorphism because the reduction
`ℱ' ⟶ ℱ` of the extension is one (`Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_epi`),
and that is the only thing used about it here; its invertibility
(`Deformation.ToposThickening.isIso_reductionTensorMap_thickening`) is a *consequence* of the
short exactness proved here and so cannot be used to prove it. Everything else is the
interchangeability of the multiplication map of Stacks 08M4 with the inclusion of the ideal
product, which is
`Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_comp_eq_zero_iff`: a morphism out of
`ℱ'` kills one exactly when it kills the other, so the two have the same cokernels, and the
universal property transfers in both directions.

No sectionwise image is computed: that the image of `I ⊗_O ℱ ⟶ ℱ'` is `I·ℱ'` on the nose rather
than merely locally is carried by the uniqueness of a cokernel.

## References

* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap reductionTensorMap
  multiplicationMap_eq_of_tmul reductionTensorMap_tmul reductionTensorMap_epi)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}]
  {j : RingedToposHom X X'} (hj : FirstOrderThickening j)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing j)))
  (E : Abelian.YonedaExtension ((structureRestrict j).obj F)
    ((structureRestrict j).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F).obj hj.I)) 0)

/-- **The multiplication map of an extension whose canonical action map is the identity.** The
multiplication map `I ⊗_{O'} ℱ' ⟶ ℱ'` of Stacks 08M4 is the reduction comparison
`I ⊗_{O'} ℱ' ⟶ I ⊗_O ℱ`, which carries `α ⊗ x` to `α ⊗ q(x)`, followed by the inclusion
`I ⊗_O ℱ ⟶ ℱ'` of the extension.

Both sides are determined by their values on the images of pure tensors, and on `α ⊗ x` both
are `α·x`: for the left-hand side by construction, for the right-hand side because the
canonical action map is characterised by sending `α ⊗ q(x)` into `α·x` and is here the
identity. -/
theorem multiplicationMap_eq_comp_f
    (hE : (extensionActionMap hj E).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F).obj hj.I)) :
    multiplicationMap j.fSharp hj.I E.Z.left hj.incl =
      reductionTensorMap j.fSharp hj.I E.Z.left F E.g ≫ E.f := by
  refine (multiplicationMap_eq_of_tmul j.fSharp hj.I E.Z.left hj.incl _ ?_).symm
  intro U a x
  have h1 := reductionTensorMap_tmul j.fSharp hj.I E.Z.left F E.g U a x
  refine (comp_val_app (reductionTensorMap j.fSharp hj.I E.Z.left F E.g) E.f U _).trans ?_
  refine (congrArg (fun y ↦ E.f.val.app U y) h1).trans ?_
  have h2 := (extensionActionMap hj E).2 U a x
  rw [hE] at h2
  exact h2

/-- **The reduction of such an extension kills the multiplication map**, the inclusion
`I ⊗_O ℱ ⟶ ℱ'` being a kernel of it. -/
theorem multiplicationMap_comp_g_eq_zero
    (hE : (extensionActionMap hj E).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F).obj hj.I)) :
    multiplicationMap j.fSharp hj.I E.Z.left hj.incl ≫ E.g = 0 := by
  rw [multiplicationMap_eq_comp_f hj F E hE, Category.assoc, yonedaExtension_comp_zero E,
    comp_zero]

/-- **The reduction of such an extension kills the ideal product `I·ℱ'`.** A morphism out of
`ℱ'` killing the multiplication map kills the ideal product. -/
theorem idealProduct_ι_comp_g_eq_zero
    (hE : (extensionActionMap hj E).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F).obj hj.I)) :
    (idealProductSubmodule hj E.Z.left).ι ≫ E.g = 0 :=
  Stacks.SheafOfModules.FlatSquareZero.imageProductSubmodule_ι_comp_eq_zero j.fSharp hj.I
    E.Z.left hj.incl E.g (multiplicationMap_comp_g_eq_zero hj F E hE)

/-- **The reduction of such an extension is a cokernel of the multiplication map.** It is a
cokernel of the inclusion `I ⊗_O ℱ ⟶ ℱ'`, the extension being short exact, and the
multiplication map is that inclusion precomposed with the reduction comparison, which is an
epimorphism. -/
noncomputable def isColimitCokernelCoforkMultiplicationMap
    (hE : (extensionActionMap hj E).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F).obj hj.I)) :
    IsColimit (CokernelCofork.ofπ E.g (multiplicationMap_comp_g_eq_zero hj F E hE)) := by
  haveI : Epi (reductionTensorMap j.fSharp hj.I E.Z.left F E.g) :=
    reductionTensorMap_epi j.fSharp hj.I E.Z.left F E.g
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk ↦ ?_
  refine CokernelCofork.IsColimit.desc' (yonedaExtension_shortExact E).gIsCokernel k ?_
  rw [multiplicationMap_eq_comp_f hj F E hE, Category.assoc] at hk
  exact (cancel_epi (reductionTensorMap j.fSharp hj.I E.Z.left F E.g)).mp
    (hk.trans comp_zero.symm)

/-- **The reduction of such an extension is a cokernel of the inclusion of the ideal
product.** A morphism out of `ℱ'` kills the inclusion of the ideal product exactly when it
kills the multiplication map, so the two have the same cokernels. -/
noncomputable def isColimitCokernelCoforkIdealProduct
    (hE : (extensionActionMap hj E).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F).obj hj.I)) :
    IsColimit (CokernelCofork.ofπ E.g (idealProduct_ι_comp_g_eq_zero hj F E hE)) := by
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {A} k hk ↦ ?_
  exact CokernelCofork.IsColimit.desc' (isColimitCokernelCoforkMultiplicationMap hj F E hE) k
    (Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_comp_eq_zero j.fSharp hj.I E.Z.left
      hj.incl k hk)

/-- **The ideal-product sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ ℱ ⟶ 0` of an extension whose canonical
action map is the identity is short exact.** This is the presentation of `ℱ = i^*ℱ'` that
Stacks 08MQ consumes. -/
theorem shortExact_idealProduct
    (hE : (extensionActionMap hj E).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F).obj hj.I)) :
    (ShortComplex.mk (idealProductSubmodule hj E.Z.left).ι E.g
      (idealProduct_ι_comp_g_eq_zero hj F E hE)).ShortExact := by
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ ?_) ?_ ?_
  · exact isColimitCokernelCoforkIdealProduct hj F E hE
  · infer_instance
  · infer_instance

/-- **The second factor `I ⊗_O ℱ ⟶ I·ℱ'` of the canonical map of Stacks 08MQ is an
isomorphism** for an extension whose canonical action map is the identity.

It is an epimorphism unconditionally
(`Deformation.ToposThickening.epi_canonicalSecondFactor`), and a monomorphism because its
composite with the inclusion of `I·ℱ'` is the inclusion `I ⊗_O ℱ ⟶ ℱ'` of the extension: both
become the multiplication map after precomposition with the reduction comparison, which is an
epimorphism. -/
theorem isIso_canonicalSecondFactor
    (hE : (extensionActionMap hj E).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F).obj hj.I)) :
    IsIso (canonicalSecondFactor j hj F E.Z.left E.g (idealProduct_ι_comp_g_eq_zero hj F E hE)
      (shortExact_idealProduct hj F E hE)) := by
  have : Epi (reductionTensorMap j.fSharp hj.I E.Z.left F E.g) :=
    reductionTensorMap_epi j.fSharp hj.I E.Z.left F E.g
  have h := reductionTensorMap_comp_canonicalSecondFactor j hj F E.Z.left E.g
    (idealProduct_ι_comp_g_eq_zero hj F E hE) (shortExact_idealProduct hj F E hE)
  rw [multiplicationMap_eq_comp_f hj F E hE] at h
  have : Mono (canonicalSecondFactor j hj F E.Z.left E.g
      (idealProduct_ι_comp_g_eq_zero hj F E hE) (shortExact_idealProduct hj F E hE)) :=
    mono_of_mono_fac ((cancel_epi (reductionTensorMap j.fSharp hj.I E.Z.left F E.g)).mp h)
  have := epi_canonicalSecondFactor j hj F E.Z.left E.g
    (idealProduct_ι_comp_g_eq_zero hj F E hE) (shortExact_idealProduct hj F E hE)
  exact isIso_of_mono_of_epi _

section Assembly

variable {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  (t : RingedToposHom S S') (fb : RingedToposHom X S) (f' : RingedToposHom X' S')
  (ht : FirstOrderThickening t) (comm : f'.comp j = t.comp fb)

/-- **`IsFlatOfFixedActionIdentity` from Stacks 08MQ**, granting the three comparisons of the
two presentations of Situation 08M7 that the library does not yet carry. -/
theorem isFlatOfFixedActionIdentity_of_comparisons
    (hstrictP : IsStrictPullbackIdealMap j t fb f' hj ht comm)
    (hFred : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule j t fb f' comm F))
    (hcff : IsIso (canonicalFirstFactor j t fb f' hj ht comm F)) :
    IsFlatOfFixedActionIdentity j t fb f' hj ht comm F := by
  intro _ _ _ E hE
  refine ((isFlat_iff_isIso_canonicalMap j t fb f' hj ht comm F E.Z.left E.g
    (idealProduct_ι_comp_g_eq_zero hj F E hE) (shortExact_idealProduct hj F E hE)
    hstrictP hFred).1).mpr ?_
  have := hcff
  have := isIso_canonicalSecondFactor hj F E hE
  have := isIso_squareTransportSymm f'.fSharpInverseImage j.fSharp
    (inverseImageBaseReduction t f') (inverseImageReducedStructureMap j t fb f' comm)
    (ringMap_fSharpInverseImage_comp_fSharp j t fb f' comm)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F)).obj hj.I)
  have : IsIso (squareTransport f'.fSharpInverseImage j.fSharp
      (inverseImageBaseReduction t f') (inverseImageReducedStructureMap j t fb f' comm)
      (ringMap_fSharpInverseImage_comp_fSharp j t fb f' comm)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing j)).flip.obj F)).obj hj.I)) :=
    ⟨⟨squareTransportSymm f'.fSharpInverseImage j.fSharp (inverseImageBaseReduction t f')
        (inverseImageReducedStructureMap j t fb f' comm)
        (ringMap_fSharpInverseImage_comp_fSharp j t fb f' comm) _,
      squareTransport_comp_squareTransportSymm _ _ _ _ _ _,
      squareTransportSymm_comp_squareTransport _ _ _ _ _ _⟩⟩
  rw [canonicalMap]
  infer_instance

end Assembly

end Deformation.ToposThickening

end
