module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsEtaleLocal
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsExceptionalKernel
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HigherDirectImageModels

/-!
# The vanishing form of clause (3) of Stacks 0FUU is étale local

Fix `f : X ⟶ S` and a closed immersion `i : Z ⟶ X`, let `b : X' ⟶ X` be the blowing up along
`Z`, `j : E ⟶ X'` its exceptional divisor, and `𝒦^a` the kernel of the restriction of forms
`Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}` (`Stacks.DeRham.blowupFormsKernel`). By
`Stacks.DeRham.isIso_homology_blowupFormsRestrictionDerivedComparison_of_isZero`, clause (3) of
[Stacks, Tag 0FUU] follows from `R^q b_*𝒦^a = 0` for `q ≥ 1`. This file shows that this
vanishing is compatible with étale base change. Let `ε : X₁ ⟶ X` be étale over an étale
`S₁ ⟶ S`, and let `i₁` be the base change of `i`; then the blowup, its exceptional divisor and
`𝒦^a` all base change along `ε` ([Stacks, Tag 0805], [Stacks, Tag 0FLV]), and flat base change
for the higher direct images ([Stacks, Tag 02KH]) gives `ε^*R^q b_*𝒦^a ≅ R^q b₁_*𝒦₁^a`. Hence
the vanishing for `i` gives the vanishing for `i₁`, and the vanishing for the members of an open
cover gives it for `i`. Only the existence of these isomorphisms is used, not any compatibility
of them.

## Main definitions

* `Stacks.DeRham.blowupFormsKernelHigherDirectImage`: `R^q b_*𝒦^a`, computed in the standard
  model of the derived categories.
* `Stacks.DeRham.pullbackBlowupFormsKernelIso`: `ε'^*𝒦^a ≅ 𝒦₁^a` for the induced étale
  `ε' : X₁' ⟶ X'` of blowups.

## Main results

* `Stacks.DeRham.isQuasicoherent_blowupFormsKernel`: `𝒦^a` is quasi-coherent.
* `Stacks.DeRham.isZero_blowupFormsKernelHigherDirectImage_of_isPullback`: the vanishing passes
  to an étale base change.
* `Stacks.DeRham.isZero_pullback_blowupFormsKernelHigherDirectImage_of_isPullback`: the vanishing
  for the base change gives the vanishing of the inverse image along `ε`.
* `Stacks.DeRham.isZero_homology_derivedPushforward_blowupFormsKernel_iff`: the vanishing at the
  standard model is the vanishing of `H^q(Rb_*𝒦^a)` at any model.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.BlowupTriangle ZeroObject

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The kernel `𝒦^a` is quasi-coherent**: it is the kernel of a morphism between the
quasi-coherent `Ω^a_{X'/S}` and the direct image along the affine `j` of the quasi-coherent
`Ω^a_{E/S}`. -/
instance isQuasicoherent_blowupFormsKernel (a : ℕ) :
    (blowupFormsKernel f i (a : ℤ)).IsQuasicoherent := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (blowupMap i ≫ f) a
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (exceptionalStructure f i) a
  infer_instance

/-- **`R^q b_*𝒦^a`**, the `q`-th higher direct image along the blowing-up morphism of the kernel
of the restriction of forms, computed with injective resolutions in the standard model of the
bounded below derived categories. Whether it vanishes does not depend on the model
(`Stacks.DeRham.isZero_homology_derivedPushforward_blowupFormsKernel_iff`). -/
abbrev blowupFormsKernelHigherDirectImage (a q : ℤ) : X.Modules :=
  (@Functor.rightDerivedPlus _ _ _ _ _ _ (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) (modulePushforward (blowupMap i).toLRSHom.toShHom) _ _ q).obj
    (blowupFormsKernel f i a)

/-- **The vanishing of `R^q b_*𝒦^a` is the vanishing of `H^q(Rb_*𝒦^a)`**, at any model of the
derived categories of `𝒪_X`- and `𝒪_{X'}`-modules. -/
theorem isZero_homology_derivedPushforward_blowupFormsKernel_iff
    [HasDerivedCategory (ModuleSheaves X.toRingedSpace)]
    [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace)] (a q : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((derivedPushforward (blowupMap i).toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor _ 0).obj (blowupFormsKernel f i a)))) ↔
      IsZero (blowupFormsKernelHigherDirectImage f i a q) :=
  isZero_homology_derivedPushforward_iff _ _ _ _ _ q _

/-- `𝒦^a` is the kernel of the comparison map on direct images of forms along `j`: the
restriction of forms is that map followed by an isomorphism. -/
def blowupFormsKernelIso (a : ℤ) :
    blowupFormsKernel f i a ≅
      kernel (Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i) (blowupMap i ≫ f) a) :=
  kernelIsoOfEq (blowupFormsRestriction.eq_1 f i a) ≪≫ kernelCompMono _ _

/-- The inverse image of a kernel along a flat morphism is the kernel of the inverse image. -/
def pullbackKernelIsoOfFlat {Y Y₁ : Scheme.{u}} (g : Y₁ ⟶ Y) [Flat g] {M N : Y.Modules}
    (φ : M ⟶ N) :
    (Scheme.Modules.pullback g).obj (kernel φ) ≅ kernel ((Scheme.Modules.pullback g).map φ) :=
  haveI : PreservesFiniteLimits (Scheme.Modules.pullback g) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (Stacks.ProjectiveBundleQuotients.pullbackIso g).symm
      (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.preservesFiniteLimits_pullback g)
  PreservesKernel.iso (Scheme.Modules.pullback g) φ

section EtaleBaseChange

variable {S₁ X₁ Z₁ : Scheme.{u}} {f} (f₁ : X₁ ⟶ S₁) {i} {ε : X₁ ⟶ X} [Etale ε] {δ : Z₁ ⟶ Z}
  {i₁ : Z₁ ⟶ X₁} [IsClosedImmersion i₁] (H : IsPullback δ i₁ i ε) (e : S₁ ⟶ S) [Etale e]
  (he : ε ≫ f = f₁ ≫ e)

/-- **`𝒦^a` under étale base change**: for the induced étale morphism `ε' : X₁' ⟶ X'` of blowups
and `ε'' : E₁ ⟶ E` of exceptional divisors, `ε'^*𝒦^a ≅ 𝒦₁^a`. The inverse image along the flat
`ε'` is exact, so it carries the kernel of the restriction of forms to the kernel of its inverse
image, which is identified with the restriction of forms of the base change by the canonical
maps of [Stacks, Tag 0FLV] and flat base change in degree zero. -/
def pullbackBlowupFormsKernelIso {ε' : Stacks.Blowup.blowUp i₁.ker ⟶ Stacks.Blowup.blowUp i.ker}
    (hb : IsPullback ε' (blowupMap i₁) (blowupMap i) ε)
    {ε'' : Stacks.Blowup.exceptionalDivisor i₁.ker ⟶ Stacks.Blowup.exceptionalDivisor i.ker}
    (hj : IsPullback ε'' (exceptionalInclusion i₁) (exceptionalInclusion i) ε') (a : ℕ) :
    (Scheme.Modules.pullback ε').obj (blowupFormsKernel f i (a : ℤ)) ≅
      blowupFormsKernel f₁ i₁ (a : ℤ) := by
  haveI : Etale ε' := MorphismProperty.of_isPullback hb.flip inferInstance
  have he' : ε' ≫ (blowupMap i ≫ f) = (blowupMap i₁ ≫ f₁) ≫ e := by
    rw [reassoc_of% hb.w, he, Category.assoc]
  haveI hα := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ε' (blowupMap i ≫ f)
    (blowupMap i₁ ≫ f₁) e he' (a : ℤ)
  haveI hβ := Scheme.Hom.isIso_baseChange_comp_pushforward_map_relativeDifferentialFormsMap hj
    (blowupMap i ≫ f) (blowupMap i₁ ≫ f₁) e he' a
  exact (Scheme.Modules.pullback ε').mapIso (blowupFormsKernelIso f i (a : ℤ)) ≪≫
    pullbackKernelIsoOfFlat ε' _ ≪≫
    kernel.mapIso _ _
      (asIso (Scheme.Hom.relativeDifferentialFormsMap ε' (blowupMap i ≫ f)
        (blowupMap i₁ ≫ f₁) e he' (a : ℤ)))
      (asIso ((AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hj.w).app
          (Scheme.Hom.relativeDifferentialForms (exceptionalInclusion i ≫ blowupMap i ≫ f)
            (a : ℤ)) ≫
        (Scheme.Modules.pushforward (exceptionalInclusion i₁)).map
          (Scheme.Hom.relativeDifferentialFormsMap ε'' (exceptionalInclusion i ≫ blowupMap i ≫ f)
            (exceptionalInclusion i₁ ≫ blowupMap i₁ ≫ f₁) e
            (by rw [← Category.assoc, hj.w, Category.assoc, he']; simp only [Category.assoc])
            (a : ℤ))))
      (Scheme.Hom.pullback_map_formsDirectImageComparison_comp hj.w (blowupMap i ≫ f)
        (blowupMap i₁ ≫ f₁) e he' (a : ℤ)) ≪≫
    (blowupFormsKernelIso f₁ i₁ (a : ℤ)).symm

variable [QuasiCompact (Stacks.Blowup.blowUpToBase i.ker)]

/-- The inverse image along `ε` of `R^q b_*𝒦^a` is `R^q b₁_*𝒦₁^a`. -/
private def pullbackBlowupFormsKernelHigherDirectImageIso (H : IsPullback δ i₁ i ε)
    (he : ε ≫ f = f₁ ≫ e) (a : ℕ) (q : ℤ) :
    (Scheme.Modules.pullback ε).obj (blowupFormsKernelHigherDirectImage f i (a : ℤ) q) ≅
      blowupFormsKernelHigherDirectImage f₁ i₁ (a : ℤ) q :=
  have hb := (Stacks.Blowup.exists_isPullback_blowUpToBase_of_isPullback H).choose_spec
  have hj := (Stacks.Blowup.exists_isPullback_exceptionalDivisor hb H).choose_spec.1
  (Stacks.ProjectiveBundleQuotients.pullbackIso ε).app _ ≪≫
    Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso hb
      (blowupFormsKernel f i (a : ℤ)) q ≪≫
    (@Functor.rightDerivedPlus _ _ _ _ _ _ (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) (modulePushforward (blowupMap i₁).toLRSHom.toShHom) _ _
        q).mapIso
      (((Stacks.ProjectiveBundleQuotients.pullbackIso _).app _).symm ≪≫
        pullbackBlowupFormsKernelIso f₁ e he hb hj a)

include H he in
/-- **The vanishing of `R^q b_*𝒦^a` passes to an étale base change.** -/
theorem isZero_blowupFormsKernelHigherDirectImage_of_isPullback (a : ℕ) (q : ℤ)
    (h : IsZero (blowupFormsKernelHigherDirectImage f i (a : ℤ) q)) :
    IsZero (blowupFormsKernelHigherDirectImage f₁ i₁ (a : ℤ) q) :=
  ((Scheme.Modules.pullback ε).map_isZero h).of_iso
    (pullbackBlowupFormsKernelHigherDirectImageIso f₁ e H he a q).symm

include H he in
/-- **The vanishing of `R^q b_*𝒦^a` after an étale base change gives the vanishing of its inverse
image along `ε`.** -/
theorem isZero_pullback_blowupFormsKernelHigherDirectImage_of_isPullback (a : ℕ) (q : ℤ)
    (h : IsZero (blowupFormsKernelHigherDirectImage f₁ i₁ (a : ℤ) q)) :
    IsZero ((Scheme.Modules.pullback ε).obj
      (blowupFormsKernelHigherDirectImage f i (a : ℤ) q)) :=
  h.of_iso (pullbackBlowupFormsKernelHigherDirectImageIso f₁ e H he a q)

end EtaleBaseChange

/-- **A sheaf of modules whose restrictions to the members of an open cover vanish is zero.** -/
theorem isZero_of_isZero_pullback_ι {Y : Scheme.{u}} {M : Y.Modules} {ι : Type*}
    (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (h : ∀ k, IsZero ((Scheme.Modules.pullback (U k).ι).obj M)) : IsZero M := by
  have hiso : IsIso (0 : M ⟶ 0) :=
    Scheme.Modules.isIso_of_isIso_pullback_ι U hU (0 : M ⟶ 0) fun k =>
      isIso_of_source_target_iso_zero _ (h k).isoZero
        ((Scheme.Modules.pullback (U k).ι).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : M ⟶ 0))

end Stacks.DeRham

end
