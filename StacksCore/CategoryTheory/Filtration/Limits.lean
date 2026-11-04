module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksCore.CategoryTheory.Filtration.Preadditive
public import StacksCore.CategoryTheory.Limits.Shapes.Kernels
import StacksCore.Tactic.StacksAttribute

/-!
# Kernels, cokernels, images and coimages of filtered objects

Stacks 0122 (3): the category `Fil(𝒜)` of filtered objects has kernels, cokernels, images and
coimages, for an arbitrary index category `I` and needing only zero morphisms in `C`. The kernel
of `f : A ⟶ B` is `Ker(f.hom)` with the induced filtration `F^i(Ker f) = Ker f ∩ F^iA`, and its
cokernel is `Coker(f.hom)` with the quotient filtration `F^i(Coker f) = π(F^iB)`; these are the
induced and quotient filtrations of Stacks 0121 (5), (6). Consequently the image
`Im(f) = Ker(Coker f)` is `Im(f.hom)` with the filtration induced from `B`, and the coimage
`Coim(f) = Coker(Ker f)` is `Coim(f.hom)` with the quotient filtration from `A`.

When `C` is preadditive with a zero object and binary biproducts, `Fil(𝒜)` has all finite limits
and colimits, so the fibre products of Stacks 05SN and the pushouts of Stacks 05SM exist.
Evaluation at a step, `A ↦ F^iA`, preserves finite limits, so that
`F^i(B ×_A D) = F^iB ×_{F^iA} F^iD`. The forgetful functor preserves fibre products and pushouts,
and cartesian morphisms are stable under base change.

## Main definitions

* `kernelObj`, `kernelι`: the kernel of `f.hom` with the induced filtration, and its inclusion.
* `cokernelObj`, `cokernelπ`: the cokernel of `f.hom` with the quotient filtration, and its
  projection.
* `imageObj`: the image of `f.hom` with the filtration induced from `B`.
* `coimageObj`: the coimage of `f.hom` with the quotient filtration from `A`.
* `kernelIsoKernelObj`, `cokernelIsoCokernelObj`, `imageIso`, `coimageIso`: the isomorphisms
  between the kernel, cokernel, image and coimage in `Fil(𝒜)` and these explicit objects.

## Main results

* `kernelIsLimit`, `hasKernels`: `kernelι f` is a kernel of `f`, so `Fil(𝒜)` has kernels.
* `cokernelIsColimit`, `hasCokernels`: `cokernelπ f` is a cokernel of `f`, so `Fil(𝒜)` has
  cokernels.
* `hasFiniteLimits`, `hasFiniteColimits`: `Fil(𝒜)` has finite limits and finite colimits.
* `preservesFiniteLimits_eval`: evaluation at a step preserves finite limits.
* `isPullback_natTrans_app`: the steps of a fibre product are the fibre products of the steps.
* `isPullback_hom`, `isPushout_hom`: the forgetful functor preserves fibre products and
  pushouts.
* `isStrictHom_pullback_fst`, `isStrictHom_pullback_snd`: cartesian morphisms are stable under
  base change.

## Implementation notes

The explicit objects `kernelObj`, `cokernelObj`, `imageObj`, `coimageObj` and the morphisms
`kernelι`, `cokernelπ` are `abbrev`s for `pullbackObj`/`pullbackHom` and
`pushforwardObj`/`pushforwardHom` along `kernel.ι f.hom`, `cokernel.π f.hom`,
`Abelian.image.ι f.hom` and `Abelian.coimage.π f.hom`. In particular `imageObj f` is
definitionally `kernelObj (cokernelπ f)` and `coimageObj f` is definitionally
`cokernelObj (kernelι f)`.

Stacks 0122 (4), that `Fil(𝒜)` is in general not abelian, is not formalized. The comparison map
`Coim(f) ⟶ Im(f)` in `Fil(𝒜)` is an isomorphism exactly when `f` is strict in the sense of
Stacks 0123 (Stacks 05SI). This notion of strictness is weaker than Mathlib's cartesian
`IsStrictHom`: for `X ≠ 0` and `Y = 0`, both with the zero filtration, the comparison map of
`f : X ⟶ Y` is an isomorphism of zero objects, but `f` is not `IsStrictHom`.
-/
@[expose] public section

namespace CategoryTheory.FilteredObject

open Limits

variable {C : Type*} [Category* C] {I : Type*} [Category* I] {A B : FilteredObject C I}

section Kernel

variable [HasZeroMorphisms C] [HasKernels C] [HasPullbacks C]

/-- `Ker f` with the induced filtration `F^i(Ker f) = Ker f ∩ F^iA`: the induced filtration
`pullbackObj A (kernel.ι f.hom)` of Stacks 0121 (5). -/
noncomputable abbrev kernelObj (f : A ⟶ B) : FilteredObject C I :=
  pullbackObj A (kernel.ι f.hom)

/-- The inclusion of the kernel as a morphism of filtered objects,
`pullbackHom A (kernel.ι f.hom)`; its underlying morphism is `kernel.ι f.hom` and its level maps
are the projections `pullback.fst`. -/
noncomputable abbrev kernelι (f : A ⟶ B) : kernelObj f ⟶ A :=
  pullbackHom A (kernel.ι f.hom)

/-- The steps of the kernel filtration are the preimages `Ker f ∩ F^iA = ι⁻¹(F^iA)`. -/
lemma kernelObj_subobject (f : A ⟶ B) (i : I) :
    (kernelObj f).subobject i = (Subobject.pullback (kernel.ι f.hom)).obj (A.subobject i) :=
  Filtration.subobject_pullback _ _ _

/-- The underlying morphism of `kernelι f` is a monomorphism. -/
instance (f : A ⟶ B) : Mono (kernelι f).hom := inferInstanceAs (Mono (kernel.ι f.hom))

/-- The explicit kernel inclusion `kernelι f` is a monomorphism. -/
instance (f : A ⟶ B) : Mono (kernelι f) := mono_of_mono_hom _

/-- The composite `kernelι f ≫ f` is zero. -/
@[simp] lemma kernelι_comp (f : A ⟶ B) : kernelι f ≫ f = 0 :=
  hom_ext (by simp)

/-- The kernel of a morphism of filtered objects is the kernel of the underlying morphism with
the induced filtration. -/
noncomputable def kernelIsLimit (f : A ⟶ B) :
    IsLimit (KernelFork.ofι (kernelι f) (kernelι_comp f)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} k hk =>
      have hk' : k.hom ≫ f.hom = 0 := by simpa using congrArg Hom.hom hk
      homMk (kernel.lift f.hom k.hom hk')
        (fun i => pullback.lift (k.natTrans.app i)
          (kernel.lift f.hom (W.filtration.ι.app i ≫ k.hom)
            (by rw [Category.assoc, hk', comp_zero]))
          (by simp))
        (fun i => by
          rw [Filtration.pullback_ι_app, pullback.lift_snd]
          exact (cancel_mono (kernel.ι f.hom)).1 (by simp)))
    (fun {W} k _ => hom_ext (by simp))
    (fun {W} k _ m hm => hom_ext (equalizer.hom_ext (by simpa using congrArg Hom.hom hm)))

/-- The underlying morphism of the lift along `kernelIsLimit f` is `kernel.lift` of the underlying
morphisms. -/
@[simp] lemma kernelIsLimit_lift_hom (f : A ⟶ B) (c : KernelFork f) :
    ((kernelIsLimit f).lift c).hom =
      kernel.lift f.hom c.ι.hom (congrArg Hom.hom c.condition) :=
  rfl

/-- Stacks 0122 (3): `Fil(𝒜)` has kernels. -/
@[stacks 0122 "(3) kernels, with the induced filtration"]
noncomputable instance hasKernels : HasKernels (FilteredObject C I) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- Mathlib's chosen kernel in `Fil(𝒜)` is isomorphic to the explicit model `kernelObj f`. -/
noncomputable def kernelIsoKernelObj (f : A ⟶ B) : kernel f ≅ kernelObj f :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩

/-- `kernelIsoKernelObj f` identifies `kernel.ι f` with `kernelι f`. -/
@[reassoc (attr := simp)]
lemma kernelIsoKernelObj_hom_kernelι (f : A ⟶ B) :
    (kernelIsoKernelObj f).hom ≫ kernelι f = kernel.ι f :=
  limit.isoLimitCone_hom_π ⟨_, kernelIsLimit f⟩ WalkingParallelPair.zero

/-- The inverse of `kernelIsoKernelObj f` identifies `kernelι f` with `kernel.ι f`. -/
@[reassoc (attr := simp)]
lemma kernelIsoKernelObj_inv_kernel_ι (f : A ⟶ B) :
    (kernelIsoKernelObj f).inv ≫ kernel.ι f = kernelι f :=
  limit.isoLimitCone_inv_π ⟨_, kernelIsLimit f⟩ WalkingParallelPair.zero

end Kernel

section Cokernel

variable [HasZeroMorphisms C] [HasCokernels C] [HasImages C]

/-- `Coker f` with the quotient filtration `F^i(Coker f) = π(F^iB)`: the quotient filtration
`pushforwardObj B (cokernel.π f.hom)` of Stacks 0121 (6). -/
noncomputable abbrev cokernelObj (f : A ⟶ B) : FilteredObject C I :=
  pushforwardObj B (cokernel.π f.hom)

/-- The projection onto the cokernel as a morphism of filtered objects,
`pushforwardHom B (cokernel.π f.hom)`; its underlying morphism is `cokernel.π f.hom` and its
level maps are the `factorThruImage`s. -/
noncomputable abbrev cokernelπ (f : A ⟶ B) : B ⟶ cokernelObj f :=
  pushforwardHom B (cokernel.π f.hom)

/-- The steps of the cokernel filtration are the images `π(F^iB)`. -/
lemma cokernelObj_subobject (f : A ⟶ B) (i : I) :
    (cokernelObj f).subobject i = (Subobject.exists (cokernel.π f.hom)).obj (B.subobject i) :=
  Filtration.subobject_pushforward _ _ _

/-- The underlying morphism of `cokernelπ f` is an epimorphism. -/
instance (f : A ⟶ B) : Epi (cokernelπ f).hom := inferInstanceAs (Epi (cokernel.π f.hom))

/-- The explicit cokernel projection `cokernelπ f` is an epimorphism. -/
instance (f : A ⟶ B) : Epi (cokernelπ f) := epi_of_epi_hom _

/-- The composite `f ≫ cokernelπ f` is zero. -/
@[simp] lemma comp_cokernelπ (f : A ⟶ B) : f ≫ cokernelπ f = 0 :=
  hom_ext (by simp)

/-- The square with sides `F^iB ⟶ F^iW`, `F^iB ⟶ π(F^iB)`, `F^iW ⟶ W` and
`π(F^iB) ⟶ Coker f ⟶ W` commutes. -/
lemma cokernel_commSq (f : A ⟶ B) {W : FilteredObject C I} (k : B ⟶ W)
    (hk : f.hom ≫ k.hom = 0) (i : I) :
    CommSq (k.natTrans.app i) (factorThruImage (B.filtration.ι.app i ≫ cokernel.π f.hom))
      (W.filtration.ι.app i)
      (image.ι (B.filtration.ι.app i ≫ cokernel.π f.hom) ≫ cokernel.desc f.hom k.hom hk) :=
  ⟨by simp⟩

variable [HasStrongEpiImages C]

/-- The cokernel of a morphism of filtered objects is the cokernel of the underlying morphism
with the quotient filtration. -/
noncomputable def cokernelIsColimit (f : A ⟶ B) :
    IsColimit (CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {W} k hk =>
      have hk' : f.hom ≫ k.hom = 0 := by simpa using congrArg Hom.hom hk
      homMk (cokernel.desc f.hom k.hom hk') (fun i => (cokernel_commSq f k hk' i).lift)
        (fun i => (cokernel_commSq f k hk' i).fac_right))
    (fun {W} k _ => hom_ext (by simp))
    (fun {W} k _ m hm => hom_ext (coequalizer.hom_ext (by simpa using congrArg Hom.hom hm)))

/-- Stacks 0122 (3): `Fil(𝒜)` has cokernels. -/
@[stacks 0122 "(3) cokernels, with the quotient filtration"]
noncomputable instance hasCokernels : HasCokernels (FilteredObject C I) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

/-- Mathlib's chosen cokernel in `Fil(𝒜)` is isomorphic to the explicit model
`cokernelObj f`. -/
noncomputable def cokernelIsoCokernelObj (f : A ⟶ B) : cokernel f ≅ cokernelObj f :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

/-- `cokernelIsoCokernelObj f` identifies `cokernel.π f` with `cokernelπ f`. -/
@[reassoc (attr := simp)]
lemma cokernel_π_cokernelIsoCokernelObj_hom (f : A ⟶ B) :
    cokernel.π f ≫ (cokernelIsoCokernelObj f).hom = cokernelπ f :=
  colimit.isoColimitCocone_ι_hom ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one

/-- The inverse of `cokernelIsoCokernelObj f` identifies `cokernelπ f` with `cokernel.π f`. -/
@[reassoc (attr := simp)]
lemma cokernelπ_cokernelIsoCokernelObj_inv (f : A ⟶ B) :
    cokernelπ f ≫ (cokernelIsoCokernelObj f).inv = cokernel.π f :=
  colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one

/-- The level maps of the cokernel projection `cokernel.π f` in `Fil(𝒜)` are epimorphisms. -/
instance epi_cokernel_π_natTrans_app (f : A ⟶ B) (i : I) :
    Epi ((cokernel.π f).natTrans.app i) := by
  rw [← cokernelπ_cokernelIsoCokernelObj_inv f, comp_natTrans, NatTrans.comp_app]
  have := ((isIso_iff (cokernelIsoCokernelObj f).inv).1 inferInstance).2 i
  have : Epi ((cokernelπ f).natTrans.app i) :=
    inferInstanceAs (Epi (factorThruImage (B.filtration.ι.app i ≫ cokernel.π f.hom)))
  exact epi_comp _ _

end Cokernel

section Image

variable [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]

section ImageObj

variable [HasPullbacks C]

/-- `Im(f.hom)` with the filtration induced from `B`, `pullbackObj B (Abelian.image.ι f.hom)`;
this is definitionally `kernelObj (cokernelπ f)`. -/
noncomputable abbrev imageObj (f : A ⟶ B) : FilteredObject C I :=
  pullbackObj B (Abelian.image.ι f.hom)

/-- The steps of the image filtration are the preimages `Im f ∩ F^iB`. -/
lemma imageObj_subobject (f : A ⟶ B) (i : I) :
    (imageObj f).subobject i = (Subobject.pullback (Abelian.image.ι f.hom)).obj (B.subobject i) :=
  Filtration.subobject_pullback _ _ _

end ImageObj

section CoimageObj

variable [HasImages C]

/-- `Coim(f.hom)` with the quotient filtration from `A`,
`pushforwardObj A (Abelian.coimage.π f.hom)`; this is definitionally `cokernelObj (kernelι f)`. -/
noncomputable abbrev coimageObj (f : A ⟶ B) : FilteredObject C I :=
  pushforwardObj A (Abelian.coimage.π f.hom)

/-- The steps of the coimage filtration are the images `π(F^iA)`. -/
lemma coimageObj_subobject (f : A ⟶ B) (i : I) :
    (coimageObj f).subobject i =
      (Subobject.exists (Abelian.coimage.π f.hom)).obj (A.subobject i) :=
  Filtration.subobject_pushforward _ _ _

end CoimageObj

variable [HasPullbacks C] [HasImages C] [HasStrongEpiImages C]

/-- The image `Im(f) = Ker(Coker f)` of a morphism of filtered objects is `Im(f.hom)` with the
filtration induced from `B`: the kernel of the explicit cokernel `cokernelπ f` is a kernel of
Mathlib's `cokernel.π f`. -/
noncomputable def imageIsLimit (f : A ⟶ B) :
    IsLimit (KernelFork.ofι (kernelι (cokernelπ f))
      (by
        rw [(Iso.eq_comp_inv _).2 (cokernel_π_cokernelIsoCokernelObj_hom f), ← Category.assoc,
          kernelι_comp, zero_comp]) : KernelFork (cokernel.π f)) :=
  isKernelCompMono (kernelIsLimit (cokernelπ f)) (cokernelIsoCokernelObj f).inv
    ((Iso.eq_comp_inv _).2 (cokernel_π_cokernelIsoCokernelObj_hom f))

/-- Stacks 0122 (3): the image of `f` in `Fil(𝒜)` is `Im(f.hom)` with the induced filtration. -/
@[stacks 0122 "(3) images `Ker(Coker f)`: `Im(f.hom)` with the induced filtration"]
noncomputable def imageIso (f : A ⟶ B) : Abelian.image f ≅ imageObj f :=
  limit.isoLimitCone ⟨_, imageIsLimit f⟩

/-- `imageIso f` identifies `kernel.ι (cokernel.π f)` with `kernelι (cokernelπ f)`. -/
@[reassoc (attr := simp)]
lemma imageIso_hom_kernelι (f : A ⟶ B) :
    (imageIso f).hom ≫ kernelι (cokernelπ f) = kernel.ι (cokernel.π f) :=
  limit.isoLimitCone_hom_π ⟨_, imageIsLimit f⟩ WalkingParallelPair.zero

/-- The inverse of `imageIso f` identifies `kernelι (cokernelπ f)` with
`kernel.ι (cokernel.π f)`. -/
@[reassoc (attr := simp)]
lemma imageIso_inv_kernel_ι (f : A ⟶ B) :
    (imageIso f).inv ≫ kernel.ι (cokernel.π f) = kernelι (cokernelπ f) :=
  limit.isoLimitCone_inv_π ⟨_, imageIsLimit f⟩ WalkingParallelPair.zero

/-- The coimage `Coim(f) = Coker(Ker f)` of a morphism of filtered objects is `Coim(f.hom)` with
the quotient filtration from `A`: the cokernel of the explicit kernel `kernelι f` is a cokernel
of Mathlib's `kernel.ι f`. -/
noncomputable def coimageIsColimit (f : A ⟶ B) :
    IsColimit (CokernelCofork.ofπ (cokernelπ (kernelι f))
      (by
        rw [← kernelIsoKernelObj_hom_kernelι, Category.assoc, comp_cokernelπ, comp_zero]) :
      CokernelCofork (kernel.ι f)) :=
  isCokernelEpiComp (cokernelIsColimit (kernelι f)) (kernelIsoKernelObj f).hom
    (kernelIsoKernelObj_hom_kernelι f).symm

/-- Stacks 0122 (3): the coimage of `f` in `Fil(𝒜)` is `Coim(f.hom)` with the quotient
filtration. -/
@[stacks 0122 "(3) coimages `Coker(Ker f)`: `Coim(f.hom)` with the quotient filtration"]
noncomputable def coimageIso (f : A ⟶ B) : Abelian.coimage f ≅ coimageObj f :=
  colimit.isoColimitCocone ⟨_, coimageIsColimit f⟩

/-- `coimageIso f` identifies `cokernel.π (kernel.ι f)` with `cokernelπ (kernelι f)`. -/
@[reassoc (attr := simp)]
lemma cokernel_π_coimageIso_hom (f : A ⟶ B) :
    cokernel.π (kernel.ι f) ≫ (coimageIso f).hom = cokernelπ (kernelι f) :=
  colimit.isoColimitCocone_ι_hom ⟨_, coimageIsColimit f⟩ WalkingParallelPair.one

/-- The inverse of `coimageIso f` identifies `cokernelπ (kernelι f)` with
`cokernel.π (kernel.ι f)`. -/
@[reassoc (attr := simp)]
lemma cokernelπ_coimageIso_inv (f : A ⟶ B) :
    cokernelπ (kernelι f) ≫ (coimageIso f).inv = cokernel.π (kernel.ι f) :=
  colimit.isoColimitCocone_ι_inv ⟨_, coimageIsColimit f⟩ WalkingParallelPair.one

end Image

section Finite

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- `Fil(𝒜)` has all finite limits when `𝒜` is preadditive with a zero object, binary
biproducts and kernels; in particular the fibre products of Stacks 05SN exist. -/
@[stacks 05SN "the fibre product exists, for any `I` and any additive `𝒜` with kernels"]
noncomputable instance hasFiniteLimits [HasKernels C] : HasFiniteLimits (FilteredObject C I) :=
  have : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have : HasPullbacks C := hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C
  have : HasEqualizers (FilteredObject C I) := Preadditive.hasEqualizers_of_hasKernels
  have : HasFiniteProducts (FilteredObject C I) := hasFiniteProducts_of_has_binary_and_terminal
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- `Fil(𝒜)` has all finite colimits; in particular the pushouts of Stacks 05SM exist. -/
@[stacks 05SM "the pushout exists, for any `I`, `𝒜` additive with cokernels and strong epi images"]
noncomputable instance hasFiniteColimits [HasCokernels C] [HasImages C] [HasStrongEpiImages C] :
    HasFiniteColimits (FilteredObject C I) :=
  have : HasCoequalizers (FilteredObject C I) := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasFiniteCoproducts (FilteredObject C I) :=
    hasFiniteCoproducts_of_has_binary_and_initial
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end Finite

section ForgetPullback

variable [HasInitial C] [InitialMonoClass C] {A B D : FilteredObject C I}

/-- The underlying object of a fibre product in `Fil(𝒜)` is the fibre product of the underlying
objects. -/
theorem isPullback_hom (f : B ⟶ A) (g : D ⟶ A) [HasPullback f g] :
    IsPullback (pullback.fst f g).hom (pullback.snd f g).hom f.hom g.hom :=
  (IsPullback.of_hasPullback f g).map (forget (C := C) (I := I))

end ForgetPullback

section ForgetPushout

variable {A B D : FilteredObject C I}

/-- The underlying object of a pushout in `Fil(𝒜)` is the pushout of the underlying objects. -/
theorem isPushout_hom (f : A ⟶ B) (g : A ⟶ D) [HasPushout f g] :
    IsPushout f.hom g.hom (pushout.inl f g).hom (pushout.inr f g).hom :=
  (IsPushout.of_hasPushout f g).map (forget (C := C) (I := I))

end ForgetPushout

section EvalKernel

variable [HasZeroMorphisms C] [HasKernels C] [HasPullbacks C] {A B : FilteredObject C I}
  (g : A ⟶ B) (i : I)

/-- `F^i(Ker g) ⟶ F^iA` is a kernel of `F^iA ⟶ F^iB`, that is,
`F^i(Ker g) = Ker g ∩ F^iA = Ker(F^iA ⟶ F^iB)`. -/
noncomputable def evalKernelIsLimit :
    IsLimit (KernelFork.ofι ((eval i).map (kernel.ι g))
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero]) :
      KernelFork ((eval i).map g)) := by
  have h₁ := KernelFork.IsLimit.ofIsPullback
    (IsPullback.of_hasPullback (A.filtration.ι.app i) (kernel.ι g.hom))
    (w := kernel.condition g.hom) (kernelIsKernel g.hom)
  have hw : pullback.fst (A.filtration.ι.app i) (kernel.ι g.hom) ≫ g.natTrans.app i = 0 := by
    rw [← cancel_mono (B.filtration.ι.app i), Category.assoc, g.comm, zero_comp,
      pullback.condition_assoc, kernel.condition, comp_zero]
  have h₂ := isKernelOfComp (B.filtration.ι.app i) (A.filtration.ι.app i ≫ g.hom) h₁
    (by simpa using hw) (g.comm i)
  refine IsLimit.ofIsoLimit h₂ (Fork.ext ((eval i).mapIso (kernelIsoKernelObj g)).symm ?_)
  have he : (eval i).map (kernelIsoKernelObj g).inv ≫ (eval i).map (kernel.ι g) =
      pullback.fst (A.filtration.ι.app i) (kernel.ι g.hom) := by
    rw [← Functor.map_comp, kernelIsoKernelObj_inv_kernel_ι]
    simp
  simpa using he

/-- `eval i` preserves the kernel of `g`. -/
lemma preservesLimit_parallelPair_eval : PreservesLimit (parallelPair g 0) (eval i) :=
  preservesLimit_of_preserves_limit_cone (kernelIsKernel g)
    ((KernelFork.isLimitMapConeEquiv _ _).2 (evalKernelIsLimit g i))

end EvalKernel

section EvalFiniteLimits

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [HasKernels C]

/-- Evaluation at a step, `A ↦ F^iA`, preserves finite limits, for any index category `I` and
any additive `𝒜` with kernels. -/
instance preservesFiniteLimits_eval (i : I) : PreservesFiniteLimits (eval (C := C) i) :=
  have : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have : HasPullbacks C := hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C
  have : ∀ {X Y : FilteredObject C I} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) (eval i) :=
    (preservesLimit_parallelPair_eval · i)
  Functor.preservesFiniteLimits_of_preservesKernels (eval i)

variable {A B D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A)

/-- Stacks 05SN, the fibre product: `B ×_A D` exists in `Fil(𝒜)` (`hasFiniteLimits`) and its
filtration is computed level-wise, `F^i(B ×_A D) = F^iB ×_{F^iA} F^iD`, for any index category
`I` and any additive `𝒜` with kernels. -/
@[stacks 05SN "the fibre product is level-wise, `F^i(B ×_A D) = F^iB ×_{F^iA} F^iD`, for any `I`"]
theorem isPullback_natTrans_app (i : I) :
    IsPullback ((pullback.fst f g).natTrans.app i) ((pullback.snd f g).natTrans.app i)
      (f.natTrans.app i) (g.natTrans.app i) :=
  (IsPullback.of_hasPullback f g).map (eval i)

/-- Cartesian morphisms are stable under base change in `Fil(𝒜)`: `pullback.snd f g` is
cartesian when `f` is. -/
instance isStrictHom_pullback_snd [IsStrictHom f] : IsStrictHom (pullback.snd f g) :=
  isStrictHom_of_isPullback (isPullback_hom f g) (isPullback_natTrans_app f g)

/-- Cartesian morphisms are stable under base change in `Fil(𝒜)`: `pullback.fst f g` is
cartesian when `g` is. -/
instance isStrictHom_pullback_fst [IsStrictHom g] : IsStrictHom (pullback.fst f g) :=
  isStrictHom_of_isPullback (isPullback_hom f g).flip fun i => (isPullback_natTrans_app f g i).flip

end EvalFiniteLimits

end CategoryTheory.FilteredObject
