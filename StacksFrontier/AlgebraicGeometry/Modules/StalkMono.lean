module

public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.NowhereDense
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalkComplexIso

/-!
# Injectivity on one stalk

For a morphism `f : A ⟶ B` of modules on a scheme and a point `x`, this file records when the
stalk map of `f` at `x` is injective: it is so when `f` is a monomorphism, when `f` has a
retraction, and for a composite whose two factors both have injective stalk maps. Combined with
the surjectivity criterion of
`AlgebraicGeometry.Modules.StalkSupport` this gives bijectivity of the stalk map of a
monomorphism at a point off the support of its cokernel, which is the form in which an
isomorphism on one stalk is produced.

Two further stalk computations belong with these: the stalk map of a cokernel projection is a
monomorphism wherever the stalk map of the morphism vanishes, and the stalk map of a kernel
inclusion vanishes wherever the stalk map of the morphism is a monomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Modules.injective_stalkLinearMap_of_mono`: a monomorphism is
  injective on every stalk.
* `AlgebraicGeometry.Scheme.Modules.injective_stalkLinearMap_of_retraction` and
  `AlgebraicGeometry.Scheme.Modules.injective_stalkLinearMap_comp`: injectivity for a split
  monomorphism and for a composite.
* `AlgebraicGeometry.Scheme.Modules.bijective_stalkLinearMap_of_notMem_supp_cokernel`: a
  monomorphism has bijective stalk map off the support of its cokernel.
* `AlgebraicGeometry.Scheme.Modules.mono_stalkFunctor_map_cokernel_π` and
  `AlgebraicGeometry.Scheme.Modules.stalkFunctor_map_kernel_ι_eq_zero`: the two stalk
  computations for the cokernel projection and the kernel inclusion.
* `AlgebraicGeometry.Scheme.Modules.stalkLinearMap_eq_zero_iff`: the two readings of a
  vanishing stalk map agree.

## Implementation notes

The stalk map appears in two readings: `AlgebraicGeometry.stalkLinearMap`, a linear map over
the local ring, and the image of `f` under the stalk functor, a morphism of `ModuleCat`. They
are definitionally equal but the unfolding passes through the colimit cocone chosen for the
stalk, which is opaque under the module system; every step crossing between them is therefore
written in term mode, and `stalkLinearMap_eq_zero_iff` is provided so that the crossing happens
once.

`Mono f` is likewise two predicates, one for each of the two category instances on the modules
over the structure sheaf of a scheme, and instance search does not cross between them;
`mono_of_right_cancellation` builds the predicate for `AlgebraicGeometry.Scheme.Modules` from
the cancellation property, which is what a monomorphism in the other reading supplies.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism of modules on a scheme with the right cancellation property is a monomorphism in
the `AlgebraicGeometry.Scheme.Modules` reading. The category instance there is a copy of the one
on `SheafOfModules`, so a monomorphism in the other reading is not seen by instance search; its
cancellation property is what transports. -/
theorem mono_of_right_cancellation {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ {Z : X.Modules} (g k : Z ⟶ M), g ≫ f = k ≫ f → g = k) : Mono f := ⟨h⟩

/-- A monomorphism of modules on a scheme is injective on the stalk at every point. -/
theorem injective_stalkLinearMap_of_mono {A B : X.Modules} (f : A ⟶ B) (hf : Mono f) (x : X) :
    Function.Injective (stalkLinearMap A B f x) :=
  have _ := hf
  (ModuleCat.mono_iff_injective ((stalkFunctor X x).map f)).1
    (Stacks.AlgebraicGeometry.CoherentSubquotients.mono_stalkFunctor_map f x)

/-- The stalk map of a split monomorphism is injective; in particular the stalk map of an
isomorphism is, taking for the retraction the inverse. -/
theorem injective_stalkLinearMap_of_retraction {A B : X.Modules} (f : A ⟶ B) (g : B ⟶ A)
    (h : f ≫ g = 𝟙 A) (x : X) : Function.Injective (stalkLinearMap A B f x) :=
  have key : ∀ z : A.presheaf.stalk x, stalkLinearMap B A g x (stalkLinearMap A B f x z) = z :=
    fun z => (stalkLinearMap_comp f g x z).symm.trans
      ((congrArg (fun k : A ⟶ A => stalkLinearMap A A k x z) h).trans (stalkLinearMap_id A x z))
  fun z w hzw => (key z).symm.trans ((congrArg (stalkLinearMap B A g x) hzw).trans (key w))

/-- The stalk map of a composite is injective as soon as the stalk maps of its two factors
are. -/
theorem injective_stalkLinearMap_comp {A B C : X.Modules} (u : A ⟶ B) (v : B ⟶ C) (x : X)
    (hu : Function.Injective (stalkLinearMap A B u x))
    (hv : Function.Injective (stalkLinearMap B C v x)) :
    Function.Injective (stalkLinearMap A C (u ≫ v) x) := fun z w hzw =>
  hu (hv ((stalkLinearMap_comp u v x z).symm.trans (hzw.trans (stalkLinearMap_comp u v x w))))

/-- **An isomorphism on one stalk.** The stalk map of a monomorphism is bijective at every point
off the support of its cokernel: injectivity holds everywhere, and surjectivity is the pointwise
stalkwise criterion. -/
theorem bijective_stalkLinearMap_of_notMem_supp_cokernel {A B : X.Modules} (f : A ⟶ B)
    (hf : Mono f) (x : X) (hx : x ∉ SheafOfModules.supp (cokernel f)) :
    Function.Bijective (stalkLinearMap A B f x) :=
  ⟨injective_stalkLinearMap_of_mono f hf x,
    (surjective_stalkLinearMap_iff_notMem_supp_cokernel f x).2 hx⟩

/-- A vanishing stalk map, in the two readings of the stalk map. -/
theorem stalkLinearMap_eq_zero_iff {A B : X.Modules} (f : A ⟶ B) (x : X) :
    stalkLinearMap A B f x = 0 ↔ (stalkFunctor X x).map f = 0 :=
  ⟨fun h => by ext z; exact LinearMap.congr_fun h z,
    fun h => by ext z; exact ConcreteCategory.congr_hom h z⟩

/-- Where the stalk map of `f` vanishes, the stalk map of the projection to its cokernel is a
monomorphism: taking stalks preserves cokernels, and the cokernel of a zero morphism is an
isomorphism. -/
theorem mono_stalkFunctor_map_cokernel_π {A F : X.Modules} (f : A ⟶ F) (x : X)
    (h : (stalkFunctor X x).map f = 0) : Mono ((stalkFunctor X x).map (cokernel.π f)) :=
  have _ : IsIso (cokernel.π ((stalkFunctor X x).map f)) := cokernel.π_of_zero h
  mono_of_mono_fac (PreservesCokernel.π_iso_hom (stalkFunctor X x) f)

/-- Where the stalk map of `f` is a monomorphism, the stalk map of the inclusion of its kernel
vanishes: that inclusion composed with `f` is zero, and the stalk functor preserves both the
composition and the zero morphism. -/
theorem stalkFunctor_map_kernel_ι_eq_zero {A B : X.Modules} (f : A ⟶ B) (x : X)
    (hm : Mono ((stalkFunctor X x).map f)) : (stalkFunctor X x).map (kernel.ι f) = 0 :=
  have h1 : (stalkFunctor X x).map (kernel.ι f) ≫ (stalkFunctor X x).map f = 0 :=
    ((stalkFunctor X x).map_comp (kernel.ι f) f).symm.trans
      ((congrArg (stalkFunctor X x).map (kernel.condition f)).trans
        (@Functor.map_zero _ _ _ _ _ _ _
          (AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesZeroMorphisms X.ringCatSheaf x)
          _ _))
  hm.right_cancellation _ 0 (h1.trans zero_comp.symm)

end AlgebraicGeometry.Scheme.Modules

end
