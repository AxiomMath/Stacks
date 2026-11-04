module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Quasi-coherence in a short exact sequence of modules

Stacks 03M1 lists the closure properties of the quasi-coherent modules on an algebraic space
inside all `𝒪_X`-modules.  Two of its clauses concern exactness: clause (3), that the kernel and
the cokernel of a morphism of quasi-coherent modules are quasi-coherent, and clause (4), that in
a short exact sequence of `𝒪_X`-modules quasi-coherence of two of the three terms gives it for
the third.  The sub-object and the quotient halves of clause (4) and the two halves of
clause (3) are related by formal arguments in an abelian category, and this file carries out
those arguments, on an arbitrary site and over an arbitrary sheaf of rings.

A sub-object in a short exact sequence is a kernel and a quotient is a cokernel, so each half of
clause (3) gives the corresponding half of clause (4) at once.  The converse needs one extra
step in each direction, because a kernel or a cokernel is a term of a short exact sequence only
after the image has been interposed: for `f : M ⟶ N` the two sequences

```text
0 → Im f → N → Coker f → 0        0 → Ker f → M → Coim f → 0
```

are short exact, and `Coim f ≅ Im f`, so the sub-object half of clause (4) produces `Im f` from
`Coker f` and then `Ker f` from `Im f`.  Hence that half of clause (4) gives closure under
kernels *as soon as closure under cokernels is available*, and dually.

## Main results

* `SheafOfModules.IsQuasicoherentOnSite.X₁_of_shortExact` and
  `SheafOfModules.IsQuasicoherentOnSite.X₃_of_shortExact`: **the two outer terms of
  Stacks 03M1(4)**, from closure of quasi-coherence under kernels, respectively cokernels.
* `SheafOfModules.isClosedUnderKernels_isQuasicoherentOnSite` and
  `SheafOfModules.isClosedUnderCokernels_isQuasicoherentOnSite`: **the converse direction**,
  that is Stacks 03M1(3) from Stacks 03M1(4) and the other half of clause (3).
* `SheafOfModules.isClosedUnderKernels_isQuasicoherentOnSite_of_ulift`: **closure under kernels
  descends the universe of the module sections**, which is how the kernel clause is obtained at
  a module universe in which the ambient category of all modules is not known to be abelian.
* `CategoryTheory.Abelian.shortExact_image` and
  `CategoryTheory.Abelian.shortExact_coimage`: the two short exact sequences of the image and
  the coimage of a morphism in an abelian category, on which the converse direction rests.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_X₁_of_shortExact` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_X₃_of_shortExact`: the same two statements on
  the small étale ringed site of an algebraic space, where the abelian structure on the modules
  needs no hypothesis.

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, the universe-flexible form of
Stacks 03DL(6), and the closure properties are Mathlib's
`CategoryTheory.ObjectProperty.IsClosedUnderKernels` and
`CategoryTheory.ObjectProperty.IsClosedUnderCokernels` for the object property
`SheafOfModules.isQuasicoherentOnSite`; nothing is restated.  The two sheafification conditions
under which the ambient category of modules is abelian are carried as instance arguments, and on
the small étale ringed site of an algebraic space at the module universe of the schemes they are
supplied by `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`.

The middle term of Stacks 03M1(4) is *not* among the statements below.  Quasi-coherence of an
extension of quasi-coherent modules is independent of closure under kernels and cokernels — it
is the extension clause of a weak Serre class, which neither of the other two implies — so no
formal argument carries it, and it is not recorded here.

The two short exact sequences are those of the abelian image and the abelian coimage of a
morphism.  They are stated for an arbitrary abelian category, since nothing about sheaves of
modules enters them.

## What is not proved

Closure of quasi-coherence under kernels and under cokernels is a hypothesis throughout, not a
theorem.  It is the content of Stacks 0GNB(3), whose proof is not formal: a presentation of a
cokernel is assembled from presentations of the source and the target of the morphism, and the
one step that does not follow from those is that the generators of the source lift along the
presentation of the target.  Over an affine object that lift is the vanishing of the first
cohomology of a quasi-coherent module on an affine scheme, Stacks 03DW, through the comparison
of quasi-coherent modules on a small étale site with modules over the ring of Stacks 03DX.  The
reduction of the lift to that vanishing is
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app`; once
Stacks 03DW and Stacks 03DX are available on the small étale site, the closure properties
assumed below become theorems and the statements here become the full clauses (3) and (4) of
Stacks 03M1.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m

namespace CategoryTheory.Abelian

variable {D : Type u} [Category.{v} D] [Abelian D] {M N : D} (f : M ⟶ N)

/-- The image of a morphism sits in a short exact sequence with its target and its cokernel. -/
theorem shortExact_image :
    (ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (by simp)).ShortExact :=
  ⟨ShortComplex.exact_kernel _⟩

/-- The coimage of a morphism sits in a short exact sequence with its source and its kernel. -/
theorem shortExact_coimage :
    (ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f)) (by simp)).ShortExact :=
  ⟨ShortComplex.exact_cokernel _⟩

end CategoryTheory.Abelian

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **Closure of quasi-coherence under kernels descends the universe of the module sections.**
Raising the universe of the sections is a functor preserving zero morphisms and finite limits,
so it carries a kernel to a kernel, and it both preserves and reflects quasi-coherence; hence
the kernel of a morphism of quasi-coherent modules with sections in `Type m` is quasi-coherent
as soon as this is known for modules with sections in the universe containing the site, the
coefficient rings and `Type m`.

This is how the kernel clause of Stacks 03M1 is obtained at an arbitrary universe of module
sections from a universe in which the ambient category of all modules is abelian.  No
sheafification hypothesis appears, because limits of sheaves of modules are computed on
sections and so exist over any site. -/
theorem isClosedUnderKernels_isQuasicoherentOnSite_of_ulift
    (h : (isQuasicoherentOnSite.{u, v, r, max u v r m} R).IsClosedUnderKernels) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderKernels where
  kernels_le := by
    have := h
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine IsQuasicoherentOnSite.of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk) ?_
    have lift : ∀ {X : SheafOfModules.{m} R}, X.IsQuasicoherentOnSite →
        IsQuasicoherentOnSite
          ((uliftForPresentationFunctor.{u, v, r, m, max u v r} (R := R)).obj X) :=
      fun hX => isQuasicoherentOnSite_uliftForPresentation hX
    have hker := (isQuasicoherentOnSite.{u, v, r, max u v r m} R).prop_kernel
      ((uliftForPresentationFunctor.{u, v, r, m, max u v r} (R := R)).map f) (lift hM) (lift hN)
    exact IsQuasicoherentOnSite.of_uliftForPresentation
      (IsQuasicoherentOnSite.of_iso
        (PreservesKernel.iso (uliftForPresentationFunctor.{u, v, r, m, max u v r} (R := R)) f).symm
          hker)

section Abelian

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Stacks 03M1(4), the sub-object.**  In a short exact sequence of modules on a site, if the
middle term and the quotient are quasi-coherent then so is the sub-object: the sub-object is a
kernel of the second map, and quasi-coherence is assumed closed under kernels. -/
theorem IsQuasicoherentOnSite.X₁_of_shortExact
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderKernels]
    {T : ShortComplex (SheafOfModules.{m} R)} (hT : T.ShortExact)
    (h₂ : T.X₂.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) :
    T.X₁.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite.{u, v, r, m} R).prop_of_isLimit_kernelFork hT.fIsKernel h₂ h₃

/-- **Stacks 03M1(4), the quotient.**  In a short exact sequence of modules on a site, if the
sub-object and the middle term are quasi-coherent then so is the quotient: the quotient is a
cokernel of the first map, and quasi-coherence is assumed closed under cokernels. -/
theorem IsQuasicoherentOnSite.X₃_of_shortExact
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderCokernels]
    {T : ShortComplex (SheafOfModules.{m} R)} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite) :
    T.X₃.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite.{u, v, r, m} R).prop_of_isColimit_cokernelCofork hT.gIsCokernel h₁ h₂

/-- **Stacks 03M1(3), kernels, from Stacks 03M1(4).**  If quasi-coherence of modules on a site
passes to the sub-object of a short exact sequence and is closed under cokernels, then it is
closed under kernels.

The kernel of `f : M ⟶ N` is the sub-object of the short exact sequence whose quotient is the
coimage of `f`, and the coimage is isomorphic to the image, which is in turn the sub-object of
the short exact sequence whose middle term is `N` and whose quotient is the cokernel of `f`. -/
theorem isClosedUnderKernels_isQuasicoherentOnSite
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderCokernels]
    (h : ∀ T : ShortComplex (SheafOfModules.{m} R), T.ShortExact →
      T.X₂.IsQuasicoherentOnSite → T.X₃.IsQuasicoherentOnSite → T.X₁.IsQuasicoherentOnSite) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine IsQuasicoherentOnSite.of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk) ?_
    have hcoker : (cokernel f).IsQuasicoherentOnSite :=
      (isQuasicoherentOnSite.{u, v, r, m} R).prop_cokernel f hM hN
    have himage : (kernel (cokernel.π f)).IsQuasicoherentOnSite :=
      h _ (Abelian.shortExact_image f) hN hcoker
    have hcoimage : (cokernel (kernel.ι f)).IsQuasicoherentOnSite :=
      IsQuasicoherentOnSite.of_iso (Abelian.coimageIsoImage f).symm himage
    exact h _ (Abelian.shortExact_coimage f) hM hcoimage

/-- **Stacks 03M1(3), cokernels, from Stacks 03M1(4).**  If quasi-coherence of modules on a site
passes to the quotient of a short exact sequence and is closed under kernels, then it is closed
under cokernels.

The cokernel of `f : M ⟶ N` is the quotient of the short exact sequence whose sub-object is the
image of `f`, and the image is isomorphic to the coimage, which is in turn the quotient of the
short exact sequence whose sub-object is the kernel of `f` and whose middle term is `M`. -/
theorem isClosedUnderCokernels_isQuasicoherentOnSite
    [(isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderKernels]
    (h : ∀ T : ShortComplex (SheafOfModules.{m} R), T.ShortExact →
      T.X₁.IsQuasicoherentOnSite → T.X₂.IsQuasicoherentOnSite → T.X₃.IsQuasicoherentOnSite) :
    (isQuasicoherentOnSite.{u, v, r, m} R).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine IsQuasicoherentOnSite.of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk) ?_
    have hker : (kernel f).IsQuasicoherentOnSite :=
      (isQuasicoherentOnSite.{u, v, r, m} R).prop_kernel f hM hN
    have hcoimage : (cokernel (kernel.ι f)).IsQuasicoherentOnSite :=
      h _ (Abelian.shortExact_coimage f) hker hM
    have himage : (kernel (cokernel.π f)).IsQuasicoherentOnSite :=
      IsQuasicoherentOnSite.of_iso (Abelian.coimageIsoImage f) hcoimage
    exact h _ (Abelian.shortExact_image f) himage hN

end Abelian

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 03M1(4), the sub-object, on an algebraic space.**  In a short exact sequence of
`𝒪_F`-modules, if the middle term and the quotient are quasi-coherent then so is the
sub-object, granted closure of quasi-coherence under kernels. -/
theorem isQuasicoherentOnSite_X₁_of_shortExact
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels]
    {T : ShortComplex (Modules.{u, u} B S hS F hF)} (hT : T.ShortExact)
    (h₂ : T.X₂.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) :
    T.X₁.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.X₁_of_shortExact hT h₂ h₃

/-- **Stacks 03M1(4), the quotient, on an algebraic space.**  In a short exact sequence of
`𝒪_F`-modules, if the sub-object and the middle term are quasi-coherent then so is the
quotient, granted closure of quasi-coherence under cokernels. -/
theorem isQuasicoherentOnSite_X₃_of_shortExact
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels]
    {T : ShortComplex (Modules.{u, u} B S hS F hF)} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite) :
    T.X₃.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.X₃_of_shortExact hT h₁ h₂

end AlgebraicGeometry.Space

end
