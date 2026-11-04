module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# Kernels and cokernels of quasi-coherent modules on an algebraic space

Stacks 03M1(3) asserts that the kernel and the cokernel of a morphism of quasi-coherent
`𝒪_X`-modules on an algebraic space `X` are quasi-coherent.  Both halves are statements about a
fixed universe of module sections, and the passage between two such universes is formal: raising
the universe of the sections of a sheaf of modules both preserves and reflects quasi-coherence,
so the clause at one universe of sections gives the clause at another as soon as the lift carries
the limit or colimit in question to the corresponding one.

For kernels that is automatic, because limits of sheaves of modules are computed on sections;
this is `SheafOfModules.isClosedUnderKernels_isQuasicoherentOnSite_of_ulift`.  For cokernels the
lift has to be known to preserve finite colimits, which it does where presheaves of abelian
groups with sections in the lower universe sheafify, and that condition is carried here as an
instance argument.  On the small étale ringed site of an algebraic space it holds in the universe
of the schemes, and also in every universe containing the objects of the site.

## Main results

* `SheafOfModules.isClosedUnderCokernels_isQuasicoherentOnSite_of_ulift`: **closure of
  quasi-coherence under cokernels descends the universe of the module sections.**
* `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_above` and
  `AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_above`: the two
  sheafification conditions on the small étale ringed site of an algebraic space in every
  universe of module sections containing the objects of the site.  With them the
  `𝒪_F`-modules with sections in such a universe form an abelian category, and in particular
  every morphism between them has a kernel and a cokernel.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_isClosedUnderCokernels`: the
  cokernel of a morphism of quasi-coherent `𝒪_F`-modules with sections in the universe of the
  schemes is quasi-coherent, granted the cokernel clause for sections in the universe containing
  the objects of the small étale site.

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, the universe-flexible form of
Stacks 03DL(6), and the closure properties are Mathlib's
`CategoryTheory.ObjectProperty.IsClosedUnderKernels` and
`CategoryTheory.ObjectProperty.IsClosedUnderCokernels` for the object property
`SheafOfModules.isQuasicoherentOnSite`; nothing is restated.

The cokernel reduction is shorter than the kernel one because
`CategoryTheory.ObjectProperty.IsClosedUnderCokernels` is phrased for a cokernel cofork
specified by its universal property: the universe lift of the sections carries that cofork to one
of the lifted morphism, and no cokernel object has to be named.  The two sheafification
conditions in the lower universe are exactly what makes that lift preserve finite colimits.

In the universe of the schemes the two conditions on the small étale ringed site of an algebraic
space are those of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`, which rest on essential
smallness of the site there.  In a universe containing the objects of the site they need no
property of the site at all: presheaves of abelian groups valued in any universe containing that
of a site sheafify, by transport along a small model.

## What is not proved

Closure of quasi-coherence under cokernels is a hypothesis below, not a theorem, and no
`@[stacks 03M1]` tag is therefore carried.  Clause (3) of Stacks 03M1 is the content of
Stacks 0GNB(3), whose proof is not formal: a presentation of a cokernel is assembled from
presentations of the source and the target of the morphism, and the step that does not follow
from those is that the generators of the source lift along the presentation of the target.  Over
an affine object that lift is the vanishing of the first cohomology of a quasi-coherent module on
an affine scheme, Stacks 03DW, which the proof of Stacks 0GNB routes through the equivalence of
Stacks 03DX between quasi-coherent modules on a scheme and on its small étale site.  The
reduction of the lift to that surjectivity is
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app`; once
Stacks 03DW and Stacks 03DX are available on the small étale site, the hypothesis below becomes a
theorem and the statement becomes the cokernel half of Stacks 03M1(3) outright.

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

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **Closure of quasi-coherence under cokernels descends the universe of the module sections.**
Raising the universe of the sections is a functor preserving zero morphisms and finite colimits,
so it carries a cokernel cofork to a cokernel cofork, and it both preserves and reflects
quasi-coherence; hence a cokernel of a morphism of quasi-coherent modules with sections in
`Type (max r m)` is quasi-coherent as soon as this is known for modules with sections in the
universe containing the site, the coefficient rings and `Type m`.

This is the cokernel counterpart of
`SheafOfModules.isClosedUnderKernels_isQuasicoherentOnSite_of_ulift`.  Unlike that statement it
asks for sheafification of presheaves of abelian groups with sections in `Type (max r m)`, since
that is what makes the universe lift preserve a cokernel; limits, by contrast, are computed on
sections over every site. -/
theorem isClosedUnderCokernels_isQuasicoherentOnSite_of_ulift
    [HasWeakSheafify J AddCommGrpCat.{max r m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    (h : (isQuasicoherentOnSite.{u, v, r, max u v r m} R).IsClosedUnderCokernels) :
    (isQuasicoherentOnSite.{u, v, r, max r m} R).IsClosedUnderCokernels where
  cokernels_le := by
    have := h
    have _ : HasSheafify J AddCommGrpCat.{max u v r m} :=
      GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, u} J
    have _ : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
      AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m, u, v} J
    have _ : PreservesFiniteColimits
        (uliftForPresentationFunctor.{u, v, r, max r m, max u v r} (R := R)) :=
      preservesFiniteColimits_uliftForPresentationFunctor.{u, v, r, m, max u v r}
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine IsQuasicoherentOnSite.of_uliftForPresentation.{u, v, r, max r m} ?_
    exact (isQuasicoherentOnSite.{u, v, r, max u v r m} R).prop_of_isColimit_cokernelCofork
      (isColimitCoforkMapOfIsColimit'
        (uliftForPresentationFunctor.{u, v, r, max r m, max u v r} (R := R)) k.condition
        (hk.ofIsoColimit (Cofork.ext (Iso.refl _) (by simp))))
      (isQuasicoherentOnSite_uliftForPresentation hM)
      (isQuasicoherentOnSite_uliftForPresentation hN)

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Presheaves of abelian groups whose sections lie in a universe containing the
objects of the small étale site of an algebraic space have sheafifications.

The content is `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`; this restates it
for the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does
not unfold.  In the universe of the schemes the finer statement is
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify`, which rests on essential smallness of
the site there. -/
instance (priority := low) smallEtaleRingedSite_hasSheafify_above :
    HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{max (u + 1) m} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max (u + 1) m, u, u + 1} _

/-- With sections in a universe containing the objects of the small étale site of an algebraic
space, the local equivalences of presheaves of abelian groups are exactly the locally
bijective morphisms.

The content is `AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`; this
restates it for the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
instance (priority := low) smallEtaleRingedSite_wEqualsLocallyBijective_above :
    ((smallEtaleRingedSite B S hS F hF).J).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) m} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max (u + 1) m, u + 1, u} _

/-- **The cokernel half of Stacks 03M1(3) for module sections in the universe of the schemes.**
The cokernel of a morphism of quasi-coherent `𝒪_F`-modules on an algebraic space `F` is
quasi-coherent, granted the same closure property for modules whose sections lie in the universe
containing the objects of the small étale site.

Raising the universe of the sections carries a presenting cokernel cofork to a cokernel cofork
and the statement descends; the cokernel itself exists because presheaves of abelian groups on
the small étale site sheafify in the universe of the schemes. -/
theorem isQuasicoherentOnSite_cokernel_of_isClosedUnderCokernels
    (h : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels)
    {M N : Modules.{u, u} B S hS F hF} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N) : (cokernel f).IsQuasicoherentOnSite :=
  have := SheafOfModules.isClosedUnderCokernels_isQuasicoherentOnSite_of_ulift.{u + 1, u, u, u}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) h
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))).prop_cokernel f hM hN

end AlgebraicGeometry.Space

end
