module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealFibreSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjointPullPush
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingInverseImageKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafRingUnit

/-!
# The defining ideal sheaf of a closed subspace, read on the small étale site of the subspace

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S`, with inclusion
`i : Z ⟶ X` and defining ideal sheaf `𝓘 ⊆ 𝒪_X`.  This file transports `𝓘` along `i^{-1}` and
reads the result on sections:

**every section of `i^{-1}𝒪_X` over an object of the small étale site of `Z` that
`i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` kills is the image of a section of `i^{-1}𝓘`.**

No thickening hypothesis is used: only that `i` is a closed immersion, which every closed
subspace inclusion is.

## The three steps

1. **The fibre square.**  `AlgebraicGeometry.Space.mem_definingIdealAt_iff` describes `𝓘`
   sectionwise, as a membership, and a membership says nothing about a section of an inverse
   image.  What transports is the universal property, so the membership is first turned into a
   pullback square of sheaves of *sets*, exhibiting `𝓘` as the fibre of `i^♯ : 𝒪_X ⟶ i_*𝒪_Z`
   over the zero section.  That step is the abstract
   `Stacks.Sheaves.ToposPullback.isPullback_submoduleInclSheafSets`.
2. **Left exactness.**  The inverse image of a morphism of topoi preserves finite limits — it is
   the field `CategoryTheory.MorphismOfTopoi.preservesFiniteLimits` — so it carries that square
   to a square over the site of `Z`, and
   `Stacks.Sheaves.ToposPullback.existsUnique_sections_of_isPullback` reads the resulting square
   on sections.  What it produces is the kernel of the *inverse image* `i^{-1}(i^♯)` of the
   direct-image form of the structure map.
3. **The counit.**  The kernel wanted is that of the inverse-image form
   `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z`, and the two differ by the counit `i^{-1}i_*𝒪_Z ⟶ 𝒪_Z`: the
   inverse-image form is the inverse image of the direct-image form followed by that counit,
   which is `CategoryTheory.Adjunction.homEquiv_counit` for the ring-level adjunction
   `Stacks.Sheaves.ToposPushforward.ringImageAdjunction`.  For a closed immersion the counit is
   an **isomorphism**, by [Stacks Project, Tag 04E5], part (1)
   (`AlgebraicGeometry.Space.smallEtalePullbackPushforwardCounitIso`), hence injective on
   sections, so the two kernels agree.

That the counit is invertible is the same input as the full faithfulness of `i_*`; it is what
replaces, for a general closed subspace, the invertibility of the *unit* that the ideal
transport of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InverseImageKernelIdeal.lean` needs and that only
a thickening has.

## Main results

* `AlgebraicGeometry.Space.structureSharpRingInverseImage_eq_comp_ringCounit`: the inverse-image
  form of the structure map is the inverse image of the direct-image form followed by the
  counit.  For an arbitrary morphism of algebraic spaces.
* `AlgebraicGeometry.Space.injective_app_ringCounit`: for a closed immersion the counit at the
  structure sheaf is injective on sections.
* `AlgebraicGeometry.Space.app_pullbackRingSheafMap_structureSharp_eq_zero`: a section killed by
  the inverse-image form of the structure map is killed by the inverse image of the
  direct-image form.
* `AlgebraicGeometry.Space.isPullback_definingIdealSheaf`: **the defining ideal sheaf as a fibre
  square**, which is the presentation this development did not have.
* `AlgebraicGeometry.Space.exists_inverseImage_definingIdealSheaf_eq`: **the kernel of
  `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` on sections is the image of `i^{-1}𝓘`.**

## No tag is registered

The defining ideal sheaf is the kernel of the structure map by [Stacks Project, Tag 03MB], which
is where that is registered; reading it on the smaller site is a proof step towards exactness at
the middle term of [Stacks Project, Tag 05ZA], not a clause of either tag.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  as the kernel of the structure map.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1), the counit of
  a closed immersion of small étale topoi.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the two forms of the
  structure map.
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence,
  whose middle-exactness clause this serves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse-image form of the structure map through the counit -/

section Counit

variable {X Y : AlgebraicSpaces B S hS}

/-- **The inverse-image form of the structure map is the inverse image of the direct-image form
followed by the counit of `f^{-1} ⊣ f_*`.**

`AlgebraicGeometry.Space.structureSharpRingInverseImage` is defined as the adjunct of
`AlgebraicGeometry.Space.structureSharp` along the ring-level adjunction
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction`, and the inverse direction of an
adjunction bijection is `CategoryTheory.Adjunction.homEquiv_counit`. -/
theorem structureSharpRingInverseImage_eq_comp_ringCounit (f : X ⟶ Y) :
    structureSharpRingInverseImage B S hS f =
      pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
          (smallToposMorphismTypeU B S hS f).inverseImage (structureSharp B S hS f) ≫
        ringCounit (smallToposMorphismTypeU B S hS f) (structureRingSheaf B S hS X) :=
  Adjunction.homEquiv_counit (ringImageAdjunction (smallToposMorphismTypeU B S hS f))
    (structureRingSheaf B S hS Y) (structureRingSheaf B S hS X) (structureSharp B S hS f)

/-- **For a closed immersion the counit `f^{-1}f_*𝒪_X ⟶ 𝒪_X` is injective on sections.**

The counit of sheaves of sets along a closed immersion is an isomorphism by
[Stacks Project, Tag 04E5], part (1), and the underlying morphism of sheaves of sets of
`Stacks.Sheaves.ToposPushforward.ringCounit` is that counit on the nose
(`Stacks.Sheaves.ToposPushforward.ringSheafMap_ringCounit`), so its sections are a bijection. -/
theorem injective_app_ringCounit (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
    (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective ((ringCounit (smallToposMorphismTypeU B S hS f)
      (structureRingSheaf B S hS X)).hom.app W) :=
  fun _ _ h ↦ injective_sections_of_iso
    ((smallEtalePullbackPushforwardCounitIso B S hS f hf).app
      (Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X))) W h

/-- **A section of `f^{-1}𝒪_Y` killed by the inverse-image form of the structure map is killed by
the inverse image of the direct-image form**, for a closed immersion.

The two differ by the counit, by
`AlgebraicGeometry.Space.structureSharpRingInverseImage_eq_comp_ringCounit`, and the counit is
injective on sections and carries zero to zero, being a morphism of sheaves of rings. -/
theorem app_pullbackRingSheafMap_structureSharp_eq_zero (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : (structureRingSheafInverseImage B S hS f).obj.obj W)
    (ha : (structureSharpRingInverseImage B S hS f).hom.app W a = 0) :
    (pullbackRingSheafMap (SmallEtale.topology B S hS X.1)
        (smallToposMorphismTypeU B S hS f).inverseImage
        (structureSharp B S hS f)).hom.app W a = 0 := by
  refine injective_app_ringCounit B S hS f hf W ?_
  refine Eq.trans ?_ (((ringCounit (smallToposMorphismTypeU B S hS f)
    (structureRingSheaf B S hS X)).hom.app W).hom.map_zero).symm
  exact (congrArg (fun m : structureRingSheafInverseImage B S hS f ⟶
        structureRingSheaf B S hS X ↦ m.hom.app W a)
    (structureSharpRingInverseImage_eq_comp_ringCounit B S hS f)).symm.trans ha

end Counit

/-! ### The defining ideal sheaf as a fibre square, and its inverse image -/

section Ideal

variable {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The defining ideal sheaf of a closed subspace is the fibre of the structure map over the
zero section**, as a pullback square of sheaves of sets on the small étale site of `X`.

This is the presentation of `𝓘` that carries along a left exact functor, and it is the abstract
`Stacks.Sheaves.ToposPullback.isPullback_submoduleInclSheafSets` fed with the sectionwise
membership criterion `AlgebraicGeometry.Space.mem_definingIdealAt_iff`. -/
theorem isPullback_definingIdealSheaf :
    IsPullback (submoduleInclSheafSets (definingIdealSheaf B S hS X Z)) (terminal.from _)
      (structureSharpSet B S hS (subspaceInclusion B S hS X Z))
      (Sheaf.ringZeroHom
        (structureRingSheafDirectImage B S hS (subspaceInclusion B S hS X Z))) :=
  isPullback_submoduleInclSheafSets (structureSharp B S hS (subspaceInclusion B S hS X Z))
    (definingIdealSheaf B S hS X Z) (mem_definingIdealAt_iff B S hS X Z)

/-- **Every section of `i^{-1}𝒪_X` killed by `i^♯ : i^{-1}𝒪_X ⟶ 𝒪_Z` is the image of a section of
`i^{-1}𝓘`**, for an arbitrary closed subspace `Z ⊆ X`.

The fibre square `AlgebraicGeometry.Space.isPullback_definingIdealSheaf` is carried along
`i^{-1}`, which preserves finite limits, and read on sections by
`Stacks.Sheaves.ToposPullback.existsUnique_sections_of_isPullback`; the hypothesis it is fed is
`AlgebraicGeometry.Space.app_pullbackRingSheafMap_structureSharp_eq_zero`, which is where the
counit of the closed immersion identifies the kernel of `i^♯` with the kernel of `i^{-1}(i^♯)`.

The section of `i^{-1}𝓘` is in fact unique, since the square is a pullback; only its existence
is recorded, because that is what the vanishing of a derivation needs. -/
theorem exists_inverseImage_definingIdealSheaf_eq
    (W : (SmallEtale B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (a : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS X Z)).obj.obj W)
    (ha : (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS X Z)).hom.app W a = 0) :
    ∃ m : (Sheaf.sectionsFunctor
        (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) W).obj
        ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage.obj
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
            (definingIdealSheaf B S hS X Z).toSheafOfModules)),
      (Sheaf.sectionsFunctor
          (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) W).map
        ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage.map
          (submoduleInclSheafSets (definingIdealSheaf B S hS X Z))) m = a :=
  (existsUnique_sections_of_isPullback
      (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage
      (structureSharp B S hS (subspaceInclusion B S hS X Z)) _
      (isPullback_definingIdealSheaf B S hS Z) W a
      (app_pullbackRingSheafMap_structureSharp_eq_zero B S hS
        (subspaceInclusion B S hS X Z) Z.2.2 W a ha)).exists

end Ideal

end AlgebraicGeometry.Space

end
