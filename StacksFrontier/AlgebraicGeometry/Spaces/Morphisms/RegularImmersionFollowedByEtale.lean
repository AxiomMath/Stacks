module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionEtale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Immersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified

/-!
# A regular immersion of schemes followed by an étale morphism of algebraic spaces

Let `X` be an algebraic space over a scheme `S` of the big fppf site, let `W` be an object of the
site with an étale morphism `φ : W ⟶ X` of algebraic spaces, and let `i : Z ⟶ W` be a morphism of
the site whose underlying morphism of schemes is a regular immersion. This file shows that the
composite `Z ⟶ X` is **unramified and a local complete intersection morphism** of algebraic
spaces.

This is the seventh step of the proof of Stacks 06DA, where `W` is an affine étale chart of the
fibre `X_y` of the 1-morphism and `Z` is the regular slice cut out of it; the conclusion is
exactly the condition defining the local complete intersection locus of Stacks 06CJ.

Each half is a two-link chain of results already in the library. On the unramified side a
regular immersion of schemes is an immersion, hence unramified, and an étale morphism of
algebraic spaces is unramified (Stacks 06CR), and unramifiedness is stable under composition
(Stacks 03ZI). On the local-complete-intersection side a regular immersion of schemes is a local
complete intersection morphism (Stacks 069L), an étale morphism of algebraic spaces is one as
well — being syntomic, by Stacks 06CP and Stacks 06C9 — and the property is stable under
composition (Stacks 06C8).

## Main results

* `AlgebraicGeometry.Space.isUnramified_yoneda_map`: **Stacks 03ML for unramifiedness**, a
  morphism of the site whose underlying morphism of schemes is unramified is an unramified
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isLocalCompleteIntersection_yoneda_map`: the same for local complete
  intersection morphisms.
* `AlgebraicGeometry.Space.isLocalCompleteIntersection_of_isEtale`: **Stacks 06CP and 06C9**, an
  étale morphism of algebraic spaces is a local complete intersection morphism.
* `AlgebraicGeometry.Space.isUnramified_yoneda_map_comp_of_isRegularImmersion` and
  `AlgebraicGeometry.Space.isLocalCompleteIntersection_yoneda_map_comp_of_isRegularImmersion`:
  the two conclusions for the composite.

## Implementation notes

The two transfer results from schemes to algebraic spaces are instances of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map`, which needs only that the property
of scheme morphisms be étale local on the source and the target; for unramifiedness that is
`AlgebraicGeometry.unramified_isEtaleLocalOnSourceAndTarget` and for the Koszul property it is
`AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism` applied to
Stacks 069P for étale coverings.

That an étale morphism of algebraic spaces is a local complete intersection morphism is proved
chartwise rather than through
`AlgebraicGeometry.Space.isSyntomic_iff_isFlat_and_isLocalCompleteIntersection` and
`AlgebraicGeometry.Space.isSyntomic_of_isSmooth`, because the scheme morphism in a commuting square
of étale charts of an étale morphism is itself étale
(`AlgebraicGeometry.Space.etale_of_comp_etale_chart`) and is therefore syntomic directly; this
avoids producing the smoothness of the morphism of algebraic spaces as an intermediate step.

The source and the middle object of the composite are objects of the site, so their
algebraic-space hypotheses are supplied by Stacks 025Z
(`AlgebraicGeometry.isAlgebraicSpace_yoneda`) and are not arguments below; only the target
carries one.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03ZI](https://stacks.math.columbia.edu/tag/03ZI)
* [Stacks Project, Tag 069L](https://stacks.math.columbia.edu/tag/069L)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
* [Stacks Project, Tag 06C8](https://stacks.math.columbia.edu/tag/06C8)
* [Stacks Project, Tag 06C9](https://stacks.math.columbia.edu/tag/06C9)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CP](https://stacks.math.columbia.edu/tag/06CP)
* [Stacks Project, Tag 06CQ](https://stacks.math.columbia.edu/tag/06CQ)
* [Stacks Project, Tag 06CR](https://stacks.math.columbia.edu/tag/06CR)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
-/

@[expose] public section

open CategoryTheory

open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transfer from the site to algebraic spaces -/

/-- **Stacks 03ML for unramifiedness.** A morphism of the big fppf site of `S` whose underlying
morphism of schemes is unramified is an unramified morphism of algebraic spaces over `S`.
Unramifiedness of scheme morphisms is étale local on the source and the target, so the
every-chart condition of Stacks 03MJ holds. -/
theorem isUnramified_yoneda_map {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : Unramified ((BigFppfOver.toScheme B S hS).map k)) :
    IsUnramified B S hS (yoneda.map k) :=
  holdsOnEveryEtaleChart_yoneda_map B S hS unramified_isEtaleLocalOnSourceAndTarget k hk

/-- **Stacks 03ML for local complete intersection morphisms.** A morphism of the big fppf site of
`S` whose underlying morphism of schemes is a local complete intersection morphism is a local
complete intersection morphism of algebraic spaces over `S`. The Koszul property of scheme
morphisms is étale local on the source and the target by Stacks 069P. -/
theorem isLocalCompleteIntersection_yoneda_map {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : IsLocalCompleteIntersectionMorphism ((BigFppfOver.toScheme B S hS).map k)) :
    IsLocalCompleteIntersection B S hS (yoneda.map k) :=
  holdsOnEveryEtaleChart_yoneda_map B S hS
    (isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism
      isLocalCompleteIntersectionMorphism_isLocalAtSource_etale) k hk

/-- **Stacks 06CP and Stacks 06C9.** An étale morphism of algebraic spaces over `S` is a local
complete intersection morphism.

In a commuting square of étale charts the morphism of schemes on top is étale, hence syntomic by
Stacks 01UG, hence a local complete intersection morphism by Stacks 069K. Nothing is asked of
the target. -/
theorem isLocalCompleteIntersection_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (hf : IsEtale B S hS f) :
    IsLocalCompleteIntersection B S hS f := by
  intro U V a b h ha hb hcomm
  have : Etale ((BigFppfOver.toScheme B S hS).map h) :=
    etale_of_comp_etale_chart B S hS (hf U a ha) hb hcomm
  exact ((syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism _).mp
    (syntomic_of_etale _)).2

/-! ### The composite -/

/-- **A regular immersion of schemes followed by an étale morphism of algebraic spaces is
unramified.** A regular immersion is in particular an immersion, hence unramified as a morphism
of schemes and so as a morphism of algebraic spaces; an étale morphism of algebraic spaces is
unramified by Stacks 06CR; and unramifiedness is stable under composition by Stacks 03ZI. -/
theorem isUnramified_yoneda_map_comp_of_isRegularImmersion
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Z W : BigFppfOver B S hS} (i : Z ⟶ W)
    [_root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map i)]
    (φ : yoneda.obj W ⟶ X) (hφ : IsEtale B S hS φ) :
    IsUnramified B S hS (yoneda.map i ≫ φ) :=
  isUnramified_comp B S hS (isAlgebraicSpace_yoneda B S hS Z)
    (isAlgebraicSpace_yoneda B S hS W) hX (yoneda.map i) φ
    (isUnramified_yoneda_map B S hS i (unramified_of_isImmersion _))
    (isUnramified_of_isEtale B S hS hφ)

/-- **A regular immersion of schemes followed by an étale morphism of algebraic spaces is a local
complete intersection morphism.** A regular immersion of schemes is a local complete intersection
morphism by Stacks 069L, hence so is the induced morphism of algebraic spaces; an étale morphism
of algebraic spaces is one by Stacks 06CP and Stacks 06C9; and the property is stable under
composition by Stacks 06C8. -/
theorem isLocalCompleteIntersection_yoneda_map_comp_of_isRegularImmersion
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {Z W : BigFppfOver B S hS} (i : Z ⟶ W)
    [_root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map i)]
    (hi : IsRegularImmersion ((BigFppfOver.toScheme B S hS).map i))
    (φ : yoneda.obj W ⟶ X) (hφ : IsEtale B S hS φ) :
    IsLocalCompleteIntersection B S hS (yoneda.map i ≫ φ) :=
  isLocalCompleteIntersection_comp B S hS (isAlgebraicSpace_yoneda B S hS Z)
    (isAlgebraicSpace_yoneda B S hS W) hX (yoneda.map i) φ
    (isLocalCompleteIntersection_yoneda_map B S hS i
      (isLocalCompleteIntersectionMorphism_of_isRegularImmersion _ hi))
    (isLocalCompleteIntersection_of_isEtale B S hS hφ)

end AlgebraicGeometry.Space

end
