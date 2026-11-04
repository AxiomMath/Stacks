module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalEtaleRestrictionSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceImmersionFirstMapComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceImmersionMiddleExactness
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness at the middle term of the conormal sequence of a general immersion

[Stacks Project, Tag 05ZA] attaches to an **immersion** `i : Z ⟶ X` of algebraic spaces over `B`
with structure morphism `b : X ⟶ Bb` the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
and asserts that it is exact.  This file proves **exactness at the middle term for an arbitrary
immersion**, which completes the tag.

The source's proof replaces `X` by the open subspace `X ∖ ∂Z` of [Stacks Project, Tag 04CE], in
which the immersion becomes a closed immersion, and transports the closed case back along the
étale inclusion of that open subspace.  Both halves of the transport are now available: the
closed case at the ambient open is
`AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion`, and the comparison
of the two first arrows across the étale inclusion is
`AlgebraicGeometry.Space.kernelConormalFirstMap_etaleAmbient`.  What is carried out here is the
assembly: the two sequences are compared by an isomorphism of short complexes, so exactness
transfers by `CategoryTheory.ShortComplex.exact_iff_of_iso`.

## Main results

* `AlgebraicGeometry.Space.kernelIdealSquareMapIsoOfEtale`: the map of kernel ideal sheaves of a
  cartesian square whose transverse morphism is étale, as an isomorphism.
* `AlgebraicGeometry.Space.kernelIdealEtaleAmbientIso`: the comparison `ι^*𝓘_{i₀ ≫ ι} ≅ 𝓘_{i₀}`
  of the kernel ideal sheaves along the étale inclusion of the ambient open subspace, with its
  pinning `AlgebraicGeometry.Space.kernelIdealEtaleAmbientIso_hom_comp_ι`.
* `AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion_etaleAmbient`:
  exactness of the sequence written out of the kernel ideal sheaf, for a closed immersion
  followed by an étale morphism whose square is cartesian.
* `AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isImmersion`: the same for an
  arbitrary immersion, through the factorisation of [Stacks Project, Tag 04CE].
* `AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact`: **exactness at the middle term of
  the conormal sequence of [Stacks Project, Tag 05ZA], for an arbitrary immersion**, at the
  tag's own first arrow `AlgebraicGeometry.Space.conormalSequenceFirstMapOfImmersion`.

## Implementation notes

The three legs of the comparison of short complexes are isomorphisms of their own, so no
`CategoryTheory.IsIso` is ever inferred:

* the left leg is the comparison of inverse images of [Stacks Project, Tag 03LU] followed by the
  inverse image of `AlgebraicGeometry.Space.kernelIdealEtaleAmbientIso`.  The latter is the map
  of [Stacks Project, Tag 03LW] attached to the cartesian square, which is invertible because
  its transverse morphism is étale — that is
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow`,
  read in degree one and transported onto the kernel ideal sheaves themselves;
* the middle leg is the comparison of inverse images followed by the inverse image of the
  étale-source localisation of [Stacks Project, Tag 04CU];
* the right leg is the identity: `(i₀ ≫ ι) ≫ b` and `i₀ ≫ (ι ≫ b)` are the same morphism, so
  the two sequences have the same third term and no transport is needed there.

The first square is `AlgebraicGeometry.Space.kernelConormalFirstMap_etaleAmbient`.  The second
is the uniqueness clause of [Stacks Project, Tag 04CX],
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`: both composites are comparison maps
for the square whose top edge is `i₀ ≫ ι` and whose bottom edge is an identity, one by
[Stacks Project, Tag 05Z7] and one by definition.

Two points of elaboration:

* the whole assembly is carried at plain variables, with the factorisation entering only as an
  equality `i₀ ≫ ι = i` of morphisms which the engine `subst`s away.  At the geometric
  instantiation the `subst` is unavailable and the identification of `(i₀ ≫ ι) ≫ b` with
  `i₀ ≫ (ι ≫ b)` would be requested at the terms of [Stacks Project, Tag 04CE];
* the exactness being transported is named in a `have` **before**
  `CategoryTheory.ShortComplex.exact_iff_of_iso` is applied, so that the target short complex is
  fixed when the comparison isomorphism is elaborated; with the isomorphism written inside the
  `refine` the elaborator postpones and exhausts the heartbeat budget.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 05Z7](https://stacks.math.columbia.edu/tag/05Z7)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The comparison of kernel ideal sheaves of a cartesian square with étale transverse edge -/

section Square

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X Z ZU : AlgebraicSpaces B S hS}

/-- **The map of kernel ideal sheaves attached to a cartesian square whose transverse morphism is
étale is an isomorphism**, in every degree.

It is the comparison of the inverse image of modules with the étale restriction of modules,
followed by the equality of the étale restriction of `Ker(i^♯)ⁿ` with `Ker(i_U^♯)ⁿ`; that the
composite is the map of [Stacks Project, Tag 03LW] attached to the square is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow`. -/
def kernelIdealSquareMapIsoOfEtale (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (modulePullback B S hS φ).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≅
      (kernelIdealSheafZPow B S hS iU n).toSheafOfModules :=
  (modulePullbackIsoEtaleModulePullback B S hS φ hφ).app
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules ≪≫
    eqToIso (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n)

/-- The forward map of `AlgebraicGeometry.Space.kernelIdealSquareMapIsoOfEtale` is the map of
[Stacks Project, Tag 03LW] attached to the square. -/
theorem kernelIdealSquareMapIsoOfEtale_hom (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (kernelIdealSquareMapIsoOfEtale B S hS p iU i φ sq hφ n).hom =
      kernelIdealSquareMap B S hS iU i p φ sq.w.symm n :=
  modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow B S hS p iU i φ sq hφ n

end Square

/-! ### The comparison of the kernel ideal sheaves along an étale ambient inclusion -/

section EtaleAmbient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb Z Amb : AlgebraicSpaces B S hS}

/-- **The pinning of a comparison of sheaves of ideals, read at an isomorphism transported along
equalities of the two ideals.**  `AlgebraicGeometry.Space.eqToHom_comp_comp_eqToHom_comp_ι` with
the comparison supplied as an isomorphism and the transports as `CategoryTheory.eqToIso`, which
is the shape an isomorphism of sheaves of ideals built by composing isomorphisms has.

Stated at plain variables: at a geometric instantiation the forward map of such a composite is
not syntactically a composite of forward maps, and rewriting it there runs into the
`AlgebraicGeometry.Space.Modules`-versus-`CategoryTheory.SheafOfModules` spelling of the
inverse image, where the rewrite motive is not type-correct. -/
theorem mapIso_trans_trans_eqToIso_hom_comp_ι (g : Amb ⟶ X)
    {I I' : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule}
    {J J' : (SheafOfModules.unit (structureRingSheaf B S hS Amb)).Submodule}
    (hI : I = I') (hJ : J = J')
    (hIo : I'.toSheafOfModules = I.toSheafOfModules)
    (hJo : J.toSheafOfModules = J'.toSheafOfModules)
    (e : (modulePullback B S hS g).obj I.toSheafOfModules ≅ J.toSheafOfModules)
    (he : e.hom ≫ J.ι =
      (modulePullback B S hS g).map I.ι ≫ structureModulePullbackMap B S hS g) :
    ((modulePullback B S hS g).mapIso (eqToIso hIo) ≪≫ e ≪≫ eqToIso hJo).hom ≫ J'.ι =
      (modulePullback B S hS g).map I'.ι ≫ structureModulePullbackMap B S hS g :=
  eqToHom_comp_comp_eqToHom_comp_ι B S hS g hI hJ hIo hJo e.hom he

/-- **The comparison `ι^*𝓘_{i₀ ≫ ι} ≅ 𝓘_{i₀}` of the kernel ideal sheaves along an étale change
of ambient space**, for a cartesian square with `𝟙 Z` on top.

It is `AlgebraicGeometry.Space.kernelIdealSquareMapIsoOfEtale` in degree one, read at the kernel
ideal sheaves themselves rather than at their first powers through
`AlgebraicGeometry.Space.kernelIdealSheafZPow_one`; it is the invertible form of
`AlgebraicGeometry.Space.kernelIdealCompPullbackMap`, which is pinned by the same equation. -/
def kernelIdealEtaleAmbientIso (i₀ : Z ⟶ Amb) (ι : Amb ⟶ X)
    (sq : IsPullback (𝟙 Z) i₀ (i₀ ≫ ι) ι) (hι : IsEtale B S hS ι.hom) :
    (modulePullback B S hS ι).obj
        (kernelIdealSheaf B S hS (i₀ ≫ ι)).toSheafOfModules ≅
      (kernelIdealSheaf B S hS i₀).toSheafOfModules :=
  (modulePullback B S hS ι).mapIso (eqToIso (congrArg
      (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule ↦
        K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS (i₀ ≫ ι)).symm)) ≪≫
    kernelIdealSquareMapIsoOfEtale B S hS (𝟙 Z) i₀ (i₀ ≫ ι) ι sq hι 1 ≪≫
      eqToIso (congrArg
        (fun K : (SheafOfModules.unit (structureRingSheaf B S hS Amb)).Submodule ↦
          K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS i₀))

/-- **`AlgebraicGeometry.Space.kernelIdealEtaleAmbientIso` is pinned by pullback of regular
functions along `ι`.**  Followed by the inclusion `𝓘_{i₀} ⊆ 𝒪_Amb` it is the inverse image along
`ι` of the inclusion `𝓘_{i₀ ≫ ι} ⊆ 𝒪_X`, read in `𝒪_Amb` through
`AlgebraicGeometry.Space.structureModulePullbackMap`.

This is the hypothesis of `AlgebraicGeometry.Space.kernelConormalFirstMap_etaleAmbient`; the
pinning of the map of [Stacks Project, Tag 03LW] is
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι`, and the transport of a pinning onto equal
sheaves of ideals is `AlgebraicGeometry.Space.eqToHom_comp_comp_eqToHom_comp_ι`. -/
theorem kernelIdealEtaleAmbientIso_hom_comp_ι (i₀ : Z ⟶ Amb) (ι : Amb ⟶ X)
    (sq : IsPullback (𝟙 Z) i₀ (i₀ ≫ ι) ι) (hι : IsEtale B S hS ι.hom) :
    (kernelIdealEtaleAmbientIso B S hS i₀ ι sq hι).hom ≫ (kernelIdealSheaf B S hS i₀).ι =
      (modulePullback B S hS ι).map (kernelIdealSheaf B S hS (i₀ ≫ ι)).ι ≫
        structureModulePullbackMap B S hS ι :=
  mapIso_trans_trans_eqToIso_hom_comp_ι B S hS ι
    (kernelIdealSheafZPow_one B S hS (i₀ ≫ ι)) (kernelIdealSheafZPow_one B S hS i₀) _ _
    (kernelIdealSquareMapIsoOfEtale B S hS (𝟙 Z) i₀ (i₀ ≫ ι) ι sq hι 1)
    ((eq_whisker (kernelIdealSquareMapIsoOfEtale_hom B S hS (𝟙 Z) i₀ (i₀ ≫ ι) ι sq hι 1)
        (kernelIdealSheafZPow B S hS i₀ 1).ι).trans
      (kernelIdealSquareMap_comp_ι B S hS i₀ (i₀ ≫ ι) (𝟙 Z) ι sq.w.symm 1))

/-! ### Exactness at the kernel ideal sheaf -/

/-- **Exactness at the middle term of the conormal sequence written out of the kernel ideal
sheaf, for a closed immersion followed by an étale morphism.**  Let `i₀ : Z ⟶ Amb` be a closed
immersion, let `ι : Amb ⟶ X` be étale, let `i = i₀ ≫ ι`, and let the square with `𝟙 Z` on top,
`i₀` down the left, `i` down the right and `ι` along the bottom be cartesian.  Then for every
structure morphism `b : X ⟶ Bb` the short complex
```
  i^*𝓘_i ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B}
```
is exact at `i^*Ω_{X/B}`.

This is the open-subspace reduction of [Stacks Project, Tag 05ZA], carried out at plain
variables: the two short complexes at `i` and at `i₀` are compared by an isomorphism whose left
leg is `AlgebraicGeometry.Space.kernelIdealEtaleAmbientIso`, whose middle leg is the
étale-source localisation of [Stacks Project, Tag 04CU], and whose right leg is the identity. -/
theorem conormalSequenceKernel_exact_of_isClosedImmersion_etaleAmbient (i : Z ⟶ X)
    (i₀ : Z ⟶ Amb) (ι : Amb ⟶ X) (hi₀ : IsClosedImmersion B S hS i₀.hom)
    (hι : IsEtale B S hS ι.hom) (sq : IsPullback (𝟙 Z) i₀ i ι) (hfac : i₀ ≫ ι = i)
    (b : X ⟶ Bb) :
    (ShortComplex.mk _ _
      (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS i b)).Exact := by
  subst hfac
  have hex := conormalSequenceKernel_exact_of_isClosedImmersion B S hS i₀ hi₀ (ι ≫ b)
  have hfirst := kernelConormalFirstMap_etaleAmbient B S hS i₀ ι hι b
    (kernelIdealEtaleAmbientIso B S hS i₀ ι sq hι).hom
    (kernelIdealEtaleAmbientIso_hom_comp_ι B S hS i₀ ι sq hι)
  have hleft : IsSheafOfDifferentialsMap B S hS (i₀ ≫ ι) b (i₀ ≫ ι ≫ b)
      ((modulePullbackCompIso B S hS i₀ ι).inv.app (sheafOfDifferentials B S hS b) ≫
        (modulePullback B S hS i₀).map (etaleSourceLocalizationHom B S hS ι hι b) ≫
          pullbackDifferentialsMap B S hS i₀ (ι ≫ b)) :=
    isSheafOfDifferentialsMap_comp B S hS ι i₀ b (ι ≫ b) (i₀ ≫ ι ≫ b)
      (isSheafOfDifferentialsMap_etaleSourceLocalizationHom B S hS ι hι b)
      (isSheafOfDifferentialsMap_pullbackDifferentialsMap B S hS i₀ (ι ≫ b))
  have hright : IsSheafOfDifferentialsMap B S hS (i₀ ≫ ι) b (i₀ ≫ ι ≫ b)
      (pullbackDifferentialsMap B S hS (i₀ ≫ ι) b) :=
    isSheafOfDifferentialsMap_pullbackDifferentialsMap B S hS (i₀ ≫ ι) b
  have hsecond := eq_of_isSheafOfDifferentialsMap B S hS (i₀ ≫ ι) b (i₀ ≫ ι ≫ b) hleft hright
  refine (ShortComplex.exact_iff_of_iso ?_).mpr hex
  refine ShortComplex.isoMk
    (((modulePullbackCompIso B S hS i₀ ι).app
          (kernelIdealSheaf B S hS (i₀ ≫ ι)).toSheafOfModules).symm ≪≫
      (modulePullback B S hS i₀).mapIso (kernelIdealEtaleAmbientIso B S hS i₀ ι sq hι))
    (((modulePullbackCompIso B S hS i₀ ι).app (sheafOfDifferentials B S hS b)).symm ≪≫
      (modulePullback B S hS i₀).mapIso
        (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS ι hι b))
    (Iso.refl _) ?_ ?_
  · exact (Category.assoc _ _ _).trans (hfirst.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (hsecond.trans (Category.comp_id _).symm)

end EtaleAmbient

/-! ### Stacks 05ZA at an arbitrary immersion -/

section Immersion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb Z : AlgebraicSpaces B S hS}

/-- **Exactness at the middle term of the conormal sequence written out of the kernel ideal
sheaf, for an arbitrary immersion.**  For an immersion `i : Z ⟶ X` of algebraic spaces over `B`
with structure morphism `b : X ⟶ Bb` the short complex
```
  i^*𝓘_i ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B}
```
built from the kernel ideal sheaf `𝓘_i = ker(i♯)` is exact at `i^*Ω_{X/B}`.

This is
`AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion_etaleAmbient` at the
factorisation of [Stacks Project, Tag 04CE]: the closed factorisation
`AlgebraicGeometry.Space.immersionClosedFactorization`, the étale inclusion
`AlgebraicGeometry.Space.immersionAmbientInclusion` of the complement of the boundary, and the
cartesian square `AlgebraicGeometry.Space.isPullback_closedFactorization_ambientInclusion`
with `𝟙 Z` on top. -/
theorem conormalSequenceKernel_exact_of_isImmersion (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) (b : X ⟶ Bb) :
    (ShortComplex.mk _ _
      (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS i b)).Exact :=
  conormalSequenceKernel_exact_of_isClosedImmersion_etaleAmbient B S hS i
    (immersionClosedFactorization B S hS X.2 Z.2 i.hom hi)
    (immersionAmbientInclusion B S hS i hi)
    (isClosedImmersion_boundaryComplementLift B S hS X.2 Z.2 i.hom hi)
    (isEtale_immersionAmbientInclusion B S hS i hi)
    (isPullback_closedFactorization_ambientInclusion B S hS i hi)
    (immersionClosedFactorization_comp_immersionAmbientInclusion B S hS i hi) b

/-- **Stacks 05ZA, exactness at the middle term, for an arbitrary immersion.**  For an immersion
`i : Z ⟶ X` of algebraic spaces over `B` with structure morphism `b : X ⟶ B`, the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B}
```
built from the canonical first arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMapOfImmersion` and the second arrow
`AlgebraicGeometry.Space.pullbackDifferentialsMap` is exact at `i^*Ω_{X/B}`.

**No hypothesis beyond the immersion is carried.**  It is
`AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isImmersion` fed to
`AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact_of_kernelConormalFirstMap`, which
reads the first arrow out of the conormal module `𝒞_{Z/X}` of [Stacks Project, Tag 04CN] rather
than out of the kernel ideal sheaf; the two differ by the isomorphism
`AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso` of the left-hand terms. -/
@[stacks 05ZA "exactness at the middle term `i^*Ω_{X/B}`: the second arrow is a cokernel of the \
first, for an arbitrary immersion `i : Z ⟶ X`, at the tag's own first arrow \
`conormalSequenceFirstMapOfImmersion`.  Unconditional: the open-subspace reduction of the tag's \
own proof is carried out, through the factorisation of 04CE and the comparison of the two first \
arrows across the étale inclusion of the ambient open"]
theorem conormalSequenceOfImmersion_exact (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom)
    (b : X ⟶ Bb) :
    (ShortComplex.mk _ _
      (conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero
        B S hS i hi b)).Exact :=
  conormalSequenceOfImmersion_exact_of_kernelConormalFirstMap B S hS i hi b
    (conormalSequenceKernel_exact_of_isImmersion B S hS i hi b)

end Immersion

end AlgebraicGeometry.Space

end
