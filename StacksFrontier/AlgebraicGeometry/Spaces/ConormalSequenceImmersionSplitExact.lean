module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceImmersionKernelExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceImmersionSplitMono
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 05ZB at an arbitrary immersion: the conormal sequence is split exact

[Stacks Project, Tag 05ZB] says: let `i : Z ⟶ X` be an **immersion** of algebraic spaces over
`Bb` and assume `i` (étale locally) has a left inverse; then the canonical sequence
```
  0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
of [Stacks Project, Tag 05ZA] is (étale locally) split exact.  This file proves both readings
**at an arbitrary immersion**, which is the generality the source states.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionSplitMono.lean` proves the same
two clauses at an arbitrary **closed** immersion, and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSplitMono.lean` at the inclusion of a
bundled `AlgebraicGeometry.Space.ClosedSubspaces`.  A closed immersion is a special case of an
immersion — and an immersion with a left inverse need not be a closed immersion, the affine line
with the origin doubled retracting onto one of its two charts being an immersion with a left
inverse whose image is open and not closed — so the step taken here is the open-subspace
reduction of the source's own proof, not a relabelling.

## The route

It is the route [Stacks Project, Tag 05ZA] is closed by in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionKernelExactness.lean`, run on the
splitting instead of on the exactness.  [Stacks Project, Tag 04CE] factors the immersion as a
closed immersion `i₀ : Z ⟶ Amb` into the open subspace `Amb = X ∖ ∂Z` followed by the étale
inclusion `ι : Amb ⟶ X`, with the square carrying `𝟙 Z` cartesian.  A left inverse `g : X ⟶ Z`
of `i` over `Bb` restricts to the left inverse `ι ≫ g : Amb ⟶ Z` of `i₀` over `Bb`, so
`AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting` applies at `i₀` over
`ι ≫ b`; and the two short complexes are isomorphic by the very isomorphism
`AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion_etaleAmbient`
compares them by, so the splitting transports along it by
`CategoryTheory.ShortComplex.Splitting.ofIso`.

Transporting the splitting rather than its three consequences separately is what keeps the
injectivity clause free: `CategoryTheory.ShortComplex.Splitting.mono_f` reads it off the
transported splitting, so no monomorphy statement has to be moved across the factorisation by
hand.

## Main results

* `AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting_etaleAmbient`:
  the sequence written out of the kernel ideal sheaf is split exact for a closed immersion
  followed by an étale morphism whose square is cartesian, given a left inverse of the composite.
* `AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting_of_isImmersion`: the same
  for an arbitrary immersion, through the factorisation of [Stacks Project, Tag 04CE].
* `AlgebraicGeometry.Space.nonempty_conormalSequenceOfImmersion_splitting`: **Stacks 05ZB's
  global clause at an arbitrary immersion**, at the tag's own first arrow
  `AlgebraicGeometry.Space.conormalSequenceFirstMapOfImmersion` out of the conormal module
  `𝒞_{Z/X}` of [Stacks Project, Tag 04CN].
* `AlgebraicGeometry.Space.nonempty_conormalSequenceOfImmersion_splitting_of_etale`:
  **Stacks 05ZB's étale-local clause at an arbitrary immersion.**

## Implementation notes

The assembly is carried at plain variables, the factorisation entering only as an equality
`i₀ ≫ ι = i` which the engine `subst`s away; at the geometric instantiation the identification
of `(i₀ ≫ ι) ≫ b` with `i₀ ≫ (ι ≫ b)` would otherwise be requested at the terms of
[Stacks Project, Tag 04CE].  As in the exactness assembly, the splitting being transported is
named in a `have` **before** the comparison isomorphism is written, so that the source short
complex is fixed when that isomorphism elaborates.

## References

* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the sequence.
* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the tag.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-! ### The splitting across an étale change of ambient space -/

section EtaleAmbient

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb Z Amb : AlgebraicSpaces B S hS}

/-- **Split exactness of the conormal sequence written out of the kernel ideal sheaf, for a
closed immersion followed by an étale morphism.**  Let `i₀ : Z ⟶ Amb` be a closed immersion, let
`ι : Amb ⟶ X` be étale, let `i = i₀ ≫ ι`, let the square with `𝟙 Z` on top, `i₀` down the left,
`i` down the right and `ι` along the bottom be cartesian, and let `g : X ⟶ Z` be a left inverse
of `i` over the base `b : X ⟶ Bb`.  Then the short complex
```
  i^*𝓘_i ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}
```
admits a `CategoryTheory.ShortComplex.Splitting`.

The left inverse restricts: `ι ≫ g` is a left inverse of `i₀` over `ι ≫ b`, so
`AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting` applies at `i₀`, and the
splitting is carried back along the comparison of the two short complexes of
`AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion_etaleAmbient` — whose
left leg is `AlgebraicGeometry.Space.kernelIdealEtaleAmbientIso`, whose middle leg is the
étale-source localisation of [Stacks Project, Tag 04CU], and whose right leg is the identity. -/
@[sga "6 VIII 2.2" "partial"]
theorem nonempty_conormalSequenceKernel_splitting_etaleAmbient (i : Z ⟶ X)
    (i₀ : Z ⟶ Amb) (ι : Amb ⟶ X) (hi₀ : IsClosedImmersion B S hS i₀.hom)
    (hι : IsEtale B S hS ι.hom) (sq : IsPullback (𝟙 Z) i₀ i ι) (hfac : i₀ ≫ ι = i)
    (b : X ⟶ Bb) (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z) (hgb : g ≫ i ≫ b = b) :
    Nonempty (ShortComplex.mk _ _
      (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS i b)).Splitting := by
  subst hfac
  have hg₀ : i₀ ≫ ι ≫ g = 𝟙 Z := (Category.assoc i₀ ι g).symm.trans hg
  have hg₀b : (ι ≫ g) ≫ i₀ ≫ ι ≫ b = ι ≫ b := by
    rw [Category.assoc, ← Category.assoc i₀ ι b, hgb]
  have hsp := nonempty_conormalSequenceKernel_splitting B S hS i₀ hi₀ (ι ≫ g) hg₀ (ι ≫ b) hg₀b
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
  refine ⟨hsp.some.ofIso (Iso.symm ?_)⟩
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

/-! ### Stacks 05ZB at an arbitrary immersion -/

section Immersion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb Z : AlgebraicSpaces B S hS}

/-- **Split exactness of the conormal sequence written out of the kernel ideal sheaf, for an
arbitrary immersion with a left inverse.**  For an immersion `i : Z ⟶ X` of algebraic spaces over
`Bb` with structure morphism `b : X ⟶ Bb`, and a left inverse `g : X ⟶ Z` of `i` over `Bb`, the
short complex
```
  i^*𝓘_i ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb}
```
built from the kernel ideal sheaf `𝓘_i = ker(i♯)` admits a
`CategoryTheory.ShortComplex.Splitting`.

This is
`AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting_etaleAmbient`
at the factorisation of [Stacks Project, Tag 04CE]: the closed factorisation
`AlgebraicGeometry.Space.immersionClosedFactorization`, the étale inclusion
`AlgebraicGeometry.Space.immersionAmbientInclusion` of the complement of the boundary, and the
cartesian square `AlgebraicGeometry.Space.isPullback_closedFactorization_ambientInclusion`
with `𝟙 Z` on top. -/
theorem nonempty_conormalSequenceKernel_splitting_of_isImmersion (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) (b : X ⟶ Bb) (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z)
    (hgb : g ≫ i ≫ b = b) :
    Nonempty (ShortComplex.mk _ _
      (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS i b)).Splitting :=
  nonempty_conormalSequenceKernel_splitting_etaleAmbient B S hS i
    (immersionClosedFactorization B S hS X.2 Z.2 i.hom hi)
    (immersionAmbientInclusion B S hS i hi)
    (isClosedImmersion_boundaryComplementLift B S hS X.2 Z.2 i.hom hi)
    (isEtale_immersionAmbientInclusion B S hS i hi)
    (isPullback_closedFactorization_ambientInclusion B S hS i hi)
    (immersionClosedFactorization_comp_immersionAmbientInclusion B S hS i hi) b g hg hgb

/-- **Stacks 05ZB, the global clause, at an arbitrary immersion.**  Let `i : Z ⟶ X` be an
immersion of algebraic spaces over `Bb` with structure morphism `b : X ⟶ Bb`, and let `g : X ⟶ Z`
be a left inverse of `i` over `Bb`.  Then the conormal sequence of [Stacks Project, Tag 05ZA]
```
  0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
is **split exact**: it admits a `CategoryTheory.ShortComplex.Splitting`, that is a retraction of
the first arrow and a section of the second summing to the identity — so in particular the first
arrow is a monomorphism, the sequence is exact at its middle term and the second arrow is a split
epimorphism.

The sequence is the one the tag states: the first arrow is
`AlgebraicGeometry.Space.conormalSequenceFirstMapOfImmersion`, whose source is the conormal
module `𝒞_{Z/X}` of [Stacks Project, Tag 04CN].  Nothing is assumed beyond the immersion and the
left inverse over `Bb`, which are the tag's own data: the splitting at the kernel-ideal reading is
`AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting_of_isImmersion`, and the two
short complexes differ by the isomorphism
`AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso` of their left-hand terms and
nothing else. -/
@[stacks 05ZB "the global clause at an arbitrary immersion `i : Z ⟶ X` having a left inverse \
over `B`: the conormal sequence of 05ZA is split exact, that is, it admits a \
`CategoryTheory.ShortComplex.Splitting`, so its first arrow is a monomorphism, it is exact at \
the middle term `i^*Ω_{X/B}` and its second arrow is a split epimorphism.  Stated at the tag's \
own first arrow `conormalSequenceFirstMapOfImmersion` out of the conormal module of 04CN, with \
no hypothesis beyond `IsImmersion` and the tag's own left inverse over `B`.  The source's \
open-subspace reduction is carried out: the immersion is factored through the open subspace of \
04CE, where it is closed and the restricted left inverse makes \
`nonempty_conormalSequenceKernel_splitting` apply, and the splitting is transported back along \
the comparison of the two sequences across the étale inclusion of that open"]
theorem nonempty_conormalSequenceOfImmersion_splitting (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) (b : X ⟶ Bb) (g : X ⟶ Z) (hg : i ≫ g = 𝟙 Z)
    (hgb : g ≫ i ≫ b = b) :
    Nonempty (ShortComplex.mk _ _
      (conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero
        B S hS i hi b)).Splitting := by
  have hsp := nonempty_conormalSequenceKernel_splitting_of_isImmersion B S hS i hi b g hg hgb
  refine ⟨hsp.some.ofIso (Iso.symm ?_)⟩
  refine ShortComplex.isoMk
    (conormalModuleOfImmersionKernelPullbackIso B S hS i hi) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [conormalSequenceFirstMapOfImmersion]
  · simp

end Immersion

/-! ### The étale-local clause -/

section EtaleLocal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W W' Zs Zs' Bb : AlgebraicSpaces B S hS}

/-- **Stacks 05ZB, the étale-local clause, at an arbitrary immersion.**  Let `i : Zs ⟶ W` be a
morphism of algebraic spaces over `Bb` with structure morphism `b : W ⟶ Bb`, let `φ : W' ⟶ W` be
étale, let `i' : Zs' ⟶ W'` be an arbitrary immersion and `a : Zs' ⟶ Zs` étale with
`i' ≫ φ = a ≫ i`, and let `g' : W' ⟶ Zs'` be a left inverse of `i'` over `Bb`.  Then

* the restricted conormal sequence, the sequence of [Stacks Project, Tag 05ZA] at `i'` over
  `φ ≫ b`, is split exact;
* the inverse image along `a` of the second arrow of the unrestricted sequence is a split
  epimorphism.

Étaleness is assumed of `φ` and of `a` separately rather than `Zs'` being assumed to be the
preimage of `Zs`, which is weaker: in the situation of the source `a` is a base change of `φ`.
**The unrestricted morphism `i` is free**: the split epimorphism clause is
`AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etale`, which assumes nothing
of `i` or `i'`, and the restricted sequence's splitting is
`AlgebraicGeometry.Space.nonempty_conormalSequenceOfImmersion_splitting` at `i'`. -/
@[stacks 05ZB "the étale-local clause at an arbitrary immersion: for an étale `φ : W' ⟶ W`, an \
immersion `i' : Zs' ⟶ W'` and an étale `a : Zs' ⟶ Zs` with `i' ≫ φ = a ≫ i`, the immersion `i'` \
having a left inverse over `B`, the restricted conormal sequence of 05ZA is split exact — it \
admits a `CategoryTheory.ShortComplex.Splitting`, so its first arrow is a monomorphism, it is \
exact at the middle term and its second arrow is a split epimorphism — and the inverse image \
along `a` of the second arrow of the unrestricted sequence is a split epimorphism too, which is \
where the étale-localization clause of 04CU is consumed.  Stated at the tag's own first arrow \
`conormalSequenceFirstMapOfImmersion`, with `IsImmersion` of `i'` and the étale-local data of \
the tag the only hypotheses; the unrestricted `i` is an arbitrary morphism"]
theorem nonempty_conormalSequenceOfImmersion_splitting_of_etale (i : Zs ⟶ W) (b : W ⟶ Bb)
    (φ : W' ⟶ W) (hφ : IsEtale B S hS φ.hom) (i' : Zs' ⟶ W')
    (hi' : IsImmersion B S hS i'.hom) (a : Zs' ⟶ Zs) (ha : IsEtale B S hS a.hom)
    (hsq : i' ≫ φ = a ≫ i) (g' : W' ⟶ Zs') (hg' : i' ≫ g' = 𝟙 Zs')
    (hg'b : g' ≫ i' ≫ φ ≫ b = φ ≫ b) :
    Nonempty (ShortComplex.mk _ _
          (conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero B S hS i'
            hi' (φ ≫ b))).Splitting ∧
      IsSplitEpi ((modulePullback B S hS a).map (pullbackDifferentialsMap B S hS i b)) :=
  ⟨nonempty_conormalSequenceOfImmersion_splitting B S hS i' hi' (φ ≫ b) g' hg' hg'b,
    isSplitEpi_map_pullbackDifferentialsMap_of_etale B S hS i b φ hφ i' a ha hsq g' hg' hg'b⟩

end EtaleLocal

end AlgebraicGeometry.Space

end
