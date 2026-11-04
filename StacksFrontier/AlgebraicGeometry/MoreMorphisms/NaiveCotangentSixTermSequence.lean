module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentCohomologySheaves
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksCore.Tactic.StacksAttribute

/-!
# The right-hand end of the six term exact sequence of naive cotangent complexes

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` the naive cotangent complexes of `f`, of
`f ≫ g` and the pullback along `f` of the naive cotangent complex of `g` sit in a six term exact
sequence of cohomology sheaves

`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) ⟶ f^*Ω_{Y/Z} ⟶`
`Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0`,

whose last three terms are the degree `0` cohomology sheaves of the three complexes.

This file proves the right-hand end of that sequence.  Two things are needed.  First, the
sequence has six terms because all three complexes are concentrated in degrees `-1` and `0`;
for `NL_{X/Z}` and `NL_{X/Y}` that is [Stacks Project, Tag 0D0J] and is available, and the
remaining case `f^*NL_{Y/Z}` is proved below.  Second, the fourth term has to be identified:
`H^0(f^*NL_{Y/Z})` is `f^*Ω_{Y/Z}`, because the pullback of sheaves of modules along `f` is a
left adjoint and therefore preserves the cokernel that computes the degree `0` cohomology sheaf
of a complex with nothing above degree `0`.  Once the three degree `0` terms are so identified,
the exactness of the last three terms is the first exact sequence of relative differentials,
[Stacks Project, Tag 01UX].

The six term sequence itself is not proved here.  It is in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms`, with all five of
its arrows induced by the canonical maps of naive cotangent complexes of
[Stacks Project, Tag 0E1Z]: the two degree `-1` arrows, the connecting map, and the two degree
`0` arrows.  That file identifies its fourth term with `f^*Ω_{Y/Z}` by composing
`modulePullbackNaiveCotangentComplexHomologyZeroIso` below with
`RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep`, which identifies Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback` used here with the inverse-image-then-extend-scalars
model that the 08TM/0E1Z development is written over.

What this file adds to that is the exactness of the last three terms for the canonical maps of
relative differentials of [Stacks Project, Tag 01UX] rather than for the maps induced by the
canonical maps of complexes.  That the two descriptions of the arrow `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}`
agree is not proved, and neither file needs it.

## Main definitions

* `Stacks.NaiveCotangentSixTermSequence.modulePullbackNaiveCotangentComplex`: the complex
  `f^*NL_{Y/Z}`, the termwise pullback along `f` of the naive cotangent complex of `g`.
* `Stacks.NaiveCotangentSixTermSequence.mapHomologyZeroIso`: for an additive functor preserving
  finite colimits and a cochain complex with nothing in degree `1`, the degree `0` cohomology of
  the image complex is the image of the degree `0` cohomology.
* `Stacks.NaiveCotangentSixTermSequence.modulePullbackNaiveCotangentComplexHomologyZeroIso`: the
  fourth term of the sequence, `H^0(f^*NL_{Y/Z}) ≅ f^*Ω_{Y/Z}`.

## Main results

* `Stacks.NaiveCotangentSixTermSequence.isZero_homology_modulePullbackNaiveCotangentComplex`: the
  cohomology sheaves of `f^*NL_{Y/Z}` vanish outside degrees `-1` and `0`, which is what bounds
  the sequence.
* `Stacks.NaiveCotangentSixTermSequence.differentialsSequence_exact`: the last three terms
  `f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0` form an exact sequence.

## Implementation notes

`AlgebraicGeometry.Scheme.naiveCotangentComplex` is a complex of sheaves of modules in the
spelling `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf 𝒪_X)`, while
`AlgebraicGeometry.Scheme.Modules.pullback` is a functor between the `Scheme.Modules` spellings.
The two agree definitionally but not syntactically, and comparing them inside a composite of
isomorphisms forces the sheafification to unfold.  `mapHomologyZeroIso` is therefore stated for
an arbitrary additive functor between abelian categories and applied once, so that exactly one
comparison of the two spellings happens, at the application site, instead of once per component
of the composite.  For the same reason the exactness statement below is phrased on the sheaves
of relative differentials rather than on the degree `0` cohomology sheaves: the two are
identified by `modulePullbackNaiveCotangentComplexHomologyZeroIso` and by Stacks 0D0J, and
conjugating the statement by those identifications would put a composite of morphisms that cross
the two spellings into the statement itself.

The degree `0` cohomology sheaf of a complex concentrated in degrees `-1` and `0` is the
cokernel of its one nonzero differential; `homologyZeroIsoCokernelOfIsZeroXOne` records this by
composing `HomologicalComplex.isoHomologyι` with `ShortComplex.opcyclesIsoCokernel`.  It is this
description that the pullback functor is compatible with, since a left adjoint preserves
colimits but not in general kernels.

`f^*NL_{Y/Z}` is written here as the termwise image of `NL_{Y/Z}` under
`AlgebraicGeometry.Scheme.Modules.pullback`, the pullback of sheaves of modules along a morphism
of schemes.  The library's Stacks 08TM/0E1Z development writes the same pullback differently, as
the inverse image of `NL_{Y/Z}` with scalars extended to `𝒪_X`, and that model carries the name
`AlgebraicGeometry.Scheme.pullbackNaiveCotangentComplex` in
`StacksFrontier/AlgebraicGeometry/Scheme/NaiveCotangentBaseChangeHomology.lean`.  The two are
isomorphic but are not the same construction, and the names here are kept distinct from that
one's accordingly.  The module pullback is used here because it is the model whose compatibility
with degree `0` cohomology follows from its being a left adjoint, with no inverse-image theorem
in between.

## References

* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44)
* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX), the first exact
  sequence of relative differentials of a composable pair of morphisms of schemes.
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), the cohomology sheaves
  of the naive cotangent complex of a morphism of schemes.
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the canonical map to
  the shifted cone, on which the first three terms rest.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

namespace Stacks.NaiveCotangentSixTermSequence

/-! ### Degree zero cohomology and the image of a two term complex -/

section General

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- For a cochain complex with nothing in degree `1`, the degree `0` cohomology object is the
cokernel of the differential into degree `0`: the differential out of degree `0` is zero, so the
cohomology object is the degree `0` object of opcycles. -/
noncomputable def homologyZeroIsoCokernelOfIsZeroXOne (K : CochainComplex C ℤ)
    (h : IsZero (K.X 1)) :
    K.homology 0 ≅ cokernel (K.d (-1) 0) :=
  K.isoHomologyι 0 1 (by simp) (h.eq_of_tgt _ _) ≪≫
    K.opcyclesIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫ ShortComplex.opcyclesIsoCokernel _

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- An additive functor preserving finite colimits commutes with the degree `0` cohomology of a
cochain complex that has nothing in degree `1`: both are computed by the cokernel of the one
differential into degree `0`, and a colimit preserving functor carries that cokernel to the
corresponding one. -/
noncomputable def mapHomologyZeroIso (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) (h : IsZero (K.X 1)) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology 0 ≅ F.obj (K.homology 0) :=
  homologyZeroIsoCokernelOfIsZeroXOne _ (Functor.map_isZero F h) ≪≫
    (PreservesCokernel.iso F (K.d (-1) 0)).symm ≪≫
    F.mapIso (homologyZeroIsoCokernelOfIsZeroXOne K h).symm

end General

/-! ### The pullback of the naive cotangent complex -/

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The complex `f^*NL_{Y/Z}`: the naive cotangent complex of `g` pulled back along `f`, degree
by degree. -/
noncomputable abbrev modulePullbackNaiveCotangentComplex : CochainComplex X.Modules ℤ :=
  ((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (Scheme.naiveCotangentComplex g)

/-- `f^*NL_{Y/Z}` has no terms outside degrees `-1` and `0`: the pullback functor preserves zero
morphisms, so it carries the vanishing terms of `NL_{Y/Z}` to zero objects. -/
theorem isZero_modulePullbackNaiveCotangentComplex_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((modulePullbackNaiveCotangentComplex f g).X i) :=
  Functor.map_isZero _ (Scheme.naiveCotangentComplex_isZero_X g i hneg hzero)

/-- **Stacks 0E44, the extent of the sequence.** The cohomology sheaves of `f^*NL_{Y/Z}` vanish
outside degrees `-1` and `0`.  Together with the same statement for `NL_{X/Z}` and `NL_{X/Y}`
(`AlgebraicGeometry.Scheme.isZero_homology_naiveCotangentComplex`) this is why the sequence of
Stacks 0E44 has six terms, starting at `H^{-1}(f^*NL_{Y/Z})` and ending at `0` after the degree
`0` cohomology sheaf of `NL_{X/Y}`. -/
@[stacks 0E44 "the vanishing of H^i(f^*NL_{Y/Z}) outside degrees -1 and 0 only"]
theorem isZero_homology_modulePullbackNaiveCotangentComplex (i : ℤ) (hneg : i ≠ -1)
    (hzero : i ≠ 0) :
    IsZero ((modulePullbackNaiveCotangentComplex f g).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (isZero_modulePullbackNaiveCotangentComplex_X f g i hneg hzero)).isZero_homology

/-- **Stacks 0E44, the fourth term.** The degree `0` cohomology sheaf of `f^*NL_{Y/Z}` is
`f^*Ω_{Y/Z}`.  The pullback of sheaves of modules along `f` is a left adjoint, hence preserves
the cokernel that computes the degree `0` cohomology sheaf of a complex with nothing above
degree `0`, and `H^0(NL_{Y/Z})` is `Ω_{Y/Z}` by Stacks 0D0J. -/
@[stacks 0E44 "the fourth term for Mathlib's model of the pullback: the identification \
H^0(f^*NL_{Y/Z}) = f^*Omega_{Y/Z}, which \
Stacks.NaiveCotangentSixTermSequence.pullbackHomologyZeroIso carries to the model the sequence \
itself is written over"]
noncomputable def modulePullbackNaiveCotangentComplexHomologyZeroIso :
    (modulePullbackNaiveCotangentComplex f g).homology 0 ≅
      (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials g) :=
  mapHomologyZeroIso (Scheme.Modules.pullback f) (Scheme.naiveCotangentComplex g)
      (Scheme.naiveCotangentComplex_isZero_X g 1 (by decide) (by decide)) ≪≫
    (Scheme.Modules.pullback f).mapIso (Scheme.naiveCotangentComplexHomologyZeroIso g)

/-! ### The last three terms -/

/-- **Stacks 0E44, the last three terms.** For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`
the last three terms of the six term sequence of cohomology sheaves,

`f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0`,

form an exact sequence: the composite of the two canonical maps of relative differentials is
zero, the resulting short complex is exact at `Ω_{X/Z}`, and the second map is an epimorphism.
The three terms are the degree `0` cohomology sheaves of `f^*NL_{Y/Z}`, of `NL_{X/Z}` and of
`NL_{X/Y}`, by `modulePullbackNaiveCotangentComplexHomologyZeroIso` and by Stacks 0D0J. -/
@[stacks 0E44 "the last three terms and their exactness, for the canonical maps of relative \
differentials of 01UX; the six term sequence itself, with the arrows induced by the canonical \
maps of naive cotangent complexes throughout, is in \
StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms"]
theorem differentialsSequence_exact :
    ∃ h : Scheme.Hom.relativeDifferentialsMap f g (f ≫ g) (𝟙 Z)
        (Category.comp_id (f ≫ g)).symm ≫ f.toRelativeDifferentials g = 0,
      (ShortComplex.mk _ _ h).Exact ∧ Epi (f.toRelativeDifferentials g) := by
  obtain ⟨h, hexact⟩ := Scheme.Hom.toRelativeDifferentials_exact f g
  exact ⟨h, hexact, Scheme.Hom.toRelativeDifferentials_epi f g⟩

end Stacks.NaiveCotangentSixTermSequence

end
