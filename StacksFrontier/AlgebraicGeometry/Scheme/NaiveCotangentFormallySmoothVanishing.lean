module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallySmooth
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegs
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# The vanishing of `H⁻¹(NL_{X/S})` for a formally smooth morphism

[Stacks, Tag 0D0L] characterises formal smoothness of a morphism of schemes `f : X ⟶ S` by two
conditions on its naive cotangent complex: the vanishing `H⁻¹(NL_{X/S}) = 0`, and local
projectivity of `H⁰(NL_{X/S}) = Ω_{X/S}`. This file proves the **necessity of the first
condition**: for a formally smooth `f` the degree `-1` cohomology sheaf of `NL_{X/S}` is zero.

## Main results

* `Stacks.Smooth.formallySmooth_stalk_inverseImageStructureMap`: the stalk at `x` of the
  structural map `f^{-1}𝒪_S ⟶ 𝒪_X` of a formally smooth morphism is a formally smooth ring map.
* `Stacks.Smooth.injective_cotangentComplex_of_formallySmooth`: for a formally smooth algebra
  the map `I/I² ⟶ Ω` of the canonical presentation is injective.
* `Stacks.Smooth.injective_stalkFunctor_map_naiveCotangentComplex_d`: the stalk at `x` of the
  one nonzero differential of `NL_{X/S}` is injective.
* `Stacks.Smooth.exactAt_negOne_naiveCotangentComplex_of_formallySmooth`: `NL_{X/S}` is exact in
  degree `-1`, and
  `Stacks.Smooth.isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth`: **the
  vanishing clause of [Stacks, Tag 0D0L]**, `H⁻¹(NL_{X/S}) = 0`.
* `Stacks.Smooth.exactAt_naiveCotangentComplex_of_formallySmooth` and
  `Stacks.Smooth.isZero_homology_naiveCotangentComplex_of_formallySmooth`: `NL_{X/S}` is
  concentrated in degree `0`, the form in which the proof of [Stacks, Tag 0FV4] uses the tag.

## Route

The proof is stalkwise, and is the assembly of four facts each proved elsewhere.

1. Exactness of a complex of sheaves of `𝒪_X`-modules in a given degree is exactness of all its
   complexes of stalks in that degree
   (`AlgebraicGeometry.SheafOfModules.exactAt_iff_forall_stalk_exactAt`, the module-valued form
   of [Stacks, Tag 01AG]). Since `NL_{X/S}` has no term in degree `-2`, exactness in degree
   `-1` of a stalk complex is injectivity of its one nonzero differential.
2. The stalk at `x` of that differential is, under the identifications of
   `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne` and `...stalkLegZero` of the two terms
   of `NL_{X/S}` with the conormal module and the cotangent space of the canonical presentation
   of `𝒪_{X,x}` over `(f^{-1}𝒪_S)_x`, the map `cotangentComplex` of that presentation; this is
   `Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d`, which is [Stacks, Tag 0D09] for
   `NL_{X/S}`. Both identifications are bijections, so injectivity of the one map is
   injectivity of the other.
3. That presentation is a presentation of a formally smooth algebra: the stalk map
   `𝒪_{S,f(x)} ⟶ 𝒪_{X,x}` is formally smooth by
   `AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth`, and it differs from
   the stalk of `f^{-1}𝒪_S ⟶ 𝒪_X` — which is the base ring the identifications of step 2 use —
   only by precomposition with the isomorphism of base rings
   `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`, by
   `Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp`.
4. For a formally smooth algebra the map `I/I² ⟶ Ω` of the canonical presentation is injective:
   its failure to be injective is `H¹` of the cotangent complex
   (`Algebra.Extension.cotangentComplex_injective_iff`), which vanishes for a formally smooth
   algebra by `Algebra.FormallySmooth.subsingleton_h1Cotangent`.

## Scope

Together with
`Stacks.Smooth.isLocallyProjective_homology_zero_naiveCotangentComplex_of_formallySmooth` this
completes the **forward** implication of [Stacks, Tag 0D0L]: both conditions the tag attaches to
`NL_{X/S}` are consequences of formal smoothness. The two clauses carry separate clause-scoped
attributes, on the two statements that prove them.

The **converse** — that the two conditions together imply formal smoothness — is proved in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothConverse`, as
`Stacks.Smooth.formallySmooth_of_isZero_homology_negOne_of_isLocallyProjective_homology_zero`,
and the tag is registered for the whole equivalence on
`Stacks.Smooth.formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective_homology_zero`.
It is *not* blocked by [Stacks, Tag 0D0F]: that tag is proved in full and unconditionally, as
`Stacks.Smooth.formallySmooth_tfae` in
`StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothTFAE`, including its implication (3) ⟹ (1).
By that implication the converse reduces to formal smoothness of the ring map
`Γ(S, V) ⟶ Γ(X, U)` on every pair of affine opens with `f(U) ⊆ V`, hence by
`Algebra.formallySmooth_iff` to two things: projectivity of `Ω[Γ(X, U)⁄Γ(S, V)]`, which the
locally projective clause gives at once through `Stacks.Smooth.cotangentSectionsEquiv`
([Stacks, Tag 01UT]); and the vanishing of `H¹(L_{Γ(X, U)/Γ(S, V)})`, which is the step the
converse's own file is built around.

What this file's hypothesis supplies is that vanishing over the **local** base: by
`Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff`,
`H⁻¹(NL_{X/S}) = 0` is exactly injectivity, at every point `x`, of the `cotangentComplex` of
the canonical presentation of `𝒪_{X,x}` over `(f^{-1}𝒪_S)_x`, i.e. the vanishing of
`H¹(L_{𝒪_{X,x}/𝒪_{S,f x}})`. Passing from that to the vanishing over `Γ(S, V)` is a change of
the base ring along the localization `Γ(S, V) → 𝒪_{S, f x}`. Mathlib's Jacobi–Zariski left
exactness `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat` does not do it: it asks for
`Module.Flat 𝒪_{S, f x} 𝒪_{X,x}`, which this tag does not grant. What does it is
`Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom`
— the ring-level core of [Stacks, Tag 0D0I] — whose `H₁` half is a bijection between `H¹` of
the chart's complex base-changed to `𝒪_{X,x}` and `H¹(L_{𝒪_{X,x}/(f^{-1}𝒪_S)_x})`; the
converse's file assembles that bijection with the flatness of `𝒪_{X,x}` over `Γ(X, U)` and
`Module.support_eq_empty_iff`, which turns "vanishes after localizing at every prime" into
"vanishes".

## References

* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L)
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalks of the naive
  cotangent complex.
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG), exactness is stalkwise.
* [Stacks Project, Tag 07BP](https://stacks.math.columbia.edu/tag/07BP), the vanishing of `H¹`
  of the cotangent complex read on the canonical presentation.
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F), formal smoothness read
  on affine opens, proved in full as `Stacks.Smooth.formallySmooth_tfae`; its implication
  (3) ⟹ (1) is what the converse of Tag 0D0L would be built on.
* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), the naive cotangent
  complex on an affine chart, whose ring-level core carries the base-ring comparison the
  converse needs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)

universe u

namespace Stacks.Smooth

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The stalk of the structural map of a formally smooth morphism is formally smooth.** For a
formally smooth morphism of schemes `f : X ⟶ S` and a point `x` of `X`, the ring map
`(f^{-1}𝒪_S)_x ⟶ 𝒪_{X,x}` obtained by taking stalks at `x` of the structural map
`f^{-1}𝒪_S ⟶ 𝒪_X` is formally smooth.

The stalk map `𝒪_{S,f(x)} ⟶ 𝒪_{X,x}` of `f` is formally smooth by
`AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth`, and it factors as the
map in question precomposed with the isomorphism of base rings
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso`. Composing in the other direction with
that isomorphism — which is formally smooth, being bijective — recovers the map in question. -/
theorem formallySmooth_stalk_inverseImageStructureMap (hf : FormallySmoothScheme f) (x : X) :
    (CommRingCat.Hom.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (inverseImageStructureMap f.toLRSHom.toShHom).hom)).FormallySmooth := by
  have key : (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom ≫
      f.stalkMap x =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (inverseImageStructureMap f.toLRSHom.toShHom).hom := by
    rw [Stacks.SheafifyStalk.stalkMap_eq_stalkInverseImageStructureSheafIso_hom_comp f x]
    exact (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom_inv_id_assoc _
  rw [← key]
  exact RingHom.FormallySmooth.comp
    (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f x).hom))
    (Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth hf x)

/-- **For a formally smooth algebra the cotangent complex of the canonical presentation is
injective.** If `A` is a formally smooth `R`-algebra, the `A`-linear map `I/I² ⟶ Ω` attached to
the canonical presentation `R[A] ⟶ A` of `A` over `R` is injective.

Its kernel is `H¹` of the cotangent complex of `R ⟶ A`
(`Algebra.Extension.cotangentComplex_injective_iff`, the canonical presentation having formally
smooth polynomial ring), and that vanishes for a formally smooth algebra. -/
theorem injective_cotangentComplex_of_formallySmooth (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FormallySmooth R A] :
    Function.Injective (Algebra.Generators.self R A).toExtension.cotangentComplex := by
  have : Algebra.FormallySmooth R (Algebra.Generators.self R A).toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth R (MvPolynomial A R))
  rw [Algebra.Extension.cotangentComplex_injective_iff]
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

/-- **The stalk of the differential of `NL_{X/S}` is injective for a formally smooth
morphism.** For a formally smooth morphism of schemes `f : X ⟶ S` and a point `x` of `X`, the
map of `𝒪_{X,x}`-modules obtained by taking stalks at `x` of the one nonzero differential
`NL_{X/S}^{-1} ⟶ NL_{X/S}^0` is injective.

By `Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d` ([Stacks, Tag 0D09]) that map is, up to the
bijections identifying its source and target, the map `cotangentComplex` of the canonical
presentation of `𝒪_{X,x}` over `(f^{-1}𝒪_S)_x`, which is injective because that algebra is
formally smooth. -/
theorem injective_stalkFunctor_map_naiveCotangentComplex_d (hf : FormallySmoothScheme f)
    (x : X) :
    Function.Injective ((stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.toRingedSpace.carrier) X.toRingedSpace.sheaf) x).map
      ((Scheme.naiveCotangentComplex f).d (-1) 0)) := by
  let A := inverseImageSheaf f.toLRSHom.toShHom
  let B := X.toRingedSpace.sheaf
  let a := inverseImageStructureMap f.toLRSHom.toShHom
  let := algebraStalk a.hom x
  have hfs : Algebra.FormallySmooth (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x)) :=
    formallySmooth_stalk_inverseImageStructureMap f hf x
  intro ω₁ ω₂ hω
  refine (Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne A B a x).injective
    (injective_cotangentComplex_of_formallySmooth _ _ ?_)
  rw [← Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d A B a x ω₁,
    ← Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d A B a x ω₂]
  exact congrArg (Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero A B a x) hω

/-- **`NL_{X/S}` is exact in degree `-1` for a formally smooth morphism.** For a formally smooth
morphism of schemes `f : X ⟶ S` the naive cotangent complex `NL_{X/S}` is exact in degree `-1`.

Exactness is stalkwise ([Stacks, Tag 01AG]); the complex has no term in degree `-2`, so
exactness of a stalk complex in degree `-1` is injectivity of its one nonzero differential,
which is `Stacks.Smooth.injective_stalkFunctor_map_naiveCotangentComplex_d`. -/
theorem exactAt_negOne_naiveCotangentComplex_of_formallySmooth (hf : FormallySmoothScheme f) :
    (Scheme.naiveCotangentComplex f).ExactAt (-1) := by
  rw [AlgebraicGeometry.SheafOfModules.exactAt_iff_forall_stalk_exactAt]
  intro x
  rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp)]
  refine (ShortComplex.exact_iff_mono _ ?_).mpr ?_
  · have := AlgebraicGeometry.SheafOfModules.stalkFunctor_additive
      (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf) x
    exact ((stalkFunctor _ x).map_isZero
      (Scheme.naiveCotangentComplex_isZero_X f (-2) (by decide) (by decide))).eq_zero_of_src _
  · exact (ModuleCat.mono_iff_injective _).mpr
      (injective_stalkFunctor_map_naiveCotangentComplex_d f hf x)

/-- **The vanishing clause of [Stacks, Tag 0D0L], in the direction that formal smoothness is the
hypothesis.** For a formally smooth morphism of schemes `f : X ⟶ S` the degree `-1` cohomology
sheaf `H⁻¹(NL_{X/S})` of the naive cotangent complex vanishes.

The tag states an equivalence between formal smoothness of `f` and the conjunction of this
vanishing with local projectivity of `H⁰(NL_{X/S}) = Ω_{X/S}`, the latter being
`Stacks.Smooth.isLocallyProjective_homology_zero_naiveCotangentComplex_of_formallySmooth`. This
statement is the vanishing clause in the direction that takes formal smoothness as the
hypothesis; the equivalence itself is
`Stacks.Smooth.formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective_homology_zero`,
and the `Scope` section of this file sets out how its converse half is proved. -/
theorem isZero_homology_negOne_naiveCotangentComplex_of_formallySmooth
    (hf : FormallySmoothScheme f) :
    IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) :=
  (exactAt_negOne_naiveCotangentComplex_of_formallySmooth f hf).isZero_homology

/-- **`NL_{X/S}` is exact outside degree `0` for a formally smooth morphism.** For a formally
smooth morphism of schemes `f : X ⟶ S` the naive cotangent complex `NL_{X/S}` is exact in every
degree other than `0`.

In degrees other than `-1` and `0` the complex has no term at all; in degree `-1` this is
`Stacks.Smooth.exactAt_negOne_naiveCotangentComplex_of_formallySmooth`. -/
theorem exactAt_naiveCotangentComplex_of_formallySmooth (hf : FormallySmoothScheme f) (n : ℤ)
    (hn : n ≠ 0) : (Scheme.naiveCotangentComplex f).ExactAt n := by
  by_cases hneg : n = -1
  · exact hneg ▸ exactAt_negOne_naiveCotangentComplex_of_formallySmooth f hf
  · exact HomologicalComplex.ExactAt.of_isZero
      (Scheme.naiveCotangentComplex_isZero_X f n hneg hn)

/-- **`NL_{X/S}` is concentrated in degree `0` for a formally smooth morphism.** For a formally
smooth morphism of schemes `f : X ⟶ S` every cohomology sheaf of `NL_{X/S}` outside degree `0`
vanishes.

Together with the degree-zero clause of [Stacks, Tag 0D0J]
(`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`, which identifies
`H⁰(NL_{X/S})` with `Ω_{X/S}`) this is the assertion `NL_{X/S} = Ω_{X/S}` that the proof of
[Stacks, Tag 0FV4] extracts from [Stacks, Tag 0D0L]: the cohomology sheaves of `NL_{X/S}` are
those of `Ω_{X/S}` placed in degree `0`.

No morphism of complexes to `Ω_{X/S}` placed in degree `0` is constructed, and no object of
`D(𝒪_X)` appears, so this is a statement about cohomology sheaves only. -/
theorem isZero_homology_naiveCotangentComplex_of_formallySmooth (hf : FormallySmoothScheme f)
    (n : ℤ) (hn : n ≠ 0) : IsZero ((Scheme.naiveCotangentComplex f).homology n) :=
  (exactAt_naiveCotangentComplex_of_formallySmooth f hf n hn).isZero_homology

end Stacks.Smooth

end
