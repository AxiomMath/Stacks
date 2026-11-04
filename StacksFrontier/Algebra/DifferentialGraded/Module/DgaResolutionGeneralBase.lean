module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRegularRight
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorComposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.DgaResolutionDerivedEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.DgaResolutionKFlatBase

/-!
# Stacks 0BZ8 for a general middle algebra

Let `R` be a ring and let `(A, d)`, `(B, d)` and `(C, d)` be differential graded `R`-algebras such
that the ordinary tensor product `A ⊗_R C` represents `A ⊗^𝐋_R C` in `D(R)`. Let `N` be a
differential graded `(A, B)`-bimodule and `N'` a differential graded `(B, C)`-bimodule. Stacks Tag
0BZ8 says that the composition `D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is
isomorphic to `- ⊗_A^𝐋 N''` for some differential graded `(A, C)`-bimodule `N''`.

The second half of the proof — the case of a `B` which is K-flat as a complex of `R`-modules — is
`StacksFrontier/Algebra/DifferentialGraded/Module/DgaResolutionKFlatBase.lean`. This file is the
first half, the reduction of a general `B` to that case. It does *not* proceed by proving the map
of Tag 0BZ4 to be an isomorphism: for a general `B` that map need not be one, even under the
representability hypothesis. Instead `B` is replaced by a quasi-isomorphic K-flat differential
graded algebra `(B', d)` (Tag 0BZ7) and the *conclusion* is transported along the equivalence
`D(B', d) ≌ D(B, d)` of Tag 09S6.

## The three composites

Write `T_M = - ⊗_?^𝐋 M`. Tag 0BZ7 in the form Tag 09S6 consumes
(`DifferentialGradedAlgebra.exists_kFlat_resolution_bijective_cohomologyMap`) gives a
homomorphism `ψ : (B', d) → (B, d)` with `B'` K-flat and `H^k(ψ)` bijective in every degree, so
`T_{B}` for the regular `(B', B)`-bimodule `B` of `ψ` is an equivalence `D(B', d) ≌ D(B, d)` with
derived restriction of scalars as quasi-inverse, and restriction of scalars is itself a derived
tensor product: it is `T_{B}` for the regular `(B, B')`-bimodule `B` of `ψ`
(`DifferentialGraded.Bimodule.derivedTensorRegularRightIso`, the tensor half of Tag 0BYX). So
with `M = ` the regular `(B, B')`-bimodule and `M' = ` the regular `(B', B)`-bimodule the
composite `T_M ⋙ T_{M'}` is the identity of `D(B, d)`, and the source's reduction reads

`T_N ⋙ T_{N'} ≅ (T_N ⋙ T_M) ⋙ (T_{M'} ⋙ T_{N'})`,

which is the three composites of the source:

* `D(A) → D(B) → D(B')`, the composite `T_N ⋙ T_M`, is a derived tensor product by **Tag 09S4**
  (`DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlatAlgebra`), whose only
  hypothesis is K-flatness of the *third* algebra — here `B'`, which is why the resolution is
  taken K-flat;
* `D(B') → D(B) → D(C)`, the composite `T_{M'} ⋙ T_{N'}`, is a derived tensor product by **Tag
  0BZ3** (`DifferentialGraded.Bimodule.derivedTensorFunctorCompTensorIso`), whose hypothesis is
  that `B ⊗_B^𝐋 N' ⟶ B ⊗_B N' = N'` is an isomorphism; that is the invertibility of the
  comparison of Tag 09LS at the regular module, which holds because the regular module is
  orthogonal on the left to the acyclic modules (Tag 09K1);
* `D(A) → D(B') → D(C)` is the K-flat case of Tag 0BZ8, now available at the K-flat middle
  algebra `B'`
  (`DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIsoOfKFlatBase`), with the
  same representability hypothesis — which is a hypothesis on `A` and `C` only and is therefore
  untouched by the replacement of `B`.

## Main definitions

* `DifferentialGraded.Bimodule.resolutionCompTensorBimodule`: the differential graded
  `(A, C)`-bimodule `N''` produced by the reduction, namely
  `(Ñ ⊗_B B̃) ⊗_{B'} (B ⊗_{B'} Ñ')` in the notation of Tag 0BZ5.
* `DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIsoOfResolution`: the
  isomorphism of Tag 0BZ8 at a given K-flat resolution `ψ : (B', d) → (B, d)`, with the bimodule
  `N''` named.

## Main results

* `DifferentialGraded.Bimodule.exists_derivedTensorFunctorCompIso`: **Stacks Tag 0BZ8**, with no
  hypothesis on `B` — representability of `A ⊗^𝐋_R C` by `A ⊗_R C` is the only hypothesis, as in
  the source.

## Implementation notes

*Why the conclusion is existential in `N''`.* That is the source's conclusion: Tag 0BZ8 asserts
the composite to be isomorphic to `- ⊗_A^𝐋 N''` "for some differential graded `(A, C)`-bimodule
`N''`", and does not name `N''`. The bimodule produced here *is* named, by
`DifferentialGraded.Bimodule.resolutionCompTensorBimodule`, so
`DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIsoOfResolution` is stronger
than the source's statement; what is not claimed is that `N''` can be taken to be
`compTensorResolution N N'`, the bimodule of Tag 0BZ5, since the reduction passes through `B'`
and the identification of the two bimodules is not part of the source's proof. For a K-flat `B`
the bimodule *is* `compTensorResolution N N'`, by Tag 0BZ5 — that is the K-flat half.

*Associativity and unitality are definitional.* `CategoryTheory.Functor.assoc`,
`CategoryTheory.Functor.id_comp` and `CategoryTheory.Functor.comp_id` all hold by `rfl`, so the
chain of whiskered isomorphisms below needs no associators or unitors: the four isomorphisms
compose directly.

*Universes.* As everywhere in this chapter's differential graded interface, the base ring, the
algebras and the modules live in a single universe `u`, following Stacks Tag 09JJ; the resolution
of Tag 0BZ7 is taken at that diagonal.

## References

* [Stacks Project, Tag 0BZ8](https://stacks.math.columbia.edu/tag/0BZ8), the result proved here.
* [Stacks Project, Tag 0BZ7](https://stacks.math.columbia.edu/tag/0BZ7), the K-flat resolution,
  and [Tag 09S6](https://stacks.math.columbia.edu/tag/09S6), the equivalence it gives.
* [Stacks Project, Tag 09S4](https://stacks.math.columbia.edu/tag/09S4) for the first composite,
  [Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3) for the second and
  [Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5) for the K-flat case the third is.
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) for restriction of
  scalars as a derived tensor product, and
  [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1) for the left orthogonality of the
  regular module.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **The differential graded `(A, C)`-bimodule `N''` of Stacks Tag 0BZ8 for a general middle
algebra.** Given a homomorphism `ψ : (B', d) → (B, d)` of differential graded algebras, it is the
composite bimodule of Tag 0BZ5 formed from `N ⊗_B B` — the composite of `N` with the regular
`(B, B')`-bimodule of `ψ`, i.e. `N` restricted to `B'` on the right — and `B ⊗_{B'} N'` — the
composite of the regular `(B', B)`-bimodule of `ψ` with `N'`. -/
def resolutionCompTensorBimodule {A B C B' : DifferentialGradedAlgebra.{u, u} R}
    (ψ : B'.Hom B) (N : Bimodule A B) (N' : Bimodule B C) : Bimodule A C :=
  compTensorResolution (compTensorResolution N (regularRight ψ))
    (compTensor (Bimodule.regular ψ) N')

/-- **The reduction of Stacks Tag 0BZ8 to a K-flat middle algebra, at a given resolution.** Let
`ψ : (B', d) → (B, d)` be a homomorphism of differential graded algebras with `B'` K-flat as a
complex of `R`-modules and `H^k(ψ)` bijective for every `k`, and assume `A ⊗_R C` represents
`A ⊗^𝐋_R C` in `D(R)`. Then the composition `D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and
`- ⊗_B^𝐋 N'` is isomorphic to `- ⊗_A^𝐋 N''` for the differential graded `(A, C)`-bimodule
`N'' = ` `DifferentialGraded.Bimodule.resolutionCompTensorBimodule`.

The three composites of the source's proof are the three isomorphisms `i₁`, `i₂`, `i₃` below:
Tag 09S4 at the K-flat third algebra `B'`, Tag 0BZ3 at the regular bimodule, and the K-flat half
of Tag 0BZ8 at the middle algebra `B'`. The identity of `D(B, d)` that is inserted between
`- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is the counit of the equivalence of Tag 09S6, whose quasi-inverse is
derived restriction of scalars along `ψ` and hence is itself a derived tensor product. -/
def dgaResolutionDerivedTensorFunctorCompIsoOfResolution
    {A B C B' : DifferentialGradedAlgebra.{u, u} R} (ψ : B'.Hom B)
    (hflat : CochainComplex.KFlat.{u, u} (regularModule B').toCochainComplex)
    (hψ : ∀ k : ℤ, Function.Bijective (ψ.cohomologyMap k))
    (hrep : DgaResolutionRepresentsDerivedTensor A C)
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (resolutionCompTensorBimodule ψ N N') :=
  -- the quasi-inverse of Tag 09S6, composed with the equivalence, is the identity of `D(B, d)`
  let e₀ : derivedTensorFunctor (regularRight ψ) ⋙
      derivedTensorFunctor (Bimodule.regular ψ) ≅ Functor.id (derivedCategory' B) :=
    Functor.isoWhiskerRight (derivedTensorRegularRightIso ψ)
        (derivedTensorFunctor (Bimodule.regular ψ)) ≪≫
      (derivedExtensionEquivalence ψ hψ).counitIso
  -- `D(A) → D(B) → D(B')`, by Tag 09S4 at the K-flat third algebra `B'`
  let i₁ := derivedTensorFunctorCompIsoOfKFlatAlgebra A B B' hflat N (regularRight ψ)
  -- `D(B') → D(B) → D(C)`, by Tag 0BZ3 at the regular bimodule
  let i₂ := derivedTensorFunctorCompTensorIso (Bimodule.regular ψ) N'
    (isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N'
      ((toHomotopyCategory B).obj (Bimodule.regular ψ).rightModule)
      (leftOrthogonal_acyclic_toHomotopyCategory_regularModule B))
  -- `D(A) → D(B') → D(C)`, the K-flat half of Tag 0BZ8 at the middle algebra `B'`
  let i₃ := dgaResolutionDerivedTensorFunctorCompIsoOfKFlatBase hflat hrep
    (compTensorResolution N (regularRight ψ)) (compTensor (Bimodule.regular ψ) N')
  Functor.isoWhiskerLeft (derivedTensorFunctor N)
      (Functor.isoWhiskerRight e₀.symm (derivedTensorFunctor N')) ≪≫
    Functor.isoWhiskerRight i₁
      (derivedTensorFunctor (Bimodule.regular ψ) ⋙ derivedTensorFunctor N') ≪≫
    Functor.isoWhiskerLeft
      (derivedTensorFunctor (compTensorResolution N (regularRight ψ))) i₂ ≪≫
    i₃

/-- **Stacks Tag 0BZ8.** *"Let `R` be a ring. Let `(A, d)`, `(B, d)`, and `(C, d)` be differential
graded `R`-algebras. Assume that `A ⊗_R C` represents `A ⊗^𝐋_R C` in `D(R)`. Let `N` be a
differential graded `(A, B)`-bimodule. Let `N'` be a differential graded `(B, C)`-bimodule. Then
the composition `D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to
`- ⊗_A^𝐋 N''` for some differential graded `(A, C)`-bimodule `N''`."*

Representability is the only hypothesis: there is none on `B`. The bimodule is produced
explicitly by `DifferentialGraded.Bimodule.resolutionCompTensorBimodule`, from the K-flat
resolution `ψ : (B', d) → (B, d)` of Tag 0BZ7 that
`DifferentialGradedAlgebra.exists_kFlat_resolution_bijective_cohomologyMap` supplies; the
isomorphism is
`DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIsoOfResolution`. For a `B`
that is already K-flat the bimodule can be taken to be `compTensorResolution N N'`, the bimodule
of Tag 0BZ5, by
`DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIsoOfKFlatBase`. -/
@[stacks 0BZ8 "the composition of the two derived tensor functors is a derived tensor functor, \
with no hypothesis on the middle algebra"]
theorem exists_derivedTensorFunctorCompIso {A B C : DifferentialGradedAlgebra.{u, u} R}
    (hrep : DgaResolutionRepresentsDerivedTensor A C)
    (N : Bimodule A B) (N' : Bimodule B C) :
    ∃ N'' : Bimodule A C,
      Nonempty (derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
        derivedTensorFunctor N'') := by
  obtain ⟨B', ψ, hflat, hψ⟩ := exists_kFlat_resolution_bijective_cohomologyMap B
  exact ⟨resolutionCompTensorBimodule ψ N N',
    ⟨dgaResolutionDerivedTensorFunctorCompIsoOfResolution ψ hflat hψ hrep N N'⟩⟩

end DifferentialGraded.Bimodule

end
