module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomCounitTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Checking the derived homothety at another internal hom

Let `(X, 𝒪_X)` be a ringed space and let `K` be an object of `D(𝒪_X)`. The *homothety* of `K`,

`𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)`,

is `Stacks.SheafOfModules.derivedSheafHomothety`, and by
`Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_isIso_derivedSheafHomothety` its
invertibility is what the evaluation hypothesis `hev` of [Stacks, Tag 0ATP] reduces to at a pair
of objects differing by an invertible object.

That reduction leaves the homothety tied to the particular object `R𝓗om_{𝒪_X}(K, K)` that
[Stacks, Tag 08DI] constructs. This file cuts the tie. Both the homothety and the evaluation
morphism are determined by the *universal property* — `R𝓗om_{𝒪_X}(K, M)` is an internal hom
from `K` to `M` through the evaluation morphism,
`Stacks.SheafOfModules.tensorHomBijective_derivedSheafHomCounit` — so each may be checked at
any other object carrying an internal-hom structure for the same pair, by
`CategoryTheory.MonoidalCategory.isIso_iff_of_tensorHomBijective` and
`CategoryTheory.MonoidalCategory.isIso_iff_of_whiskerRight_comp_eq_leftUnitor`.

This is the form in which an affine-local input can be supplied. Over a Noetherian ring `A` the
derived hom `R𝐻om_A(ω, ω')` of two dualizing complexes is an internal hom through the evaluation
morphism `Dualizing.evaluationTensorMap`
(`Dualizing.tensorHomBijective_evaluationTensorMap`) and that evaluation morphism is invertible
(`Dualizing.isIso_evaluationTensorMap_of_isDualizingComplex`). What the results below say is
that *any* such datum transported to `D(𝒪_{Spec A})` closes the affine case of `hev`, with no
further reference to `R𝓗om_{𝒪_X}` and with nothing more owed about pairs, invertible objects or
homotheties.

## Main results

* `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_tensorHomBijective` — **the evaluation
  morphism `e_{K,M}` is invertible as soon as some internal hom for `(K, M)` has invertible
  evaluation.**
* `Stacks.SheafOfModules.isIso_derivedSheafHomothety_of_whiskerRight_comp` — **the homothety of
  `K` is invertible as soon as some internal hom for `(K, K)` has an invertible homothety.**
* `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_whiskerRight_comp` — the two previous
  results' common consequence through the invertible-object transport: an invertible homothety at
  any internal hom for `(K, K)`, together with `K ⊗^L_{𝒪_X} L ≅ M` for an invertible `L`, makes
  `e_{K,M}` invertible.
* `Stacks.SheafOfModules.isIso_derivedSheafHomothety_iff_tensorHomBijective_tensorUnit` — the
  homothety of `K` is invertible exactly when `𝒪_X[0]` is itself an internal hom from `K` to `K`
  through the left unitor, that is, exactly when
  `(Z ⟶ 𝒪_X[0]) → (Z ⊗^L_{𝒪_X} K ⟶ K)`, `b ↦ b ▷ K ≫ λ_`, is bijective for every `Z`.

## Implementation notes

Nothing here is specific to `D(𝒪_X)`: each statement is the corresponding statement of
`StacksFrontier/CategoryTheory/Monoidal/InternalHomEvaluationBijection.lean` with the internal-hom
hypothesis for the canonical side discharged by
`Stacks.SheafOfModules.tensorHomBijective_derivedSheafHomCounit` and, for the homothety, the
defining equation discharged by
`Stacks.SheafOfModules.whiskerRight_derivedSheafHomothety_comp`. The monoidal structure is
`Stacks.SheafOfModules.derivedMonoidalStructure`, whose tensor product is the derived tensor
product of [Stacks, Tag 06YU] and whose unit is the structure sheaf in degree zero, so `𝟙_` is
`𝒪_X[0]` with nothing interposed; the invertible-object transport also needs the braiding
`Stacks.SheafOfModules.derivedSymmetricStructure` of [Stacks, Tag 0FPT].

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-! ### The evaluation morphism at another internal hom -/

/-- **An invertible evaluation morphism at one internal hom for `(K, M)` makes the evaluation
morphism of [Stacks, Tag 08DI] invertible.** If `H` is an object of `D(𝒪_X)` and
`c : H ⊗^L_{𝒪_X} K ⟶ M` exhibits `H` as an internal hom from `K` to `M`, then

`e_{K,M} : R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_X} K ⟶ M`

is invertible exactly when `c` is. Invertibility of an internal-hom evaluation morphism depends
only on the pair, the two internal homs differing by an isomorphism compatible with the two
evaluation morphisms. -/
theorem isIso_derivedSheafHomCounit_of_tensorHomBijective
    (K M : DerivedCategory (StructureSheafModules Rc))
    {H : DerivedCategory (StructureSheafModules Rc)}
    (c : letI := derivedMonoidalStructure Rc; H ⊗ K ⟶ M)
    (hc : letI := derivedMonoidalStructure Rc
      ∀ Z : DerivedCategory (StructureSheafModules Rc),
        Function.Bijective fun x : Z ⟶ H => x ▷ K ≫ c)
    (h : IsIso c) :
    IsIso (derivedSheafHomCounit Rc K M) := by
  let := derivedMonoidalStructure Rc
  exact (MonoidalCategory.isIso_iff_of_tensorHomBijective
    (derivedSheafHomCounit Rc K M) c
    (tensorHomBijective_derivedSheafHomCounit Rc K M) hc).2 h

/-! ### The homothety at another internal hom -/

/-- **An invertible homothety at one internal hom for `(K, K)` makes the homothety of
[Stacks, Tag 08DI] invertible.** Let `c : H ⊗^L_{𝒪_X} K ⟶ K` exhibit `H` as an internal hom from
`K` to itself and let `a : 𝒪_X[0] ⟶ H` satisfy `a ▷ K ≫ c = λ_ K`, the defining equation of a
homothety. If `a` is invertible then so is `Stacks.SheafOfModules.derivedSheafHomothety`.

So the homothety of `K` need not be produced at `R𝓗om_{𝒪_X}(K, K)`: any object with an
internal-hom structure for `(K, K)` serves, for instance one transported along derived
sheafification from a ring. -/
theorem isIso_derivedSheafHomothety_of_whiskerRight_comp
    (K : DerivedCategory (StructureSheafModules Rc))
    {H : DerivedCategory (StructureSheafModules Rc)}
    (c : letI := derivedMonoidalStructure Rc; H ⊗ K ⟶ K)
    (hc : letI := derivedMonoidalStructure Rc
      ∀ Z : DerivedCategory (StructureSheafModules Rc),
        Function.Bijective fun x : Z ⟶ H => x ▷ K ≫ c)
    {a : letI := derivedMonoidalStructure Rc
      𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ H}
    (ha : letI := derivedMonoidalStructure Rc; a ▷ K ≫ c = (λ_ K).hom)
    (h : IsIso a) :
    IsIso (derivedSheafHomothety Rc K) := by
  let := derivedMonoidalStructure Rc
  exact (MonoidalCategory.isIso_iff_of_whiskerRight_comp_eq_leftUnitor c
    (derivedSheafHomCounit Rc K K) hc
    (tensorHomBijective_derivedSheafHomCounit Rc K K) ha
    (whiskerRight_derivedSheafHomothety_comp Rc K)).1 h

/-- **The evaluation hypothesis of [Stacks, Tag 0ATP] from a homothety at any internal hom.**
Let `K` and `M` be objects of `D(𝒪_X)` with `K ⊗^L_{𝒪_X} L ≅ M` for an invertible `L`
([Stacks, Tag 0FFN]). If some object `H` is an internal hom from `K` to `K` through
`c : H ⊗^L_{𝒪_X} K ⟶ K` and carries an invertible homothety `a : 𝒪_X[0] ⟶ H`, then

`e_{K,M} : R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_X} K ⟶ M`

is invertible.

This is `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_isIso_derivedSheafHomothety` with
its hypothesis moved off `R𝓗om_{𝒪_X}(K, K)`: the whole affine-local input of the evaluation
hypothesis `hev` of `Stacks.SheafOfModules.exists_isInvertible_tensor_iso_of_affineLocal` is then
a single morphism of `D(𝒪_X)` out of the structure sheaf, at an internal hom of the supplier's
choosing. -/
theorem isIso_derivedSheafHomCounit_of_whiskerRight_comp
    (K M : DerivedCategory (StructureSheafModules Rc))
    {L H : DerivedCategory (StructureSheafModules Rc)}
    (hL : letI := derivedMonoidalStructure Rc; MonoidalCategory.IsInvertible L)
    (u : letI := derivedMonoidalStructure Rc; K ⊗ L ≅ M)
    (c : letI := derivedMonoidalStructure Rc; H ⊗ K ⟶ K)
    (hc : letI := derivedMonoidalStructure Rc
      ∀ Z : DerivedCategory (StructureSheafModules Rc),
        Function.Bijective fun x : Z ⟶ H => x ▷ K ≫ c)
    {a : letI := derivedMonoidalStructure Rc
      𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ H}
    (ha : letI := derivedMonoidalStructure Rc; a ▷ K ≫ c = (λ_ K).hom)
    (h : IsIso a) :
    IsIso (derivedSheafHomCounit Rc K M) :=
  isIso_derivedSheafHomCounit_of_isIso_derivedSheafHomothety Rc K M hL u
    (isIso_derivedSheafHomothety_of_whiskerRight_comp Rc K c hc ha h)

/-! ### The homothety as a statement about morphism groups -/

/-- **The homothety of `K` is invertible exactly when `𝒪_X[0]` is an internal hom from `K` to
`K` through the left unitor**, that is, exactly when

`(Z ⟶ 𝒪_X[0]) → (Z ⊗^L_{𝒪_X} K ⟶ K)`, `b ↦ b ▷ K ≫ λ_ K`

is a bijection for every object `Z` of `D(𝒪_X)`.

The unit carries the homothety `𝟙` at the left unitor, so this is the comparison of two
internal homs for `(K, K)` again, one of them `𝒪_X[0]` itself. It turns invertibility of a
morphism into a statement about morphism groups, which is the form a computation at an affine
scheme can address. -/
theorem isIso_derivedSheafHomothety_iff_tensorHomBijective_tensorUnit
    (K : DerivedCategory (StructureSheafModules Rc)) :
    letI := derivedMonoidalStructure Rc
    IsIso (derivedSheafHomothety Rc K) ↔
      ∀ Z : DerivedCategory (StructureSheafModules Rc),
        Function.Bijective fun b : Z ⟶ 𝟙_ (DerivedCategory (StructureSheafModules Rc)) =>
          b ▷ K ≫ (λ_ K).hom := by
  let := derivedMonoidalStructure Rc
  exact MonoidalCategory.isIso_iff_tensorHomBijective_tensorUnit
    (derivedSheafHomCounit Rc K K) (tensorHomBijective_derivedSheafHomCounit Rc K K)
    (whiskerRight_derivedSheafHomothety_comp Rc K)

end Stacks.SheafOfModules

end
