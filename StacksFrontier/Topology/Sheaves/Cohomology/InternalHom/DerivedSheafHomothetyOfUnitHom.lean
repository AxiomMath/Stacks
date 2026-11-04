module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitHomothety
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyCriteria
import StacksCore.Tactic.StacksAttribute

/-!
# The homothety of an object whose derived internal hom to itself is the structure sheaf

Let `(X, 𝒪_X)` be a ringed space and let `K` be an object of `D(𝒪_X)`. The *homothety* of `K`,

`𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)`,

is `Stacks.SheafOfModules.derivedSheafHomothety`, and by
`Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_isIso_derivedSheafHomothety` its
invertibility is what the evaluation hypothesis `hev` of [Stacks, Tag 0ATP] reduces to at a pair
of objects differing by an invertible object.

**This file discharges that hypothesis from an isomorphism of objects.** If

`R𝓗om_{𝒪_X}(K, K) ≅ 𝒪_X[0]`

in `D(𝒪_X)` — any isomorphism, with no compatibility with the homothety or with the evaluation
morphism assumed — then the homothety of `K` is an isomorphism.

That the object isomorphism suffices is not formal nonsense about morphisms between isomorphic
objects: it uses that `R𝓗om_{𝒪_X}(K, K)` carries a composition for which the homothety is a
left unit, which the universal property of [Stacks, Tag 08DI] supplies, and that a left unit on
an object isomorphic to the tensor unit is invertible. Both steps are
`StacksFrontier/CategoryTheory/Monoidal/InternalHomUnitHomothety.lean`, in an arbitrary monoidal
category.

This is what an affine-local computation can supply. Over a ring `A` the derived hom
`R𝐻om_A(ω, ω)` of a dualizing complex is `A` in degree zero, and the comparison of
[Stacks, Tag 0A6H] (3)(a) carries that to `D(𝒪_{Spec A})` **as an isomorphism of objects**,
which is the only part of that comparison available: nothing identifies it with an evaluation
morphism, and nothing is needed. What the results below say is that an object computation of
`R𝓗om_{𝒪_X}(K, K)` closes the affine case of `hev` at the diagonal, and closes it at a pair as
soon as the pair differs by an invertible object.

## Main results

* `Stacks.SheafOfModules.isIso_derivedSheafHomothety_of_iso_tensorUnit` — **the homothety of `K`
  is invertible as soon as `R𝓗om_{𝒪_X}(K, K)` is isomorphic to `𝒪_X[0]` as an object.**
* `Stacks.SheafOfModules.tensorHomBijective_tensorUnit_of_iso_tensorUnit` — equivalently,
  `𝒪_X[0]` is then itself an internal hom from `K` to `K` through the left unitor:
  `(Z ⟶ 𝒪_X[0]) → (Z ⊗^L_{𝒪_X} K ⟶ K)`, `b ↦ b ▷ K ≫ λ_`, is bijective for every `Z`.
* `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_self_of_iso_tensorUnit` — the evaluation
  morphism `e_{K,K}` is then an isomorphism.
* `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_iso_tensorUnit` — **the evaluation
  hypothesis `hev` of [Stacks, Tag 0ATP] at a pair,** from the object computation at the
  diagonal together with `K ⊗^L_{𝒪_X} L ≅ M` for an invertible `L` ([Stacks, Tag 0FFN]).

## Implementation notes

The monoidal structure is `Stacks.SheafOfModules.derivedMonoidalStructure`, whose tensor product
*is* the derived tensor product of [Stacks, Tag 06YU] and whose unit *is* the structure sheaf in
degree zero, so `𝟙_` may be read as `𝒪_X[0]` with nothing interposed; the hypothesis of the last
result also needs the braiding `Stacks.SheafOfModules.derivedSymmetricStructure` of
[Stacks, Tag 0FPT], through the invertible-object transport it is proved by.

Nothing here is specific to `D(𝒪_X)`: each statement is the corresponding statement of
`StacksFrontier/CategoryTheory/Monoidal/InternalHomUnitHomothety.lean` with the internal-hom
hypothesis discharged by `Stacks.SheafOfModules.tensorHomBijective_derivedSheafHomCounit` and
the homothety's defining equation by
`Stacks.SheafOfModules.whiskerRight_derivedSheafHomothety_comp`.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
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

/-! ### The homothety from an object computation -/

/-- **The homothety of `K` is invertible as soon as `R𝓗om_{𝒪_X}(K, K)` is isomorphic to
`𝒪_X[0]`.** The isomorphism is arbitrary: no compatibility with the homothety or with the
evaluation morphism of [Stacks, Tag 08DI] is assumed.

The evaluation morphism exhibits `R𝓗om_{𝒪_X}(K, K)` as an internal hom from `K` to `K`
(`Stacks.SheafOfModules.tensorHomBijective_derivedSheafHomCounit`) and the homothety is a left
unit for the composition that universal property produces, so
`CategoryTheory.MonoidalCategory.isIso_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit`
applies. -/
theorem isIso_derivedSheafHomothety_of_iso_tensorUnit
    (K : DerivedCategory (StructureSheafModules Rc))
    (ψ : letI := derivedMonoidalStructure Rc
      ((derivedSheafHom Rc).obj (op K)).obj K ≅
        𝟙_ (DerivedCategory (StructureSheafModules Rc))) :
    IsIso (derivedSheafHomothety Rc K) := by
  let := derivedMonoidalStructure Rc
  exact MonoidalCategory.isIso_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit
    (derivedSheafHomCounit Rc K K) (tensorHomBijective_derivedSheafHomCounit Rc K K)
    (whiskerRight_derivedSheafHomothety_comp Rc K) ψ

/-- **An object computation of `R𝓗om_{𝒪_X}(K, K)` makes `𝒪_X[0]` an internal hom from `K` to `K`
through the left unitor**, that is, makes

`(Z ⟶ 𝒪_X[0]) → (Z ⊗^L_{𝒪_X} K ⟶ K)`, `b ↦ b ▷ K ≫ λ_ K`

a bijection for every object `Z` of `D(𝒪_X)`. This is the morphism-group form of the previous
result, through
`Stacks.SheafOfModules.isIso_derivedSheafHomothety_iff_tensorHomBijective_tensorUnit`. -/
theorem tensorHomBijective_tensorUnit_of_iso_tensorUnit
    (K : DerivedCategory (StructureSheafModules Rc))
    (ψ : letI := derivedMonoidalStructure Rc
      ((derivedSheafHom Rc).obj (op K)).obj K ≅
        𝟙_ (DerivedCategory (StructureSheafModules Rc))) :
    letI := derivedMonoidalStructure Rc
    ∀ Z : DerivedCategory (StructureSheafModules Rc),
      Function.Bijective fun b : Z ⟶ 𝟙_ (DerivedCategory (StructureSheafModules Rc)) =>
        b ▷ K ≫ (λ_ K).hom :=
  (isIso_derivedSheafHomothety_iff_tensorHomBijective_tensorUnit Rc K).1
    (isIso_derivedSheafHomothety_of_iso_tensorUnit Rc K ψ)

/-! ### The evaluation morphism from an object computation -/

/-- **The evaluation morphism at the diagonal is an isomorphism as soon as
`R𝓗om_{𝒪_X}(K, K)` is isomorphic to `𝒪_X[0]`**: that is,

`e_{K,K} : R𝓗om_{𝒪_X}(K, K) ⊗^L_{𝒪_X} K ⟶ K`

is an isomorphism. -/
theorem isIso_derivedSheafHomCounit_self_of_iso_tensorUnit
    (K : DerivedCategory (StructureSheafModules Rc))
    (ψ : letI := derivedMonoidalStructure Rc
      ((derivedSheafHom Rc).obj (op K)).obj K ≅
        𝟙_ (DerivedCategory (StructureSheafModules Rc))) :
    IsIso (derivedSheafHomCounit Rc K K) :=
  isIso_derivedSheafHomCounit_self_of_isIso_derivedSheafHomothety Rc K
    (isIso_derivedSheafHomothety_of_iso_tensorUnit Rc K ψ)

/-- **The evaluation hypothesis `hev` of [Stacks, Tag 0ATP] from an object computation at the
diagonal.** Let `K` and `M` be objects of `D(𝒪_X)` with `K ⊗^L_{𝒪_X} L ≅ M` for an invertible
`L` ([Stacks, Tag 0FFN]). If `R𝓗om_{𝒪_X}(K, K)` is isomorphic to `𝒪_X[0]` as an object then

`e_{K,M} : R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_X} K ⟶ M`

is an isomorphism.

So the whole affine-local input of `hev` is a *computation of one object* of `D(𝒪_X)`, with no
identification of any comparison isomorphism with any evaluation morphism. -/
theorem isIso_derivedSheafHomCounit_of_iso_tensorUnit
    (K M : DerivedCategory (StructureSheafModules Rc))
    {L : DerivedCategory (StructureSheafModules Rc)}
    (hL : letI := derivedMonoidalStructure Rc; MonoidalCategory.IsInvertible L)
    (u : letI := derivedMonoidalStructure Rc; K ⊗ L ≅ M)
    (ψ : letI := derivedMonoidalStructure Rc
      ((derivedSheafHom Rc).obj (op K)).obj K ≅
        𝟙_ (DerivedCategory (StructureSheafModules Rc))) :
    IsIso (derivedSheafHomCounit Rc K M) :=
  isIso_derivedSheafHomCounit_of_isIso_derivedSheafHomothety Rc K M hL u
    (isIso_derivedSheafHomothety_of_iso_tensorUnit Rc K ψ)

end Stacks.SheafOfModules

end
