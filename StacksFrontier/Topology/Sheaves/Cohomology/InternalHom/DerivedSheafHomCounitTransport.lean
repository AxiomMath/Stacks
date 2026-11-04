module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomEvaluationBijection
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InvertibleDerivedSheafHomCounit
import StacksCore.Tactic.StacksAttribute

/-!
# The evaluation morphism of `D(𝒪_X)`, at the diagonal and at a general target

Let `(X, 𝒪_X)` be a ringed space and let `K`, `M` be objects of `D(𝒪_X)`. The evaluation
morphism

`e_{K,M} : R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_X} K ⟶ M`

is `Stacks.SheafOfModules.derivedSheafHomCounit`, the bijection of [Stacks, Tag 08DI] at the
identity. This file proves two things about it, both for arbitrary objects of `D(𝒪_X)` and with
no hypothesis on the space.

*The bijection of [Stacks, Tag 08DI] is evaluation after tensoring*, so
`R𝓗om_{𝒪_X}(K, M)` is an internal hom from `K` to `M` **through `e_{K,M}`** in the sense of
`StacksFrontier/CategoryTheory/Monoidal/InternalHomEvaluationBijection.lean`.

*Hence the target may be moved by an invertible object.* If `M ⊗^L_{𝒪_X} L ≅ M'` for an
invertible object `L` of `D(𝒪_X)` ([Stacks, Tag 0FFN]) then `e_{K,M'}` is an isomorphism exactly
when `e_{K,M}` is. In particular, for two objects differing by an invertible object the
evaluation morphism at the pair is an isomorphism as soon as the one at the **diagonal** is, and
the diagonal case is in turn implied by invertibility of the single morphism

`𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)`

adjoint to the left unitor of `K` — the *homothety* of `K`,
`Stacks.SheafOfModules.derivedSheafHomothety`.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafHomothety` — the morphism `𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)`
  matched with the left unitor `𝒪_X[0] ⊗^L_{𝒪_X} K ≅ K` by the bijection of [Stacks, Tag 08DI].

## Main results

* `Stacks.SheafOfModules.whiskerRight_comp_derivedSheafHomCounit` — the bijection of
  [Stacks, Tag 08DI] is `a ↦ a ▷ K ≫ e_{K,M}`.
* `Stacks.SheafOfModules.tensorHomBijective_derivedSheafHomCounit` — hence `R𝓗om_{𝒪_X}(K, M)`
  is an internal hom from `K` to `M` through `e_{K,M}`.
* `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_iff_of_isInvertible` — **the transport of
  the target along an invertible object**: with `M ⊗^L_{𝒪_X} L ≅ M'` and `L` invertible,
  `e_{K,M'}` is invertible exactly when `e_{K,M}` is.
* `Stacks.SheafOfModules.whiskerRight_derivedSheafHomothety_comp` — the homothety composed with
  the evaluation morphism at the diagonal is the left unitor, on the nose.
* `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_self_of_isIso_derivedSheafHomothety` — an
  invertible homothety makes the evaluation morphism at the diagonal an isomorphism.
* `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_isIso_derivedSheafHomothety` — the two
  put together: an invertible homothety of `K` makes `e_{K,M}` an isomorphism for every `M`
  obtained from `K` by tensoring with an invertible object.

## Implementation notes

The monoidal structure is `Stacks.SheafOfModules.derivedMonoidalStructure`, whose tensor product
**is** the derived tensor product `Stacks.SheafOfModules.derivedTensor` of [Stacks, Tag 06YU] and
whose unit **is** the structure sheaf in degree zero, both by `rfl`
(`Stacks.SheafOfModules.curriedTensor_derivedMonoidalStructure`). So `a ▷ K` is
`((derivedTensor Rc).map a).app K` with no comparison in between, which is what lets the
bijection of [Stacks, Tag 08DI] be read as a family of monoidal statements at all; and the source
of `derivedSheafHomothety` is the unit of that structure with nothing interposed. A braiding is
needed for the transport and is `Stacks.SheafOfModules.derivedSymmetricStructure`.

The proof of `whiskerRight_comp_derivedSheafHomCounit` is the `hfun` step of
`Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_isInvertible`, and keeps that proof's
spelling: the naturality equation of [Stacks, Tag 08J8] is used in the *site* spelling
throughout, and `a ≫ 𝟙` is removed by `congrArg` against an explicitly written function rather
than by `rw [Category.comp_id]`, which exhausts the elaborator's budget here. See the
implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/InvertibleDerivedSheafHomCounit.lean`.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
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

/-! ### The evaluation morphism exhibits the derived internal hom -/

/-- **The bijection of [Stacks, Tag 08DI] is tensoring with the identity followed by the
evaluation morphism.** For objects `K`, `M`, `Z` of `D(𝒪_X)` and `a : Z ⟶ R𝓗om_{𝒪_X}(K, M)`,

`a ▷ K ≫ e_{K,M} = (the bijection of 08DI) a`.

This is the naturality of [Stacks, Tag 08J8] in its source variable at the identity of
`R𝓗om_{𝒪_X}(K, M)`, the evaluation morphism being the image of that identity by definition. -/
theorem whiskerRight_comp_derivedSheafHomCounit
    (K M Z : DerivedCategory (StructureSheafModules Rc))
    (a : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M) :
    letI := derivedMonoidalStructure Rc
    a ▷ K ≫ derivedSheafHomCounit Rc K M = derivedSheafHomTensorEquiv Rc Z K M a := by
  let := derivedMonoidalStructure Rc
  have hnat : ∀ (b : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M)
      (g : ((derivedSheafHom Rc).obj (op K)).obj M ⟶ ((derivedSheafHom Rc).obj (op K)).obj M),
      RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z K M (b ≫ g) =
        b ▷ K ≫ RingedSite.derivedCurryHomEquiv (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op K)).obj M) K M g :=
    fun b g => RingedSite.derivedCurryHomEquiv_naturality_source (ringedSite Rc) b g
  have hcounit : derivedSheafHomCounit Rc K M =
      RingedSite.derivedCurryHomEquiv (ringedSite Rc)
        (((derivedSheafHom Rc).obj (op K)).obj M) K M
        (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M)) := rfl
  rw [hcounit]
  have h0 := hnat a (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M))
  exact h0.symm.trans
    (congrArg (fun v : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M =>
      RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z K M v) (Category.comp_id a))

/-- **The derived internal hom is an internal hom through its evaluation morphism.** For objects
`K` and `M` of `D(𝒪_X)` and every object `Z`, the map

`(Z ⟶ R𝓗om_{𝒪_X}(K, M)) → (Z ⊗^L_{𝒪_X} K ⟶ M)`, `a ↦ a ▷ K ≫ e_{K,M}`

is a bijection: by `Stacks.SheafOfModules.whiskerRight_comp_derivedSheafHomCounit` it *is* the
bijection of [Stacks, Tag 08DI]. This is the hypothesis shape of the criteria of
`StacksFrontier/CategoryTheory/Monoidal/InternalHomEvaluationBijection.lean`. -/
theorem tensorHomBijective_derivedSheafHomCounit
    (K M : DerivedCategory (StructureSheafModules Rc))
    (Z : DerivedCategory (StructureSheafModules Rc)) :
    letI := derivedMonoidalStructure Rc
    Function.Bijective fun a : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M =>
      a ▷ K ≫ derivedSheafHomCounit Rc K M := by
  let := derivedMonoidalStructure Rc
  have hfun : (fun a : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M =>
        a ▷ K ≫ derivedSheafHomCounit Rc K M) =
      ⇑(derivedSheafHomTensorEquiv Rc Z K M) :=
    funext fun a => whiskerRight_comp_derivedSheafHomCounit Rc K M Z a
  rw [hfun]
  exact (derivedSheafHomTensorEquiv Rc Z K M).bijective

/-! ### Moving the target by an invertible object -/

/-- **The evaluation morphisms at `(K, M)` and at `(K, M ⊗^L_{𝒪_X} L)` are isomorphisms
together**, for `L` an invertible object of `D(𝒪_X)` ([Stacks, Tag 0FFN]).

This is `CategoryTheory.MonoidalCategory.isIso_iff_of_tensorHomBijective_of_isInvertible` read at
`D(𝒪_X)`: the bijection of [Stacks, Tag 08DI] supplies the internal-hom hypothesis at both pairs
by `Stacks.SheafOfModules.tensorHomBijective_derivedSheafHomCounit`, and the braiding is the
symmetry of [Stacks, Tag 0FPT]. Nothing about dualizing complexes or about the space enters. -/
theorem isIso_derivedSheafHomCounit_iff_of_isInvertible
    (K M M' : DerivedCategory (StructureSheafModules Rc))
    {L : DerivedCategory (StructureSheafModules Rc)}
    (hL : letI := derivedMonoidalStructure Rc; MonoidalCategory.IsInvertible L)
    (u : letI := derivedMonoidalStructure Rc; M ⊗ L ≅ M') :
    IsIso (derivedSheafHomCounit Rc K M') ↔ IsIso (derivedSheafHomCounit Rc K M) := by
  let := derivedMonoidalStructure Rc
  let := derivedSymmetricStructure Rc
  exact MonoidalCategory.isIso_iff_of_tensorHomBijective_of_isInvertible
    (derivedSheafHomCounit Rc K M) (derivedSheafHomCounit Rc K M')
    (tensorHomBijective_derivedSheafHomCounit Rc K M)
    (tensorHomBijective_derivedSheafHomCounit Rc K M') hL u

/-! ### The homothety and the diagonal -/

/-- **The homothety of an object of `D(𝒪_X)`**, `𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)`: the unique
morphism whose whiskering with the evaluation morphism at the diagonal is the left unitor
`𝒪_X[0] ⊗^L_{𝒪_X} K ≅ K`, that is, the morphism matched with that unitor by the bijection of
[Stacks, Tag 08DI].

It exists and is unique because that bijection *is* `a ↦ a ▷ K ≫ e_{K,K}`
(`Stacks.SheafOfModules.whiskerRight_comp_derivedSheafHomCounit`); the two halves are
`Stacks.SheafOfModules.whiskerRight_derivedSheafHomothety_comp` and
`Stacks.SheafOfModules.eq_derivedSheafHomothety_of_whiskerRight_comp`, and together they pin the
morphism down. The unit of `Stacks.SheafOfModules.derivedMonoidalStructure` is the structure
sheaf in degree zero, so no comparison stands between the source written here and `𝒪_X[0]`. -/
def derivedSheafHomothety (K : DerivedCategory (StructureSheafModules Rc)) :
    letI := derivedMonoidalStructure Rc
    𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
      ((derivedSheafHom Rc).obj (op K)).obj K :=
  let := derivedMonoidalStructure Rc
  Function.surjInv
    (tensorHomBijective_derivedSheafHomCounit Rc K K
      (𝟙_ (DerivedCategory (StructureSheafModules Rc)))).surjective (λ_ K).hom

/-- **The homothety followed by evaluation is the left unitor**, the defining property of
`Stacks.SheafOfModules.derivedSheafHomothety`. -/
theorem whiskerRight_derivedSheafHomothety_comp
    (K : DerivedCategory (StructureSheafModules Rc)) :
    letI := derivedMonoidalStructure Rc
    derivedSheafHomothety Rc K ▷ K ≫ derivedSheafHomCounit Rc K K = (λ_ K).hom :=
  let := derivedMonoidalStructure Rc
  Function.surjInv_eq
    (tensorHomBijective_derivedSheafHomCounit Rc K K
      (𝟙_ (DerivedCategory (StructureSheafModules Rc)))).surjective (λ_ K).hom

/-- **The homothety is the only morphism with that property.** The bijection of
[Stacks, Tag 08DI] is injective, so a morphism `𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)` whose whiskering
with the evaluation morphism at the diagonal is the left unitor is the homothety. -/
theorem eq_derivedSheafHomothety_of_whiskerRight_comp
    (K : DerivedCategory (StructureSheafModules Rc))
    (a : letI := derivedMonoidalStructure Rc
      𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
        ((derivedSheafHom Rc).obj (op K)).obj K)
    (ha : letI := derivedMonoidalStructure Rc
      a ▷ K ≫ derivedSheafHomCounit Rc K K = (λ_ K).hom) :
    a = derivedSheafHomothety Rc K :=
  let := derivedMonoidalStructure Rc
  (tensorHomBijective_derivedSheafHomCounit Rc K K
      (𝟙_ (DerivedCategory (StructureSheafModules Rc)))).injective
    (ha.trans (whiskerRight_derivedSheafHomothety_comp Rc K).symm)

/-- **An invertible homothety makes the evaluation morphism at the diagonal an isomorphism.** If
`𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)` is an isomorphism then so is

`e_{K,K} : R𝓗om_{𝒪_X}(K, K) ⊗^L_{𝒪_X} K ⟶ K`,

the composite of its whiskering with `e_{K,K}` being the left unitor. -/
theorem isIso_derivedSheafHomCounit_self_of_isIso_derivedSheafHomothety
    (K : DerivedCategory (StructureSheafModules Rc))
    (h : IsIso (derivedSheafHomothety Rc K)) :
    IsIso (derivedSheafHomCounit Rc K K) := by
  let := derivedMonoidalStructure Rc
  have := h
  have : IsIso (derivedSheafHomothety Rc K ▷ K ≫ derivedSheafHomCounit Rc K K) := by
    rw [whiskerRight_derivedSheafHomothety_comp Rc K]
    infer_instance
  exact IsIso.of_isIso_comp_left (derivedSheafHomothety Rc K ▷ K)
    (derivedSheafHomCounit Rc K K)

/-- **The evaluation morphism at a pair differing by an invertible object, from the homothety.**
Let `K` and `M` be objects of `D(𝒪_X)` with `K ⊗^L_{𝒪_X} L ≅ M` for an invertible `L`. If the
homothety of `K` is an isomorphism then

`e_{K,M} : R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_X} K ⟶ M`

is an isomorphism.

This is the shape in which the evaluation hypothesis `hev` of
`Stacks.SheafOfModules.exists_isInvertible_tensor_iso_of_affineLocal` ([Stacks, Tag 0ATP]) is
reduced to a statement about one object: two dualizing complexes differ by an invertible object,
and what is then owed is the homothety of a single dualizing complex and nothing about pairs. -/
theorem isIso_derivedSheafHomCounit_of_isIso_derivedSheafHomothety
    (K M : DerivedCategory (StructureSheafModules Rc))
    {L : DerivedCategory (StructureSheafModules Rc)}
    (hL : letI := derivedMonoidalStructure Rc; MonoidalCategory.IsInvertible L)
    (u : letI := derivedMonoidalStructure Rc; K ⊗ L ≅ M)
    (h : IsIso (derivedSheafHomothety Rc K)) :
    IsIso (derivedSheafHomCounit Rc K M) :=
  (isIso_derivedSheafHomCounit_iff_of_isInvertible Rc K K M hL u).2
    (isIso_derivedSheafHomCounit_self_of_isIso_derivedSheafHomothety Rc K h)

end Stacks.SheafOfModules

end
