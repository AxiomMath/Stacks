module

public import StacksFrontier.CategoryTheory.Monoidal.CounitAtAnInvertibleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingHomEquivNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The evaluation morphism of a derived internal hom out of an invertible object

Let `(X, 𝒪_X)` be a ringed space. The bijection of [Stacks, Tag 08DI] identifies morphisms
`Z ⟶ R𝓗om_{𝒪_X}(L, M)` with morphisms `Z ⊗^L_{𝒪_X} L ⟶ M`, and the identification is

`u ↦ (u ⊗ 1_L) ≫ e`,

where `e : R𝓗om_{𝒪_X}(L, M) ⊗^L_{𝒪_X} L ⟶ M` is the evaluation morphism
`Stacks.SheafOfModules.derivedSheafHomCounit` — that is the naturality of [Stacks, Tag 08DI]
in its source variable, `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`,
read at the identity of `R𝓗om_{𝒪_X}(L, M)`.

From that formula and nothing else it follows that **if `L` is an invertible object of `D(𝒪_X)`
then the evaluation morphism is an isomorphism for every `M`**. The abstract statement is
`CategoryTheory.MonoidalCategory.isIso_of_isInvertible_of_tensorHomBijective`.

## Why this is wanted

The invertibility criterion
`Stacks.SheafOfModules.isInvertible_of_isIso_derivedUnitEvaluation` turns invertibility of the
*morphism* `R𝓗om_{𝒪_X}(L, 𝒪_X) ⊗^L_{𝒪_X} L ⟶ 𝒪_X` into invertibility of the *object* `L`, and
is what makes the invertible-object half of [Stacks, Tag 0ATP] local on a covering family.
Going the other way — from an invertible object to invertibility of that morphism — is what
lets the criterion be *fed* from a statement which only asserts that an inverse object exists,
which is the form in which the affine case of [Stacks, Tag 0A7F] is formalized
(`Stacks.Duality.exists_isInvertible_tensor_iso_derivedTilde`). The two together make
invertibility of the object and invertibility of its unit evaluation equivalent; see
`Stacks.SheafOfModules.isInvertible_iff_isIso_derivedUnitEvaluation`.

## Main results

* `Stacks.SheafOfModules.isIso_derivedSheafHomCounit_of_isInvertible`: the evaluation morphism
  out of an invertible object is an isomorphism.

## Implementation notes

The naturality input is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, the specialisation of
the three-variable naturality of [Stacks, Tag 08J8] to the source variable. It is stated on a
ringed site, and `Stacks.SheafOfModules.ringedSite` reads a ringed space as one, so no
comparison layer stands between the two settings.

*The spelling of the proof is forced.* The two settings are
interchangeable for the elaborator only in particular positions, and the budget it exhausts on
the others cannot be raised here. What holds, at the arguments below:

* the bijection of [Stacks, Tag 08DI] in the space spelling and
  `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` in the site spelling match by `rfl` when
  applied to a *variable*, and the evaluation morphism matches the site bijection at an
  explicitly written identity (the `hcounit` step);
* they do **not** match when applied to a *composite* `a ≫ g`. So the naturality equation is
  used in the site spelling throughout — `hnat` — and the composite never crosses over;
* `rw [Category.comp_id]` and `simp only [Category.comp_id]` on the naturality equation both
  exhaust the budget, so `a ≫ 𝟙` is removed by `congrArg` against an explicitly written
  function instead, which computes no motive;
* `u ▷ L` for `Stacks.SheafOfModules.derivedMonoidalStructure` *is*
  `((derivedTensor Rc).map u).app L` by `rfl`, the monoidal structure being re-seated onto the
  derived tensor product, so the whiskering needs no comparison;
* the bijection is read off the equivalence by `EquivLike.bijective` rather than
  by `AddEquiv.bijective`. The two differ in where the additive structure of
  `Z ⟶ R𝓗om_{𝒪_X}(L, M)` comes from: `AddEquiv.bijective` takes it as an instance argument, so
  it is synthesised afresh at the hom-type as the site spelling writes it, and there
  `Preadditive.homGroup` does not match; `EquivLike.bijective` takes the equivalence itself as
  the instance-carrying argument, so the additive structure used is the one
  `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` already carries.

The implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/LeftDualIsTheDerivedDual.lean` record the
same obstruction at the same bijection. It is no longer worked around there: the quantified form
`AlgebraicGeometry.RingedSite.DerivedCurrySourceNatural` is the theorem
`AlgebraicGeometry.RingedSite.derivedCurrySourceNatural`, proved by `apply` after `intro`, which
is the one spelling that matches the two statements without exhausting the budget.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
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

/-- **The evaluation morphism out of an invertible object is an isomorphism.** If `L` is an
invertible object of `D(𝒪_X)` ([Stacks, Tag 0FFN]) then

`R𝓗om_{𝒪_X}(L, M) ⊗^L_{𝒪_X} L ⟶ M`

is an isomorphism for every object `M` of `D(𝒪_X)`.

Nothing about dualizing complexes or about the space enters. The bijection of
[Stacks, Tag 08DI] exhibits `R𝓗om_{𝒪_X}(L, M)` as an internal hom *through this very morphism*
— that is its naturality in the source variable,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, at the identity — and
`CategoryTheory.MonoidalCategory.isIso_tensorHomEquiv_id_of_isInvertible` is that situation. -/
theorem isIso_derivedSheafHomCounit_of_isInvertible
    (L M : DerivedCategory (StructureSheafModules Rc))
    (hL : letI := derivedMonoidalStructure Rc; MonoidalCategory.IsInvertible L) :
    IsIso (derivedSheafHomCounit Rc L M) := by
  let := derivedMonoidalStructure Rc
  refine MonoidalCategory.isIso_of_isInvertible_of_tensorHomBijective
    (derivedSheafHomCounit Rc L M) (fun Z => ?_) hL
  have hnat : ∀ (a : Z ⟶ ((derivedSheafHom Rc).obj (op L)).obj M)
      (g : ((derivedSheafHom Rc).obj (op L)).obj M ⟶ ((derivedSheafHom Rc).obj (op L)).obj M),
      RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z L M (a ≫ g) =
        a ▷ L ≫ RingedSite.derivedCurryHomEquiv (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op L)).obj M) L M g :=
    fun a g => RingedSite.derivedCurryHomEquiv_naturality_source (ringedSite Rc) a g
  have hcounit : derivedSheafHomCounit Rc L M =
      RingedSite.derivedCurryHomEquiv (ringedSite Rc)
        (((derivedSheafHom Rc).obj (op L)).obj M) L M
        (𝟙 (((derivedSheafHom Rc).obj (op L)).obj M)) := rfl
  have hfun : (fun a : Z ⟶ ((derivedSheafHom Rc).obj (op L)).obj M =>
        a ▷ L ≫ derivedSheafHomCounit Rc L M) =
      ⇑(RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z L M) := by
    rw [hcounit]
    refine funext fun a => ?_
    have h0 := hnat a (𝟙 (((derivedSheafHom Rc).obj (op L)).obj M))
    exact h0.symm.trans
      (congrArg (fun v : Z ⟶ ((derivedSheafHom Rc).obj (op L)).obj M =>
        RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z L M v) (Category.comp_id a))
  rw [hfun]
  exact EquivLike.bijective (RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z L M)

end Stacks.SheafOfModules

end
