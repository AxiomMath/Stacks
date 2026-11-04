module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUniversalTransport
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAlgebraDescent

/-!
# The exterior-algebra description of the self-Ext algebra, and the comparison map

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` generate a sheaf of
ideals `𝓘`, write `O_X = O♯/𝓘`, and let `K` be a Koszul complex resolving the quotient. The
self-Ext sheaves `Ext^n_{O♯}(O_X, O_X)` form, under composition, a sheaf of graded
`O_X`-algebras whose degree-one generator has square zero
(`Stacks.RegularSequence.KoszulChainData.extSelfAlgebra`,
`Stacks.RegularSequence.KoszulChainData.squareZero_extSelfAlgebra`), and the universal property
of the exterior algebra over `O_X` of its degree-one piece produces the comparison map of Stacks
0BQY in every degree,

`⋀ⁱ_{O_X}(Ext^1_{O♯}(O_X, O_X)) ⟶ Ext^i_{O♯}(O_X, O_X)`.

This file records that the two possible formulations of the assertion of Stacks 0BQY are the
same assertion: the self-Ext algebra *is* an exterior algebra on its degree-one piece if and only
if the comparison map is an isomorphism in every degree. One direction is
`Stacks.RegularSequence.KoszulChainData.isIso_extComparison`, two graded algebras universal for
the same property being degreewise isomorphic by the map `desc` produces. The other is the
transport of a universal property along a degreewise isomorphism,
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_desc_isIso`.

The equivalence holds in every degree at once, degree zero included: both sides of the
comparison are formed over `O_X`, so no exterior-power comparison across two rings arises, and
the quantifier over `i : ℤ` needs no restriction.

## Main statements

* `Stacks.RegularSequence.KoszulChainData.extComparison_app_homogeneousProd`: **the comparison
  map carries a wedge of degree-one local sections to their composition product**, and
  `stalkMap_extComparison_germ_homogeneousProd` is the same formula on germs.
* `Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebra_of_isIso`: if the
  comparison map is an isomorphism in every degree, the self-Ext algebra is an exterior algebra
  on its degree-one piece.
* `Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebra_iff`: **the two
  formulations of Stacks 0BQY are equivalent.**
* `Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebra_iff_bijective_stalkMap`:
  the same, read pointwise — isomorphy of a morphism of sheaves of modules is detected on stalks,
  so the assertion is that the stalk of the comparison is bijective at every point in every
  degree.

## Implementation notes

**None of the equivalences is the tag.** Each carries the invertibility of the comparison as a
hypothesis on one side, which is the content of Stacks 0BQY itself; what is recorded here is
that the content may be established either as a universal property or as the invertibility of a
single named map, whichever is more convenient. Nothing in this development therefore carries
the `0BQY` attribute.

The remaining mathematical content is a germ-level computation. At a point `x`, writing `S` for
the stalk of `O_X`, the stalk of `Ext^1` is the dual of a free `S`-module of rank `r`
(`Stacks.RegularSequence.KoszulChainData.ext1StalkDualEquiv`) and the stalk of `Ext^m` is the
`m`-th exterior power of that dual
(`Stacks.RegularSequence.KoszulChainData.extStalkDualEquiv`); the stalk of the source of the
comparison is the `m`-th exterior power over `S` of the stalk of `Ext^1`. What is missing is the
identification of the stalk of the comparison itself with the duality pairing between the two,
which is the statement that the composition product of `m` degree-one classes becomes iterated
contraction — `Koszul.listContractionDual` — under those identifications. With that,
`Koszul.bijective_of_listContractionDual` gives bijectivity at every stalk by recognition rather
than by construction, and the theorems below convert it into the universal property.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

/-- **The comparison map of Stacks 0BQY is the composition product on wedges of degree-one local
sections.** The wedge of `s₀, …, s_{i-1}`, that is the ordered product of their images under the
degree-one generator of the exterior algebra over `O_X`, is carried to the ordered product of the
`sⱼ` themselves in the self-Ext algebra, which is their composition product.

This is what makes the comparison *the* map induced by composition. It holds for the single
reason that the comparison is a homomorphism of graded algebras extending the identity of the
degree-one piece. -/
theorem extComparison_app_homogeneousProd (i : ℕ) (U : (Opens ↥X)ᵒᵖ)
    (s : Fin i → ((extSelfAlgebra Rc K).piece 1).val.obj U) :
    (extComparison Rc K (i : ℤ)).val.app U
        ((extSelfExteriorAlgebra Rc K).exterior.toPresheafGradedAlgebra.homogeneousProd U i
          fun j => (extSelfExteriorAlgebra Rc K).exteriorGenerator.val.app U (s j)) =
      (extSelfAlgebra Rc K).toPresheafGradedAlgebra.homogeneousProd U i s :=
  SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd_comp
    ((extSelfExteriorAlgebra Rc K).exterior_isExteriorAlgebra.desc (extSelfAlgebra Rc K)
      (𝟙 ((extSelfAlgebra Rc K).piece 1)) (squareZero_extSelfAlgebra Rc K))
    (𝟙 ((extSelfAlgebra Rc K).piece 1))
    (((extSelfExteriorAlgebra Rc K).exterior_isExteriorAlgebra.desc_extends
      (extSelfAlgebra Rc K) (𝟙 ((extSelfAlgebra Rc K).piece 1))
      (squareZero_extSelfAlgebra Rc K)).trans (Category.id_comp _).symm) U i s

/-- **The stalk of the comparison map on the germ of a wedge.** The germ at `x` of the wedge of
`i` degree-one local sections is carried to the germ of their composition product. Germs of
wedges span the stalk of an exterior power, so this formula determines the stalk map, which is
the form in which a pointwise computation consumes it. -/
theorem stalkMap_extComparison_germ_homogeneousProd (i : ℕ) (x : ↥X) (U : Opens ↥X)
    (hx : x ∈ U) (s : Fin i → ((extSelfAlgebra Rc K).piece 1).val.obj (op U)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap _ x (extComparison Rc K (i : ℤ))).hom
        ((TopCat.Presheaf.germ
            ((extSelfExteriorAlgebra Rc K).exterior.piece (i : ℤ)).val.presheaf U x hx).hom
          ((extSelfExteriorAlgebra Rc K).exterior.toPresheafGradedAlgebra.homogeneousProd
            (op U) i fun j =>
              (extSelfExteriorAlgebra Rc K).exteriorGenerator.val.app (op U) (s j))) =
      (TopCat.Presheaf.germ ((extSelfAlgebra Rc K).piece (i : ℤ)).val.presheaf U x hx).hom
        ((extSelfAlgebra Rc K).toPresheafGradedAlgebra.homogeneousProd (op U) i s) :=
  (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x (extComparison Rc K (i : ℤ)) U hx _).trans
    (congrArg
      (fun z => (TopCat.Presheaf.germ ((extSelfAlgebra Rc K).piece (i : ℤ)).val.presheaf U x
        hx).hom z) (extComparison_app_homogeneousProd Rc K i (op U) s))

/-- **The self-Ext algebra is an exterior algebra on its degree-one piece as soon as the
comparison of Stacks 0BQY is an isomorphism in every degree.**

The comparison is the unital homomorphism that the universal property of the exterior algebra
over `O_X` of the degree-one piece produces from the tautological degree-one generator, which has
square zero; a degreewise isomorphism out of an exterior algebra transports the universal
property to its target. -/
theorem isExteriorAlgebra_extSelfAlgebra_of_isIso
    (h : ∀ i : ℤ, IsIso (extComparison Rc K i)) :
    SheafOfModules.GradedAlgebra.IsExteriorAlgebra (extSelfAlgebra Rc K)
      (𝟙 ((extSelfAlgebra Rc K).piece 1)) :=
  (extSelfExteriorAlgebra Rc K).exterior_isExteriorAlgebra.of_desc_isIso
    (𝟙 ((extSelfAlgebra Rc K).piece 1)) (squareZero_extSelfAlgebra Rc K) h

/-- **The two formulations of Stacks 0BQY are equivalent**: the self-Ext algebra of a
Koszul-regular quotient is an exterior algebra on its degree-one piece if and only if the
comparison map

`⋀ⁱ_{O_X}(Ext^1_{O♯}(O_X, O_X)) ⟶ Ext^i_{O♯}(O_X, O_X)`

induced by composition is an isomorphism for every `i : ℤ`. No degree is excluded, both sides
being formed over `O_X`. -/
theorem isExteriorAlgebra_extSelfAlgebra_iff :
    SheafOfModules.GradedAlgebra.IsExteriorAlgebra (extSelfAlgebra Rc K)
        (𝟙 ((extSelfAlgebra Rc K).piece 1)) ↔ ∀ i : ℤ, IsIso (extComparison Rc K i) :=
  ⟨fun hA i => isIso_extComparison Rc K hA i, isExteriorAlgebra_extSelfAlgebra_of_isIso Rc K⟩

/-- **Stacks 0BQY read pointwise.** Isomorphy of a morphism of sheaves of modules is detected on
stalks, so the self-Ext algebra of a Koszul-regular quotient is an exterior algebra on its
degree-one piece exactly when the stalk of the comparison map is bijective at every point of the
space, in every degree. -/
theorem isExteriorAlgebra_extSelfAlgebra_iff_bijective_stalkMap :
    SheafOfModules.GradedAlgebra.IsExteriorAlgebra (extSelfAlgebra Rc K)
        (𝟙 ((extSelfAlgebra Rc K).piece 1)) ↔
      ∀ (i : ℤ) (x : ↥X), Function.Bijective
        (AlgebraicGeometry.SheafOfModules.stalkMap _ x (extComparison Rc K i)).hom :=
  (isExteriorAlgebra_extSelfAlgebra_iff Rc K).trans
    (forall_congr' fun i => AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
      (extComparison Rc K i))

end Stacks.RegularSequence.KoszulChainData

end
