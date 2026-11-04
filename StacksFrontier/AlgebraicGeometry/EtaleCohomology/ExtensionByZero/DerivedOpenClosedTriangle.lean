module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactFunctorsTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence

/-!
# The distinguished triangle of a closed subscheme and its open complement

Let `X` be a scheme, let `i : Z ⟶ X` be a closed immersion and let `j : U ⟶ X` be an open
immersion whose image is the complement of the image of `i`.  For every object `K` of the derived
category of abelian sheaves on the small étale site of `X` there is a distinguished triangle
`j_! j^{-1} K ⟶ K ⟶ i_* i^{-1} K ⟶ (j_! j^{-1} K)[1]`,
the first two arrows being the counit of `j_! ⊣ j^{-1}` and the unit of `i^{-1} ⊣ i_*` induced on
the derived category.

This is the derived form of the short exact sequence of Stacks Tag 095L, which this file takes
from `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence`.  The
four functors involved are exact, so their derived versions are computed by applying them to any
complex of sheaves representing `K`; that is what `CategoryTheory.Functor.mapDerivedCategory`
does, and it is why no right or left derived functor appears.

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroOfRestriction`: the endofunctor `j_! j^{-1}` of abelian
  sheaves on `X_étale`, for an étale morphism `j`.
* `Stacks.EtaleCohomology.etaleAbelianDirectImageOfInverseImage`: the endofunctor `i_* i^{-1}`.

## Main results

* `Stacks.EtaleCohomology.exists_distTriang_extensionByZero_etaleAbelianDirectImage`: **Stacks
  Project, Tag 0GKL** for abelian coefficients, the distinguished triangle
  `j_! j^{-1} K ⟶ K ⟶ i_* i^{-1} K ⟶ (j_! j^{-1} K)[1]`.
* `Stacks.EtaleCohomology.etaleAbelianDirectImageOfInverseImage_preservesFiniteColimits`: the
  functor `i_* i^{-1}` is right exact for a closed immersion `i`, hence (being left exact for
  formal reasons) exact.

## Coefficients

Stacks Tag 0GKL is stated for an arbitrary coefficient ring `Λ` and the derived category
`D(X_étale, Λ)` of sheaves of `Λ`-modules; the theorem below is the case of abelian sheaves,
that is `Λ = ℤ`, and its tag attribute carries the qualifier `"abelian coefficients"`.  The
general case is
`Stacks.EtaleCohomology.exists_distTriang_etaleModuleExtensionByZero_directImage` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle`, which
carries the unqualified tag.  Nothing in the derived-category argument uses the coefficients:
the general statement `DerivedCategory.exists_distTriang_of_natTrans_shortExact` in
`StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactFunctorsTriangle` holds over any abelian
category.  Its input for module coefficients, the short exact sequence of Tag 095L for sheaves
of `Λ`-modules, is proved in that file by the stalkwise argument of the abelian case, `j_!` and
its exactness for module coefficients being
`Stacks.EtaleCohomology.etaleModuleExtensionByZero` and
`Stacks.EtaleCohomology.etaleModuleExtensionByZero_preservesFiniteLimits`.

## Implementation notes

Exactness of `j_! j^{-1}` is a composite of two exactness statements already in the library:
restriction along an étale morphism is exact because it is simultaneously a left and a right
adjoint, and `j_!` is exact by Stacks Tag 03S5
(`Stacks.EtaleCohomology.extensionByZero_preservesFiniteLimits`).

Exactness of `i_* i^{-1}` is *not* taken from a pushforward-exactness theorem for closed
immersions.  Left exactness is formal — `i^{-1}` preserves finite limits and `i_*` is a right
adjoint — and right exactness is read off the short exact sequence itself: the component
`F ⟶ i_* i^{-1} F` of the unit is an epimorphism for every `F`, so
`CategoryTheory.Functor.preservesEpimorphisms_of_epi_natTrans_app_from_id` makes `i_* i^{-1}`
preserve epimorphisms, and a functor between abelian categories preserving kernels and
epimorphisms preserves homology, hence finite colimits.  To make this an instance, available
while the statement of the triangle is being elaborated, it is proved for an arbitrary closed
immersion: the open complement of the image of `i` is an open subscheme of `X` whose inclusion
is an open immersion with the required range, so the short exact sequence applies to it.

Additivity of `i_* i^{-1}` is proved for the composite directly, from preservation of binary
products, rather than by restating additivity of `i_*`: the library already has that twice, as
`Stacks.EtaleCohomology.etaleAbelianDirectImage_additive` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors` and in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDirectImage`, neither of which
is in this file's import closure.

The composite of the two canonical arrows vanishes by
`Stacks.EtaleCohomology.extensionByZero_counit_comp_inverseImage_unit`, so the short complex the
triangle refers to is built from exactly those two arrows and nothing is chosen.

The existence of a derived category with hom sets in a fixed universe is an instance hypothesis
`[HasDerivedCategory.{w} _]`, as throughout Mathlib; it can always be supplied by
`HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0GKL](https://stacks.math.columbia.edu/tag/0GKL)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe w u v

namespace Stacks.EtaleCohomology

/-! ### The two endofunctors -/

/-- The endofunctor `j_! j^{-1}` of abelian sheaves on the small étale site of `X`, for an étale
morphism `j : U ⟶ X`: restrict to `U`, then extend by zero. -/
abbrev extensionByZeroOfRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  etaleRestriction.{u, v} j ⋙ extensionByZero.{u, v} j

/-- The endofunctor `i_* i^{-1}` of abelian sheaves on the small étale site of `X`, for a
morphism of schemes `i : Z ⟶ X`: take the inverse image to `Z`, then push forward. -/
abbrev etaleAbelianDirectImageOfInverseImage {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  etaleAbelianInverseImage.{u, v} i ⋙ etaleAbelianDirectImage.{u, v} i

/-- The composite `i_* i^{-1}` is additive, preserving binary products: the inverse image
preserves finite limits and the direct image preserves all limits, being a right adjoint. -/
instance etaleAbelianDirectImageOfInverseImage_additive {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (etaleAbelianDirectImageOfInverseImage.{u, v} i).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### Exactness of `i_* i^{-1}` -/

section Complementary

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

include hij

/-- Each component `F ⟶ i_* i^{-1} F` of the unit of `i^{-1} ⊣ i_*` is an epimorphism: it is the
right-hand map of the short exact sequence of Stacks Tag 095L. -/
theorem epi_etaleAbelianInverseImageDirectImageAdj_unit_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    Epi ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit.app F) := by
  obtain ⟨_, hF⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v} i j hij F
  exact hF.epi_g

/-- The composite `i_* i^{-1}` preserves epimorphisms: the unit of `i^{-1} ⊣ i_*` is a natural
transformation from the identity functor with epimorphic components. -/
theorem etaleAbelianDirectImageOfInverseImage_preservesEpimorphisms_of_range_eq_compl :
    (etaleAbelianDirectImageOfInverseImage.{u, v} i).PreservesEpimorphisms :=
  Functor.preservesEpimorphisms_of_epi_natTrans_app_from_id
    (etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit
    (epi_etaleAbelianInverseImageDirectImageAdj_unit_app.{u, v} i j hij)

end Complementary

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The composite `i_* i^{-1}` along a closed immersion preserves epimorphisms.  The open
complement of the image of `i` is an open subscheme of `X` whose inclusion has exactly the
complementary range, so the short exact sequence of Stacks Tag 095L applies. -/
instance etaleAbelianDirectImageOfInverseImage_preservesEpimorphisms :
    (etaleAbelianDirectImageOfInverseImage.{u, v} i).PreservesEpimorphisms := by
  let V : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  exact etaleAbelianDirectImageOfInverseImage_preservesEpimorphisms_of_range_eq_compl.{u, v}
    i V.ι (by simp [V])

/-- The composite `i_* i^{-1}` along a closed immersion is right exact: it preserves kernels,
being left exact, and it preserves epimorphisms, so it preserves homology and therefore finite
colimits.  Together with left exactness this says that `i_* i^{-1}` is exact. -/
instance etaleAbelianDirectImageOfInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (etaleAbelianDirectImageOfInverseImage.{u, v} i) := by
  have := Functor.preservesHomology_of_preservesEpis_and_kernels
    (etaleAbelianDirectImageOfInverseImage.{u, v} i)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end ClosedImmersion

/-! ### The distinguished triangle -/

/-- **Stacks Project, Tag 0GKL, for abelian coefficients.**  Let `X` be a scheme, let
`i : Z ⟶ X` be a closed immersion and let `j : U ⟶ X` be an open immersion whose image is the
complement of the image of `i`.  For every object `K` of the derived category of abelian sheaves
on the small étale site of `X` there is a distinguished triangle
`j_! j^{-1} K ⟶ K ⟶ i_* i^{-1} K ⟶ (j_! j^{-1} K)[1]`,
whose first arrow is the counit of `j_! ⊣ j^{-1}` and whose second arrow is the unit of
`i^{-1} ⊣ i_*`, both induced on the derived category by exactness of the four functors
involved.

The source states the triangle for sheaves of `Λ`-modules over an arbitrary ring `Λ`; this is the
case `Λ = ℤ`, the general case being
`Stacks.EtaleCohomology.exists_distTriang_etaleModuleExtensionByZero_directImage`. -/
@[stacks 0GKL "abelian coefficients"]
theorem exists_distTriang_extensionByZero_etaleAbelianDirectImage {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    ∃ δ : (etaleAbelianDirectImageOfInverseImage.{u, v} i).mapDerivedCategory.obj K ⟶
        ((extensionByZeroOfRestriction.{u, v} j).mapDerivedCategory.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk
        (((extensionByZeroOfRestriction.{u, v} j).mapDerivedCategoryTransToId
          (extensionByZeroAdj.{u, v} j).counit).app K)
        (((etaleAbelianDirectImageOfInverseImage.{u, v} i).mapDerivedCategoryTransFromId
          (etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit).app K) δ ∈
        distTriang (DerivedCategory
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) := by
  refine DerivedCategory.exists_distTriang_of_natTrans_shortExact
    (extensionByZeroOfRestriction.{u, v} j) (etaleAbelianDirectImageOfInverseImage.{u, v} i)
    (extensionByZeroAdj.{u, v} j).counit
    (etaleAbelianInverseImageDirectImageAdj.{u, v} i).unit
    (extensionByZero_counit_comp_inverseImage_unit i j hij) (fun F ↦ ?_) K
  obtain ⟨_, hF⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, v} i j hij F
  exact hF

end Stacks.EtaleCohomology

end
