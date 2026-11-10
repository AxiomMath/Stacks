module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiAbelianSheafify
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonEmbedding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonExactness
import StacksCore.Tactic.StacksAttribute

/-!
# The derived unit of the Zariski comparison morphism

Let `X` be an object of the locally quasi-compact Zariski site, and let `π_X^{-1} ⊣ π_{X,*}` be
the comparison adjunction on abelian sheaves. Part of Stacks 0DCU is the assertion that for a
complex `F` of abelian sheaves on the space `X` the canonical map

`F ⟶ Rπ_{X,*} π_X^{-1} F`

is an isomorphism.

Both functors of the comparison adjunction are exact — the inverse image by
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianComparisonInverseImage_exact`, the
direct image by
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianComparisonDirectImage_exact` — so
each is induced on unbounded derived categories by its termwise action on complexes, with no
resolution needed: the right derived functor of `π_{X,*}` *is* the induced functor. The
adjunction therefore descends to the derived categories by localization, and the derived unit is
the localization of the termwise unit.

Termwise, the unit is the unit of the comparison adjunction in each degree, which is an
isomorphism by
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianComparisonAdjunction_unit_isIso`; a
map of complexes which is an isomorphism in every degree is an isomorphism, which gives the
claim on the image of `DerivedCategory.Q`, and every object of the derived category is
isomorphic to one of those.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianDerivedComparisonAdjunction`: the
  comparison adjunction on unbounded derived categories.

## Main results

* `abelianDerivedComparisonAdjunction_unit_isIso` (in the namespace
  `Stacks.Topology.LocallyQuasiCompactZariskiSituation`): its unit is a natural isomorphism.
* `abelianDerivedComparisonAdjunction_unit_isIso_unconditional`, in the same namespace: the
  same with the two sheafifications discharged rather than assumed. It is registered for the tag
  beside the form above.

## Implementation notes

The exactness of both functors is recorded as the four `PreservesFinite(Co)limits` instances
below, together with additivity, because that is the input the derived-category machinery takes.

`HasDerivedCategory.standard` is made a local instance, as the choice of universe for the
derived category is immaterial to the statement.

Stacks 0DCU numbers seven clauses, the last of which the source splits into (7a) and (7b), and
each is in the library and carries the tag where it is stated: the cohomology comparison
`zariskiCohomologyComparisonIso` (1), the exactness of the direct image
`abelianComparisonDirectImage_exact` (2), the invertibility of the unit
`abelianComparisonAdjunction_unit_isIso` (3), its derived counterpart
`abelianDerivedComparisonAdjunction_unit_isIso` (4), the commutative square
`zariskiComparisonSquareIso` (5), the relative cohomology comparison
`relativeZariskiCohomologyIso` (6), and the compatibility of the comparison with pushforward
along a *proper* morphism, `properDirectImageComparisonIsoOfProperMap` (7a) and
`properDerivedImageComparison_isIso` (7b). The clause stated in this file is (4); clause (3), the
underived unit it rests on, is in `ZariskiComparisonEmbedding.lean`.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- The comparison inverse image is right exact, being exact. -/
instance abelianComparisonInverseImage_preservesFiniteColimits
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    PreservesFiniteColimits (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X) :=
  ((exactFunctor_iff _).1 (S.abelianComparisonInverseImage_exact.{u, w, max (u + 1) v} X)).2

/-- The comparison direct image is left exact, being a right adjoint. -/
instance abelianComparisonDirectImage_preservesFiniteLimits
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    PreservesFiniteLimits (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}) :=
  ((exactFunctor_iff _).1 (abelianComparisonDirectImage_exact.{u, w, v} S X)).1

/-- The comparison direct image is right exact: this is the content of Stacks 0DCU for the
direct image, and is what makes its right derived functor the induced functor on complexes. -/
instance abelianComparisonDirectImage_preservesFiniteColimits
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    PreservesFiniteColimits (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}) :=
  ((exactFunctor_iff _).1 (abelianComparisonDirectImage_exact.{u, w, v} S X)).2

/-- The comparison inverse image is additive, being left exact. -/
noncomputable instance abelianComparisonInverseImage_additive
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category)
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] :
    (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The comparison direct image is additive, being left exact. -/
noncomputable instance abelianComparisonDirectImage_additive
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category)
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] :
    (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The comparison adjunction on unbounded derived categories, obtained by localizing the
termwise adjunction on complexes. Both functors are exact, so each is induced by its termwise
action and no resolutions intervene. -/
noncomputable def abelianDerivedComparisonAdjunction
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category)
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] :
    (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapDerivedCategory ⊣
      (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).mapDerivedCategory := by
  let _ : CatCommSq
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapHomologicalComplex
        (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapDerivedCategory :=
    ⟨(S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapDerivedCategoryFactors.symm⟩
  let _ : CatCommSq
      ((S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).mapHomologicalComplex
        (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).mapDerivedCategory :=
    ⟨(S.comparisonDirectImage X AddCommGrpCat).mapDerivedCategoryFactors.symm⟩
  exact ((S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).mapHomologicalComplex
      (ComplexShape.up ℤ)).localization
    DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ))
    DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)) _ _

/-- **Stacks 0DCU, the derived-unit clause.** The canonical map from a complex of abelian
sheaves on the space `X` to the derived direct image of its inverse image on the localized
Zariski site is an isomorphism, naturally in the complex. -/
@[stacks 0DCU "derived_unit"]
theorem abelianDerivedComparisonAdjunction_unit_isIso
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category)
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] :
    IsIso (abelianDerivedComparisonAdjunction.{u, w, v} S X).unit := by
  let C := Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}
  let F := S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X
  let G := S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}
  let adj : F ⊣ G := S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X
  let adjC := adj.mapHomologicalComplex (ComplexShape.up ℤ)
  have _ : IsIso adj.unit := abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  have hterm (P : CochainComplex C ℤ) : IsIso (adjC.unit.app P) := by
    have (i : ℤ) : IsIso ((adjC.unit.app P).f i) := by
      change IsIso (adj.unit.app (P.X i))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  let P : CochainComplex C ℤ := DerivedCategory.Q.objPreimage Y
  let eY : DerivedCategory.Q.obj P ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  have hQ : IsIso ((abelianDerivedComparisonAdjunction.{u, w, v} S X).unit.app
      (DerivedCategory.Q.obj P)) := by
    rw [abelianDerivedComparisonAdjunction, Adjunction.localization_unit_app]
    have _ := hterm P
    infer_instance
  have hn := (abelianDerivedComparisonAdjunction.{u, w, v} S X).unit.naturality eY.hom
  rw [Functor.id_map] at hn
  refine (isIso_comp_left_iff eY.hom _).mp ?_
  rw [hn]
  infer_instance

/-- **Stacks 0DCU, the derived-unit clause, with no hypothesis.** The canonical map from a
complex of abelian sheaves on the space `X` to the derived direct image of its inverse image on
the localized Zariski site is an isomorphism, naturally in the complex.

The two sheafifications the derived adjunction is built from are not assumed: both sites are
essentially small at this coefficient universe, so `hasSheafify_opensSite` and
`hasSheafify_zariskiSlice` supply them. -/
@[stacks 0DCU "derived_unit, with the two sheafifications discharged rather than assumed"]
theorem abelianDerivedComparisonAdjunction_unit_isIso_unconditional
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    letI := hasSheafify_opensSite.{u, w, v} S X
    letI := hasSheafify_zariskiSlice.{u, w, v} S X
    IsIso (abelianDerivedComparisonAdjunction.{u, w, v} S X).unit :=
  let := hasSheafify_opensSite.{u, w, v} S X
  let := hasSheafify_zariskiSlice.{u, w, v} S X
  abelianDerivedComparisonAdjunction_unit_isIso.{u, w, v} S X

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
