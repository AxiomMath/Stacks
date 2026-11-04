module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# Inverse image on abelian étale sheaves, and restriction on étale cohomology

A morphism of schemes `i : Y ⟶ X` induces an inverse-image functor
`etaleAbelianInverseImage i` on abelian sheaves for the small étale topology, namely left Kan
extension along the opposite of base change followed by sheafification. This file establishes
the three properties of that functor which make it usable on cohomology, and then builds the
restriction map on étale cohomology that it induces.

The key property is **left exactness**. It does not come for free: it holds because base change
`smallEtaleBaseChange i` is representably flat, so the comma categories indexing the Kan
extension are filtered, and filtered colimits of abelian groups are exact. Carrying that
argument out requires evaluating the left Kan extension pointwise as a colimit over a
costructured-arrow category whose objects *and* morphisms live in `Type (u + 1)`. Mathlib's own
`CategoryTheory.lanEvaluationIsoColim` restricts all three category universes to the coefficient
hom universe and so does not apply; the universe-independent form
`Stacks.Topology.lanCompEvaluationIsoColim` is used instead. The same universe constraint forces
the coefficient category to sit in a universe at least `max (u + 1) v`, which is why the
`HasSheafify` hypotheses here are hypotheses rather than instances — Mathlib's instance for the
small étale site only covers coefficients in `Type u`-sized categories.

Restriction on cohomology is then assembled from two ingredients: the action of an exact functor
on `Ext`, and the canonical identification of the inverse image of the constant sheaf with the
constant sheaf. The latter is not a choice either — both functors are left adjoint to evaluation
at the final object, so they agree up to a unique isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianInverseImage` — inverse image on abelian étale sheaves.
* `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso` — inverse image carries the
  constant sheaf on a group to the constant sheaf on that group.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` — the induced map
  `H^q(X, F) → H^q(Y, i⁻¹F)` on étale cohomology.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianInverseImage_preservesFiniteLimits` — inverse image on
  abelian étale sheaves is left exact.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_apply` — the defining formula for
  restriction.

## References

* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

/-- The inverse-image functor on abelian sheaves for the small étale site: left Kan extension
along the opposite of base change, followed by sheafification. -/
public abbrev etaleAbelianInverseImage {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtaleBaseChange i) AddCommGrpCat.{max (u + 1) v}
    X.smallEtaleTopology Y.smallEtaleTopology

section InverseImage

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- Étale inverse image on abelian sheaves is left exact. The Kan extension is computed
pointwise as a colimit over a filtered costructured-arrow category, and the forgetful functor
from abelian groups preserves such filtered colimits, so the colimit functor is left exact;
sheafification is left exact in general. -/
public instance etaleAbelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (etaleAbelianInverseImage.{u, v} i) := by
  let G := smallEtaleBaseChange i
  have : PreservesFiniteLimits
      (G.op.lan : (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤ _) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max (u + 1) v}
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation _ J
    intro K
    have : IsFiltered (CostructuredArrow G.op K) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G K.unop)
    have : PreservesFilteredColimitsOfSize.{u, u + 1}
        (forget AddCommGrpCat.{max (u + 1) v}) :=
      preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
    have : PreservesFiniteLimits
        (colim : (CostructuredArrow G.op K ⥤ AddCommGrpCat.{max (u + 1) v}) ⥤ _) := by
      infer_instance
    exact preservesLimitsOfShape_of_natIso
      (Stacks.Topology.lanCompEvaluationIsoColim
        AddCommGrpCat.{max (u + 1) v} G.op K).symm
  infer_instance

/-- Étale inverse image on abelian sheaves is a left adjoint, with right adjoint the direct
image. -/
public instance etaleAbelianInverseImage_isLeftAdjoint :
    (etaleAbelianInverseImage.{u, v} i).IsLeftAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange i) _ _ _).isLeftAdjoint

/-- Étale inverse image on abelian sheaves is additive, since it preserves binary products. -/
public instance etaleAbelianInverseImage_additive :
    (etaleAbelianInverseImage.{u, v} i).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Inverse image carries the constant sheaf on an abelian group to the constant sheaf on that
group. There is no choice in the identification: both functors are left adjoint to evaluation at
the final object of the relevant site, and base change carries the final object to the final
object. -/
public def etaleAbelianInverseImageConstantIso :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
        etaleAbelianInverseImage.{u, v} i ≅
      constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} := by
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT.isTerminalObj (smallEtaleBaseChange i)
  exact ((constantSheafAdj _ _ hT).comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange i) _ _ _)).leftAdjointUniq
        (constantSheafAdj _ _ hGT)

end InverseImage

/-- The canonical map on étale cohomology induced by inverse image along a morphism of schemes:
apply the exact inverse-image functor to an `Ext` class out of the constant sheaf `ℤ`, then
identify the inverse image of that constant sheaf with the constant sheaf on the target. -/
public noncomputable def etaleCohomologyRestrictionMap
    {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Sheaf.H.{w} F q →+
      Sheaf.H.{w}
        ((Functor.sheafPullbackConstruction.sheafPullback
          (smallEtaleBaseChange i) AddCommGrpCat.{max (u + 1) v}
          X.smallEtaleTopology Y.smallEtaleTopology).obj F) q :=
  ((Abelian.Ext.mk₀
      ((etaleAbelianInverseImageConstantIso.{u, v} i).app (AddCommGrpCat.of (ULift ℤ))).inv).precomp
        ((etaleAbelianInverseImage.{u, v} i).obj F) (Nat.zero_add q)).comp
    ((etaleAbelianInverseImage.{u, v} i).mapExtAddHom
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift ℤ))) F q)

/-- Restriction is the map on `Ext` induced by exact inverse image, transported along the
canonical constant-sheaf comparison. -/
public theorem etaleCohomologyRestrictionMap_apply
    {X Y : Scheme.{u}} (i : Y ⟶ X)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    etaleCohomologyRestrictionMap i F q x =
      (Abelian.Ext.mk₀
        ((etaleAbelianInverseImageConstantIso.{u, v} i).app (AddCommGrpCat.of (ULift ℤ))).inv).comp
          (x.mapExactFunctor (etaleAbelianInverseImage.{u, v} i)) (Nat.zero_add q) := rfl

end Stacks.EtaleCohomology

end
