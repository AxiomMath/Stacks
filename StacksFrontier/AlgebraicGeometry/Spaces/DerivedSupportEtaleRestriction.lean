module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Étale restriction of a derived object away from its support

Let `X` be an algebraic space over a scheme `S` and let `E` be an object of `D(𝒪_X)` whose
cohomology sheaves are all supported on a subset `T` of `|X|`, in the sense of Stacks 08GF.
If `g : Y ⟶ X` is étale and the image of `|Y|` in `|X|` misses `T`, then the restriction of
`E` to `Y` vanishes.

## Main results

* `AlgebraicGeometry.Space.isZero_etaleModulePullback_mapDerivedCategory_of_disjoint`
  is the vanishing of the restriction.
* `AlgebraicGeometry.Space.isZero_etaleModulePullback_mapDerivedCategory_of_range_subset` is the
  case where `T` is the complement of the range of an open subspace and `|Y|` lands inside that
  range.
* `AlgebraicGeometry.Space.cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback` is
  the converse direction: a vanishing restriction forces support off the image of `|Y|`.

## Implementation notes

A derived object vanishes exactly when all of its cohomology vanishes,
`DerivedCategory.isZero_iff_forall_isZero_homology`; restriction along an étale morphism is
exact, so it commutes with cohomology by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, giving `Hⁿ(E|_Y) ≅ (Hⁿ E)|_Y`; the
support of a restriction along an étale morphism is the inverse image of the support, which is
`AlgebraicGeometry.Space.supportOfSheaf_toSheaf_etaleModulePullback`; and a module with empty
support is zero, by
`AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero`, which is Stacks 04K5.

## References

* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- **The restriction of a supported derived object to an étale space missing its support
vanishes.**  If every cohomology sheaf of `E` is supported on `T` and the image of `|Y|` in
`|X|` is disjoint from `T`, then `E|_Y = 0` in `D(𝒪_Y)`. -/
theorem isZero_etaleModulePullback_mapDerivedCategory_of_disjoint
    {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (T : Set (points B S hS X.1))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : CohomologySupportedOn B S hS X.1 X.2 T E)
    (hdisj : Disjoint (Set.range (pointsMap B S hS Y.1 g.hom)) T) :
    IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  refine IsZero.of_iso ?_
    (((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryHomologyIso n).app E)
  show IsZero ((etaleModulePullback.{u, u} B S hS g hg).obj
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj E))
  have hsupp := supportOfSheaf_toSheaf_etaleModulePullback B S hS g hg
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj E)
  exact (supportOfSheaf_eq_empty_iff_isZero B S hS Y _).mp
    (Set.eq_empty_iff_forall_notMem.mpr fun p hp =>
      Set.disjoint_left.mp hdisj ⟨p, rfl⟩ (hE n (hsupp.subset hp)))

/-- If every cohomology sheaf of `E` is supported on the complement of the range of the map on
points of `i`, and the image of `|Y|` lies inside that range, then `E|_Y = 0`. -/
theorem isZero_etaleModulePullback_mapDerivedCategory_of_range_subset
    {X Y : AlgebraicSpaces B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : Z ⟶ X.1}
    (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : CohomologySupportedOn B S hS X.1 X.2
      (Set.range (pointsMap B S hS Z i))ᶜ E)
    (hrange : Set.range (pointsMap B S hS Y.1 g.hom) ⊆ Set.range (pointsMap B S hS Z i)) :
    IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E) :=
  isZero_etaleModulePullback_mapDerivedCategory_of_disjoint B S hS g hg _ E hE
    (Set.disjoint_right.mpr fun _ ha hb => ha (hrange hb))

/-- **The restriction of a module along an étale morphism vanishes exactly when its support
misses the image of the points.** -/
theorem isZero_etaleModulePullback_iff_disjoint_supportOfSheaf
    {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    IsZero ((etaleModulePullback.{u, u} B S hS g hg).obj M) ↔
      Disjoint (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M))
        (Set.range (pointsMap B S hS Y.1 g.hom)) := by
  rw [← supportOfSheaf_eq_empty_iff_isZero B S hS Y,
    supportOfSheaf_toSheaf_etaleModulePullback B S hS g hg M, Set.preimage_eq_empty_iff]

/-- **An object of `D(𝒪_X)` whose restriction along an étale morphism `g : Y ⟶ X` vanishes has
its cohomology supported outside the image of `|Y|`.** -/
theorem cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback
    {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E)) :
    CohomologySupportedOn B S hS X.1 X.2
      (Set.range (pointsMap B S hS Y.1 g.hom))ᶜ E := fun i =>
  Set.subset_compl_iff_disjoint_right.2
    ((isZero_etaleModulePullback_iff_disjoint_supportOfSheaf B S hS g hg _).1
      ((Functor.map_isZero
          (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i) hE).of_iso
        (((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryHomologyIso i).app E).symm))

end AlgebraicGeometry.Space

end
