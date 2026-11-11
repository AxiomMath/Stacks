module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationDerivedInverseImageTriangulated
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# `a⁻¹` as an equivalence onto the cartesian bounded below derived category

Let `C` be a site with equalizers and fibre products, let `K` be a hypercovering of it and let
`a` be the augmentation of Stacks 0D8B from the total site `(C/K)_total` to `C`. Let
`𝒜 ⊂ Ab((C/K)_total)` be the weak Serre subcategory of cartesian abelian sheaves, which is
Stacks 0D7J. Stacks 0D8I asserts that

`a⁻¹ : D⁺(C) ⟶ D⁺_𝒜((C/K)_total)`

is an equivalence of categories, with quasi-inverse `R a_*`.

The proof is the one of Stacks 0D7U, carried out here for the adjunction `a⁻¹ ⊣ R a_*` on
*abelian* sheaves: the two derived functors restrict to the bounded below subcategories, the
restricted adjunction has both adjoints fully faithful by Stacks 0D7Q and 0D7R, and an adjunction
whose two adjoints are fully faithful is an equivalence. The library's own Stacks 0D7U,
`Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalence`, cannot be used instead: it
is stated for a `RingedToposSiteHom` and sheaves of *modules*, and says nothing about the
abelian-sheaf adjunction of a simplicial site.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalInverseImageObjIso`: the
  derived inverse image is the functor induced on derived categories by the exact degreewise
  inverse image, so `a⁻¹` of a complex is computed degreewise.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalInverseImageHomologyObjIso`
  and `.derivedTotalInverseImageSingleFunctorObjIso`: consequently `H^q(a⁻¹E) = a⁻¹H^q(E)`, and
  `a⁻¹` of a sheaf placed in degree zero is `a⁻¹` of it placed in degree zero.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalInverseImageEquivalence`:
  **the equivalence `D⁺(C) ≌ D⁺_𝒜((C/K)_total)` for a general augmentation**, granted that the
  unit is invertible on `D⁺(C)` and the counit on `D⁺_𝒜((C/K)_total)`.
* `Stacks.CategoryTheory.Hypercovering.derivedTotalInverseImageEquivalenceOfHypercovering`:
  the same for the augmentation of Stacks 0D8B attached to a hypercovering, assembled from the
  inputs of Stacks 0D8G and Stacks 0D8E passed as arguments, together with
  `.derivedTotalInverseImageEquivalenceOfHypercovering_functor` and `..._inverse` identifying
  its two functors with the restrictions of `a⁻¹` and of `R a_*`. Stacks 0D8I itself, with
  those inputs proved, is
  `Stacks.CategoryTheory.Hypercovering.derivedTotalInverseImageEquivalenceOfHypercovering'` in
  `StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBoundedBelowEquivalenceUnconditional`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.isGE_derivedTotalInverseImage_obj`,
  `.isLE_derivedTotalInverseImage_obj` and `.isGE_derivedTotalPushforward_obj`: both derived
  functors preserve boundedness below, and `a⁻¹` also boundedness above. The statement about
  `R a_*` is the orthogonality argument: `D^{≥n}` is the right orthogonal of `D^{≤n-1}`, and a
  morphism from `D^{≤n-1}` into `R a_*E` is adjoint to one out of `a⁻¹` of it, which stays in
  `D^{≤n-1}`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.derivedCategoryBPlus_derivedTotalPushforward_obj` and
  `.derivedCategoryBPlus_derivedTotalInverseImage_obj`: the two functors restrict to the
  bounded below subcategories. Both are unconditional; the cartesianness of `H^q(a⁻¹E)` is
  Stacks 0D7H.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.isIso_derivedCounit_app_of_isCartesian`:
  **the abelian form of Stacks 0D7S for this adjunction** — the counit is invertible at every
  object of `D⁺_𝒜((C/K)_total)` as soon as the unit is invertible on `D(C)` and every cartesian
  abelian sheaf is `a⁻¹` of an abelian sheaf on `C`.

## The inputs taken as arguments

`Stacks.CategoryTheory.Hypercovering.derivedTotalInverseImageEquivalenceOfHypercovering` takes
three named arguments, so that it can be stated in this file, before the library proves them.

* `hunit` and `hacyclic` are the two inputs of Stacks 0D8G, in the shape of
  `Stacks.CategoryTheory.Hypercovering.isIso_derivedAugmentationUnit_app_of_hypercovering`: the
  first is Stacks 0D8E in its abelian form, that the underived unit `F ⟶ a_*a⁻¹F` is an
  isomorphism, and the second is that `a⁻¹` of a K-injective complex computes `R a_*`. Both are
  proved for the augmentation of a hypercovering in `CategoryTheory.SimplicialSemiRepresentable`.
* `hsurj` is the essential surjectivity clause of Stacks 0D8E (2): every cartesian abelian sheaf
  on the total site lies in the essential image of `a⁻¹`. It is
  `CategoryTheory.SimplicialSemiRepresentable`
  `.essImage_situationTotalInverseImageAb_of_isCartesianAbSheaf`.

The unconditional Stacks 0D8I, discharging all three, is
`Stacks.CategoryTheory.Hypercovering.derivedTotalInverseImageEquivalenceOfHypercovering'`.

Nothing else is assumed. In particular the exactness of `a⁻¹` on derived categories, the
restriction of both functors to the bounded below subcategories, and the propagation of the
counit from `𝒜` to all of `D⁺_𝒜` are proved here.

## Implementation notes

`D⁺(C)` and `D⁺_𝒜((C/K)_total)` are both `DerivedCategoryB.derivedCategoryBPlus`, of the weak
Serre subcategory of *all* abelian sheaves on `C` and of the cartesian abelian sheaves on the
total site respectively. The source writes the first as `D⁺_{Ab(C)}(C)`, and
`derivedCategoryBPlus_top_iff` records that it is cohomological boundedness below and nothing
more. Taking the subcategory downstairs to be everything is what makes the restriction of
`R a_*` unconditional here, since the only condition left on its image is boundedness below.

The equivalence is the restricted adjunction, not an isomorphism assembled by hand, so its two
functors are the restrictions of `a⁻¹` and of `R a_*` on the nose. The propagation of the counit
along the truncation triangles is `CategoryTheory.NatTrans.isIso_app_of_isGE`, the generic
dévissage engine, and the propagation of the unit is not needed at all: Stacks 0D8G already gives
it on the whole unbounded derived category.

## References

* [Stacks Project, Tag 0D8I](https://stacks.math.columbia.edu/tag/0D8I)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0D7Q](https://stacks.math.columbia.edu/tag/0D7Q)
* [Stacks Project, Tag 0D7R](https://stacks.math.columbia.edu/tag/0D7R)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-! ### The derived inverse image is the degreewise inverse image -/

/-- The canonical comparison from the derived inverse image to the degreewise one is invertible:
`a⁻¹` is exact, so the degreewise functor already inverts the quasi-isomorphisms. -/
theorem isIso_derivedTotalInverseImageComparison :
    IsIso (derivedTotalInverseImageComparison S D K a) :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts (derivedTotalInverseImage S D K a)
    (derivedTotalInverseImageComparison S D K a)
    (fun _ _ s hs ↦ inverseImageInverts S D K a s hs trivial trivial)

/-- **`a⁻¹E` is computed degreewise.** The derived inverse image agrees with the functor induced
on derived categories by the exact functor `a⁻¹` of abelian sheaves. -/
def derivedTotalInverseImageObjIso (X : DerivedCategory (Sheaf K AddCommGrpCat.{u})) :
    (derivedTotalInverseImage S D K a).obj X ≅
      (totalInverseImageAb S D K a).mapDerivedCategory.obj X :=
  have := isIso_derivedTotalInverseImageComparison S D K a
  (derivedTotalInverseImage S D K a).mapIso
      (DerivedCategory.Qh.objObjPreimageIso X).symm ≪≫
    asIso ((derivedTotalInverseImageComparison S D K a).app
      (DerivedCategory.Qh.objPreimage X)) ≪≫
    ((totalInverseImageAb S D K a).mapDerivedCategoryFactorsh.app
      (DerivedCategory.Qh.objPreimage X)).symm ≪≫
    (totalInverseImageAb S D K a).mapDerivedCategory.mapIso
      (DerivedCategory.Qh.objObjPreimageIso X)

/-- **`H^q(a⁻¹E) = a⁻¹H^q(E)`**: the derived inverse image is degreewise, and an exact functor
commutes with the cohomology functors. -/
def derivedTotalInverseImageHomologyObjIso
    (X : DerivedCategory (Sheaf K AddCommGrpCat.{u})) (q : ℤ) :
    (DerivedCategory.homologyFunctor (Sheaf S.totalTopology AddCommGrpCat.{u}) q).obj
        ((derivedTotalInverseImage S D K a).obj X) ≅
      (totalInverseImageAb S D K a).obj
        ((DerivedCategory.homologyFunctor (Sheaf K AddCommGrpCat.{u}) q).obj X) :=
  (DerivedCategory.homologyFunctor (Sheaf S.totalTopology AddCommGrpCat.{u}) q).mapIso
      (derivedTotalInverseImageObjIso S D K a X) ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (totalInverseImageAb S D K a) q).app X

/-- **`a⁻¹` of a sheaf placed in degree zero is `a⁻¹` of it, placed in degree zero.** -/
def derivedTotalInverseImageSingleFunctorObjIso (F : Sheaf K AddCommGrpCat.{u}) :
    (derivedTotalInverseImage S D K a).obj
        ((DerivedCategory.singleFunctor (Sheaf K AddCommGrpCat.{u}) 0).obj F) ≅
      (DerivedCategory.singleFunctor (Sheaf S.totalTopology AddCommGrpCat.{u}) 0).obj
        ((totalInverseImageAb S D K a).obj F) :=
  derivedTotalInverseImageObjIso S D K a _ ≪≫
    ((totalInverseImageAb S D K a).mapDerivedCategorySingleFunctor 0).app F

/-! ### Boundedness -/

/-- **The derived inverse image preserves boundedness below.** It is degreewise, and an exact
functor commutes with the cohomology functors. -/
theorem isGE_derivedTotalInverseImage_obj (X : DerivedCategory (Sheaf K AddCommGrpCat.{u}))
    (n : ℤ) (hX : X.IsGE n) : ((derivedTotalInverseImage S D K a).obj X).IsGE n := by
  have := hX
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact ((totalInverseImageAb S D K a).map_isZero
    (DerivedCategory.isZero_of_isGE X n i hi)).of_iso
      (derivedTotalInverseImageHomologyObjIso S D K a X i)

/-- **The derived inverse image preserves boundedness above**, by the same argument. -/
theorem isLE_derivedTotalInverseImage_obj (X : DerivedCategory (Sheaf K AddCommGrpCat.{u}))
    (n : ℤ) (hX : X.IsLE n) : ((derivedTotalInverseImage S D K a).obj X).IsLE n := by
  have := hX
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact ((totalInverseImageAb S D K a).map_isZero
    (DerivedCategory.isZero_of_isLE X n i hi)).of_iso
      (derivedTotalInverseImageHomologyObjIso S D K a X i)

/-! ### The derived adjunction is an adjunction of triangulated functors -/

/-- The derived direct image commutes with the shift, being the right adjoint of a functor which
does. -/
instance commShift_derivedTotalPushforward :
    (derivedTotalPushforward S D K a).CommShift ℤ :=
  (derivedTotalAdjunction S D K a).rightAdjointCommShift ℤ

/-- The derived adjunction is compatible with the shift. -/
instance commShift_derivedTotalAdjunction : (derivedTotalAdjunction S D K a).CommShift ℤ :=
  (derivedTotalAdjunction S D K a).commShift_of_leftAdjoint ℤ

/-- The derived adjunction is an adjunction of triangulated functors, its left adjoint being
triangulated. -/
instance isTriangulated_derivedTotalAdjunction :
    (derivedTotalAdjunction S D K a).IsTriangulated :=
  Adjunction.IsTriangulated.mk' (derivedTotalAdjunction S D K a)

/-- The derived direct image is a triangulated functor, being the right adjoint of one. -/
instance isTriangulated_derivedTotalPushforward :
    (derivedTotalPushforward S D K a).IsTriangulated :=
  (derivedTotalAdjunction S D K a).isTriangulated_rightAdjoint

/-- **The derived direct image preserves boundedness below.** `D^{≥n}` is the right orthogonal
of `D^{≤n-1}`, and a morphism from an object `L` of `D^{≤n-1}` into `R a_*E` is adjoint to a
morphism `a⁻¹L ⟶ E` with `a⁻¹L` again in `D^{≤n-1}`, hence zero. -/
theorem isGE_derivedTotalPushforward_obj
    (X : DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u})) (n : ℤ) (hX : X.IsGE n) :
    ((derivedTotalPushforward S D K a).obj X).IsGE n := by
  have := hX
  change DerivedCategory.TStructure.t.IsGE ((derivedTotalPushforward S D K a).obj X) n
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro L g hL
  have := isLE_derivedTotalInverseImage_obj S D K a L (n - 1) hL
  have hzero := DerivedCategory.TStructure.t.zero
    (((derivedTotalAdjunction S D K a).homEquiv L X).symm g) (n - 1) n (by omega)
  have hz0 : ((derivedTotalAdjunction S D K a).homEquiv L X).symm 0 = 0 := by
    rw [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  exact ((derivedTotalAdjunction S D K a).homEquiv L X).symm.injective (hzero.trans hz0.symm)

/-! ### The two functors restrict to the bounded below subcategories -/

/-- **`D⁺(C)` is `D⁺_{Ab(C)}(C)`**: the bounded below subcategory attached to the weak Serre
subcategory of *all* abelian sheaves is cohomological boundedness below and nothing more, the
condition on the cohomology sheaves being vacuous. This is the identification the source makes
when it writes the source of the equivalence as `D⁺(C)`. -/
theorem derivedCategoryBPlus_top_iff {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (X : DerivedCategory A) :
    DerivedCategoryB.derivedCategoryBPlus (⊤ : ObjectProperty A) X ↔
      DerivedCategoryB.IsBoundedBelow X :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ ↦ trivial⟩⟩

/-- `D⁺(C)`: the bounded below derived category of abelian sheaves on the augmentation site,
written as `D⁺_{Ab(C)}(C)`, the bounded below subcategory attached to the weak Serre subcategory
of *all* abelian sheaves, which is how the source reads it. The condition on the cohomology
sheaves is vacuous: `derivedCategoryBPlus_top_iff`. -/
abbrev derivedPlusBase : ObjectProperty (DerivedCategory (Sheaf K AddCommGrpCat.{u})) :=
  DerivedCategoryB.derivedCategoryBPlus ⊤

/-- `D⁺_𝒜((C/K)_total)`: the bounded below objects of the derived category of abelian sheaves on
the total site all of whose cohomology sheaves are cartesian, `𝒜` being the weak Serre
subcategory of Stacks 0D7J. -/
abbrev derivedPlusCartesian :
    ObjectProperty (DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u})) :=
  DerivedCategoryB.derivedCategoryBPlus (IsCartesianAbSheaf S)

/-- **`R a_*` carries `D⁺_𝒜((C/K)_total)` into `D⁺(C)`.** Only boundedness below is at stake,
the weak Serre subcategory downstairs being all of `Ab(C)`. -/
theorem derivedCategoryBPlus_derivedTotalPushforward_obj
    (X : DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u}))
    (hX : DerivedCategoryB.IsBoundedBelow X) :
    derivedPlusBase D K
      ((derivedTotalPushforward S D K a).obj X) := by
  obtain ⟨n, hGE⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE X).1 hX
  exact (derivedCategoryBPlus_top_iff _).2 ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2
    ⟨n, isGE_derivedTotalPushforward_obj S D K a X n hGE⟩)

/-- **`a⁻¹` carries `D⁺(C)` into `D⁺_𝒜((C/K)_total)`.** It preserves boundedness below, and its
cohomology sheaves are `a⁻¹` of those of its argument, hence cartesian by Stacks 0D7H. -/
theorem derivedCategoryBPlus_derivedTotalInverseImage_obj
    (X : DerivedCategory (Sheaf K AddCommGrpCat.{u})) (hX : DerivedCategoryB.IsBoundedBelow X) :
    DerivedCategoryB.derivedCategoryBPlus (IsCartesianAbSheaf S)
      ((derivedTotalInverseImage S D K a).obj X) := by
  obtain ⟨n, hGE⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE X).1 hX
  refine ⟨(DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2
    ⟨n, isGE_derivedTotalInverseImage_obj S D K a X n hGE⟩, fun q ↦ ?_⟩
  exact ObjectProperty.prop_of_iso (P := IsCartesianAbSheaf S)
    (derivedTotalInverseImageHomologyObjIso S D K a X q).symm
    (isCartesianAbSheaf_totalInverseImageAb S D K a _)

/-! ### The counit on the cartesian bounded below derived category -/

/-- **The counit is invertible at a cartesian abelian sheaf placed in degree zero**, granted that
the derived unit is invertible and that every cartesian abelian sheaf is `a⁻¹` of an abelian
sheaf on `C`. Writing `M = a⁻¹N`, the sheaf `M` in degree zero is `a⁻¹` of `N` in degree zero,
and the counit at `a⁻¹` of an object at which the unit is invertible is invertible. -/
theorem isIso_derivedCounit_app_singleFunctor_obj
    (hunit : ∀ X, IsIso ((derivedTotalAdjunction S D K a).unit.app X))
    (hsurj : ∀ G : Sheaf S.totalTopology AddCommGrpCat.{u}, IsCartesianAbSheaf S G →
      (totalInverseImageAb S D K a).essImage G)
    (M : Sheaf S.totalTopology AddCommGrpCat.{u}) (hM : IsCartesianAbSheaf S M) :
    IsIso ((derivedTotalAdjunction S D K a).counit.app
      ((DerivedCategory.singleFunctor (Sheaf S.totalTopology AddCommGrpCat.{u}) 0).obj M)) := by
  obtain ⟨N, ⟨e⟩⟩ := hsurj M hM
  have eL := derivedTotalInverseImageSingleFunctorObjIso S D K a N ≪≫
    (DerivedCategory.singleFunctor (Sheaf S.totalTopology AddCommGrpCat.{u}) 0).mapIso e
  exact (NatTrans.isIso_app_iff_of_iso (derivedTotalAdjunction S D K a).counit eL).mp
    (Adjunction.isIso_counit_app_obj_of_isIso_unit_app (derivedTotalAdjunction S D K a) _
      (hunit _))

/-- **The abelian form of Stacks 0D7S for the derived augmentation adjunction.** The counit
`a⁻¹R a_*E ⟶ E` is invertible at every object `E` of `D⁺_𝒜((C/K)_total)`, granted the same two
inputs: the cohomology sheaves of `E` are cartesian, so the counit is invertible on each of them
placed in degree zero, and the dévissage along the truncation triangles propagates that to `E`
itself. Both `a⁻¹ ⋙ R a_*` and the identity are exact, commute with the shift and preserve
boundedness below. -/
theorem isIso_derivedCounit_app_of_isCartesian
    (hunit : ∀ X, IsIso ((derivedTotalAdjunction S D K a).unit.app X))
    (hsurj : ∀ G : Sheaf S.totalTopology AddCommGrpCat.{u}, IsCartesianAbSheaf S G →
      (totalInverseImageAb S D K a).essImage G)
    (X : DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u}))
    (hX : DerivedCategoryB.derivedCategoryBPlus (IsCartesianAbSheaf S) X) :
    IsIso ((derivedTotalAdjunction S D K a).counit.app X) := by
  obtain ⟨n, hGE⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE X).1 hX.1
  exact NatTrans.isIso_app_of_isGE (derivedTotalAdjunction S D K a).counit
    (fun L m h ↦ isGE_derivedTotalInverseImage_obj S D K a _ m
      (isGE_derivedTotalPushforward_obj S D K a L m h))
    (fun _ _ h ↦ h) X n hGE
    (fun q ↦ isIso_derivedCounit_app_singleFunctor_obj S D K a hunit hsurj _ (hX.2 q))

/-! ### The equivalence -/

/-- **`a⁻¹` restricted to `D⁺(C) ⥤ D⁺_𝒜((C/K)_total)`**, the forward functor of the
equivalence. -/
abbrev derivedTotalInverseImagePlus :
    (derivedPlusBase D K).FullSubcategory ⥤ (derivedPlusCartesian S).FullSubcategory :=
  (derivedPlusCartesian S).lift ((derivedPlusBase D K).ι ⋙ derivedTotalInverseImage S D K a)
    (fun X ↦ derivedCategoryBPlus_derivedTotalInverseImage_obj S D K a X.obj
      ((derivedCategoryBPlus_top_iff X.obj).1 X.property))

/-- **`R a_*` restricted to `D⁺_𝒜((C/K)_total) ⥤ D⁺(C)`**, the quasi-inverse of the
equivalence. -/
abbrev derivedTotalPushforwardPlus :
    (derivedPlusCartesian S).FullSubcategory ⥤ (derivedPlusBase D K).FullSubcategory :=
  (derivedPlusBase D K).lift ((derivedPlusCartesian S).ι ⋙ derivedTotalPushforward S D K a)
    (fun X ↦ derivedCategoryBPlus_derivedTotalPushforward_obj S D K a X.obj X.property.1)

/-- The restriction of the derived adjunction `a⁻¹ ⊣ R a_*` to the bounded below
subcategories. -/
def derivedTotalAdjunctionBoundedBelow :
    derivedTotalInverseImagePlus S D K a ⊣ derivedTotalPushforwardPlus S D K a :=
  (derivedTotalAdjunction S D K a).restrictFullyFaithful
    (derivedPlusBase D K).fullyFaithfulι
    (derivedPlusCartesian S).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- **`a⁻¹` is an equivalence `D⁺(C) ≌ D⁺_𝒜((C/K)_total)` with quasi-inverse `R a_*`**, for a
general augmentation, granted that the unit is invertible on `D⁺(C)` and the counit on
`D⁺_𝒜((C/K)_total)`.

The restricted left adjoint is fully faithful because `D⁺(C)` lies in the subcategory of
Stacks 0D7Q where the unit is invertible, the restricted right adjoint because
`D⁺_𝒜((C/K)_total)` lies in the subcategory of Stacks 0D7R where the counit is invertible; an
adjunction whose two adjoints are fully faithful is an equivalence. -/
def derivedTotalInverseImageEquivalence
    (hunitPlus : derivedPlusBase D K ≤
      (derivedTotalAdjunction S D K a).unitIsIso)
    (hcounitPlus : derivedPlusCartesian S ≤
      (derivedTotalAdjunction S D K a).counitIsIso) :
    (derivedPlusBase D K).FullSubcategory ≌
      (derivedPlusCartesian S).FullSubcategory :=
  letI hL := (derivedTotalAdjunction S D K a).fullyFaithfulιCompLeftAdjointOfLE hunitPlus
  letI hR := (derivedTotalAdjunction S D K a).fullyFaithfulιCompRightAdjointOfLE hcounitPlus
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (derivedTotalAdjunctionBoundedBelow S D K a).toEquivalence

/-- **The forward functor of the equivalence is `a⁻¹`.** -/
theorem derivedTotalInverseImageEquivalence_functor
    (hunitPlus : derivedPlusBase D K ≤ (derivedTotalAdjunction S D K a).unitIsIso)
    (hcounitPlus : derivedPlusCartesian S ≤ (derivedTotalAdjunction S D K a).counitIsIso) :
    (derivedTotalInverseImageEquivalence S D K a hunitPlus hcounitPlus).functor =
      derivedTotalInverseImagePlus S D K a :=
  rfl

/-- **The quasi-inverse of the equivalence is `R a_*`.** -/
theorem derivedTotalInverseImageEquivalence_inverse
    (hunitPlus : derivedPlusBase D K ≤ (derivedTotalAdjunction S D K a).unitIsIso)
    (hcounitPlus : derivedPlusCartesian S ≤ (derivedTotalAdjunction S D K a).counitIsIso) :
    (derivedTotalInverseImageEquivalence S D K a hunitPlus hcounitPlus).inverse =
      derivedTotalPushforwardPlus S D K a :=
  rfl

end CategoryTheory.SimplicialSiteSituation.Augmentation

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J)
  (hunit : IsIso (Augmentation.abelianTotalAdjunction (hypercoveringSituation J H) (Cat.of C)
    J.toGrothendieck (hypercoveringAugmentation J H)).unit)
  (hacyclic : Augmentation.InverseImageComputesDerivedPushforward
    (hypercoveringSituation J H) (Cat.of C) J.toGrothendieck (hypercoveringAugmentation J H))
  (hsurj : ∀ G : Sheaf (hypercoveringSituation J H).totalTopology AddCommGrpCat.{u},
    (hypercoveringSituation J H).IsCartesianAbSheaf G →
      (Augmentation.totalInverseImageAb (hypercoveringSituation J H) (Cat.of C)
        J.toGrothendieck (hypercoveringAugmentation J H)).essImage G)

include hunit hacyclic hsurj in
/-- **The equivalence of Stacks 0D8I, from the inputs of Stacks 0D8G and 0D8E.** For a site `C`
with equalizers and fibre products, a hypercovering `K` of it, the augmentation `a` of
Stacks 0D8B and the weak Serre subcategory `𝒜 ⊂ Ab((C/K)_total)` of cartesian abelian sheaves of
Stacks 0D7J, the derived inverse image is an equivalence

`a⁻¹ : D⁺(C) ⟶ D⁺_𝒜((C/K)_total)`

with quasi-inverse `R a_*`. Both functors of the equivalence are the restrictions of `a⁻¹` and
of `R a_*` on the nose, since the equivalence is the restricted adjunction.

Three arguments are taken. `hunit` and `hacyclic` are the two inputs of Stacks 0D8G, in the shape
of `isIso_derivedAugmentationUnit_app_of_hypercovering`: the first is Stacks 0D8E in its abelian
form, that the underived unit `F ⟶ a_*a⁻¹F` is an isomorphism, and the second is that `a⁻¹` of a
K-injective complex computes `R a_*`. `hsurj` is the essential surjectivity clause of
Stacks 0D8E (2), that every cartesian abelian sheaf on the total site lies in the essential image
of `a⁻¹`. The library proves all three for a hypercovering, and
`derivedTotalInverseImageEquivalenceOfHypercovering'` is Stacks 0D8I with them discharged. -/
def derivedTotalInverseImageEquivalenceOfHypercovering :
    (DerivedCategoryB.derivedCategoryBPlus
        (⊤ : ObjectProperty (Sheaf J.toGrothendieck AddCommGrpCat.{u}))).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus
        ((hypercoveringSituation J H).IsCartesianAbSheaf)).FullSubcategory :=
  have hall : ∀ X, IsIso ((Augmentation.derivedTotalAdjunction (hypercoveringSituation J H)
      (Cat.of C) J.toGrothendieck (hypercoveringAugmentation J H)).unit.app X) :=
    isIso_derivedAugmentationUnit_app_of_hypercovering J H hunit hacyclic
  Augmentation.derivedTotalInverseImageEquivalence _ _ _ _ (fun X _ ↦ hall X)
    (fun X hX ↦ Augmentation.isIso_derivedCounit_app_of_isCartesian _ _ _ _ hall hsurj X hX)

include hunit hacyclic hsurj in
/-- The forward functor of `derivedTotalInverseImageEquivalenceOfHypercovering` is `a⁻¹`: it is
the restriction of the derived inverse image to the bounded below subcategories. -/
theorem derivedTotalInverseImageEquivalenceOfHypercovering_functor :
    (derivedTotalInverseImageEquivalenceOfHypercovering J H hunit hacyclic hsurj).functor =
      Augmentation.derivedTotalInverseImagePlus (hypercoveringSituation J H) (Cat.of C)
        J.toGrothendieck (hypercoveringAugmentation J H) :=
  rfl

include hunit hacyclic hsurj in
/-- The quasi-inverse of `derivedTotalInverseImageEquivalenceOfHypercovering` is `R a_*`: it is
the restriction of the derived direct image to the bounded below subcategories. -/
theorem derivedTotalInverseImageEquivalenceOfHypercovering_inverse :
    (derivedTotalInverseImageEquivalenceOfHypercovering J H hunit hacyclic hsurj).inverse =
      Augmentation.derivedTotalPushforwardPlus (hypercoveringSituation J H) (Cat.of C)
        J.toGrothendieck (hypercoveringAugmentation J H) :=
  rfl

end Stacks.CategoryTheory.Hypercovering

end
