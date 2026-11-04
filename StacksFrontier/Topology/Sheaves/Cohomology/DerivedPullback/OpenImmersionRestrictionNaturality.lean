module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChangeDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional

/-!
# Naturality of the derived-pullback-is-restriction comparison in the open subspace

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose pullback `f^*` of sheaves of
modules is exact — an open immersion, for instance.  Then
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory` identifies the left
derived pullback `Lf^*` with the functor `D(f^*)` induced degreewise.  That identification is a
comparison between two *left derived functors of the same functor*, so it is pinned down by the
universal property, and therefore it is compatible with everything else that is: in particular
with the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Tag 0D5S.

This file records that compatibility.  Specialized to the inclusion of an open subspace `V ⊆ X`
and of an open subspace `W` of `V`, it says that the comparison for the composite inclusion is the
comparison for `V`, followed by the comparison for `W` inside `V`, followed by the degreewise
composition isomorphism — which is the *naturality in the open subspace* that
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso` was missing.  The
passage from the open-immersion spelling to the restriction-functor spelling of Tag 08BW is
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso_eq`: the restriction
comparison is the open-immersion comparison followed by the degreewise change of spelling
`Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso`.

## Main definitions

* `Stacks.Homology.mapDerivedCategoryComparisonOfIso`: the comparison exhibiting
  `G.mapDerivedCategory` as a left derived functor of `K(F) ⋙ Q_h` along an isomorphism
  `F ≅ G` with `G` exact.  It is the structure map against which
  `Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso` is characterized.
* `Stacks.Homology.mapDerivedCategoryIsoOfIso`: an isomorphism of exact functors induces an
  isomorphism of the functors they induce on derived categories.
* `Stacks.Homology.mapDerivedCategoryCompComparison`: the comparison exhibiting
  `D(F) ⋙ D(G)` as a left derived functor of `K(H) ⋙ Q_h` along an isomorphism `F ⋙ G ≅ H`.
* `Stacks.Homology.mapDerivedCategoryCompIso`: an isomorphism `F ⋙ G ≅ H` of exact functors
  induces `D(F) ⋙ D(G) ≅ D(H)`.  This is
  `CategoryTheory.Functor.mapDerivedCategoryCompIso`, which is in turn
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` followed by the degreewise change
  of functor; the development has one construction of this comparison, not three.

## Main results

* `Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_hom_app` and
  `Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app`: the universal property that
  characterizes the two comparisons of
  `StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor`, read at an object of
  the homotopy category.  Everything below is deduced from these.
* `Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_eq`: the twisted comparison is the
  untwisted one followed by the degreewise change of functor.
* `Stacks.Homology.mapDerivedCategoryCompIso_hom_app` and
  `Stacks.Homology.whiskerLeft_mapDerivedCategoryCompIso_hom`: the universal property of the
  composition isomorphism of induced functors, at an object and as an equality of natural
  transformations.
* `Stacks.Homology.mapDerivedCategoryCompIso_refl_eq`: **the two constructions of the composition
  comparison agree.**  At `e = Iso.refl` the comparison here is the inverse of
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, which is stated with its sides
  swapped.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory_comp`: **the
  compatibility.**  For composable morphisms of ringed spaces with exact pullbacks, the square
  built from the composition isomorphism of Tag 0D5S, the two comparisons and the degreewise
  composition isomorphism commutes.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso_comp`: the same for two
  composable open immersions, where no exactness hypothesis is left over, stated as an equality of
  isomorphisms.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso_ofRestrict_comp`:
  **naturality in the open subspace**, at an open subspace of an open subspace.
* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso_eq`: the restriction
  comparison in the spelling of Tag 08BW is the open-immersion comparison followed by the
  degreewise change of spelling.

## Implementation notes

**Why the universal property, and not a diagram chase.**  All four functors in the square are
left derived functors of degreewise pullback along `f ≫ g`: two of them by Tag 0D5S and its
inputs, and the two degreewise ones because an exact functor is its own left derived functor.  A
natural transformation *into* a left derived functor is determined by its composite with the
structure map, `CategoryTheory.Functor.leftDerived_ext`; so the square commutes as soon as it
commutes after composing with the structure map of the target, and there it is the already
recorded factorization `derivedPullbackCompIsoCanonical_hom_app_comp_comparison` of
`Stacks.Cohomology.DerivedPushforwardComposition`,
together with naturality of the comparison for `f`.  No property of ringed spaces is used.

**The chase that is left is abstract.**  After the four factorizations are inserted, what remains
is an identity between two composites of six morphisms in a single category, valid for formal
reasons; it is isolated as the private `comp_chase`, stated for an arbitrary functor between
arbitrary categories, so that the remaining rewriting happens in a context with no derived
categories in it.  This is deliberate: `rewrite` on a goal that mentions
`Stacks.Homology.mapDerivedCategoryCompIso` has to re-check the motive, and that unfolds a lift
through a localization, which does not terminate inside the default heartbeat budget.

**The composition comparison is not built here.**  It used to be, out of the uniqueness of a left
derived functor; it is now
`CategoryTheory.Functor.mapDerivedCategoryCompIso`, hence
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` inverted and followed by the
degreewise change of functor.  What the file still owns is the *characterization*
`Stacks.Homology.mapDerivedCategoryCompIso_hom_app` — unchanged, and now read off the value
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh` of that one construction over
`DerivedCategory.Qh` — and the identification
`Stacks.Homology.mapDerivedCategoryCompIso_refl_eq` of the two readings, which is what lets a
square built here meet one built from the comparison over `DerivedCategory.Q`.

**Why the `Functor.Additive` instance of restriction is passed by hand.**  The implementation
notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/OpenImmersionRestriction.lean` explain
that the two spellings `structureSheafRing (X.restrict U.isOpenEmbedding)` and
`ExtensionByZeroModules.resRing U (structureSheafRing X)` of the structure sheaf of an open
subspace give two routes to the `CategoryTheory.Preadditive` instance of the category of modules
on `U`, equal only at default transparency.  Instance search therefore does not find
`ExtensionByZeroModules.jStar_additive` for the spelling in which
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso` is stated, and the
instance binders of `Stacks.Homology.mapDerivedCategoryIsoOfIso` are named so that it can be
supplied as a term, where the conversion check runs at default transparency.  This is the same
crossing that file pays twice.

**No `@[stacks]` attribute.**  Nothing here is a result of the Stacks project: the content is the
universal property of a left derived functor, applied to comparisons that this development
constructs.  Tag 0D5S, which the square uses, is registered at
`Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparisonCanonical`.

**Blocked consumers.**  The missing naturality is named as the obstruction in the implementation
notes of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentAffineEssentialSurjectivity.lean` (the
globalization of the essential-surjectivity half of Stacks 0DI8 off its affine case), of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedCategory/GlueingOverAFiniteCover.lean` (the
two-open case of Stacks 0D6A, where `Stacks.Cohomology.GlueingComplexes.exists_glueing` is stated
for derived pullback and Situation 0D67 for restriction functors), and of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/OpenImmersionRestriction.lean` itself.

## References

* [Stacks Project, Lemma 20.28.6 (Tag 079W)](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Lemma 20.28.9 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Lemma 20.33.4 (Tag 08BW)](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Lemma 20.47.1 (Tag 08DG)](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Lemma 20.47.2 (Tag 08DR)](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Homology

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

/-! ### The universal property of the two comparisons -/

/-- **The functor an exact functor induces on derived categories is a left derived functor.**
Its structure map `CategoryTheory.Functor.mapDerivedCategoryFactorsh` is invertible, so it
inverts the quasi-isomorphisms. -/
instance isLeftDerivedFunctor_mapDerivedCategoryFactorsh (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh

/-- **`G.mapDerivedCategory` as a left derived functor of `K(F) ⋙ Q_h` along `e : F ≅ G`.**  This
is the structure map that
`Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso` compares against: the comparison
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of `G`, followed by `e⁻¹` read on homotopy
categories. -/
def mapDerivedCategoryComparisonOfIso (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    DerivedCategory.Qh ⋙ G.mapDerivedCategory ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  G.mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight (mapHomotopyCategoryIso e.symm (ComplexShape.up ℤ))
      DerivedCategory.Qh

/-- At the identity isomorphism the structure map is the comparison of `F` itself. -/
theorem mapDerivedCategoryComparisonOfIso_refl (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    mapDerivedCategoryComparisonOfIso F F (Iso.refl F) = F.mapDerivedCategoryFactorsh := by
  ext K
  simp [mapDerivedCategoryComparisonOfIso, mapHomotopyCategoryIso,
    NatTrans.mapHomotopyCategory_id]

/-- **The universal property of `Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso`.**  It is
the unique map of left derived functors whose composite with the structure map of the target is
the structure map of the source. -/
theorem whiskerLeft_leftDerivedIsoMapDerivedCategoryOfIso_hom (F G : A ⥤ B)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (e : F ≅ G) :
    Functor.whiskerLeft DerivedCategory.Qh
        (leftDerivedIsoMapDerivedCategoryOfIso F G LF α e).hom ≫
      (mapDerivedCategoryComparisonOfIso F G e).hom = α := by
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G.mapDerivedCategory
    (mapDerivedCategoryComparisonOfIso F G e)
  exact (Functor.leftDerivedNatTrans_fac LF G.mapDerivedCategory α
    (mapDerivedCategoryComparisonOfIso F G e).hom
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (𝟙 (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))).trans
    (Category.comp_id α)

/-- `Stacks.Homology.whiskerLeft_leftDerivedIsoMapDerivedCategoryOfIso_hom` at an object of the
homotopy category. -/
theorem leftDerivedIsoMapDerivedCategoryOfIso_hom_app (F G : A ⥤ B)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (e : F ≅ G) (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (leftDerivedIsoMapDerivedCategoryOfIso F G LF α e).hom.app (DerivedCategory.Qh.obj K) ≫
        (mapDerivedCategoryComparisonOfIso F G e).hom.app K = α.app K :=
  NatTrans.congr_app (whiskerLeft_leftDerivedIsoMapDerivedCategoryOfIso_hom F G LF α e) K

/-- **The universal property of `Stacks.Homology.leftDerivedIsoMapDerivedCategory`.** -/
theorem whiskerLeft_leftDerivedIsoMapDerivedCategory_hom (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    Functor.whiskerLeft DerivedCategory.Qh
        (leftDerivedIsoMapDerivedCategory F LF α).hom ≫
      F.mapDerivedCategoryFactorsh.hom = α :=
  mapDerivedCategoryComparisonOfIso_refl F ▸
    whiskerLeft_leftDerivedIsoMapDerivedCategoryOfIso_hom F F LF α (Iso.refl F)

/-- `Stacks.Homology.whiskerLeft_leftDerivedIsoMapDerivedCategory_hom` at an object of the
homotopy category. -/
theorem leftDerivedIsoMapDerivedCategory_hom_app (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (leftDerivedIsoMapDerivedCategory F LF α).hom.app (DerivedCategory.Qh.obj K) ≫
        F.mapDerivedCategoryFactorsh.hom.app K = α.app K :=
  NatTrans.congr_app (whiskerLeft_leftDerivedIsoMapDerivedCategory_hom F LF α) K

/-! ### Change of functor -/

/-- **An isomorphism of exact functors induces an isomorphism of the functors they induce on
derived categories.**  The instance binders are named because the intended application crosses
two definitionally equal spellings of a category of modules, for which instance search does not
find the additivity witness; see the implementation notes. -/
def mapDerivedCategoryIsoOfIso (F G : A ⥤ B) [instFa : F.Additive] [instGa : G.Additive]
    [instFl : PreservesFiniteLimits F] [instFc : PreservesFiniteColimits F]
    [instGl : PreservesFiniteLimits G] [instGc : PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  leftDerivedIsoMapDerivedCategoryOfIso F G F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.hom e

/-- The universal property of `Stacks.Homology.mapDerivedCategoryIsoOfIso`. -/
theorem mapDerivedCategoryIsoOfIso_hom_app (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryIsoOfIso F G e).hom.app (DerivedCategory.Qh.obj K) ≫
        (mapDerivedCategoryComparisonOfIso F G e).hom.app K =
      F.mapDerivedCategoryFactorsh.hom.app K :=
  leftDerivedIsoMapDerivedCategoryOfIso_hom_app F G F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh.hom e K

/-- **The twisted comparison factors through the untwisted one.**  Identifying a left derived
functor with `G.mapDerivedCategory` along `e : F ≅ G` is identifying it with
`F.mapDerivedCategory` and then changing the functor degreewise. -/
theorem leftDerivedIsoMapDerivedCategoryOfIso_eq (F G : A ⥤ B)
    [instFa : F.Additive] [instGa : G.Additive]
    [instFl : PreservesFiniteLimits F] [instFc : PreservesFiniteColimits F]
    [instGl : PreservesFiniteLimits G] [instGc : PreservesFiniteColimits G]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (e : F ≅ G) :
    leftDerivedIsoMapDerivedCategoryOfIso F G LF α e =
      leftDerivedIsoMapDerivedCategory F LF α ≪≫ mapDerivedCategoryIsoOfIso F G e := by
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G.mapDerivedCategory
    (mapDerivedCategoryComparisonOfIso F G e)
  refine Iso.ext (Functor.leftDerived_ext G.mapDerivedCategory
    (mapDerivedCategoryComparisonOfIso F G e).hom
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_)
  ext K
  have h1 := leftDerivedIsoMapDerivedCategoryOfIso_hom_app F G LF α e K
  have h2 := mapDerivedCategoryIsoOfIso_hom_app F G e K
  have h3 := leftDerivedIsoMapDerivedCategory_hom_app F LF α K
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, Iso.trans_hom]
  rw [Category.assoc, h2, h3]
  exact h1

/-! ### Composition -/

/-- **`D(F) ⋙ D(G)` as a left derived functor of `K(H) ⋙ Q_h` along `e : F ⋙ G ≅ H`.**  It is the
comparison of `F`, then the comparison of `G`, then `e` read on homotopy categories; all three
are invertible, so the composite exhibits `D(F) ⋙ D(G)` as a left derived functor. -/
def mapDerivedCategoryCompComparison (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ⋙ G ≅ H) :
    DerivedCategory.Qh ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ≅
      H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactorsh G.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ))
      DerivedCategory.Qh

/-- `Stacks.Homology.mapDerivedCategoryCompComparison` at an object of the homotopy category,
written out: each whiskering contributes its component. -/
theorem mapDerivedCategoryCompComparison_hom_app (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ⋙ G ≅ H) (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompComparison F G H e).hom.app K =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K) := by
  simp [mapDerivedCategoryCompComparison]

/-- The composite of the two induced functors is a left derived functor of `K(H) ⋙ Q_h`. -/
instance isLeftDerivedFunctor_mapDerivedCategoryCompComparison (F : A ⥤ B) (G : B ⥤ C)
    (H : A ⥤ C) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ⋙ G ≅ H) :
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory).IsLeftDerivedFunctor
      (mapDerivedCategoryCompComparison F G H e).hom
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (mapDerivedCategoryCompComparison F G H e)

/-- **An isomorphism `F ⋙ G ≅ H` of exact functors induces `D(F) ⋙ D(G) ≅ D(H)`.**

This is `CategoryTheory.Functor.mapDerivedCategoryCompIso`, hence — unfolding that one step
further — the comparison `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` of
`D(F ⋙ G)` with `D(F) ⋙ D(G)`, inverted, followed by the degreewise change of functor that `e`
gives.  It used to be built a second time here, out of the uniqueness of a left derived functor;
`Stacks.Homology.mapDerivedCategoryCompIso_hom_app` is that characterization, and it is now a
theorem about the one construction rather than its definition. -/
def mapDerivedCategoryCompIso (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  CategoryTheory.Functor.mapDerivedCategoryCompIso e

/-- The universal property of `Stacks.Homology.mapDerivedCategoryCompIso`.  It is the value of
the comparison over `DerivedCategory.Qh`,
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh`, with the structure map of `D(H)`
moved to the other side. -/
theorem mapDerivedCategoryCompIso_hom_app (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G H e).hom.app (DerivedCategory.Qh.obj K) ≫
        H.mapDerivedCategoryFactorsh.hom.app K =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.mapDerivedCategoryFactorsh.hom.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K) := by
  have h : (mapDerivedCategoryCompIso F G H e).hom.app (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.mapDerivedCategoryFactorsh.hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K) ≫
            H.mapDerivedCategoryFactorsh.inv.app K :=
    CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh e K
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]

/-- `Stacks.Homology.mapDerivedCategoryCompIso_hom_app` as an equality of natural
transformations: this is the factorization through which the comparison is recognised as the map
of left derived functors determined by
`Stacks.Homology.mapDerivedCategoryCompComparison`. -/
theorem whiskerLeft_mapDerivedCategoryCompIso_hom (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H) :
    Functor.whiskerLeft DerivedCategory.Qh (mapDerivedCategoryCompIso F G H e).hom ≫
        H.mapDerivedCategoryFactorsh.hom =
      (mapDerivedCategoryCompComparison F G H e).hom := by
  ext K
  exact (mapDerivedCategoryCompIso_hom_app F G H e K).trans
    (mapDerivedCategoryCompComparison_hom_app F G H e K).symm

/-- **The two constructions of "the derived category of a composite is the composite of the
derived categories" agree.**  At `e = Iso.refl (F ⋙ G)` the comparison built here out of
`D(F) ⋙ D(G) ≅ D(H)` is the inverse of
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, which reads
`D(F ⋙ G) ≅ D(F) ⋙ D(G)`.

This is what lets a square assembled from `Stacks.Homology.mapDerivedCategoryCompIso` — such as
`Stacks.Cohomology.derivedPullbackSquare_eq_mapDerivedCategory`, the derived base change of
[Stacks, Tag 08HY] read degreewise — meet one assembled from
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`, such as
`CategoryTheory.TwoSquare.mapDerivedCategory` and the mates statement
`CategoryTheory.mateEquiv_mapDerivedCategory` built on it.  Both sides lift a functor through
`DerivedCategory.Q`, so it is enough to compare them on the image of a cochain complex, where the
degreewise comparison attached to `Iso.refl` is an identity. -/
theorem mapDerivedCategoryCompIso_refl_eq (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] :
    mapDerivedCategoryCompIso F G (F ⋙ G) (Iso.refl (F ⋙ G)) =
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).symm := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun P => ?_)
  have hid : DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).hom.app P) =
      𝟙 (DerivedCategory.Q.obj
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    DerivedCategory.Q.map_id _
  have h : (mapDerivedCategoryCompIso F G (F ⋙ G) (Iso.refl (F ⋙ G))).hom.app
        (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
              (ComplexShape.up ℤ)).hom.app P) ≫
            (F ⋙ G).mapDerivedCategoryFactors.inv.app P :=
    CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Q (Iso.refl (F ⋙ G)) P
  rw [h, hid, Iso.symm_hom,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q]
  exact congrArg (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫ ·)
    (Category.id_comp ((F ⋙ G).mapDerivedCategoryFactors.inv.app P))

end Stacks.Homology

namespace Stacks.Cohomology.DerivedOpenImmersion

universe u

attribute [local instance] HasDerivedCategory.standard

open Stacks.Homology
open Stacks.DerivedPullback.Composition

/-- The formal identity left over after the four universal properties are inserted into the
compatibility square.  Stated for an arbitrary functor between arbitrary categories: the
rewriting is then done in a context that mentions no derived category, which is what keeps it
inside the heartbeat budget. -/
private theorem comp_chase {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {c₁ c₂ c₃ : D} {d₁ d₂ d₃ d₄ : E}
    (i₁ : c₁ ⟶ c₂) (f₁ : c₂ ⟶ c₃) (eg : c₁ ⟶ c₃) (hg : i₁ ≫ f₁ = eg)
    (Q : F.obj c₂ ⟶ d₁) (R : d₁ ⟶ d₂) (Q' : F.obj c₃ ⟶ d₂) (S : d₂ ⟶ d₃)
    (ef : F.obj c₃ ⟶ d₃) (hf : Q' ≫ S = ef)
    (hnat : F.map f₁ ≫ Q' = Q ≫ R) (T : d₃ ⟶ d₄) :
    F.map eg ≫ ef ≫ T = F.map i₁ ≫ Q ≫ R ≫ S ≫ T := by
  subst hg hf
  simp only [F.map_comp, Category.assoc]
  rw [← Category.assoc (F.map f₁), hnat, Category.assoc]

section Comp

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]
  [PreservesFiniteLimits (modulePullback g)] [PreservesFiniteColimits (modulePullback g)]
  [PreservesFiniteLimits (modulePullback (f ≫ g))]
  [PreservesFiniteColimits (modulePullback (f ≫ g))]

/-- **The identification of the derived pullback with the degreewise pullback is compatible with
composition.**  For morphisms of ringed spaces `f` and `g` along which pullback of sheaves of
modules is exact, the square

`Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*`, `Lg^* ⋙ Lf^* ⟶ D(g^*) ⋙ D(f^*) ⟶ D((f ≫ g)^*)`

commutes, the horizontal maps being the composition isomorphism of Tag 0D5S and the degreewise
composition isomorphism of `Stacks.DerivedPullback.Composition.modulePullbackComp`.

Both targets are left derived functors of degreewise pullback along `f ≫ g`, so it suffices to
compare after composing with the structure map of `D((f ≫ g)^*)`; there the left-hand side is
the factorization `derivedPullbackCompIsoCanonical_hom_app_comp_comparison` of
`Stacks.Cohomology.DerivedPushforwardComposition`,
and the right-hand side is read off the universal properties of the three comparisons. -/
theorem derivedPullbackIsoMapDerivedCategory_comp :
    (derivedPullbackCompIsoCanonical f g).hom ≫
        (derivedPullbackIsoMapDerivedCategory (f ≫ g)).hom =
      Functor.whiskerRight (derivedPullbackIsoMapDerivedCategory g).hom (derivedPullback f) ≫
        Functor.whiskerLeft (modulePullback g).mapDerivedCategory
          (derivedPullbackIsoMapDerivedCategory f).hom ≫
        (mapDerivedCategoryCompIso (modulePullback g) (modulePullback f)
          (modulePullback (f ≫ g)) (modulePullbackComp f g)).hom := by
  refine Functor.leftDerived_ext (modulePullback (f ≫ g)).mapDerivedCategory
    (modulePullback (f ≫ g)).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
    _ _ _ ?_
  ext K
  have key : ∀ {X' Y' : RingedSpace.{u, u}} (h : X' ⟶ Y')
      [PreservesFiniteLimits (modulePullback h)] [PreservesFiniteColimits (modulePullback h)]
      (L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y')) (ComplexShape.up ℤ)),
      (derivedPullbackIsoMapDerivedCategory h).hom.app (DerivedCategory.Qh.obj L) ≫
        (modulePullback h).mapDerivedCategoryFactorsh.hom.app L =
          (derivedPullbackComparison h).app L := fun h _ _ L =>
    leftDerivedIsoMapDerivedCategory_hom_app (modulePullback h) (derivedPullback h)
      (derivedPullbackComparison h) L
  have h0 := DerivedPushforwardComposition.derivedPullbackCompIsoCanonical_hom_app_comp_comparison
    f g K
  have hcomp := mapDerivedCategoryCompIso_hom_app (modulePullback g) (modulePullback f)
    (modulePullback (f ≫ g)) (modulePullbackComp f g) K
  dsimp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Category.assoc, key (f ≫ g) K]
  refine h0.trans ?_
  simp only [Category.assoc, hcomp]
  have hnat : (derivedPullback f).map
        ((modulePullback g).mapDerivedCategoryFactorsh.hom.app K) ≫
      (derivedPullbackIsoMapDerivedCategory f).hom.app
        (DerivedCategory.Qh.obj (((modulePullback g).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)) =
      (derivedPullbackIsoMapDerivedCategory f).hom.app
          ((modulePullback g).mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
        (modulePullback f).mapDerivedCategory.map
          ((modulePullback g).mapDerivedCategoryFactorsh.hom.app K) :=
    (derivedPullbackIsoMapDerivedCategory f).hom.naturality _
  exact comp_chase (derivedPullback f) _ _ _ (key g K) _ _ _ _ _ (key f _) hnat _

end Comp

section OpenImmersion

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [SheafedSpace.IsOpenImmersion f] [SheafedSpace.IsOpenImmersion g]

/-- **The comparison of Tag 079W along an open immersion is compatible with composition**, with
no exactness hypothesis left over: pullback along an open immersion is exact.  This is
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory_comp` read as an
equality of isomorphisms. -/
theorem derivedPullbackOpenImmersionIso_comp :
    derivedPullbackOpenImmersionIso (f ≫ g) =
      (derivedPullbackCompIsoCanonical f g).symm ≪≫
        Functor.isoWhiskerRight (derivedPullbackOpenImmersionIso g) (derivedPullback f) ≪≫
        Functor.isoWhiskerLeft ((modulePullback g).mapDerivedCategory)
          (derivedPullbackOpenImmersionIso f) ≪≫
        mapDerivedCategoryCompIso (modulePullback g) (modulePullback f)
          (modulePullback (f ≫ g)) (modulePullbackComp f g) :=
  Iso.ext ((Iso.inv_comp_eq (derivedPullbackCompIsoCanonical f g)).2
    (derivedPullbackIsoMapDerivedCategory_comp f g).symm).symm

end OpenImmersion

section Opens

/-- **Naturality in the open subspace.**  Let `V` be an open subspace of a ringed space `X` and
`W` an open subspace of `V`.  The comparison identifying the derived pullback along the composite
inclusion `W ⟶ V ⟶ X` with the degreewise pullback is the comparison for `V`, then the comparison
for `W` inside `V`, then the degreewise composition isomorphism — the composition isomorphism of
Tag 0D5S mediating.

This is the compatibility the Stacks 08DR induction over the opens of a space needs, and the
instance of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso_comp` at the two
canonical inclusions. -/
theorem derivedPullbackOpenImmersionIso_ofRestrict_comp (X : RingedSpace.{u, u})
    (V : Opens X.carrier)
    (W : Opens (X.restrict V.isOpenEmbedding).carrier) :
    derivedPullbackOpenImmersionIso
        ((X.restrict V.isOpenEmbedding).ofRestrict W.isOpenEmbedding ≫
          X.ofRestrict V.isOpenEmbedding) =
      (derivedPullbackCompIsoCanonical
          ((X.restrict V.isOpenEmbedding).ofRestrict W.isOpenEmbedding)
          (X.ofRestrict V.isOpenEmbedding)).symm ≪≫
        Functor.isoWhiskerRight
            (derivedPullbackOpenImmersionIso (X.ofRestrict V.isOpenEmbedding))
            (derivedPullback
              ((X.restrict V.isOpenEmbedding).ofRestrict W.isOpenEmbedding)) ≪≫
        Functor.isoWhiskerLeft
            ((modulePullback (X.ofRestrict V.isOpenEmbedding)).mapDerivedCategory)
            (derivedPullbackOpenImmersionIso
              ((X.restrict V.isOpenEmbedding).ofRestrict W.isOpenEmbedding)) ≪≫
        mapDerivedCategoryCompIso (modulePullback (X.ofRestrict V.isOpenEmbedding))
          (modulePullback ((X.restrict V.isOpenEmbedding).ofRestrict W.isOpenEmbedding))
          (modulePullback
            ((X.restrict V.isOpenEmbedding).ofRestrict W.isOpenEmbedding ≫
              X.ofRestrict V.isOpenEmbedding))
          (modulePullbackComp
            ((X.restrict V.isOpenEmbedding).ofRestrict W.isOpenEmbedding)
            (X.ofRestrict V.isOpenEmbedding)) :=
  derivedPullbackOpenImmersionIso_comp _ _

/-- **The restriction-functor spelling of the comparison factors through the open-immersion
spelling.**  `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`, the
comparison stated in the vocabulary `ExtensionByZeroModules.jStar` of the Mayer--Vietoris
sequence of Tag 08BW, is
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` followed by the
degreewise change of spelling
`Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso`.

Together with
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso_ofRestrict_comp` this
transports the naturality in the open subspace into that vocabulary.  The additivity of `jStar`
is supplied as a term, for the reason given in the implementation notes. -/
theorem derivedPullbackOpenRestrictionIso_eq (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    derivedPullbackOpenRestrictionIso X U =
      derivedPullbackOpenImmersionIso (X.ofRestrict U.isOpenEmbedding) ≪≫
        mapDerivedCategoryIsoOfIso (modulePullback (X.ofRestrict U.isOpenEmbedding))
          (jStar U (structureSheafRing X))
          (instGa := ExtensionByZeroModules.jStar_additive U (structureSheafRing X))
          (instGl := ExtensionByZeroModules.preservesFiniteLimits_jStar U (structureSheafRing X))
          (instGc := ExtensionByZeroModules.preservesFiniteColimits_jStar U (structureSheafRing X))
          (modulePullbackJStarIso X U) :=
  leftDerivedIsoMapDerivedCategoryOfIso_eq (modulePullback (X.ofRestrict U.isOpenEmbedding))
    (jStar U (structureSheafRing X))
    (instGa := ExtensionByZeroModules.jStar_additive U (structureSheafRing X))
    (instGl := ExtensionByZeroModules.preservesFiniteLimits_jStar U (structureSheafRing X))
    (instGc := ExtensionByZeroModules.preservesFiniteColimits_jStar U (structureSheafRing X))
    (derivedPullback (X.ofRestrict U.isOpenEmbedding))
    (derivedPullbackComparison (X.ofRestrict U.isOpenEmbedding))
    (modulePullbackJStarIso X U)

end Opens

end Stacks.Cohomology.DerivedOpenImmersion

end
