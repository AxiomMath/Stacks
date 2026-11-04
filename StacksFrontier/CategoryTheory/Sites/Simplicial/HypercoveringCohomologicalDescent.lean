module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationFirstPage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# Cohomological descent along the augmentation of a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE) and let `a` be an augmentation of `S`
towards a site `(D, K)` (Stacks 0D6Z). On abelian sheaves the total augmentation of Stacks 0D70
gives an adjoint pair `a⁻¹ ⊣ a_*` with `a⁻¹` exact. This module derives that pair on the
*unbounded* derived categories: `a⁻¹` is derived degreewise, `R a_*` is the total right derived
functor computed by K-injective resolutions, the two are adjoint, and the unit of the derived
adjunction is the canonical map

`E ⟶ R a_* a⁻¹ E`.

Stacks 0D8G asserts that this map is an isomorphism when the site has equalizers and fibre
products and the simplicial site is the one of Stacks 0D8B attached to a hypercovering. What is
proved here is the reduction of that assertion to two inputs, both of which this library does
not yet have; see "What Stacks 0D8G still lacks here" below.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.abelianTotalAdjunction`: the adjoint pair
  `a⁻¹ ⊣ a_*` on abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalPushforward` and
  `.derivedTotalPushforwardUnit`: `R a_*` on unbounded derived categories, with its canonical
  comparison from the degreewise direct image.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalInverseImage` and
  `.derivedTotalInverseImageComparison`: `a⁻¹` on unbounded derived categories, with its
  canonical comparison to the degreewise inverse image.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalAdjunction`: the derived
  adjunction `a⁻¹ ⊣ R a_*`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedAugmentationUnit`: the canonical
  map `E ⟶ R a_* a⁻¹ E`, the unit of that adjunction.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward`:
  the second of the two assumed inputs, that `a⁻¹` of a K-injective complex computes `R a_*`.
* `Stacks.CategoryTheory.Hypercovering.hypercoveringSituation` and `.hypercoveringAugmentation`:
  the simplicial-site situation and the augmentation of Stacks 0D8B attached to a
  hypercovering.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.isIso_derivedTotalInverseImageComparison_app`: the derived inverse image is the degreewise
  one, because `a⁻¹` is exact.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedAugmentationUnit_fac_app`: the
  derived unit is compatible with the underived one.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.isIso_derivedAugmentationUnit`: the
  canonical map is an isomorphism as soon as the underived unit is an isomorphism and `a⁻¹` of a
  K-injective complex computes `R a_*`.
* `Stacks.CategoryTheory.Hypercovering.isIso_derivedAugmentationUnit_app_of_hypercovering`: the
  same statement in the situation of Stacks 0D8G — a site with equalizers and fibre products and
  the simplicial site of Stacks 0D8B attached to a hypercovering of it.
* `CategoryTheory.Adjunction.isIso_mapHomotopyCategoryAdjunction_unit_app`: an adjunction of
  additive functors whose unit is invertible induces one whose unit is invertible on the
  unbounded homotopy categories.

## What Stacks 0D8G still lacks here

The source's proof has three steps: the injective case, the bounded below case by Leray
acyclicity, and the unbounded case by a product total complex. Two of its inputs are missing in
this library, and they enter
`Stacks.CategoryTheory.Hypercovering.isIso_derivedAugmentationUnit_app_of_hypercovering` as the
hypotheses `hunit` and `hacyclic`.

* `hunit` is **Stacks 0D8E** in its abelian form: the unit `F ⟶ a_*a⁻¹F` of the underived
  adjunction is an isomorphism. The source proves it from the equalizer description of `a_*a⁻¹F`
  — which is available here, as
  `CategoryTheory.SimplicialSiteSituation.Augmentation.augmentedCechComplex_exactAt_zero` and
  `.augmentedCechComplex_exactAt_one` — together with the identification
  `a_{n,*}a_n⁻¹F = ℋom(F(K_n)^#, F)`. The latter is available, cosimplicially and in abelian
  form, as
  `CategoryTheory.SimplicialSemiRepresentable.cechCosimplicialObjectIsoSheafHomCosimplicialObject`,
  and with it Stacks 0D8F,
  `CategoryTheory.SimplicialSemiRepresentable.cechComplexIsoSheafHomComplex`; the passage from it
  to the invertibility of the unit is not carried out here.
* `hacyclic` is the derived-level content of the source's steps 1 and 3: for a K-injective
  complex `I` of abelian sheaves on `(D, K)`, the complex `a⁻¹I` on the total site computes
  `R a_*`. The source gets it for an injective sheaf from the spectral sequence of Stacks 0D7A,
  which is available, with its convergence, as
  `CategoryTheory.SimplicialSiteSituation.Augmentation.higherDirectImageSpectralSequence`, and in
  the unbounded case from the product total complex of Cohomology on Sites, Section 21.35; the
  passage from these to `hacyclic` is not carried out here.

Nothing of either input is assumed in the general machinery: the construction of `R a_*`, of
`a⁻¹` on derived categories, of the derived adjunction and of its unit is unconditional.

## Implementation notes

`R a_*` is the total right derived functor of the degreewise direct image followed by
localization, in the standard model of the derived category. It exists with no hypothesis beyond
the augmentation: abelian sheaves on a site are a Grothendieck abelian category, so every complex
admits a quasi-isomorphism into a K-injective one, and Stacks 070K applies. The derived inverse
image is the total *left* derived functor rather than
`CategoryTheory.Functor.mapDerivedCategory`, because that is the shape
`CategoryTheory.Adjunction.derived` consumes; `isIso_derivedTotalInverseImageComparison_app`
records that it agrees with the degreewise functor, which is what pins it down as `a⁻¹`.

The derived adjunction is Maltsiniotis' theorem, `CategoryTheory.Adjunction.derived`, applied to
the degreewise adjunction on homotopy categories. It asks both derived functors to be *absolute*,
that is to stay derived functors after postcomposition with an arbitrary functor. For `R a_*`
this is because its comparison is invertible on the K-injective complexes, and for `a⁻¹` because
its comparison is invertible everywhere, `a⁻¹` being exact; the two are
`Stacks.Cohomology.Localization.rightDerived_of_kInjectives` and
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions`.

The reduction to K-injective complexes is
`Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives`: a morphism of functors out of the
unbounded derived category is invertible as soon as it is invertible at the K-injective
complexes. That is why the hypothesis `hacyclic` is stated at K-injective complexes and the
conclusion holds for every object of `D(C)`, with no boundedness assumption and no restriction on
the coefficients.

The hypothesis that the site has equalizers and fibre products is not needed by the general
machinery; it is needed for `Stacks.CategoryTheory.Hypercovering.HypercoveringOfTerminal` to be
well formed at all, since the matching maps of a hypercovering are defined through coskeleta, and
it appears as the instance arguments `[HasEqualizers C]` and `[HasPullbacks C]` of the
hypercovering statement.

## References

* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8F](https://stacks.math.columbia.edu/tag/0D8F)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Adjunction

/-! ### Adjunctions with invertible unit, degreewise on complexes -/

section

variable {ι : Type*} {A : Type*} [Category A] [Preadditive A] {B : Type*} [Category B]
  [Preadditive B] {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]

/-- The unit of the adjunction induced degreewise on categories of homological complexes is
invertible as soon as the unit of the original adjunction is: it is that unit in every degree. -/
theorem isIso_mapHomologicalComplexAdjunction_unit_app (adj : G ⊣ F) [IsIso adj.unit]
    (c : ComplexShape ι) (L : HomologicalComplex B c) :
    IsIso ((mapHomologicalComplexAdjunction adj c).unit.app L) := by
  have : ∀ n : ι, IsIso (((mapHomologicalComplexAdjunction adj c).unit.app L).f n) :=
    fun n => inferInstanceAs (IsIso (adj.unit.app (L.X n)))
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The unit of the adjunction induced on homotopy categories is invertible as soon as the unit
of the original adjunction is: every object of the homotopy category is the class of a complex,
and there the unit is the class of the degreewise unit. -/
theorem isIso_mapHomotopyCategoryAdjunction_unit_app (adj : G ⊣ F) [IsIso adj.unit]
    (c : ComplexShape ι) (X : HomotopyCategory B c) :
    IsIso ((mapHomotopyCategoryAdjunction adj c).unit.app X) := by
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective X
  subst hL
  have := isIso_mapHomologicalComplexAdjunction_unit_app adj c L
  exact inferInstanceAs (IsIso ((HomotopyCategory.quotient B c).map
    ((mapHomologicalComplexAdjunction adj c).unit.app L)))

end

end CategoryTheory.Adjunction

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-! ### The adjoint pair `a⁻¹ ⊣ a_*` on abelian sheaves -/

/-- The inverse image of abelian sheaves along the total augmentation is left adjoint to its
direct image, both being read off the geometric adjunction of the morphism of topoi of
Stacks 0D70. -/
def abelianTotalAdjunction :
    totalInverseImageAb S D K a ⊣ abelianTotalPushforward S D K a :=
  Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward S.totalTopology
    (totalMorphismOfTopoi S D K a)

/-- The inverse image of abelian sheaves along the total augmentation is additive, being a left
adjoint between abelian categories. -/
instance additive_totalInverseImageAb : (totalInverseImageAb S D K a).Additive :=
  (abelianTotalAdjunction S D K a).left_adjoint_additive

/-- The inverse image of abelian sheaves along the total augmentation is left exact; this is the
left-exactness half of Stacks 04JC. -/
instance preservesFiniteLimits_totalInverseImageAb :
    PreservesFiniteLimits (totalInverseImageAb S D K a) :=
  Sites.abelianInverseImage_preservesFiniteLimits (totalMorphismOfTopoi S D K a)

/-- The inverse image of abelian sheaves along the total augmentation is right exact; this is the
right-exactness half of Stacks 04JC. -/
instance preservesFiniteColimits_totalInverseImageAb :
    PreservesFiniteColimits (totalInverseImageAb S D K a) :=
  Sites.abelianInverseImage_preservesFiniteColimits (totalMorphismOfTopoi S D K a)

/-! ### The derived direct image `R a_*` -/

/-- The direct image of abelian sheaves along the total augmentation, applied degreewise and
followed by localization: a right derived functor of this functor is `R a_*`. -/
abbrev homotopyTotalPushforward :
    HomotopyCategory (Sheaf S.totalTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{u}) :=
  (abelianTotalPushforward S D K a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- K-injective resolutions compute the derived direct image pointwise: abelian sheaves on the
total site form a Grothendieck abelian category, so every complex admits a quasi-isomorphism
into a K-injective one. -/
@[sga "4½ Etat_0 4.2.3" "clause a), special case"]
instance hasPointwiseRightDerivedFunctor_homotopyTotalPushforward :
    (homotopyTotalPushforward S D K a).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} (homotopyTotalPushforward S D K a)
    Stacks.Cohomology.Localization.enoughKInjectives).1

/-- The derived direct image along the total augmentation exists, with no hypothesis beyond the
augmentation. -/
instance hasRightDerivedFunctor_homotopyTotalPushforward :
    (homotopyTotalPushforward S D K a).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- `R a_*`: the derived direct image along the total augmentation, on unbounded derived
categories. -/
abbrev derivedTotalPushforward :
    DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf K AddCommGrpCat.{u}) :=
  (homotopyTotalPushforward S D K a).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- The canonical comparison `a_*L ⟶ R a_* L` from the degreewise direct image. -/
abbrev derivedTotalPushforwardUnit :
    homotopyTotalPushforward S D K a ⟶
      DerivedCategory.Qh ⋙ derivedTotalPushforward S D K a :=
  (homotopyTotalPushforward S D K a).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-! ### The derived inverse image `a⁻¹` -/

/-- The inverse image of abelian sheaves along the total augmentation, applied degreewise and
followed by localization: a left derived functor of this functor is `a⁻¹` on derived
categories. -/
abbrev homotopyTotalInverseImage :
    HomotopyCategory (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u}) :=
  (totalInverseImageAb S D K a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Every complex is its own resolution by the class of all objects, so that class is a
resolving datum for the quasi-isomorphisms. -/
theorem hasTopResolutions (X : HomotopyCategory (Sheaf K AddCommGrpCat.{u})
      (ComplexShape.up ℤ)) :
    ∃ (Y : HomotopyCategory (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ))
      (_ : (⊤ : ObjectProperty _) Y) (s : Y ⟶ X),
      HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) s :=
  ⟨X, trivial, 𝟙 X, MorphismProperty.id_mem _ _⟩

/-- The degreewise inverse image inverts every quasi-isomorphism, `a⁻¹` being exact. -/
theorem inverseImageInverts {X Y : HomotopyCategory (Sheaf K AddCommGrpCat.{u})
      (ComplexShape.up ℤ)} (s : X ⟶ Y)
    (hs : HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ) s)
    (_ : (⊤ : ObjectProperty _) X) (_ : (⊤ : ObjectProperty _) Y) :
    IsIso ((homotopyTotalInverseImage S D K a).map s) :=
  Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso
    (totalInverseImageAb S D K a) _ hs

/-- The derived inverse image is computed by the identity resolutions. -/
instance hasPointwiseLeftDerivedFunctor_homotopyTotalInverseImage :
    (homotopyTotalInverseImage S D K a).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions _ ⊤
    (hasTopResolutions D K) _ (fun s hs hX hY => inverseImageInverts S D K a s hs hX hY)

/-- The derived inverse image along the total augmentation exists, with no hypothesis beyond the
augmentation. -/
instance hasLeftDerivedFunctor_homotopyTotalInverseImage :
    (homotopyTotalInverseImage S D K a).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

/-- `a⁻¹` on unbounded derived categories. -/
abbrev derivedTotalInverseImage :
    DerivedCategory (Sheaf K AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u}) :=
  (homotopyTotalInverseImage S D K a).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- The canonical comparison from `a⁻¹` on derived categories to the degreewise inverse image. -/
abbrev derivedTotalInverseImageComparison :
    DerivedCategory.Qh ⋙ derivedTotalInverseImage S D K a ⟶ homotopyTotalInverseImage S D K a :=
  (homotopyTotalInverseImage S D K a).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- **The derived inverse image is the degreewise inverse image.** Its canonical comparison is
invertible at every complex, because `a⁻¹` is exact and therefore already inverts the
quasi-isomorphisms. -/
instance isIso_derivedTotalInverseImageComparison_app
    (X : HomotopyCategory (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :
    IsIso ((derivedTotalInverseImageComparison S D K a).app X) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions _ ⊤ (hasTopResolutions D K) _
    (fun s hs hX hY => inverseImageInverts S D K a s hs hX hY) DerivedCategory.Qh _ _ X trivial

/-! ### The derived adjunction and its unit -/

/-- The adjoint pair `a⁻¹ ⊣ a_*` read degreewise on the unbounded homotopy categories. -/
abbrev homotopyTotalAdjunction :
    (totalInverseImageAb S D K a).mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      (abelianTotalPushforward S D K a).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Adjunction.mapHomotopyCategoryAdjunction (abelianTotalAdjunction S D K a) (ComplexShape.up ℤ)

/-- The derived inverse image stays a left derived functor after composition with the derived
direct image: its comparison is invertible everywhere, hence so is its image under any
functor. -/
instance comp_isLeftDerivedFunctor :
    (derivedTotalInverseImage S D K a ⋙ derivedTotalPushforward S D K a).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedTotalInverseImage S D K a)
          (derivedTotalPushforward S D K a)).inv ≫
        Functor.whiskerRight (derivedTotalInverseImageComparison S D K a)
          (derivedTotalPushforward S D K a))
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions _ ⊤
    (hasTopResolutions D K) _ (fun s hs hX hY => inverseImageInverts S D K a s hs hX hY)
    DerivedCategory.Qh _ _ _

/-- The derived direct image stays a right derived functor after composition with the derived
inverse image: its comparison is invertible on the K-injective complexes, hence so is its image
under any functor. -/
instance comp_isRightDerivedFunctor :
    (derivedTotalPushforward S D K a ⋙ derivedTotalInverseImage S D K a).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedTotalPushforwardUnit S D K a)
          (derivedTotalInverseImage S D K a) ≫
        (Functor.associator DerivedCategory.Qh (derivedTotalPushforward S D K a)
          (derivedTotalInverseImage S D K a)).hom)
      (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I hI => ?_)
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    (homotopyTotalPushforward S D K a) (derivedTotalPushforward S D K a)
    (derivedTotalPushforwardUnit S D K a) I
  rw [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id]
  infer_instance

/-- **The derived adjunction `a⁻¹ ⊣ R a_*`** on unbounded derived categories, Maltsiniotis'
derived adjunction of the degreewise pair. -/
def derivedTotalAdjunction :
    derivedTotalInverseImage S D K a ⊣ derivedTotalPushforward S D K a :=
  (homotopyTotalAdjunction S D K a).derived
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    (derivedTotalInverseImageComparison S D K a) (derivedTotalPushforwardUnit S D K a)

/-- The canonical map `E ⟶ R a_* a⁻¹ E`, the unit of the derived adjunction. -/
abbrev derivedAugmentationUnit :
    𝟭 (DerivedCategory (Sheaf K AddCommGrpCat.{u})) ⟶
      derivedTotalInverseImage S D K a ⋙ derivedTotalPushforward S D K a :=
  (derivedTotalAdjunction S D K a).unit

/-- The derived unit is the underived one: after the two canonical comparisons, the leg of
`E ⟶ R a_* a⁻¹ E` at the class of a complex `L` is the degreewise unit `L ⟶ a_*a⁻¹L`. -/
theorem derivedAugmentationUnit_fac_app
    (X : HomotopyCategory (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :
    (derivedAugmentationUnit S D K a).app (DerivedCategory.Qh.obj X) ≫
        (derivedTotalPushforward S D K a).map
          ((derivedTotalInverseImageComparison S D K a).app X) =
      DerivedCategory.Qh.map ((homotopyTotalAdjunction S D K a).unit.app X) ≫
        (derivedTotalPushforwardUnit S D K a).app
          (((totalInverseImageAb S D K a).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) :=
  (homotopyTotalAdjunction S D K a).derivedη_fac_app
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    (derivedTotalInverseImageComparison S D K a) (derivedTotalPushforwardUnit S D K a) X

/-- The second input of Stacks 0D8G: the inverse image of a K-injective complex of abelian
sheaves on the augmentation site computes the derived direct image, that is, the canonical map
`a_*a⁻¹I ⟶ R a_*a⁻¹I` is an isomorphism for every K-injective `I`. -/
def InverseImageComputesDerivedPushforward : Prop :=
  ∀ I : CochainComplex (Sheaf K AddCommGrpCat.{u}) ℤ, I.IsKInjective →
    IsIso ((derivedTotalPushforwardUnit S D K a).app
      (((totalInverseImageAb S D K a).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj I)))

/-- **The canonical map `E ⟶ R a_* a⁻¹ E` is an isomorphism**, granted two inputs: that the
underived unit `F ⟶ a_*a⁻¹F` is an isomorphism, and that `a⁻¹` of a K-injective complex computes
`R a_*`.

Both are hypotheses, not consequences of the augmentation: the first is Stacks 0D8E for the
simplicial site of a hypercovering and the second is the derived content of the source's
computation of `R a_*a⁻¹` on an injective sheaf. What the proof contributes is the reduction of
the unbounded statement to the K-injective complexes and the identification of the derived unit
with the underived one. -/
theorem isIso_derivedAugmentationUnit (hunit : IsIso (abelianTotalAdjunction S D K a).unit)
    (hacyclic : InverseImageComputesDerivedPushforward S D K a) :
    IsIso (derivedAugmentationUnit S D K a) := by
  have := hunit
  refine Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives _ (fun I hI => ?_)
  have := hacyclic I hI
  set X := (HomotopyCategory.quotient (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj I
  have : IsIso ((homotopyTotalAdjunction S D K a).unit.app X) :=
    Adjunction.isIso_mapHomotopyCategoryAdjunction_unit_app _ _ _
  have hcomp : IsIso ((derivedAugmentationUnit S D K a).app (DerivedCategory.Qh.obj X) ≫
      (derivedTotalPushforward S D K a).map
        ((derivedTotalInverseImageComparison S D K a).app X)) := by
    rw [derivedAugmentationUnit_fac_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((derivedTotalPushforward S D K a).map
    ((derivedTotalInverseImageComparison S D K a).app X))

end CategoryTheory.SimplicialSiteSituation.Augmentation

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory CategoryTheory.SimplicialSemiRepresentable
open CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J)

/-- The simplicial-site situation `n ↦ C/K_n` of Stacks 0D8B attached to a hypercovering. -/
def hypercoveringSituation : SimplicialSiteSituation.{u} :=
  situation J.toGrothendieck H.toSimplicialObject

/-- The augmentation `a` of Stacks 0D8B attached to a hypercovering: the one given by the
degree-zero localization functor `j_0 : C/K_0 ⥤ C`. -/
def hypercoveringAugmentation :
    Augmentation (hypercoveringSituation J H) (Cat.of C) J.toGrothendieck :=
  situationAugmentation J.toGrothendieck H.toSimplicialObject

/-- **Stacks 0D8G**, granted the two inputs the library does not have. For a site `C` with
equalizers and fibre products, a hypercovering `K` of it, and the augmentation
`a : Sh((C/K)_total) ⟶ Sh(C)` of Stacks 0D8B, the canonical map `E ⟶ R a_* a⁻¹ E` is an
isomorphism for every object `E` of the unbounded derived category of abelian sheaves on `C`.

`E` is arbitrary: no boundedness is assumed, and the coefficients are the full category of
abelian sheaves.

The two hypotheses are the inputs discussed in the module docstring. `hunit` is Stacks 0D8E in
its abelian form, that the underived unit `F ⟶ a_*a⁻¹F` is an isomorphism. `hacyclic` says that
`a⁻¹` of a K-injective complex of abelian sheaves on `C` computes `R a_*`; it is the derived
content of the source's computation of `R a_*a⁻¹` by the Čech complex, which rests on the
spectral sequence of Stacks 0D7A and the product total complex. Neither hypothesis is used by
the construction of `a⁻¹`, of `R a_*`, of their adjunction or of its unit. -/
@[stacks 0D8G "granted Tag 0D8E and the Ra_*-acyclicity of a⁻¹ of a K-injective complex"]
theorem isIso_derivedAugmentationUnit_app_of_hypercovering
    (hunit : IsIso (Augmentation.abelianTotalAdjunction (hypercoveringSituation J H) (Cat.of C)
      J.toGrothendieck (hypercoveringAugmentation J H)).unit)
    (hacyclic : Augmentation.InverseImageComputesDerivedPushforward
      (hypercoveringSituation J H) (Cat.of C) J.toGrothendieck (hypercoveringAugmentation J H))
    (E : DerivedCategory (Sheaf J.toGrothendieck AddCommGrpCat.{u})) :
    IsIso ((Augmentation.derivedAugmentationUnit (hypercoveringSituation J H) (Cat.of C)
      J.toGrothendieck (hypercoveringAugmentation J H)).app E) :=
  have := Augmentation.isIso_derivedAugmentationUnit _ _ _ _ hunit hacyclic
  NatIso.isIso_app_of_isIso _ E

end Stacks.CategoryTheory.Hypercovering

end
