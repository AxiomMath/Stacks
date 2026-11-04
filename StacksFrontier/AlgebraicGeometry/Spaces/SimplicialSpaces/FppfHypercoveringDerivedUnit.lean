module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleDescentBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleFppfComparisonSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfToSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianInverseImageSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.ComparisonSquareUnit
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianConstantSheafGlobalSections
public import StacksFrontier.CategoryTheory.Sites.SheafEquivOfTopologyEq
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionTerms
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInjective
public import
  StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectComponentCohomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectPushforwardAcyclic

/-!
# Fppf hypercoverings compute étale cohomology: the assembly

Let `a : U → X` be an fppf hypercovering of an algebraic space over `S` (Section 0DH4) and
`a : Sh(U_étale) → Sh(X_étale)` the morphism of topoi of Section 0DE7. Stacks 0DH7 asserts that
`K ⟶ Ra_*(a⁻¹K)` is an isomorphism for `K ∈ D⁺(X_étale)`, and Stacks 0DH8 that
`RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)`. The source's proof runs through the commutative diagram of
Stacks 0DH5
```
Sh((Spaces/U)_{fppf,total}) --h--> Sh(U_étale)
          | a_fppf                    | a
Sh((Spaces/X)_fppf)       --h₋₁--> Sh(X_étale)
```
and the computation `Ra_*a⁻¹ = Ra_*Rh_*h⁻¹a⁻¹ = Rh₋₁,*Ra_{fppf,*}a_fppf⁻¹h₋₁⁻¹ = Rh₋₁,*h₋₁⁻¹ = id`.

The four sides of the square are:

* the right side is the augmentation `a` of Section 0DE7
  (`AlgebraicGeometry.Space.etaleAugmentationMorphism`);
* the bottom side is the comparison `h₋₁ = a_X : Sh((Spaces/X)_fppf) → Sh(X_étale)`
  (`AlgebraicGeometry.Space.fppfSpacesEtaleMorphism`), and the components `h_n` of `h` are the
  comparisons `a_{U_n}`; what Stacks 0DGG says about them on single sheaves is the property
  `AlgebraicGeometry.Space.FppfSpacesEtaleAcyclic`;
* the left side is the augmentation `a_fppf` of the total site of `U` regarded as a hypercovering
  of `X` in the fppf site (Stacks 09X8); its contribution, `N = a_{fppf,*}a_fppf⁻¹N` and
  `R^q a_{fppf,*}(a_fppf⁻¹N) = 0` for `q > 0` (Stacks 0DA8, 0D8N), is proved here
  (`AlgebraicGeometry.Space.IsFppfHypercovering.fppfAugmentation_descent`);
* the top side is the comparison `h` of `AlgebraicGeometry.Space.etaleFppfComparisonMorphism`,
  read here on abelian sheaves (`etaleFppfComparisonAbAdjunction`); the square commutes on
  abelian sheaves (`fppfComparisonSquareAbelianInverseImageIso`, from Stacks 0DH5 on sheaves of
  sets), and `h` is described in each simplicial degree `n` by `h_n = a_{U_n}`
  (`etaleFppfComparisonDegreeIso`, Stacks 0D96, by Beck–Chevalley for the Guitart exact square of
  component inclusions).

The restrictions to a simplicial degree `n` on both total sites are exact, the restrictions on
`U_étale` jointly reflect isomorphisms, and the restriction on the fppf total site preserves
injective objects (Stacks 09WH). For Stacks 0DH8 the identity `Γ(X_étale, a_*F) = Γ(U_étale, F)`
is `etaleAugmentationGammaIso`.

## Main results

* `AlgebraicGeometry.Space.IsFppfHypercovering.fppfAugmentation_descent`: Stacks 0DA8 (2) and
  Stacks 0D8N for the augmentation of the fppf total site of an fppf hypercovering.
* `AlgebraicGeometry.Space.fppfComparisonSquareAbelianInverseImageIso`: the square of Stacks 0DH5
  on abelian sheaves.
* `AlgebraicGeometry.Space.IsFppfHypercovering.isIso_derivedUnit_of_fppfSpacesEtaleAcyclic`: the
  statement of Stacks 0DH7, from Stacks 0DGG on single sheaves for `X` and every `U_n`.
* `AlgebraicGeometry.Space.IsFppfHypercovering.derivedGlobalSectionsIsoOfFppfSpacesEtaleAcyclic`:
  the statement of Stacks 0DH8 from the same input.

## References

* [Stacks Project, Tag 0DH7](https://stacks.math.columbia.edu/tag/0DH7)
* [Stacks Project, Tag 0DH8](https://stacks.math.columbia.edu/tag/0DH8)
* [Stacks Project, Tag 0DH5](https://stacks.math.columbia.edu/tag/0DH5)
* [Stacks Project, Tag 0DGG](https://stacks.math.columbia.edu/tag/0DGG)
* [Stacks Project, Tag 0D8N](https://stacks.math.columbia.edu/tag/0D8N)
* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering
open Stacks.Topos.AbelianPushforward CategoryTheory.SimplicialSemiRepresentable

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

/-! ### The augmentation of the fppf total site -/

/-- The inverse image `a_fppf⁻¹ : Ab((Spaces/X)_fppf) ⥤ Ab((Spaces/U)_{fppf,total})` of the
augmentation of the fppf total site. -/
abbrev fppfAugmentationAbelianInverseImage :=
  CategoryTheory.SimplicialSemiRepresentable.abelianTotalInverseImageOver
    (fppfPretopology B S hS).toGrothendieck A.right (fppfHypercover A)

/-- The direct image `a_{fppf,*}` of the augmentation of the fppf total site. -/
abbrev fppfAugmentationAbelianDirectImage :=
  CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardOver
    (fppfPretopology B S hS).toGrothendieck A.right (fppfHypercover A)

/-- The adjunction `a_fppf⁻¹ ⊣ a_{fppf,*}` on abelian sheaves. -/
abbrev fppfAugmentationAbelianAdjunction :
    fppfAugmentationAbelianInverseImage A ⊣ fppfAugmentationAbelianDirectImage A :=
  CategoryTheory.SimplicialSemiRepresentable.abelianTotalAdjunctionOver _ _ _

/-- The direct image `a_{fppf,*}` on abelian sheaves is additive. -/
instance fppfAugmentationAbelianDirectImage_additive :
    (fppfAugmentationAbelianDirectImage A).Additive :=
  CategoryTheory.SimplicialSemiRepresentable.additive_abelianTotalPushforwardOver _ _ _

/-- The inverse image `a_fppf⁻¹` on abelian sheaves preserves finite limits. -/
instance fppfAugmentationAbelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (fppfAugmentationAbelianInverseImage A) :=
  Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _
    (totalForget (fppfHypercover A)) AddCommGrpCat.{u + 1}

/-- Abelian sheaves on `(Spaces/X)_fppf` for the topology generated by the fppf pretopology, in
which the total site is built, are abelian sheaves for the fppf topology, in which the comparison
`a_X` is built: the two topologies are equal (`fppfPretopology_toGrothendieck`). -/
def fppfOverSheafEquiv (Y : AlgebraicSpaces B S hS) :
    Sheaf ((fppfTopology B S hS).over Y) AddCommGrpCat.{u + 1} ≌
      Sheaf ((fppfPretopology B S hS).toGrothendieck.over Y) AddCommGrpCat.{u + 1} :=
  sheafEquivOfTopologyEq (congrArg (·.over Y) (fppfPretopology_toGrothendieck B S hS).symm)
    AddCommGrpCat.{u + 1}

/-- The functor of `fppfOverSheafEquiv Y` is additive. -/
instance fppfOverSheafEquiv_functor_additive (Y : AlgebraicSpaces B S hS) :
    (fppfOverSheafEquiv Y).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of `fppfOverSheafEquiv Y` is additive. -/
instance fppfOverSheafEquiv_inverse_additive (Y : AlgebraicSpaces B S hS) :
    (fppfOverSheafEquiv Y).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of `fppfOverSheafEquiv Y` preserves homology. -/
instance fppfOverSheafEquiv_inverse_preservesHomology (Y : AlgebraicSpaces B S hS) :
    (fppfOverSheafEquiv Y).inverse.PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The inverse image `a_fppf⁻¹` of the augmentation of the fppf total site, read on abelian
sheaves for the fppf topology. -/
abbrev fppfAugmentationInverseImage :=
  (fppfOverSheafEquiv A.right).functor ⋙ fppfAugmentationAbelianInverseImage A

/-- The direct image `a_{fppf,*}`, read on abelian sheaves for the fppf topology. -/
abbrev fppfAugmentationDirectImage :=
  fppfAugmentationAbelianDirectImage A ⋙ (fppfOverSheafEquiv A.right).inverse

/-- The adjunction `a_fppf⁻¹ ⊣ a_{fppf,*}` on abelian sheaves for the fppf topology. -/
abbrev fppfAugmentationAdjunction :
    fppfAugmentationInverseImage A ⊣ fppfAugmentationDirectImage A :=
  (fppfOverSheafEquiv A.right).toAdjunction.comp (fppfAugmentationAbelianAdjunction A)

/-- The inverse image `a_fppf⁻¹` for the fppf topology preserves monomorphisms. -/
instance fppfAugmentationInverseImage_preservesMonomorphisms :
    (fppfAugmentationInverseImage A).PreservesMonomorphisms :=
  inferInstance

/-- The direct image `a_{fppf,*}` for the fppf topology is additive. -/
instance fppfAugmentationDirectImage_additive : (fppfAugmentationDirectImage A).Additive :=
  inferInstance

variable {A}

/-- **Stacks 0DA8 (2) and Stacks 0D8N for an fppf hypercovering.** Let `a : U → X` be an fppf
hypercovering of an algebraic space. For every abelian sheaf `N` on `(Spaces/X)_fppf` the unit
`N ⟶ a_{fppf,*}a_fppf⁻¹N` is an isomorphism and `R^q a_{fppf,*}(a_fppf⁻¹N) = 0` for `q > 0`:
`U` is a hypercovering of `X` in the fppf site (Stacks 09X8). -/
theorem IsFppfHypercovering.fppfAugmentation_descent (hA : IsFppfHypercovering A)
    (N : Sheaf ((fppfPretopology B S hS).toGrothendieck.over A.right) AddCommGrpCat.{u + 1}) :
    IsIso ((fppfAugmentationAbelianAdjunction A).unit.app N) ∧
      ∀ q : ℕ, 0 < q → IsZero (((fppfAugmentationAbelianDirectImage A).rightDerived q).obj
        ((fppfAugmentationAbelianInverseImage A).obj N)) := by
  have h := isHypercoveringAugmentation_of_isFppfHypercovering hA
  have : IsIso (fppfAugmentationAbelianAdjunction A).unit :=
    isIso_abelianUnit_augmented' _ _ _ h
  exact ⟨inferInstance, fun q hq ↦
    isZero_rightDerived_abelianTotalPushforwardOver_of_isHypercovering _ _ _ h N q hq⟩

/-- **Stacks 0DA8 (2) and Stacks 0D8N for an fppf hypercovering, for the fppf topology**: the
same statement for abelian sheaves on `(Spaces/X)_fppf` in the spelling of the comparison `a_X`. -/
theorem IsFppfHypercovering.fppfAugmentation_descent' (hA : IsFppfHypercovering A)
    (N : Sheaf ((fppfTopology B S hS).over A.right) AddCommGrpCat.{u + 1}) :
    IsIso ((fppfAugmentationAdjunction A).unit.app N) ∧
      ∀ q : ℕ, 0 < q → IsZero (((fppfAugmentationDirectImage A).rightDerived q).obj
        ((fppfAugmentationInverseImage A).obj N)) := by
  obtain ⟨hu, hv⟩ := hA.fppfAugmentation_descent ((fppfOverSheafEquiv A.right).functor.obj N)
  refine ⟨?_, fun q hq ↦ ?_⟩
  · rw [Adjunction.comp_unit_app]
    infer_instance
  · exact ((fppfOverSheafEquiv A.right).inverse.map_isZero (hv q hq)).of_iso
      ((Functor.rightDerivedCompIso (fppfAugmentationAbelianDirectImage A)
        (fppfOverSheafEquiv A.right).inverse q).app _)

/-! ### The assembly -/

variable (A)

/-- The inverse image `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` of the augmentation of Section 0DE7. -/
abbrev etaleAugmentationAbelianInverseImage :=
  Sites.abelianInverseImage (etaleAugmentationMorphism A)

/-- The adjunction `a⁻¹ ⊣ a_*` on abelian sheaves. -/
abbrev etaleAugmentationAbelianAdjunction :=
  abelianInverseImageAdjPushforward (etaleSimplicialSite A).totalTopology
    (etaleAugmentationMorphism A)

/-- The inverse image `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` preserves finite limits. -/
instance etaleAugmentationAbelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (etaleAugmentationAbelianInverseImage A) :=
  Sites.abelianInverseImage_preservesFiniteLimits (etaleAugmentationMorphism A)

/-- The inverse image `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` preserves finite colimits. -/
instance etaleAugmentationAbelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (etaleAugmentationAbelianInverseImage A) :=
  Sites.abelianInverseImage_preservesFiniteColimits (etaleAugmentationMorphism A)

/-- The inverse image `a⁻¹ : Ab(X_étale) ⥤ Ab(U_étale)` is additive. -/
instance etaleAugmentationAbelianInverseImage_additive :
    (etaleAugmentationAbelianInverseImage A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The direct image `a_* : Ab(U_étale) ⥤ Ab(X_étale)` is additive. -/
instance etaleAugmentationAbelianDirectImage_additive :
    (abelianPushforward (etaleSimplicialSite A).totalTopology
      (etaleAugmentationMorphism A)).Additive :=
  (etaleAugmentationAbelianAdjunction A).right_adjoint_additive

/-- `a_*` preserves injective objects, being right adjoint to the exact functor `a⁻¹`. -/
instance etaleAugmentationAbelianDirectImage_preservesInjectiveObjects :
    (abelianPushforward (etaleSimplicialSite A).totalTopology
      (etaleAugmentationMorphism A)).PreservesInjectiveObjects :=
  ⟨fun {I} hI => (etaleAugmentationAbelianAdjunction A).map_injective I hI⟩

/-- The global sections functor on abelian sheaves on `Y_{spaces, étale}` is additive. -/
instance sheafΓ_spacesEtale_additive (Y : AlgebraicSpaces B S hS) :
    (Sheaf.Γ (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}).Additive :=
  (constantSheafΓAdj _ AddCommGrpCat.{u + 1}).right_adjoint_additive

/-- The global sections functor on abelian sheaves on `Y_{spaces, étale}` preserves finite
limits. -/
instance sheafΓ_spacesEtale_preservesFiniteLimits (Y : AlgebraicSpaces B S hS) :
    PreservesFiniteLimits (Sheaf.Γ (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}) :=
  haveI : PreservesLimitsOfSize.{0, 0}
      (Sheaf.Γ (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}) :=
    (constantSheafΓAdj _ AddCommGrpCat.{u + 1}).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- The global sections functor on abelian sheaves on `U_étale` is additive. -/
instance sheafΓ_etaleSimplicialSite_additive :
    (Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1}).Additive :=
  (constantSheafΓAdj _ AddCommGrpCat.{u + 1}).right_adjoint_additive

/-! ### The comparison in one simplicial degree -/

/-- The equivalence of abelian sheaves on the component of degree `n` of `U_étale` with abelian
sheaves on `U_{n, spaces, étale}`. -/
abbrev etaleDegreeSheafEquiv (n : SimplexCategory) :
    Sheaf ((etaleSimplicialSite A).situation.componentTopology n) AddCommGrpCat.{u + 1} ≌
      Sheaf (SpacesEtale.topology B S hS (A.left.obj (op n))) AddCommGrpCat.{u + 1} :=
  EtaleComponent.sheafEquiv n AddCommGrpCat.{u + 1}

/-- The equivalence of abelian sheaves on the component of degree `n` of the fppf total site
with abelian sheaves on `(Spaces/U_n)_fppf`: the component is `(Spaces/X)/(U_n/X)`, which is
`(Spaces/U_n)_fppf` by the iterated slice equivalence. -/
abbrev fppfDegreeSheafEquiv (n : SimplexCategory) :
    Sheaf ((fppfTotalSituation A).componentTopology n) AddCommGrpCat.{u + 1} ≌
    Sheaf ((fppfTopology B S hS).over (A.left.obj (op n))) AddCommGrpCat.{u + 1} :=
  (sheafEquivOfTopologyEq (componentTopology_eq _ (fppfHypercover A) n) AddCommGrpCat.{u + 1}).trans
    ((CategoryTheory.SimplicialOver.componentSheafEquivalence A.left A.hom
      (fppfPretopology B S hS).toGrothendieck (op n)).trans
      (fppfOverSheafEquiv (A.left.obj (op n))).symm)

/-- The direct image of abelian sheaves along the comparison `V ↦ V/U_n` of degree `n`. -/
abbrev etaleFppfDegreeAbDirectImage (n : SimplexCategory) :
    Sheaf ((fppfTotalSituation A).componentTopology n) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((etaleSimplicialSite A).situation.componentTopology n) AddCommGrpCat.{u + 1} :=
  (etaleToFppfDegree A n).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    ((etaleSimplicialSite A).situation.componentTopology n)
    ((fppfTotalSituation A).componentTopology n)

/-- The direct image along the comparison of degree `n` is the direct image `a_{U_n,*}` of
Section 0DGE, read through the identifications of the two components with the sites of `U_n`:
both are restriction along `V ↦ V/U_n`. -/
def etaleFppfDegreeAbDirectImageIso (n : SimplexCategory) :
    ((fppfDegreeSheafEquiv A n).functor ⋙
        fppfSpacesEtaleAbelianDirectImage (A.left.obj (op n))) ⋙
      (etaleDegreeSheafEquiv A n).inverse ≅ etaleFppfDegreeAbDirectImage A n :=
  NatIso.ofComponents (fun _ ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _))
    (fun _ ↦ by
      apply Sheaf.hom_ext
      rfl)

/-- The adjunction of the comparison of degree `n`: the adjunction `a_{U_n}^{-1} ⊣ a_{U_n,*}` of
Section 0DGE, read through the identifications of the two components with the sites of `U_n`. -/
def etaleFppfDegreeAbAdjunction (n : SimplexCategory) :
    (etaleDegreeSheafEquiv A n).functor ⋙
        (fppfSpacesEtaleAbelianInverseImage (A.left.obj (op n)) ⋙
          (fppfDegreeSheafEquiv A n).inverse) ⊣ etaleFppfDegreeAbDirectImage A n :=
  ((etaleDegreeSheafEquiv A n).toAdjunction.comp
    ((fppfSpacesEtaleAbelianAdjunction (A.left.obj (op n))).comp
      (fppfDegreeSheafEquiv A n).symm.toAdjunction)).ofNatIsoRight
    (etaleFppfDegreeAbDirectImageIso A n)

variable {A} in
/-- **Stacks 0DGG on single sheaves, read in simplicial degree `n`**: the property
`FppfSpacesEtaleAcyclic` of `U_n` gives the same statement for the comparison of degree `n` of
the total sites, the two being identified through the equivalences of the components with the
sites of `U_n`. -/
theorem FppfSpacesEtaleAcyclic.degree {n : SimplexCategory}
    (h : FppfSpacesEtaleAcyclic (A.left.obj (op n)))
    (G : Sheaf ((etaleSimplicialSite A).situation.componentTopology n) AddCommGrpCat.{u + 1}) :
    IsIso ((etaleFppfDegreeAbAdjunction A n).unit.app G) ∧
      ∀ q : ℕ, 0 < q → IsZero (((etaleFppfDegreeAbDirectImage A n).rightDerived q).obj
        (((etaleDegreeSheafEquiv A n).functor ⋙
          (fppfSpacesEtaleAbelianInverseImage (A.left.obj (op n)) ⋙
            (fppfDegreeSheafEquiv A n).inverse)).obj G)) := by
  obtain ⟨hu, hv⟩ := h ((etaleDegreeSheafEquiv A n).functor.obj G)
  refine ⟨?_, fun q hq ↦ ?_⟩
  · have e : (etaleFppfDegreeAbAdjunction A n).unit.app G =
        ((etaleDegreeSheafEquiv A n).toAdjunction.comp
          ((fppfSpacesEtaleAbelianAdjunction (A.left.obj (op n))).comp
            (fppfDegreeSheafEquiv A n).symm.toAdjunction)).unit.app G ≫
          (etaleFppfDegreeAbDirectImageIso A n).hom.app _ := by
      rw [← Adjunction.homEquiv_id, etaleFppfDegreeAbAdjunction,
        Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
      rfl
    rw [e, Adjunction.comp_unit_app, Adjunction.comp_unit_app]
    infer_instance
  · let EC := etaleDegreeSheafEquiv A n
    let ED := fppfDegreeSheafEquiv A n
    have : EC.functor.Additive := Functor.additive_of_preserves_binary_products _
    have : ED.functor.Additive := Functor.additive_of_preserves_binary_products _
    have : EC.functor.PreservesHomology := Functor.preservesHomologyOfExact _
    let sq : etaleFppfDegreeAbDirectImage A n ⋙ EC.functor ≅
        ED.functor ⋙ fppfSpacesEtaleAbelianDirectImage (A.left.obj (op n)) :=
      Functor.isoWhiskerRight (etaleFppfDegreeAbDirectImageIso A n).symm EC.functor ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ EC.counitIso ≪≫
          Functor.rightUnitor _
    have e₁ := (Functor.rightDerivedIsoOfSquare ED.functor (etaleFppfDegreeAbDirectImage A n)
      (fppfSpacesEtaleAbelianDirectImage (A.left.obj (op n))) EC.functor sq q).app
        (ED.inverse.obj ((fppfSpacesEtaleAbelianInverseImage (A.left.obj (op n))).obj
          (EC.functor.obj G)))
    have e₂ := ((fppfSpacesEtaleAbelianDirectImage (A.left.obj (op n))).rightDerived q).mapIso
      (ED.counitIso.app ((fppfSpacesEtaleAbelianInverseImage (A.left.obj (op n))).obj
        (EC.functor.obj G)))
    have hz : IsZero (EC.functor.obj (((etaleFppfDegreeAbDirectImage A n).rightDerived q).obj
        (ED.inverse.obj ((fppfSpacesEtaleAbelianInverseImage (A.left.obj (op n))).obj
          (EC.functor.obj G))))) :=
      (hv q hq).of_iso (e₁ ≪≫ e₂)
    exact (EC.inverse.map_isZero hz).of_iso (EC.unitIso.app _)

/-! ### The comparison morphism `h` on abelian sheaves -/

/-- The direct image `h_*` of sheaves of sets along the comparison is a right adjoint. -/
instance isRightAdjoint_etaleToFppfTotal_sheafPushforwardContinuous :
    ((etaleToFppfTotal A).sheafPushforwardContinuous (Type (u + 1))
      (etaleSimplicialSite A).situation.totalTopology
      (fppfTotalSituation A).totalTopology).IsRightAdjoint :=
  ⟨_, ⟨(etaleFppfComparisonMorphism A).adj⟩⟩

/-- The inverse image `h⁻¹` of the comparison morphism of Stacks 0DH5 on abelian sheaves. -/
abbrev etaleFppfComparisonAbInverseImage :
    Sheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (fppfTotalSituation A).totalTopology AddCommGrpCat.{u + 1} :=
  Sites.abelianInverseImage (etaleFppfComparisonMorphism A)

/-- The direct image `h_*` of the comparison morphism on abelian sheaves: restriction along
`u : (n, V) ↦ V/U_n`. -/
abbrev etaleFppfComparisonAbDirectImage :
    Sheaf (fppfTotalSituation A).totalTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1} :=
  (etaleToFppfTotal A).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (etaleSimplicialSite A).situation.totalTopology (fppfTotalSituation A).totalTopology

/-- The adjunction `h⁻¹ ⊣ h_*` on abelian sheaves. -/
abbrev etaleFppfComparisonAbAdjunction :
    etaleFppfComparisonAbInverseImage A ⊣ etaleFppfComparisonAbDirectImage A :=
  abelianInverseImageAdjRestriction (etaleToFppfTotal A)
    (etaleSimplicialSite A).situation.totalTopology (fppfTotalSituation A).totalTopology
    (etaleFppfComparisonMorphism A) (Iso.refl _)

/-- The direct image `h_*` on abelian sheaves is additive. -/
instance etaleFppfComparisonAbDirectImage_additive :
    (etaleFppfComparisonAbDirectImage A).Additive where

/-- Restriction of abelian sheaves on `U_étale` to the component of simplicial degree `n`. -/
abbrev etaleRestrictAb (n : SimplexCategory) :
    Sheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf ((etaleSimplicialSite A).situation.componentTopology n) AddCommGrpCat.{u + 1} :=
  (etaleSimplicialSite A).situation.restrictAb n

/-- Restriction to simplicial degree `n` preserves finite limits. -/
instance etaleRestrictAb_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (etaleRestrictAb A n) :=
  SimplicialSiteSituation.preservesFiniteLimits_componentRestrictionAb _ n

/-- Restriction to simplicial degree `n` preserves finite colimits. -/
instance etaleRestrictAb_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (etaleRestrictAb A n) :=
  SimplicialSiteSituation.preservesFiniteColimits_componentRestrictionAb _ n

/-- Restriction to simplicial degree `n` is additive. -/
instance etaleRestrictAb_additive (n : SimplexCategory) : (etaleRestrictAb A n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction to simplicial degree `n` preserves homology. -/
instance etaleRestrictAb_preservesHomology (n : SimplexCategory) :
    (etaleRestrictAb A n).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The restrictions to the simplicial degrees jointly reflect isomorphisms of abelian sheaves on
`U_étale`. -/
theorem isIso_of_forall_isIso_etaleRestrictAb_map
    {F G : Sheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (h : ∀ n, IsIso ((etaleRestrictAb A n).map f)) : IsIso f :=
  SimplicialSiteSituation.isIso_of_forall_isIso_restrictAb_map (etaleSimplicialSite A).situation f h

/-- The inverse image `h⁻¹` on abelian sheaves preserves monomorphisms. -/
instance etaleFppfComparisonAbInverseImage_preservesMonomorphisms :
    (etaleFppfComparisonAbInverseImage A).PreservesMonomorphisms :=
  haveI : PreservesFiniteLimits (etaleFppfComparisonAbInverseImage A) :=
    Sites.abelianInverseImage_preservesFiniteLimits (etaleFppfComparisonMorphism A)
  inferInstance

/-- The functor `u : (n, V) ↦ V/U_n` is continuous for the total topologies. -/
instance etaleToFppfTotal_isContinuous_etaleTotalTopology :
    (etaleToFppfTotal A).IsContinuous (etaleSimplicialSite A).totalTopology
      (fppfTotalSituation A).totalTopology :=
  etaleToFppfTotal_isContinuous A

/-- The inclusion of the component of degree `n` into the total site of `U_étale` is continuous. -/
instance etaleComponentFunctor_isContinuous (n : SimplexCategory) :
    (SimplicialSiteSituation.componentFunctor (etaleSimplicialSite A).situation n).IsContinuous
      ((etaleSimplicialSite A).situation.componentTopology n)
      (etaleSimplicialSite A).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isContinuous _ n

/-- The inclusion of the component of degree `n` into the total site of `U_étale` is
cocontinuous. -/
instance etaleComponentFunctor_isCocontinuous (n : SimplexCategory) :
    (SimplicialSiteSituation.componentFunctor (etaleSimplicialSite A).situation n).IsCocontinuous
      ((etaleSimplicialSite A).situation.componentTopology n)
      (etaleSimplicialSite A).totalTopology :=
  SimplicialSiteSituation.componentFunctor_isCocontinuous _ n

/-- **Stacks 0D96 for `h` on abelian sheaves**: restricting `h⁻¹G` to simplicial degree `n` is the
inverse image along the comparison `a_{U_n}` of degree `n` of the restriction of `G`, by the
Beck–Chevalley property of the Guitart exact square of component inclusions of `u`. -/
def etaleFppfComparisonDegreeIso (n : SimplexCategory) :
    etaleRestrictAb A n ⋙
        ((etaleDegreeSheafEquiv A n).functor ⋙
          (fppfSpacesEtaleAbelianInverseImage (A.left.obj (op n)) ⋙
            (fppfDegreeSheafEquiv A n).inverse)) ≅
      etaleFppfComparisonAbInverseImage A ⋙ (fppfTotalSituation A).restrictAb n :=
  TwoSquare.sheafBeckChevalleyIso (etaleToFppfSquare A n) (etaleFppfComparisonAbAdjunction A)
    (etaleFppfDegreeAbAdjunction A n)

/-- The mate of `etaleFppfComparisonDegreeIso A n`, comparing the direct images `h_*` and
`a_{U_n,*}` through restriction to degree `n`, is an isomorphism. -/
instance isIso_mateEquiv_etaleFppfComparisonDegreeIso (n : SimplexCategory) :
    IsIso (mateEquiv (etaleFppfComparisonAbAdjunction A) (etaleFppfDegreeAbAdjunction A n)
      (etaleFppfComparisonDegreeIso A n).hom) := by
  have h := TwoSquare.isIso_mateEquiv_sheafBeckChevalleyIso (etaleToFppfSquare A n)
    (etaleFppfComparisonAbAdjunction A) (etaleFppfDegreeAbAdjunction A n)
  exact h

/-- Restriction of abelian sheaves on the fppf total site to simplicial degree `n` is additive. -/
instance fppfTotalSituation_restrictAb_additive (n : SimplexCategory) :
    ((fppfTotalSituation A).restrictAb n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The direct image along the comparison of degree `n` is additive. -/
instance etaleFppfDegreeAbDirectImage_additive (n : SimplexCategory) :
    (etaleFppfDegreeAbDirectImage A n).Additive where

/-- The direct image `a_{fppf,*}` of sheaves of sets along `V/U_n ↦ V/X` is a right adjoint. -/
instance isRightAdjoint_totalForget_sheafPushforwardContinuous_fppf :
    ((totalForget (fppfHypercover A)).sheafPushforwardContinuous (Type (u + 1))
      (fppfTotalSituation A).totalTopology ((fppfTopology B S hS).over A.right)).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (totalForget (fppfHypercover A))
    (Type (u + 1)) (fppfTotalSituation A).totalTopology
    ((fppfTopology B S hS).over A.right)).isRightAdjoint

/-- The abelian inverse image of the augmentation of the fppf total site, as a morphism of topoi
of sheaves of sets, is restriction of abelian sheaves along `V/U_n ↦ V/X`. -/
def fppfAugmentationAbelianInverseImageIso :
    Sites.abelianInverseImage (fppfAugmentationTypesMorphism A) ≅ fppfAugmentationInverseImage A :=
  Sites.abelianInverseImageIsoSheafPushforwardContinuous (totalForget (fppfHypercover A))
    (fppfTotalSituation A).totalTopology ((fppfTopology B S hS).over A.right)
    (fppfAugmentationTypesMorphism A) (Iso.refl _) ≪≫ Iso.refl _

/-- **Stacks 0DH5, on abelian sheaves**: the square of inverse images
`h⁻¹ a⁻¹ ≅ a_fppf⁻¹ h₋₁⁻¹` commutes on abelian sheaves. -/
def fppfComparisonSquareAbelianInverseImageIso :
    etaleAugmentationAbelianInverseImage A ⋙ etaleFppfComparisonAbInverseImage A ≅
      fppfSpacesEtaleAbelianInverseImage A.right ⋙ fppfAugmentationInverseImage A :=
  StacksTag03LR.abelianInverseImageSquareIso _ _ _ _ (fppfComparisonSquareInverseImageIso A) ≪≫
    Functor.isoWhiskerLeft _ (fppfAugmentationAbelianInverseImageIso A)

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- `Γ(X_étale, a_*F) = Γ(U_étale, F)` for abelian sheaves `F` on `U_étale`: global sections of a
direct image along a morphism of topoi, `U_étale` having no final object. -/
def etaleAugmentationGammaIso :
    abelianPushforward (etaleSimplicialSite A).totalTopology (etaleAugmentationMorphism A) ⋙
        Sheaf.Γ (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1} :=
  MorphismOfTopoi.abelianPushforwardGammaIsoOfSmallSites (etaleAugmentationMorphism A)

section Assembly

variable {A}

variable [HasDerivedCategory (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (etaleSimplicialSite A).totalTopology AddCommGrpCat.{u + 1})]

/-- **The statement of Stacks 0DH7, from Stacks 0DGG on single sheaves.** Let `a : U → X` be an
fppf hypercovering of an algebraic space and `a : Sh(U_étale) → Sh(X_étale)` the morphism of topoi
of Section 0DE7. Suppose that the statement of Stacks 0DGG holds on single sheaves for `X` and
for every `U_n` (`FppfSpacesEtaleAcyclic`). Then for every `K ∈ D⁺(X_étale)` the map
`K ⟶ Ra_*(a⁻¹K)`, the unit of the derived adjunction `a⁻¹ ⊣ Ra_*`, is an isomorphism.

The proof is the source's: the commutative square of Stacks 0DH5
(`fppfComparisonSquareAbelianInverseImageIso`), the description of `h` degree by degree by the
comparisons `h_n = a_{U_n}` (Stacks 0D96, `etaleFppfComparisonDegreeIso`), Stacks 0D8N and 0DA8
for `a_fppf` (`IsFppfHypercovering.fppfAugmentation_descent'`), assembled by
`CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_unit_app_of_degreewise`. -/
theorem IsFppfHypercovering.isIso_derivedUnit_of_fppfSpacesEtaleAcyclic
    (hA : IsFppfHypercovering A)
    (hAcycX : FppfSpacesEtaleAcyclic A.right)
    (hAcycU : ∀ n : SimplexCategory, FppfSpacesEtaleAcyclic (A.left.obj (op n)))
    (K : DerivedCategory.Plus (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (etaleAugmentationAbelianAdjunction A)).unit.app K) :=
  CategoryTheory.Adjunction.isIso_derivedPlusAdjunction_unit_app_of_degreewise
    (etaleAugmentationAbelianAdjunction A) (etaleFppfComparisonAbAdjunction A)
    (fppfAugmentationAdjunction A) (fppfSpacesEtaleAbelianAdjunction A.right)
    (fppfComparisonSquareAbelianInverseImageIso A)
    (fun n ↦ etaleRestrictAb A n)
    (fun n ↦ (fppfTotalSituation A).restrictAb n) (fun n ↦ etaleFppfDegreeAbAdjunction A n)
    (fun n ↦ etaleFppfComparisonDegreeIso A n)
    (fun f h ↦ isIso_of_forall_isIso_etaleRestrictAb_map A f h)
    (fun n G ↦ (hAcycU n).degree G) hAcycX (fun N ↦ hA.fppfAugmentation_descent' N) K

variable [HasDerivedCategory AddCommGrpCat.{u + 1}]

/-- **The statement of Stacks 0DH8, from Stacks 0DGG on single sheaves.** Under the hypotheses of
`IsFppfHypercovering.isIso_derivedUnit_of_fppfSpacesEtaleAcyclic`,
`RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)` naturally in `K ∈ D⁺(X_étale)`; the forward map is the
pullback on derived global sections through the factorization
`RΓ(U_étale, -) = RΓ(X_étale, -) ∘ Ra_*` of Stacks 08J6, which rests on
`Γ(X_étale, a_*F) = Γ(U_étale, F)` (`etaleAugmentationGammaIso`). -/
def IsFppfHypercovering.derivedGlobalSectionsIsoOfFppfSpacesEtaleAcyclic
    (hA : IsFppfHypercovering A)
    (hAcycX : FppfSpacesEtaleAcyclic A.right)
    (hAcycU : ∀ n : SimplexCategory, FppfSpacesEtaleAcyclic (A.left.obj (op n))) :
    (Sheaf.Γ (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ≅
      (etaleAugmentationAbelianInverseImage A).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (etaleSimplicialSite A).totalTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  CategoryTheory.Adjunction.derivedGlobalSectionsIsoOfDegreewise
    (etaleAugmentationAbelianAdjunction A) (etaleFppfComparisonAbAdjunction A)
    (fppfAugmentationAdjunction A) (fppfSpacesEtaleAbelianAdjunction A.right)
    (fppfComparisonSquareAbelianInverseImageIso A)
    (fun n ↦ etaleRestrictAb A n)
    (fun n ↦ (fppfTotalSituation A).restrictAb n) (fun n ↦ etaleFppfDegreeAbAdjunction A n)
    (fun n ↦ etaleFppfComparisonDegreeIso A n)
    (fun f h ↦ isIso_of_forall_isIso_etaleRestrictAb_map A f h)
    (fun n G ↦ (hAcycU n).degree G) hAcycX (fun N ↦ hA.fppfAugmentation_descent' N) _ _
    (etaleAugmentationGammaIso A)

end Assembly

end AlgebraicGeometry.Space

end
