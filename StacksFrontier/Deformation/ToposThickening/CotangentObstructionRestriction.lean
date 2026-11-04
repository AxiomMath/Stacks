module

public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionBaseClass

/-!
# The restriction of a first Ext class of the naive cotangent complex to the base ideal

Let `g : A' ⟶ A` be a locally surjective homomorphism of sheaves of commutative rings with kernel
`I`, let `h : A ⟶ O` be a further homomorphism and `G` a sheaf of `O`-modules. A class
`ζ ∈ Ext¹_O(NL_{O/A'}, G)` gives, through the first morphism of the fundamental triangle of
`A' ⟶ A ⟶ O` (Tag 08SZ) and the identification of maps `L_{A/A'} ⊗_A O ⟶ G[1]` with `A`-linear
maps `I/I² ⟶ G`, a map `I/I² ⟶ G`. This file computes it: if `ζ` is the class of a conormal
functional `δ` on a presentation `A'[E] ⟶ O`, the map sends the class of a section `x` of `I` to
`δ` of the class of `x` read as a coefficient, up to the automorphism of `G` fixed by the
identification of `G[-1]` with `G[0][1]`.

## Main results

* `Deformation.ToposThickening.CotangentObstruction.baseExtEquiv_towerClass_conormalClass`: the
  formula.
* `Deformation.ToposThickening.CotangentObstruction.baseExtEquiv_canonicalClass_conormalClass`:
  the formula for a structure map equal to `g ≫ h`, through the canonical map `L ⟶ NL`.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal Stacks.SheafOfModules

universe t u

namespace Deformation.ToposThickening.CotangentObstruction

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A' A O : Sheaf J CommRingCat.{u}} (g : A' ⟶ A) (h : A ⟶ O)
  [Presheaf.IsLocallySurjective J g.hom]
  [HasDerivedCategory.{t} (targetModules.{u, u, u} J O)] (G : targetModules.{u, u, u} J O)
  (E : Cᵒᵖ ⥤ Type u) (α : E ⟶ underlyingPresheaf J O)
  [Presheaf.IsLocallySurjective J (presentation J A' O (g ≫ h) E α).hom]

omit [J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Presheaf.IsLocallySurjective J g.hom]
  [HasDerivedCategory.{t} (targetModules.{u, u, u} J O)] in
/-- A section of the kernel of `g` lies in the kernel of `g ≫ h`. -/
theorem mem_kernelIdeal_comp (U : Cᵒᵖ) (x : kernelIdeal g.hom U) :
    (x : A'.obj.obj U) ∈ kernelIdeal (g ≫ h).hom U := by
  show h.hom.app U (g.hom.app U x) = 0
  rw [show g.hom.app U x = 0 from x.2, map_zero]

/-- **The restriction to the base ideal of a first Ext class of `NL_{O/A'}`.** Read through the
first morphism of the fundamental triangle of `A' ⟶ A ⟶ O` and the identification of maps
`L_{A/A'} ⊗_A O ⟶ G[1]` with `A`-linear maps `I/I² ⟶ G`, the class `ζ` of a conormal functional
`δ` on a presentation by `E` sends the class of a section `x` of `I` to `δ` of the class of `x`
read as a coefficient, followed by the automorphism `negOneHomologySingleIso` of `G`. -/
theorem baseExtEquiv_towerClass_conormalClass
    (δ : (presentationConormalSequence.{u, u, max u u u, u} J A' O (g ≫ h) E α).X₁ ⟶ G)
    (ζ : DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, max u u u, u} J A' O (g ≫ h)) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧)
    (hζ : DerivedCategory.Q.map
        (naiveCotangentComplexComparison.{u, u, max u u u, u} J A' O (g ≫ h) E α) ≫ ζ =
      presentationConormalExtClass.{u, u, u, t} J A' O (g ≫ h) E α G δ)
    (U : Cᵒᵖ) (x : kernelIdeal g.hom U) :
    (baseExtEquiv.{u, u, u} J g h G (DerivedCategory.Q.map (towerNaiveMap.{u, u, u} J g h) ≫
        DerivedCategory.Q.map (naiveCotangentComplexIsoCanonical.{u, u, u} J (g ≫ h)).hom ≫
          ζ)).val.app U (conormalClass.{u, u, max u u u, u} J A' A' A (𝟙 A') g U x) =
      (DerivedCategory.negOneHomologySingleIso G
          (((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0
            (by decide)).inv.app G)).hom.val.app U
        (δ.val.app U (conormalClass.{u, u, max u u u, u} J A' (freeAlgebraSheaf J A' E) O
          (freeAlgebraSheafCoefficientMap J A' E) (presentation J A' O (g ≫ h) E α) U
          ⟨_, coeff_mem_kernelIdeal_presentation J A' O (g ≫ h) E α U
            ⟨x, mem_kernelIdeal_comp g h U x⟩⟩)) := by
  have hdP := (naiveCotangentComplex_isZero_X.{u, u, u} J (g ≫ h) _ (by simp) (by simp)).eq_of_src
    ((naiveCotangentComplex.{u, u, u} J (g ≫ h)).d ((ComplexShape.up ℤ).prev (-1)) (-1)) 0
  have M1 : (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).inv ≫
      HomologicalComplex.homologyMap (squareCotangentComplexMap (towerSquare.{u, u, u} g h) ≫
        ((squareRestrict.{u, u, u} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (naiveComparison.{u, u, u} J (g ≫ h))) (-1) ≫
        (ShortComplex.homologyMapIsoOfLeftHomologyData (squareRestrict.{u, u, u} J h)
          ((naiveCotangentComplex.{u, u, u} J (g ≫ h)).sc (-1)).leftHomologyData).hom ≫
          (squareRestrict.{u, u, u} J h).map
            ((naiveCotangentComplex.{u, u, u} J (g ≫ h)).homologyToX (-1) hdP ≫
              (naiveCotangentComplexXNegOneIso.{u, u, u} J (g ≫ h)).hom) =
      (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).inv ≫
        ((cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).hom ≫
          Stacks.Sites.Conormal.conormalSheafMapOfFac.{u, u, max u u u, u} J A A'
            (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) g (resolutionAugmentation J g (op ⦋0⦌))
            (resolutionBase.{u, u, u} J g (op ⦋0⦌))
            (resolutionBase_comp_resolutionAugmentation g)) ≫
          towerZeroConormal.{u, u, u} g h := by
    refine congrArg (_ ≫ ·) ?_
    have i1 := homologyMapIso_hom_map_homologyToX_assoc.{u, u, u} h
      (naiveCotangentComplex.{u, u, u} J (g ≫ h)) hdP (restrictedNaive_d_prev_negOne.{u, u, u} g h)
      ((squareRestrict.{u, u, u} J h).map
        (naiveCotangentComplexXNegOneIso.{u, u, u} J (g ≫ h)).hom)
    exact (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_comp _ _ _)).trans
      i1)).trans (homologyMap_towerCotangentNaive_homologyToX.{u, u, u} g h)
  set Y := ((cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).inv ≫
      HomologicalComplex.homologyMap (squareCotangentComplexMap (towerSquare.{u, u, u} g h) ≫
        ((squareRestrict.{u, u, u} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (naiveComparison.{u, u, u} J (g ≫ h))) (-1) ≫
        (ShortComplex.homologyMapIsoOfLeftHomologyData (squareRestrict.{u, u, u} J h)
          ((naiveCotangentComplex.{u, u, u} J (g ≫ h)).sc (-1)).leftHomologyData).hom).val.app U
      (conormalClass.{u, u, max u u u, u} J A' A' A (𝟙 A') g U x) with hY
  rw [baseExtEquiv_Q_map_towerNaiveMap_comp, DerivedCategory.negOneHomologyMap_Q_map_comp]
  refine Eq.trans (?_ : _ = (DerivedCategory.negOneHomologyMap _ G ζ).val.app U
    ((HomologicalComplex.homologyMap (naiveCotangentComplexIsoCanonical.{u, u, u} J (g ≫ h)).hom
      (-1)).val.app U Y))
    (negOneHomologyMap_app_eq_of_homologyToX.{t, u, u, u} J A' O (g ≫ h) E α G ζ δ hζ U
      ⟨x, mem_kernelIdeal_comp g h U x⟩ _ ?_)
  · rfl
  have hdC := naiveCotangentComplex_d_prev_negOne.{u, u, max u u u, u} J A' O (g ≫ h)
  have hP := HomologicalComplex.homologyMap_homologyToX_assoc (-1)
    (naiveCotangentComplexIsoCanonical.{u, u, u} J (g ≫ h)).hom hdP hdC
    (eqToHom (naiveCotangentComplex_X_negOne_eq_canonicalConormalSheaf.{u, u, max u u u, u} J A' O
      (g ≫ h)))
  have hI := naiveCotangentComplexIsoCanonical_hom_f_negOne.{u, u, u} (J' := J) (g ≫ h)
  have hA : ((naiveCotangentComplex.{u, u, u} J (g ≫ h)).homologyToX (-1) hdP ≫
      (naiveCotangentComplexXNegOneIso.{u, u, u} J (g ≫ h)).hom).val.app U Y =
      (towerZeroConormal.{u, u, u} g h).val.app U
        ((Stacks.Sites.Conormal.conormalSheafMapOfFac.{u, u, max u u u, u} J A A'
          (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) g (resolutionAugmentation J g (op ⦋0⦌))
          (resolutionBase.{u, u, u} J g (op ⦋0⦌))
          (resolutionBase_comp_resolutionAugmentation g)).val.app U
            (conormalClass.{u, u, max u u u, u} J A' A' A (𝟙 A') g U x)) :=
    (congrArg (fun m => m.val.app U (conormalClass.{u, u, max u u u, u} J A' A' A (𝟙 A') g U x))
      M1).trans (congrArg (fun t => (towerZeroConormal.{u, u, u} g h).val.app U
        ((Stacks.Sites.Conormal.conormalSheafMapOfFac.{u, u, max u u u, u} J A A'
          (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) g (resolutionAugmentation J g (op ⦋0⦌))
          (resolutionBase.{u, u, u} J g (op ⦋0⦌))
          (resolutionBase_comp_resolutionAugmentation g)).val.app U t))
      (congrArg (fun m => m.val.app U (conormalClass.{u, u, max u u u, u} J A' A' A (𝟙 A') g U x))
        (cotangentComplexHomologyNegOneIsoConormal.{u, u, u} J g).inv_hom_id))
  refine (congrArg (fun m => m.val.app U Y) (hP.trans (congrArg _ hI))).trans ?_
  show (naiveConormalIso J (g ≫ h)).hom.val.app U
    (((naiveCotangentComplex.{u, u, u} J (g ≫ h)).homologyToX (-1) hdP ≫
      (naiveCotangentComplexXNegOneIso.{u, u, u} J (g ≫ h)).hom).val.app U Y) = _
  rw [hA]
  have e : resolutionBase.{u, u, u} J g (op ⦋0⦌) ≫ (towerSquare.{u, u, u} g h).resolution (op ⦋0⦌) ≫
      (resolutionZeroIsoFreeAlgebra J (g ≫ h)).hom =
      freeAlgebraSheafCoefficientMap J A' (underlyingPresheaf J O) := by
    rw [← Category.assoc, (towerSquare.{u, u, u} g h).resolution_base, Category.id_comp,
      resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom]
  refine (congrArg (fun t => (naiveConormalIso J (g ≫ h)).hom.val.app U
    ((towerZeroConormal.{u, u, u} g h).val.app U t))
    (Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass.{u, u, max u u u, u} J A' A A'
      (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) (𝟙 A') (resolutionBase.{u, u, u} J g (op ⦋0⦌))
      g (resolutionAugmentation J g (op ⦋0⦌)) (resolutionBase.{u, u, u} J g (op ⦋0⦌))
      (resolutionBase_comp_resolutionAugmentation g) U x)).trans ?_
  refine (congrArg (fun t => (naiveConormalIso J (g ≫ h)).hom.val.app U t)
    (Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{u, u, max u u u, u} J A' A'
      (resolutionTerm.{u, u, u} J g (op ⦋0⦌)) (resolutionTerm.{u, u, u} J (g ≫ h) (op ⦋0⦌)) A O
      (resolutionBase.{u, u, u} J g (op ⦋0⦌)) (resolutionBase.{u, u, u} J (g ≫ h) (op ⦋0⦌))
      (resolutionAugmentation J g (op ⦋0⦌)) (resolutionAugmentation J (g ≫ h) (op ⦋0⦌))
      ((towerSquare.{u, u, u} g h).resolution (op ⦋0⦌)) h
      ((towerSquare.{u, u, u} g h).resolution_augmentation (op ⦋0⦌)) U _)).trans ?_
  have L := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass.{u, u, max u u u, u} J A' O
      (resolutionTerm.{u, u, u} J (g ≫ h) (op ⦋0⦌)) (freeAlgebraSheaf J A' (underlyingPresheaf J O))
      (resolutionBase.{u, u, u} J (g ≫ h) (op ⦋0⦌))
      (freeAlgebraSheafCoefficientMap J A' (underlyingPresheaf J O))
      (resolutionAugmentation J (g ≫ h) (op ⦋0⦌)) (canonicalPresentation J A' O (g ≫ h))
      (resolutionZeroIsoFreeAlgebra J (g ≫ h)).hom
      (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J (g ≫ h)) U
      ⟨_, kernelIdeal_le_comap_square _ _ _ _
        (Stacks.Sites.Conormal.hom_of_square
          ((towerSquare.{u, u, u} g h).resolution_augmentation (op ⦋0⦌))) U
        (show ((resolutionBase.{u, u, u} J g (op ⦋0⦌)).hom.app U x : _) ∈ _ from
          kernelIdeal_le_comap _ _ _ (Stacks.Sites.Conormal.hom_of_comp_eq
            (resolutionBase_comp_resolutionAugmentation g)) U x.2)⟩
  refine Eq.trans ?_ (Eq.trans L ?_)
  · rfl
  · congr 1
    exact Subtype.ext (congrArg (fun m => m.hom.app U (x : A'.obj.obj U)) e)

omit [J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [Presheaf.IsLocallySurjective J g.hom]
  [HasDerivedCategory.{t} (targetModules.{u, u, u} J O)]
  [Presheaf.IsLocallySurjective J (presentation J A' O (g ≫ h) E α).hom] in
/-- A section of the kernel of `g` lies in the kernel of any `φ = g ≫ h`. -/
theorem mem_kernelIdeal_of_eq {φ : A' ⟶ O} (hφ : φ = g ≫ h) (U : Cᵒᵖ)
    (x : kernelIdeal g.hom U) : (x : A'.obj.obj U) ∈ kernelIdeal φ.hom U := by
  subst hφ
  exact mem_kernelIdeal_comp g h U x

omit [Presheaf.IsLocallySurjective J (presentation J A' O (g ≫ h) E α).hom] in
/-- **The restriction to the base ideal of a first Ext class of `NL_{O/A'}`, read through the
canonical map `L ⟶ NL`.** `baseExtEquiv_towerClass_conormalClass` for a structure map
`φ : A' ⟶ O` equal to `g ≫ h`, with the first morphism of the fundamental triangle followed by
the canonical map `L_{O/A'} ⟶ NL_{O/A'}` of Tag 08US. -/
theorem baseExtEquiv_canonicalClass_conormalClass (φ : A' ⟶ O) (hφ : φ = g ≫ h)
    [hE : Presheaf.IsLocallySurjective J (presentation J A' O φ E α).hom]
    (δ : (presentationConormalSequence.{u, u, max u u u, u} J A' O φ E α).X₁ ⟶ G)
    (ζ : DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, max u u u, u} J A' O φ) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧)
    (hζ : DerivedCategory.Q.map
        (naiveCotangentComplexComparison.{u, u, max u u u, u} J A' O φ E α) ≫ ζ =
      presentationConormalExtClass.{u, u, u, t} J A' O φ E α G δ)
    (U : Cᵒᵖ) (x : kernelIdeal g.hom U) :
    (baseExtEquiv.{u, u, u} J g h G
        (DerivedCategory.Q.map (towerExtendScalarsCotangentComplexIso.{u, u, u} J g h).hom ≫
          DerivedCategory.Q.map (towerCotangentBaseChange.{u, u, u} J g h) ≫
            DerivedCategory.Q.map (eqToHom (congrArg (cotangentComplex.{u, u, u} J) hφ.symm)) ≫
              DerivedCategory.Q.map (canonicalNaiveComparison.{u, u, u} J φ) ≫ ζ)).val.app U
        (conormalClass.{u, u, max u u u, u} J A' A' A (𝟙 A') g U x) =
      (DerivedCategory.negOneHomologySingleIso G
          (((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0
            (by decide)).inv.app G)).hom.val.app U
        (δ.val.app U (conormalClass.{u, u, max u u u, u} J A' (freeAlgebraSheaf J A' E) O
          (freeAlgebraSheafCoefficientMap J A' E) (presentation J A' O φ E α) U
          ⟨_, coeff_mem_kernelIdeal_presentation J A' O φ E α U
            ⟨x, mem_kernelIdeal_of_eq g h hφ U x⟩⟩)) := by
  subst hφ
  have e : DerivedCategory.Q.map (towerExtendScalarsCotangentComplexIso.{u, u, u} J g h).hom ≫
      DerivedCategory.Q.map (towerCotangentBaseChange.{u, u, u} J g h) ≫
        DerivedCategory.Q.map (eqToHom (congrArg (cotangentComplex.{u, u, u} J) rfl)) ≫
          DerivedCategory.Q.map (canonicalNaiveComparison.{u, u, u} J (g ≫ h)) ≫ ζ =
      DerivedCategory.Q.map (towerNaiveMap.{u, u, u} J g h) ≫
        DerivedCategory.Q.map (naiveCotangentComplexIsoCanonical.{u, u, u} J (g ≫ h)).hom ≫ ζ := by
    rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, canonicalNaiveComparison,
      towerNaiveMap, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, Category.assoc]
  rw [e]
  exact baseExtEquiv_towerClass_conormalClass g h G E α δ ζ hζ U x

end Deformation.ToposThickening.CotangentObstruction

end
