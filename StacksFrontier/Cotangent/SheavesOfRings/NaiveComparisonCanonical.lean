module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationIso
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCokernel
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposNaiveComparison

/-!
# The comparison with the naive cotangent complex, into the canonical `NL_{B/A}`

Let `f : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site.  The degree-zero term
`P₀` of the standard resolution of `B` over `A` and the sheaf
`Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A B` are both the free `A`-algebra `A[B]` on the
sheaf of sets underlying `B`, and their augmentations to `B` both send the variable `[b]` to `b`.
This file constructs the isomorphism of `A`-algebras over `B` between them, the induced
isomorphism between the naive cotangent complex `CategoryTheory.Sheaf.naiveCotangentComplex` of
the presentation `P₀ ⟶ B` and the naive cotangent complex `NL_{B/A}` of Tag 08TW,
`Stacks.SheafOfModules.naiveCotangentComplex`, and transports the comparison
`L_{B/A} ⟶ NL_{B/A}` of Tag 08US to the latter.

## Main definitions

* `CategoryTheory.Sheaf.resolutionZeroIsoFreeAlgebra`: the isomorphism `P₀ ≅ A[B]` of sheaves of
  `A`-algebras over `B`.
* `HomologicalComplex.doubleMap`: the morphism of two-term complexes induced by a commuting
  square.
* `CategoryTheory.Sheaf.naiveCotangentComplexIsoCanonical`: the induced isomorphism of naive
  cotangent complexes.
* `CategoryTheory.Sheaf.canonicalNaiveComparison`: the canonical map `L_{B/A} ⟶ NL_{B/A}` into the
  naive cotangent complex of Tag 08TW, and
  `AlgebraicGeometry.RingedToposHom.canonicalNaiveComparison` the same for a morphism of ringed
  topoi.

## Main results

* `CategoryTheory.Sheaf.canonicalNaiveComparison_isIso_homologyMap` (**Tag 08US**) and
  `AlgebraicGeometry.RingedToposHom.canonicalNaiveComparison_isIso_homologyMap` (**Tag 08V2**):
  the canonical map is an isomorphism on `Hⁱ` for every `i ≥ -1`, the naive cotangent complex
  having no cohomology outside degrees `-1` and `0`; that is, it identifies `NL` with
  `τ_{≥ -1} L`.

## References

* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
* [Stacks Project, Tag 08V2](https://stacks.math.columbia.edu/tag/08V2)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w v' u' w'

/-! ### Morphisms of complexes concentrated in two degrees -/

namespace HomologicalComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁)

/-- The morphism `double f ⟶ double g` induced by a commuting square `f ≫ b = a ≫ g`. -/
noncomputable def doubleMap {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (a : X₀ ⟶ Y₀)
    (b : X₁ ⟶ Y₁) (comm : f ≫ b = a ≫ g) : double f hi₀₁ ⟶ double g hi₀₁ :=
  mkHomFromDouble hi₀₁ h (a ≫ (doubleXIso₀ g hi₀₁).inv) (b ≫ (doubleXIso₁ g hi₀₁ h).inv)
    (by rw [double_d g hi₀₁ h]; simp [reassoc_of% comm])
    (fun k _ => by rw [double_d_eq_zero₀ _ _ _ _ h.symm, comp_zero])

/-- In the first degree `doubleMap` is the given map. -/
@[simp]
lemma doubleMap_f₀ {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (a : X₀ ⟶ Y₀)
    (b : X₁ ⟶ Y₁) (comm : f ≫ b = a ≫ g) :
    (doubleMap hi₀₁ h f g a b comm).f i₀ =
      (doubleXIso₀ f hi₀₁).hom ≫ a ≫ (doubleXIso₀ g hi₀₁).inv :=
  mkHomFromDouble_f₀ _ _ _ _ _ _

/-- In the second degree `doubleMap` is the given map. -/
@[simp]
lemma doubleMap_f₁ {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (a : X₀ ⟶ Y₀)
    (b : X₁ ⟶ Y₁) (comm : f ≫ b = a ≫ g) :
    (doubleMap hi₀₁ h f g a b comm).f i₁ =
      (doubleXIso₁ f hi₀₁ h).hom ≫ b ≫ (doubleXIso₁ g hi₀₁ h).inv :=
  mkHomFromDouble_f₁ _ _ _ _ _ _

/-- The isomorphism `double f ≅ double g` induced by isomorphisms of the two terms commuting with
`f` and `g`. -/
@[simps]
noncomputable def doubleIsoOfIso {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (a : X₀ ≅ Y₀)
    (b : X₁ ≅ Y₁) (comm : f ≫ b.hom = a.hom ≫ g) : double f hi₀₁ ≅ double g hi₀₁ where
  hom := doubleMap hi₀₁ h f g a.hom b.hom comm
  inv := doubleMap hi₀₁ h g f a.inv b.inv (by
    rw [← cancel_epi a.hom, ← Category.assoc, ← comm]
    simp)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

end HomologicalComplex

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-! ### The two free algebras on `B` -/

/-- The free algebra `A[B]` of `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf`, as an `A`-algebra. -/
noncomputable abbrev freeAlgebraUnder : Under A :=
  Under.mk (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))

/-- The canonical presentation `A[B] ⟶ B` of Tag 08TU, as a morphism of `A`-algebras. -/
noncomputable abbrev canonicalPresentationUnder : freeAlgebraUnder J (B := B) ⟶ Under.mk f :=
  Under.homMk (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap J A B f)

/-- The free algebra of the standard resolution on the sheaf of sets underlying `B`. -/
noncomputable abbrev freeOnTarget : Under A :=
  (freeAlgebraSheaf J A).obj ((forgetAlgebraSheaf J A).obj (Under.mk f))

/-- The morphism of `A`-algebras from the free algebra of the standard resolution to
`A[B]`, sending the variable `[b]` to the variable `[b]`. -/
noncomputable def toFreeAlgebraUnder : freeOnTarget J f ⟶ freeAlgebraUnder J (B := B) :=
  ((freeAlgebraSheafAdjunction J A).homEquiv _ _).symm
    (ObjectProperty.homMk (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)))

/-- The morphism of sheaves of rings from `A[B]` to the free algebra of the standard resolution,
sending the variable `[b]` to the variable `[b]`. -/
noncomputable abbrev ofFreeAlgebra :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) ⟶ (freeOnTarget J f).right :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc J A _
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (freeOnTarget J f).hom
    ((freeAlgebraSheafAdjunction J A).unit.app ((forgetAlgebraSheaf J A).obj (Under.mk f))).hom

/-- The morphism of `A`-algebras from `A[B]` to the free algebra of the standard resolution,
sending the variable `[b]` to the variable `[b]`. -/
noncomputable def ofFreeAlgebraUnder : freeAlgebraUnder J (B := B) ⟶ freeOnTarget J f :=
  Under.homMk (ofFreeAlgebra J f)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc J A _ _ _ _)

/-- `A[B] ⟶ P₀ ⟶ A[B]` is the identity. -/
theorem ofFreeAlgebraUnder_toFreeAlgebraUnder :
    ofFreeAlgebraUnder J f ≫ toFreeAlgebraUnder J f = 𝟙 _ := by
  apply Under.UnderMorphism.ext
  rw [Under.comp_right, Under.id_right]
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A _ _ ?_ ?_
  · exact (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ (toFreeAlgebraUnder J f).right)
      (Under.w (ofFreeAlgebraUnder J f))).trans (Under.w (toFreeAlgebraUnder J f))).trans
        (Category.comp_id _).symm)
  · have hu := (freeAlgebraSheafAdjunction J A).homEquiv_unit _ _ (toFreeAlgebraUnder J f)
    rw [toFreeAlgebraUnder, Equiv.apply_symm_apply] at hu
    have hv := Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc J A _
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (freeOnTarget J f).hom
      ((freeAlgebraSheafAdjunction J A).unit.app ((forgetAlgebraSheaf J A).obj (Under.mk f))).hom
    refine Eq.trans ?_ (Eq.trans (Category.comp_id _) (congrArg (_ ≫ ·)
      ((congrArg (Functor.whiskerRight · (forget CommRingCat))
        ((sheafToPresheaf J CommRingCat).map_id _)).trans (Functor.whiskerRight_id' _)).symm))
    rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc]
    change (_ ≫ Functor.whiskerRight ((sheafToPresheaf J CommRingCat).map
      (ofFreeAlgebra J f)) _) ≫ _ = _
    rw [hv]
    exact (congrArg (fun t => t.hom) hu).symm

/-- `P₀ ⟶ A[B] ⟶ P₀` is the identity. -/
theorem toFreeAlgebraUnder_ofFreeAlgebraUnder :
    toFreeAlgebraUnder J f ≫ ofFreeAlgebraUnder J f = 𝟙 _ := by
  apply ((freeAlgebraSheafAdjunction J A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, toFreeAlgebraUnder, Equiv.apply_symm_apply,
    Adjunction.homEquiv_id]
  apply Sheaf.hom_ext
  exact Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc J A _ _ _ _

/-- The comparison `P₀ ⟶ A[B]` is compatible with the two augmentations to `B`. -/
theorem toFreeAlgebraUnder_comp_canonicalPresentationUnder :
    toFreeAlgebraUnder J f ≫ canonicalPresentationUnder J f =
      (freeAlgebraSheafAdjunction J A).counit.app (Under.mk f) := by
  apply ((freeAlgebraSheafAdjunction J A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, toFreeAlgebraUnder, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
  apply Sheaf.hom_ext
  change Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat).map
          (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f)) (forget CommRingCat) = 𝟙 _
  exact Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc J A B _ f (𝟙 _)

/-- The isomorphism `P₀ ≅ A[B]` of `A`-algebras between the degree-zero term of the standard
resolution and the free algebra of `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf`. -/
noncomputable def resolutionZeroIsoFreeAlgebraUnder :
    (standardResolution J f).left.obj (op ⦋0⦌) ≅ freeAlgebraUnder J (B := B) :=
  eqToIso (resObjEq J f 0) ≪≫
    { hom := toFreeAlgebraUnder J f
      inv := ofFreeAlgebraUnder J f
      hom_inv_id := toFreeAlgebraUnder_ofFreeAlgebraUnder J f
      inv_hom_id := ofFreeAlgebraUnder_toFreeAlgebraUnder J f }

/-- The isomorphism `P₀ ≅ A[B]` of sheaves of commutative rings. -/
noncomputable def resolutionZeroIsoFreeAlgebra :
    resolutionTerm J f (op ⦋0⦌) ≅
      Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) :=
  (Under.forget A).mapIso (resolutionZeroIsoFreeAlgebraUnder J f)

/-- The isomorphism `P₀ ≅ A[B]` is a morphism of `A`-algebras. -/
theorem resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom :
    resolutionBase J f (op ⦋0⦌) ≫ (resolutionZeroIsoFreeAlgebra J f).hom =
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) :=
  Under.w (resolutionZeroIsoFreeAlgebraUnder J f).hom

/-- The inverse isomorphism `A[B] ≅ P₀` is a morphism of `A`-algebras. -/
theorem coefficientMap_comp_resolutionZeroIsoFreeAlgebra_inv :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) ≫
      (resolutionZeroIsoFreeAlgebra J f).inv = resolutionBase J f (op ⦋0⦌) :=
  Under.w (resolutionZeroIsoFreeAlgebraUnder J f).inv

/-- The isomorphism `P₀ ≅ A[B]` is compatible with the two augmentations to `B`. -/
theorem resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation :
    (resolutionZeroIsoFreeAlgebra J f).hom ≫
        Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f =
      resolutionAugmentation J f (op ⦋0⦌) := by
  rw [resolutionAugmentation, augmentation_eq J f]
  exact congrArg (fun t => t.right) (congrArg (eqToHom (resObjEq J f 0) ≫ ·)
    (toFreeAlgebraUnder_comp_canonicalPresentationUnder J f))

/-- The inverse isomorphism `A[B] ≅ P₀` is compatible with the two augmentations to `B`. -/
theorem resolutionZeroIsoFreeAlgebra_inv_comp_augmentation :
    (resolutionZeroIsoFreeAlgebra J f).inv ≫ resolutionAugmentation J f (op ⦋0⦌) =
      Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f := by
  rw [← resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation, Iso.inv_hom_id_assoc]

/-! ### The naive cotangent complexes of the two presentations -/


/-- The isomorphism of conormal sheaves `I/I² ≅ I'/I'²` induced by `P₀ ≅ A[B]`, between the
conormal sheaves of the two presentations. -/
noncomputable def naiveConormalIsoAux :=
  Stacks.Sites.Conormal.conormalSheafIsoOfFac.{v, u, max u v w, u} J B _ _
    (resolutionAugmentation J f (op ⦋0⦌)) (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f)
    (resolutionZeroIsoFreeAlgebra J f)
    (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J f)

/-- The isomorphism of conormal sheaves `I/I² ≅ I'/I'²` induced by `P₀ ≅ A[B]`. -/
noncomputable def naiveConormalIso :
    (naiveSequence J f).X₁ ≅
      (Stacks.SheafOfModules.canonicalConormalSequence.{v, u, max u v w, u} J A B f).X₁ :=
  naiveConormalIsoAux J f

/-- The isomorphism `B ⊗_{P₀} Ω_{P₀/A} ≅ B ⊗_{A[B]} Ω_{A[B]/A}` induced by `P₀ ≅ A[B]`, between
the tensor-differentials sheaves of the two presentations. -/
noncomputable def naiveTensorIsoAux :=
  Stacks.Sites.Conormal.tensorSheafIsoOfFac.{v, u, max u v w, u} J A B _ _
    (resolutionBase J f (op ⦋0⦌))
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
    (resolutionAugmentation J f (op ⦋0⦌)) (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B f)
    (resolutionZeroIsoFreeAlgebra J f)
    (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J f)
    (resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom J f)

/-- The isomorphism `B ⊗_{P₀} Ω_{P₀/A} ≅ B ⊗_{A[B]} Ω_{A[B]/A}` induced by `P₀ ≅ A[B]`. -/
noncomputable def naiveTensorIso :
    (naiveSequence J f).X₂ ≅
      (Stacks.SheafOfModules.canonicalConormalSequence.{v, u, max u v w, u} J A B f).X₂ :=
  naiveTensorIsoAux J f

/-- The two isomorphisms commute with the conormal maps. -/
theorem naiveSequence_f_comp_naiveTensorIso_hom :
    (naiveSequence J f).f ≫ (naiveTensorIso J f).hom =
      (naiveConormalIso J f).hom ≫
        (Stacks.SheafOfModules.canonicalConormalSequence.{v, u, max u v w, u} J A B f).f :=
  (Stacks.Sites.Conormal.conormalSheafIsoOfFac_hom_comp_conormalSequence_f.{v, u, max u v w, u}
    J A B _ _ _ _ _ _ (resolutionZeroIsoFreeAlgebra J f)
    (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J f)
    (resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom J f)).symm

/-- The naive cotangent complex of the presentation `P₀ ⟶ B` is the naive cotangent complex
`NL_{B/A}` of Tag 08TW, through the isomorphism `P₀ ≅ A[B]` of `A`-algebras over `B`. -/
@[stacks 08US "the naive cotangent complex of the presentation P₀ = A[B] is the naive cotangent \
  complex NL_{B/A} of Tag 08TW"]
noncomputable def naiveCotangentComplexIsoCanonical :
    naiveCotangentComplex.{u, v, w} J f ≅
      Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} J A B f :=
  HomologicalComplex.doubleIsoOfIso (C := targetModules J B) ComplexShape.upIntRelNegOneZero
    (by decide) _ _ (naiveConormalIso J f) (naiveTensorIso J f)
    (naiveSequence_f_comp_naiveTensorIso_hom J f)

/-! ### The comparison on cohomology in degrees `-1` and `0` -/

/-- The differential of the naive cotangent complex into degree `-1` vanishes. -/
private theorem naiveCotangentComplex_d_negTwo_negOne :
    (naiveCotangentComplex.{u, v, w} J f).d (-2) (-1) = 0 :=
  (naiveCotangentComplex_isZero_X.{u, v, w} J f (-2) (by decide) (by decide)).eq_of_src _ _

/-- The differential of the cotangent complex into degree `-1` is killed by the comparison. -/
theorem cotangentComplex_d_comp_naiveComparison_f_negOne :
    (cotangentComplex.{u, v, w} J f).d (-2) (-1) ≫ (naiveComparison.{u, v, w} J f).f (-1) = 0 := by
  rw [← (naiveComparison.{u, v, w} J f).comm, naiveCotangentComplex_d_negTwo_negOne, comp_zero]

/-- In degree `-1` the comparison `Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²` is a cokernel of the differential of
the cotangent complex into degree `-1`. -/
noncomputable def isColimitNaiveComparisonFNegOne :
    IsColimit (CokernelCofork.ofπ ((naiveComparison.{u, v, w} J f).f (-1))
      (cotangentComplex_d_comp_naiveComparison_f_negOne.{u, v, w} J f)) := by
  have hd : (cotangentComplex.{u, v, w} J f).d (-2) (-1) =
      (cotangentComplex_degreeIso.{u, v, w} J f 2).hom ≫
        ((cotangentSimplicialModule.{u, v, w} J f).object.δ (0 : Fin 3) -
          (cotangentSimplicialModule.{u, v, w} J f).object.δ (1 : Fin 3) +
          (cotangentSimplicialModule.{u, v, w} J f).object.δ (2 : Fin 3)) ≫
        (cotangentComplex_degreeIso.{u, v, w} J f 1).inv := by
    rw [cotangentComplex_d_negTwo_negOne, objD_one]
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun g hg => (naiveCotangentComplexXNegOneIso.{u, v, w} J f).hom ≫
      naiveComparisonNegOneDesc.{u, v, w} J f
        ((cotangentComplex_degreeIso.{u, v, w} J f 1).inv ≫ g) (by
          rw [hd, Category.assoc, Category.assoc] at hg
          exact (cancel_epi (cotangentComplex_degreeIso.{u, v, w} J f 2).hom).1
            (hg.trans (comp_zero).symm)))
    (fun g hg => by
      rw [naiveComparison_f_negOne]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, naiveComparisonNegOne_comp_desc,
        Iso.hom_inv_id_assoc])
    (fun g hg m hm => by
      rw [← Iso.inv_comp_eq]
      refine naiveComparisonNegOne_cancel.{u, v, w} J f ?_
      rw [naiveComparisonNegOne_comp_desc, ← hm, naiveComparison_f_negOne]
      simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- In degree `-1` the comparison is an epimorphism. -/
instance epi_naiveComparison_f_negOne : Epi ((naiveComparison.{u, v, w} J f).f (-1)) := by
  rw [naiveComparison_f_negOne]
  infer_instance

/-- In degree `0` the comparison is an isomorphism. -/
instance isIso_naiveComparison_f_zero : IsIso ((naiveComparison.{u, v, w} J f).f 0) := by
  rw [naiveComparison_f_zero]
  infer_instance

/-- The canonical map `L_{B/A} ⟶ NL_{B/A}` is an isomorphism on the cohomology sheaf of degree
`0`. -/
theorem naiveComparison_isIso_homologyMap_zero :
    IsIso (HomologicalComplex.homologyMap (naiveComparison.{u, v, w} J f) 0) := by
  have h₁ : Epi ((naiveComparison.{u, v, w} J f).f ((ComplexShape.up ℤ).prev 0)) := by
    rw [show (ComplexShape.up ℤ).prev 0 = -1 by simp]
    infer_instance
  have h₃ : Mono ((naiveComparison.{u, v, w} J f).f ((ComplexShape.up ℤ).next 0)) := by
    rw [show (ComplexShape.up ℤ).next 0 = 1 by simp]
    exact ⟨fun g h _ => (cotangentComplex_isZero_pos.{u, v, w} J f 1 one_pos).eq_of_tgt g h⟩
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _ h₁
    (isIso_naiveComparison_f_zero.{u, v, w} J f) h₃

/-- The canonical map `L_{B/A} ⟶ NL_{B/A}` is an isomorphism on the cohomology sheaf of degree
`-1`. -/
theorem naiveComparison_isIso_homologyMap_negOne :
    IsIso (HomologicalComplex.homologyMap (naiveComparison.{u, v, w} J f) (-1)) := by
  have hK := (cotangentComplex.{u, v, w} J f).opcyclesIsCokernel (-2) (-1) (by simp)
  let e := hK.coconePointUniqueUpToIso (isColimitNaiveComparisonFNegOne.{u, v, w} J f)
  have he : (cotangentComplex.{u, v, w} J f).pOpcycles (-1) ≫ e.hom =
      (naiveComparison.{u, v, w} J f).f (-1) :=
    hK.comp_coconePointUniqueUpToIso_hom (isColimitNaiveComparisonFNegOne.{u, v, w} J f)
      WalkingParallelPair.one
  have hL := (naiveCotangentComplex.{u, v, w} J f).isIso_pOpcycles (-2) (-1) (by simp)
    (naiveCotangentComplex_d_negTwo_negOne.{u, v, w} J f)
  have hop : HomologicalComplex.opcyclesMap (naiveComparison.{u, v, w} J f) (-1) =
      e.hom ≫ (naiveCotangentComplex.{u, v, w} J f).pOpcycles (-1) := by
    rw [← cancel_epi ((cotangentComplex.{u, v, w} J f).pOpcycles (-1)),
      HomologicalComplex.p_opcyclesMap, reassoc_of% he]
  have h₁ : IsIso (HomologicalComplex.opcyclesMap (naiveComparison.{u, v, w} J f) (-1)) := by
    rw [hop]
    infer_instance
  have h₃ : Mono ((naiveComparison.{u, v, w} J f).f ((ComplexShape.up ℤ).next (-1))) := by
    rw [show (ComplexShape.up ℤ).next (-1) = 0 by simp]
    infer_instance
  exact ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono h₁ h₃

/-- The canonical map `L_{B/A} ⟶ NL_{B/A}` into the naive cotangent complex of the presentation
`P₀ ⟶ B` is an isomorphism on the cohomology sheaf of every degree `≥ -1`. Since that complex has
no cohomology outside degrees `-1` and `0`
(`CategoryTheory.Sheaf.naiveCotangentComplex_isZero_homology`), the map identifies it with the
truncation `τ_{≥ -1} L_{B/A}`. -/
theorem naiveComparison_isIso_homologyMap_unconditional (i : ℤ) (hi : -1 ≤ i) :
    IsIso (HomologicalComplex.homologyMap (naiveComparison.{u, v, w} J f) i) :=
  naiveComparison_isIso_homologyMap.{u, v, w} J f
    (naiveComparison_isIso_homologyMap_zero.{u, v, w} J f)
    (naiveComparison_isIso_homologyMap_negOne.{u, v, w} J f) i hi

/-! ### The canonical map into `NL_{B/A}` -/

/-- **Stacks 08US, the canonical map.** The canonical map `L_{B/A} ⟶ NL_{B/A}` from the cotangent
complex to the naive cotangent complex of Tag 08TW: `d x ⊗ b ↦ b · [d₀ x - d₁ x]` in degree `-1`
and `d p ⊗ b ↦ b ⊗ d p` in degree `0` (`CategoryTheory.Sheaf.naiveComparison`), read in
`NL_{B/A}` through the isomorphism `P₀ ≅ A[B]` of `A`-algebras over `B`. -/
@[stacks 08US "the canonical map `L_{B/A} → NL_{B/A}`, into the naive cotangent complex
`Stacks.SheafOfModules.naiveCotangentComplex` of Tag 08TW"]
noncomputable def canonicalNaiveComparison :
    cotangentComplex.{u, v, w} J f ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} J A B f :=
  naiveComparison.{u, v, w} J f ≫ (naiveCotangentComplexIsoCanonical J f).hom

/-- **Stacks 08US.** The canonical map `L_{B/A} ⟶ NL_{B/A}` into the naive cotangent complex of
Tag 08TW is an isomorphism on the cohomology sheaf of every degree `≥ -1`.  Since `NL_{B/A}` has
no terms outside degrees `-1` and `0` (`Stacks.SheafOfModules.naiveCotangentComplex_isZero_X`),
this says that the canonical map identifies the naive cotangent complex with the truncation
`τ_{≥ -1} L_{B/A}`. -/
@[stacks 08US "the canonical map identifies the naive cotangent complex `NL_{B/A}` of Tag 08TW
with the truncation `τ_{≥ -1} L_{B/A}`: it is an isomorphism on the cohomology sheaf of every
degree `≥ -1`, the naive complex having no terms outside degrees `-1` and `0`"]
theorem canonicalNaiveComparison_isIso_homologyMap (i : ℤ) (hi : -1 ≤ i) :
    IsIso (HomologicalComplex.homologyMap (canonicalNaiveComparison J f) i) := by
  have := naiveComparison_isIso_homologyMap_unconditional.{u, v, w} J f i hi
  rw [canonicalNaiveComparison, HomologicalComplex.homologyMap_comp]
  infer_instance

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, max u v w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- The naive cotangent complex `NL_f` of `AlgebraicGeometry.RingedToposHom.naiveCotangentComplex`
is the naive cotangent complex `NL_{𝒪_C/f⁻¹𝒪_D}` of Tag 08TW. -/
noncomputable def naiveCotangentComplexIsoCanonical :
    f.naiveCotangentComplex ≅
      Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} X.J _ X.O
        f.fSharpInverseImage :=
  Sheaf.naiveCotangentComplexIsoCanonical X.J f.fSharpInverseImage

/-- **Stacks 08V2, the canonical map.** The canonical map `L_f ⟶ NL_f` of a morphism of ringed
topoi `(f, f♯) : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)`, into `NL_f = NL_{𝒪_C/f⁻¹𝒪_D}` of Tag 08TW: the
special case at `f⁻¹𝒪_D ⟶ 𝒪_C` of the map of Tag 08US. -/
@[stacks 08V2 "the canonical map `L_f → NL_f` of a morphism of ringed topoi, into the naive
cotangent complex `NL_{𝒪_C/f⁻¹𝒪_D}` of Tag 08TW"]
noncomputable def canonicalNaiveComparison :
    f.cotangentComplex ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} X.J _ X.O
        f.fSharpInverseImage :=
  Sheaf.canonicalNaiveComparison X.J f.fSharpInverseImage

/-- **Stacks 08V2.** The canonical map `L_f ⟶ NL_f` is an isomorphism on the cohomology sheaf of
every degree `≥ -1`; since `NL_f` has no terms outside degrees `-1` and `0`, it identifies the
naive cotangent complex with the truncation `τ_{≥ -1} L_f`. -/
@[stacks 08V2 "the canonical map identifies the naive cotangent complex `NL_f` with the truncation
`τ_{≥ -1} L_f`: it is an isomorphism on the cohomology sheaf of every degree `≥ -1`, the naive
complex having no terms outside degrees `-1` and `0`; the special case of Tag 08US"]
theorem canonicalNaiveComparison_isIso_homologyMap (i : ℤ) (hi : -1 ≤ i) :
    IsIso (HomologicalComplex.homologyMap f.canonicalNaiveComparison i) :=
  Sheaf.canonicalNaiveComparison_isIso_homologyMap X.J f.fSharpInverseImage i hi

end AlgebraicGeometry.RingedToposHom

end
