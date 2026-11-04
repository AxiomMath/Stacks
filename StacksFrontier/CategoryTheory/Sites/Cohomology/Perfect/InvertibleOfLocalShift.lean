module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsTFAE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.InvertibleDerivedSheafHomCounitOnASite
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport

/-!
# Derived internal Hom between two objects which are locally shifts of each other

Let `(C, O)` be a locally ringed site and `K`, `K'` objects of `D(O)` such that
`RSheafHom(K, K) ≅ O` and such that every object of `C` has a covering on whose members `K'` is a
shift of `K`. Then `RSheafHom(K', K)` is an invertible object of `D(O)`: on such a member `V`,
`RSheafHom(K', K)|_V ≅ RSheafHom(K|_V[n], K|_V) ≅ RSheafHom(K, K)|_V[-n] ≅ O_V[-n]`, so clause (3)
of Stacks 0FPY holds, and clause (3) implies clause (1) on a locally ringed site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

variable (X : RingedSite.{u, u, u}) [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The restriction functor `D(O) ⥤ D(O|_V)`, at the standard models. -/
abbrev restrictDer (V : X.C) :
    @DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) _ _
        (HasDerivedCategory.standard _) ⥤
      @DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
        _ _ (HasDerivedCategory.standard _) :=
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
  (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The structure sheaf of a slice site is an invertible module over it. -/
theorem isInvertibleModuleOver_unit (V : X.C) :
    IsInvertibleModuleOver X V (SheafOfModules.unit _) :=
  (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr
    ⟨SheafOfModules.unit _, ⟨Stacks.TensorCoherence.tensorSheafUnitIso (O := X.O.over V) _⟩⟩

/-- **`RSheafHom(K', K)` is invertible when `K'` is locally a shift of `K` and
`RSheafHom(K, K) ≅ O`**, on a locally ringed site: clause (3) of Stacks 0FPY holds on the
covering on whose members `K'` is a shift of `K`, by Stacks 08JB. -/
theorem isInvertibleObject_derivedSheafHom_of_locallyShift (hX : IsLocallyRinged X)
    (K K' : @DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) _ _
      (HasDerivedCategory.standard _))
    (hKK : Nonempty (((@derivedSheafHomBifunctor X (HasDerivedCategory.standard _)).obj
        (op K)).obj K ≅
      (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit _)))
    (hloc : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f → ∃ n : ℤ,
        Nonempty ((restrictDer X V).obj K' ≅ ((restrictDer X V).obj K)⟦n⟧)) :
    @IsInvertibleObject X _ _ (HasDerivedCategory.standard _)
      (((@derivedSheafHomBifunctor X (HasDerivedCategory.standard _)).obj (op K')).obj K) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  have h := (isInvertibleObject_tfae (X := X)
    (((derivedSheafHomBifunctor X).obj (op K')).obj K)).2.2 hX
  refine (h.out 1 3).mpr ?_
  intro U
  obtain ⟨S, hS, hSf⟩ := hloc U
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hSf f hf
  obtain ⟨eKK⟩ := hKK
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O))
  refine ⟨n, SheafOfModules.unit _, isInvertibleModuleOver_unit X V, ⟨?_⟩⟩
  exact (derivedHomRestriction X V).iso K' K ≪≫
    ((derivedSheafHomBifunctor (X.over V)).mapIso e.symm.op).app _ ≪≫
    derivedSheafHomSourceShiftIso (X.over V) _ _ n ≪≫
    (shiftFunctor _ (-n)).mapIso ((derivedHomRestriction X V).iso K K).symm ≪≫
    (shiftFunctor _ (-n)).mapIso ((restrictDer X V).mapIso eKK) ≪≫
    (shiftFunctor _ (-n)).mapIso
      (((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategorySingleFunctor 0).app _) ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app _

section Formal

open MonoidalCategory

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

omit [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Derived internal Hom out of an invertible object is tensoring with its inverse**: if `N` is
invertible in `D(O)` and `K' ≅ RSheafHom(N, K)`, then `K' ≅ K ⊗^L L` for an invertible `L`, the
inverse of `N`. The evaluation `RSheafHom(N, K) ⊗^L N ⟶ K` is an isomorphism out of the invertible
`N`, and tensoring it with the inverse of `N` gives the claim. -/
theorem exists_isInvertibleObject_tensor_iso_of_iso_derivedSheafHom
    (K K' N : @DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) _ _
      (HasDerivedCategory.standard _))
    (hN : @IsInvertibleObject X _ _ (HasDerivedCategory.standard _) N)
    (e : K' ≅ ((@derivedSheafHomBifunctor X (HasDerivedCategory.standard _)).obj (op N)).obj K) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    ∃ L, IsInvertibleObject X L ∧ Nonempty (K' ≅ K ⊗ L) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let DM := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  let DT := derivedTensorMonoidal X
  let T := Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
  let μ : ∀ A B, @tensorObj _ _ DM.toMonoidalCategoryStruct A B ≅
      @tensorObj _ _ DT.toMonoidalCategoryStruct A B := fun A B =>
    ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O T).app A).app B
  let ε : @tensorUnit _ _ DM.toMonoidalCategoryStruct ≅
      @tensorUnit _ _ DT.toMonoidalCategoryStruct :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O
  have hNT : @IsInvertible _ _ DT N :=
    @isInvertible_of_tensorComparison_of_braided _ _ DM _ _ DT
      (derivedTensorSymmetric X).toBraidedCategory
      (𝟭 _) μ ε _ hN
  obtain ⟨H⟩ := hNT
  have hc : IsIso (derivedSheafHomCounit X N K) :=
    isIso_derivedSheafHomCounit_of_isInvertible X N K ⟨H⟩
  have hM : @IsInvertible _ _ DT H.inv := ⟨⟨N, H.isoRight, H.isoLeft⟩⟩
  have hMM : IsInvertibleObject X H.inv :=
    @isInvertible_of_tensorComparison_of_braided _ _ DT _ _ DM
      (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric X.O).toBraidedCategory
      (𝟭 _) (fun A B => (μ A B).symm) ε.symm _ hM
  refine ⟨H.inv, hMM, ⟨?_⟩⟩
  let := DT
  exact e ≪≫ (ρ_ _).symm ≪≫ whiskerLeftIso _ H.isoLeft.symm ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso (asIso (derivedSheafHomCounit X N K)) H.inv ≪≫ (μ K H.inv).symm

end Formal

end AlgebraicGeometry.RingedSite.InvertibleDerived
