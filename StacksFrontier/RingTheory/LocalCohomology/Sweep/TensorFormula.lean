module

public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.TensorCompatibility
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.ClosedSupportColimit
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.SupportedModulesEquivalence

/-!
# Local cohomology with general support and derived tensor products

Let `A` be a Noetherian ring of finite Krull dimension and let `T ⊆ Spec(A)` be stable under
specialization. Local cohomology with support in `T` is derived tensor product with the local
cohomology of the ring:
$$ RΓ_T(K) \;=\; RΓ_T(A) \otimes^{\mathbf L}_A K \qquad (K ∈ D(A)), $$
so for `K, L ∈ D(A)`
$$ RΓ_T(K \otimes^{\mathbf L}_A L) \;=\; RΓ_T(K) \otimes^{\mathbf L}_A L
   \;=\; K \otimes^{\mathbf L}_A RΓ_T(L)
   \;=\; RΓ_T(K) \otimes^{\mathbf L}_A RΓ_T(L), $$
and if `K` or `L` lies in `D_T(A)` then so does `K ⊗^L_A L`.

## Main results

* `Stacks.LocalCohomology.nonempty_derivedSupportedSections_comp_iso` — `RH^0_T` into
  `D(Mod_{A,T})` followed by the inclusion is the derived functor of `H^0_T` into `Mod_A`.
* `Stacks.LocalCohomology.exists_derivedSectionsWithSupportIn_isoTensorUnit` — the one-variable
  formula, with its inverse the canonical map `RΓ_T(A) ⊗^L_A K ⟶ A ⊗^L_A K ⟶ K`.
* `Stacks.LocalCohomology.exists_derivedSectionsWithSupportIn_tensorIso_left`,
  `Stacks.LocalCohomology.exists_derivedSectionsWithSupportIn_tensorIso_right` and
  `Stacks.LocalCohomology.exists_derivedSectionsWithSupportIn_tensorIso_both` — the three
  two-variable forms.
* `Stacks.LocalCohomology.derivedCategoryB_tensor_left` and
  `Stacks.LocalCohomology.derivedCategoryB_tensor_right` — the objects with cohomology supported
  in `T` are stable under tensoring with an arbitrary object.

## Implementation notes

The source states equalities of objects of `D(A)`. They are rendered here as isomorphisms of
functors *together with their normalization*: each isomorphism is required to carry the
augmentation `RΓ_T ⟶ id` of the tensor product to the augmentation of the relevant factor
tensored with the identity, which pins it down. Without that requirement the statements would
only assert that two functors are abstractly isomorphic.

Two inputs carry the argument. First, the augmentation `RΓ_T(K) ⟶ K` is invertible for
`K ∈ D_T(A)` and is universal among morphisms to `K` out of `D_T(A)`. Both come from the
adjunction between the derived inclusion of the modules supported in `T` and derived supported
sections (Tag 0EF0), built here through Maltsiniotis' theorem on derived adjunctions so that
its counit is the augmentation, together with the equivalence `D(Mod_{A,T}) ≃ D_T(A)` of Tag
0EF3 — the source of the hypothesis `ringKrullDim A < ⊤`. Second, `RΓ_T` inverts the
augmentation tensored with an identity; this is checked on each closed support `V(I) ⊆ T`,
where it is the tensor compatibility of Tag 0ALY for the right adjoint of Tag 0A6R, and then
transported to `T` by the filtered colimit of Tag 0EF1. This replaces the source's reduction to
the shifts `A[k]`.

That a tensor product with an object of `D_T(A)` again lies in `D_T(A)` is read off a
representative with `T`-supported terms, which exists by Tag 0EF3: the support of a tensor
product is contained in the support of either factor, and a complex of modules supported in `T`
has cohomology supported in `T`.

The module universe is the universe of the ring. The tensor compatibility for a closed support
and the Čech formula behind it are available for `ModuleCat.{u} A`, which is where the
symmetric monoidal structure on the derived category lives; the auxiliary results about
supports and about the augmentation are proved for an independent module universe.

## References

* [Stacks Project, Tag 0EF7](https://stacks.math.columbia.edu/tag/0EF7)
* [Stacks Project, Tag 0EF0](https://stacks.math.columbia.edu/tag/0EF0)
* [Stacks Project, Tag 0EF1](https://stacks.math.columbia.edu/tag/0EF1)
* [Stacks Project, Tag 0EF3](https://stacks.math.columbia.edu/tag/0EF3)
* [Stacks Project, Tag 0ALY](https://stacks.math.columbia.edu/tag/0ALY)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

open CochainComplex CochainComplex.DerivedTensor

/-- The support of a tensor product is contained in the support of either factor. -/
private theorem support_tensorProduct_subset_left {A : Type u} [CommRing A]
    {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    Module.support A (TensorProduct A M N) ⊆ Module.support A M := by
  intro p hp
  by_contra hM
  have hnotM : ∀ m : M, ∃ r ∉ p.asIdeal, r • m = 0 := Module.notMem_support_iff'.mp hM
  refine (Module.notMem_support_iff'.mpr ?_) hp
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, p.asIdeal.primeCompl.one_mem, by simp⟩
  | tmul m n =>
      obtain ⟨r, hr, hrm⟩ := hnotM m
      exact ⟨r, hr, by simp [TensorProduct.smul_tmul', hrm]⟩
  | add x y hx hy =>
      obtain ⟨r, hr, hrx⟩ := hx
      obtain ⟨s, hs, hsy⟩ := hy
      refine ⟨r * s, p.asIdeal.primeCompl.mul_mem hr hs, ?_⟩
      calc (r * s) • (x + y) = (r * s) • x + (r * s) • y := smul_add _ _ _
        _ = s • (r • x) + r • (s • y) := by simp [mul_smul, smul_comm r s]
        _ = 0 := by simp [hrx, hsy]

/-- A tensor product with a module supported in `T` is supported in `T`. -/
private theorem supportModuleProperty_tensorObj {A : Type u} [CommRing A]
    {T : Set (PrimeSpectrum A)} {M N : ModuleCat.{max u v} A}
    (hM : supportModuleProperty A T M) :
    supportModuleProperty A T (((moduleTensor.{u, v} A).obj M).obj N) :=
  (support_tensorProduct_subset_left (A := A) (M := M) (N := N)).trans hM

/-- A complex whose terms are supported in `T` has cohomology supported in `T`. -/
private theorem derivedCategoryB_of_supported_X {A : Type u} [CommRing A]
    {T : Set (PrimeSpectrum A)} (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hP : ∀ n, supportModuleProperty A T (P.X n)) :
    DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))
      (DerivedCategory.Q.obj P) := by
  intro n
  let B : ObjectProperty (ModuleCat.{max u v} A) := supportModuleProperty A T
  have hcyc : B (P.cycles n) := B.prop_of_mono (P.iCycles n) (hP n)
  have hhom : B (P.homology n) := B.prop_of_epi (P.homologyπ n) hcyc
  exact B.prop_of_iso ((DerivedCategory.homologyFunctorFactors _ n).app P).symm hhom

/-- The terms of a total tensor product with a complex supported in `T` are supported in `T`. -/
private theorem supportModuleProperty_tensorComplex_X {A : Type u} [CommRing A]
    {T : Set (PrimeSpectrum A)} (P J : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hP : ∀ n, supportModuleProperty A T (P.X n)) (n : ℤ) :
    supportModuleProperty A T ((tensorComplex.{u, v} P J).X n) := by
  show supportModuleProperty A T (∐ _)
  refine (supportModuleProperty A T).prop_colimit _ (fun i ↦ ?_)
  exact supportModuleProperty_tensorObj (hP _)

/-- Every object of the derived category is represented by a K-flat complex. -/
private theorem exists_kFlat_model {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      P.KFlat ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨J, f, hJ, -, hf, -⟩ := KFlat.exists_kFlat_resolution (DerivedCategory.Q.objPreimage K)
  exact ⟨J, hJ, ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- An object of `D_T(A)` is represented by a complex of modules supported in `T`. This is where
the equivalence of [Stacks, Tag 0EF3] enters, hence the finite-dimensionality hypothesis. -/
private theorem exists_supported_complex {A : Type u} [CommRing A] [IsNoetherianRing A]
    {T : Set (PrimeSpectrum A)} (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) K) :
    ∃ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∀ n, supportModuleProperty A T (P.X n)) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  let B : ObjectProperty (ModuleCat.{max u v} A) := supportModuleProperty A T
  let F := supportedModulesComparison.{u, max u v} A T
  let _ : F.IsEquivalence := supportedModulesComparison_isEquivalence.{u, max u v} A T hT hdim
  let X := F.objPreimage ⟨K, hK⟩
  let P := (DerivedCategory.Q (C := B.FullSubcategory)).objPreimage X
  refine ⟨(B.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, fun n ↦ (P.X n).property, ⟨?_⟩⟩
  exact (B.ι.mapDerivedCategoryFactors.app P).symm ≪≫
    B.ι.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso X) ≪≫
    (DerivedCategoryB.derivedCategoryB B).ι.mapIso (F.objObjPreimageIso ⟨K, hK⟩)

/-- The derived tensor product of a complex supported in `T` with an arbitrary complex is
represented by the total tensor product of a supported representative with a K-flat one. -/
private theorem exists_tensor_supported_model {A : Type u} [CommRing A]
    (D : DerivedTensorProductGeneral.{u, v} A)
    (P J : CochainComplex (ModuleCat.{max u v} A) ℤ) (hJ : J.KFlat)
    {K L : DerivedCategory (ModuleCat.{max u v} A)}
    (eP : DerivedCategory.Q.obj P ≅ K) (eJ : DerivedCategory.Q.obj J ≅ L) :
    Nonempty (((D.tensor.obj K).obj L) ≅
      DerivedCategory.Q.obj (tensorComplex.{u, v} P J)) := by
  obtain ⟨P', q, hP', -, hq, -⟩ := KFlat.exists_kFlat_resolution P
  have := hq
  let eP' : DerivedCategory.Q.obj P' ≅ K := asIso (DerivedCategory.Q.map q) ≪≫ eP
  have ht : QuasiIso (HomologicalComplex.mapBifunctorMap q (𝟙 J) (moduleTensor A)
      (ComplexShape.up ℤ)) := by
    have hle := KFlat.kFlat_tright_preserves_quasiIso J hJ
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map q)
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq)
    rw [MorphismProperty.inverseImage_iff] at hle
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 hle
  have := ht
  exact ⟨(D.tensor.mapIso eP'.symm).app L ≪≫
    (D.tensor.obj (DerivedCategory.Q.obj P')).mapIso eJ.symm ≪≫
    D.comparison P' J hP' hJ ≪≫ asIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      q (𝟙 J) (moduleTensor A) (ComplexShape.up ℤ)))⟩

/-- Tensoring an object of `D_T(A)` with an arbitrary object stays in `D_T(A)`. -/
private theorem derivedCategoryB_tensor_of_left {A : Type u} [CommRing A] [IsNoetherianRing A]
    (D : DerivedTensorProductGeneral.{u, v} A)
    {T : Set (PrimeSpectrum A)} (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤)
    (K L : DerivedCategory (ModuleCat.{max u v} A))
    (hK : DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) K) :
    DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))
      ((D.tensor.obj K).obj L) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_supported_complex.{u, v} hT hdim K hK
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := exists_kFlat_model.{u, v} L
  obtain ⟨e⟩ := exists_tensor_supported_model.{u, v} D P J hJ eP eJ
  intro n
  exact (supportModuleProperty A T).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e.symm)
    (derivedCategoryB_of_supported_X _ (supportModuleProperty_tensorComplex_X P J hP) n)

section SupportedAdjunction

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-- The degreewise adjunction between the inclusion of the modules supported in `T` and
degree-zero sections with support in `T`, read on homotopy categories. -/
private abbrev htpySupportedAdjunction :
    (supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      (supportedSectionsFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Adjunction.mapHomotopyCategoryAdjunction
    (inclusion_adj_supportedSectionsFunctor.{u, v} A T) (ComplexShape.up ℤ)

/-- The derived inclusion of the supported modules is the left derived functor of the inclusion,
the latter being exact. -/
private instance supportedInclusion_isLeftDerivedFunctor :
    ((supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory).IsLeftDerivedFunctor
      ((supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (ModulesSupportedIn.{u, max u v} A T) (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ _

/-- Postcomposing the derived inclusion with derived supported sections is again a left derived
functor. -/
private instance supportedInclusionComp_isLeftDerivedFunctor :
    ((supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ⋙
        derivedSupportedSections.{u, v} A T).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        ((supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι).mapDerivedCategoryFactorsh.hom
        (derivedSupportedSections.{u, v} A T))
      (HomotopyCategory.quasiIso (ModulesSupportedIn.{u, max u v} A T) (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
      ((supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι).mapDerivedCategoryFactorsh
      (derivedSupportedSections.{u, v} A T))

/-- The canonical comparison exhibiting the composite of derived supported sections with the
derived inclusion as a right derived functor. -/
private abbrev supportedCompUnit :
    (supportedSectionsFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ derivedSupportedSections.{u, v} A T ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory :=
  Functor.whiskerRight (derivedSupportedSectionsUnit.{u, v} A T)
      (supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- Degreewise, supported sections followed by the inclusion is sections with support in `T`. -/
private abbrev htpySupportedSectionsCompIso :
    (supportedSectionsFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso
    ((supportModuleProperty A T).liftCompιIso (sectionsWithSupportInFunctor.{u, v} A T)
      (sectionsWithSupportIn_supported.{u, v} A T)) (ComplexShape.up ℤ)

/-- On complexes, supported sections followed by the derived inclusion is the ambient
sections with support in `T`. -/
private abbrev supportedSectionsCompIso :
    ((supportedSectionsFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ≅
      (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (htpySupportedSectionsCompIso.{u, v} A T) DerivedCategory.Qh

variable [IsNoetherianRing A]

/-- The derived adjunction of [Stacks, Tag 0EF0] in the form produced by Maltsiniotis' theorem,
so that its counit is the derived counit of the degreewise adjunction. -/
private def supportedDerivedAdjunction (hT : StableUnderSpecialization T) :
    (supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ⊣
      derivedSupportedSections.{u, v} A T := by
  have hL : ((supportModuleProperty A T :
      ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory).IsLeftAdjoint :=
    (derivedInclusion_adj_derivedSupportedSections.{u, v} A T hT).some.isLeftAdjoint
  exact (htpySupportedAdjunction.{u, v} A T).derived
    (HomotopyCategory.quasiIso (ModulesSupportedIn.{u, max u v} A T) (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
    ((supportModuleProperty A T :
      ObjectProperty (ModuleCat.{max u v} A)).ι).mapDerivedCategoryFactorsh.hom
    (derivedSupportedSectionsUnit.{u, v} A T)

/-- The comparison of [Stacks, Tag 0EF0] between the composite of derived supported sections
with the derived inclusion and the ambient derived sections with support in `T`. -/
private def supportedDerivedComparison (hT : StableUnderSpecialization T) :
    derivedSupportedSections.{u, v} A T ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ≅
      derivedSectionsWithSupportIn.{u, v} A T := by
  have hL : ((supportModuleProperty A T :
      ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory).IsLeftAdjoint :=
    (derivedInclusion_adj_derivedSupportedSections.{u, v} A T hT).some.isLeftAdjoint
  exact Functor.rightDerivedNatIso _ _ (supportedCompUnit.{u, v} A T)
    (derivedSectionsWithSupportInUnit.{u, v} A T)
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
    (supportedSectionsCompIso.{u, v} A T)

/-- **The two constructions of `RΓ_T` on `D(A)` agree.** Deriving degree-zero sections with
support in `T` as a functor into `Mod_{A,T}` and then including into `D(A)` is isomorphic to
deriving it as a functor into `Mod_A`: both are right derived functors of the same functor on
complexes. -/
theorem nonempty_derivedSupportedSections_comp_iso (hT : StableUnderSpecialization T) :
    Nonempty (derivedSupportedSections.{u, v} A T ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ≅
      derivedSectionsWithSupportIn.{u, v} A T) :=
  ⟨supportedDerivedComparison.{u, v} A T hT⟩

/-- The comparison carries the augmentation `RΓ_T ⟶ id` to the counit of the derived
adjunction. -/
private theorem supportedDerivedComparison_counit (hT : StableUnderSpecialization T) :
    (supportedDerivedComparison.{u, v} A T hT).hom ≫
        derivedSectionsWithSupportInAugmentation.{u, v} A T =
      (supportedDerivedAdjunction.{u, v} A T hT).counit := by
  have hL : ((supportModuleProperty A T :
      ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory).IsLeftAdjoint :=
    (derivedInclusion_adj_derivedSupportedSections.{u, v} A T hT).some.isLeftAdjoint
  refine Functor.rightDerived_ext _ (supportedCompUnit.{u, v} A T)
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) _ _ _ ?_
  ext X
  have hc : (supportedDerivedComparison.{u, v} A T hT).hom =
      Functor.rightDerivedNatTrans _ _ (supportedCompUnit.{u, v} A T)
        (derivedSectionsWithSupportInUnit.{u, v} A T)
        (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
        (supportedSectionsCompIso.{u, v} A T).hom := rfl
  have he := Functor.rightDerivedNatTrans_app
    (derivedSupportedSections.{u, v} A T ⋙ (supportModuleProperty A T :
      ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory)
    (derivedSectionsWithSupportIn.{u, v} A T) (supportedCompUnit.{u, v} A T)
    (derivedSectionsWithSupportInUnit.{u, v} A T)
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
    (supportedSectionsCompIso.{u, v} A T).hom X
  rw [← hc] at he
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at he ⊢
  rw [← Category.assoc, he, Category.assoc,
    derivedSectionsWithSupportInUnit_augmentation.{u, v} A T X]
  have hadj : (supportedDerivedAdjunction.{u, v} A T hT).counit =
      Adjunction.derivedε (htpySupportedAdjunction.{u, v} A T)
        (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
        ((supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι).mapDerivedCategoryFactorsh.hom
        (derivedSupportedSectionsUnit.{u, v} A T) :=
    Adjunction.derived_counit _ _ _ _ _
  rw [hadj, Adjunction.derivedε_fac_app]
  dsimp only [supportedSectionsCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.id_comp, Category.assoc]
  have key : (htpySupportedSectionsCompIso.{u, v} A T).hom.app X ≫
      (homotopySectionsWithSupportInSubtype.{u, v} A T).app X =
      (htpySupportedAdjunction.{u, v} A T).counit.app X := rfl
  rw [← Functor.map_comp, key]
  exact Category.id_comp _

/-- `RΓ_T(L)` has cohomology supported in `T`. -/
private theorem derivedCategoryB_derivedSectionsWithSupportIn (hT : StableUnderSpecialization T)
    (L : DerivedCategory (ModuleCat.{max u v} A)) :
    DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))
      ((derivedSectionsWithSupportIn.{u, v} A T).obj L) := by
  intro n
  refine (supportModuleProperty A T).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      ((supportedDerivedComparison.{u, v} A T hT).app L)) ?_
  exact ((supportedModulesComparison.{u, max u v} A T).obj
    ((derivedSupportedSections.{u, v} A T).obj L)).property n

/-- The derived inclusion of the modules supported in `T` is full. -/
private theorem supportedInclusion_full (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) :
    ((supportModuleProperty A T :
      ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory).Full := by
  have _ : (supportedModulesComparison.{u, max u v} A T).IsEquivalence :=
    supportedModulesComparison_isEquivalence.{u, max u v} A T hT hdim
  exact (inferInstance : (supportedModulesComparison.{u, max u v} A T ⋙
    (DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))).ι).Full)

/-- The derived inclusion of the modules supported in `T` is faithful. -/
private theorem supportedInclusion_faithful (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) :
    ((supportModuleProperty A T :
      ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory).Faithful := by
  have _ : (supportedModulesComparison.{u, max u v} A T).IsEquivalence :=
    supportedModulesComparison_isEquivalence.{u, max u v} A T hT hdim
  exact (inferInstance : (supportedModulesComparison.{u, max u v} A T ⋙
    (DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))).ι).Faithful)

/-- An object with cohomology supported in `T` comes from the derived category of the modules
supported in `T`. -/
private theorem exists_supportedInclusion_iso (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) K) :
    ∃ X : DerivedCategory (ModulesSupportedIn.{u, max u v} A T),
      Nonempty ((supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory.obj X ≅ K) := by
  have _ : (supportedModulesComparison.{u, max u v} A T).IsEquivalence :=
    supportedModulesComparison_isEquivalence.{u, max u v} A T hT hdim
  refine ⟨(supportedModulesComparison.{u, max u v} A T).objPreimage ⟨K, hK⟩, ⟨?_⟩⟩
  exact (DerivedCategoryB.derivedCategoryB
    (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))).ι.mapIso
    ((supportedModulesComparison.{u, max u v} A T).objObjPreimageIso ⟨K, hK⟩)

/-- **The augmentation is invertible on `D_T(A)`.** -/
private theorem isIso_augmentation_of_supported (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) K) :
    IsIso ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app K) := by
  have _ := supportedInclusion_full.{u, v} A T hT hdim
  have _ := supportedInclusion_faithful.{u, v} A T hT hdim
  obtain ⟨X, ⟨e⟩⟩ := exists_supportedInclusion_iso.{u, v} A T hT hdim K hK
  have hcounit : IsIso ((supportedDerivedAdjunction.{u, v} A T hT).counit.app K) :=
    (supportedDerivedAdjunction.{u, v} A T hT).isIso_counit_app_of_iso e.symm
  have hcomp : IsIso ((supportedDerivedComparison.{u, v} A T hT).hom.app K ≫
      (derivedSectionsWithSupportInAugmentation.{u, v} A T).app K) := by
    rw [show (supportedDerivedComparison.{u, v} A T hT).hom.app K ≫
        (derivedSectionsWithSupportInAugmentation.{u, v} A T).app K =
      (supportedDerivedAdjunction.{u, v} A T hT).counit.app K from
      congrArg (fun α ↦ NatTrans.app α K) (supportedDerivedComparison_counit.{u, v} A T hT)]
    exact hcounit
  exact IsIso.of_isIso_comp_left
    ((supportedDerivedComparison.{u, v} A T hT).hom.app K)
    ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app K)

/-- Precomposition with an isomorphism is bijective on morphisms. -/
private theorem bijective_precomp_iso {C : Type*} [Category C] {W W' X : C} (e : W ≅ W') :
    Function.Bijective (fun f : W' ⟶ X ↦ e.hom ≫ f) :=
  ⟨fun _ _ h ↦ (cancel_epi e.hom).1 h, fun g ↦ ⟨e.inv ≫ g, by simp⟩⟩

/-- Universality of a morphism against a source is invariant under isomorphisms of the
source. -/
private theorem bijective_comp_of_iso_source {C : Type*} [Category C] {W W' X Y : C}
    (e : W ≅ W') (c : X ⟶ Y) (h : Function.Bijective (fun f : W' ⟶ X ↦ f ≫ c)) :
    Function.Bijective (fun f : W ⟶ X ↦ f ≫ c) := by
  have key : (fun f : W ⟶ X ↦ f ≫ c) = (fun g : W' ⟶ Y ↦ e.hom ≫ g) ∘
      ((fun f : W' ⟶ X ↦ f ≫ c) ∘ (fun f : W ⟶ X ↦ e.inv ≫ f)) := by
    funext f
    simp
  rw [key]
  exact (bijective_precomp_iso e).comp (h.comp (bijective_precomp_iso e.symm))

/-- **The augmentation is universal.** A morphism to `K` from an object with cohomology
supported in `T` factors uniquely through the augmentation `RΓ_T(K) ⟶ K`. -/
private theorem bijective_comp_augmentation_of_supported (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) (W K : DerivedCategory (ModuleCat.{max u v} A))
    (hW : DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) W) :
    Function.Bijective (fun f : W ⟶ (derivedSectionsWithSupportIn.{u, v} A T).obj K ↦
      f ≫ (derivedSectionsWithSupportInAugmentation.{u, v} A T).app K) := by
  have _ := supportedInclusion_full.{u, v} A T hT hdim
  have _ := supportedInclusion_faithful.{u, v} A T hT hdim
  obtain ⟨X, ⟨e⟩⟩ := exists_supportedInclusion_iso.{u, v} A T hT hdim W hW
  refine bijective_comp_of_iso_source e.symm _ ?_
  set G := (supportModuleProperty A T :
    ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory with hG
  set adj := supportedDerivedAdjunction.{u, v} A T hT with hadjdef
  set c := supportedDerivedComparison.{u, v} A T hT with hcdef
  have hff : G.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful G
  have hcc : c.inv.app K ≫ adj.counit.app K =
      (derivedSectionsWithSupportInAugmentation.{u, v} A T).app K := by
    rw [show adj.counit.app K = c.hom.app K ≫
        (derivedSectionsWithSupportInAugmentation.{u, v} A T).app K from
      (congrArg (fun α ↦ NatTrans.app α K)
        (supportedDerivedComparison_counit.{u, v} A T hT)).symm, ← Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
  have hkey : (fun f : G.obj X ⟶ (derivedSectionsWithSupportIn.{u, v} A T).obj K ↦
      f ≫ (derivedSectionsWithSupportInAugmentation.{u, v} A T).app K) =
      ⇑((Iso.homCongr (Iso.refl (G.obj X)) (c.app K).symm).trans
        (hff.homEquiv.symm.trans (adj.homEquiv X K).symm)) := by
    funext f
    have hmap : G.map (hff.homEquiv.symm (𝟙 (G.obj X) ≫ f ≫ (c.app K).symm.hom)) =
        𝟙 (G.obj X) ≫ f ≫ (c.app K).symm.hom :=
      hff.homEquiv.apply_symm_apply (𝟙 (G.obj X) ≫ f ≫ (c.app K).symm.hom)
    dsimp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv]
    rw [Adjunction.homEquiv_counit]
    show f ≫ (derivedSectionsWithSupportInAugmentation.{u, v} A T).app K =
      G.map (hff.homEquiv.symm (𝟙 (G.obj X) ≫ f ≫ (c.app K).symm.hom)) ≫ adj.counit.app K
    rw [hmap, Category.id_comp, Category.assoc]
    show _ = f ≫ c.inv.app K ≫ adj.counit.app K
    rw [hcc]
  rw [hkey]
  exact Equiv.bijective _

end SupportedAdjunction

section ClosedSupport

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))

/-- **Local cohomology with a closed support inside `T` inverts the augmentation.** -/
private theorem isIso_localCohomologyFunctor_map_augmentation
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) (I : Ideal A)
    (hI : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    IsIso ((Dualizing.localCohomologyFunctor.{u, max u v} A I
        (Ideal.fg_of_isNoetherianRing I)).map
      ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app K)) := by
  have hsupp : ∀ Z : Dualizing.PowerTorsionDerivedCategory A I
        (Ideal.fg_of_isNoetherianRing I),
      DerivedCategoryB.derivedCategoryB
        (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) Z.obj := by
    intro Z n
    exact ((isIPowerTorsion_iff_support_subset A _ I
      (Ideal.fg_of_isNoetherianRing I)).mp (Z.property n)).trans hI
  exact Dualizing.TorsionCounit.isIso_rightAdjoint_map_of_bijective
    (Dualizing.localCohomologyAdjunction.{u, max u v} A I
      (Ideal.fg_of_isNoetherianRing I)) _
    (fun Z ↦ bijective_comp_augmentation_of_supported.{u, v} A T hT hdim _ K (hsupp Z))

/-- **A map inverted by local cohomology with every closed support inside `T` is inverted by
local cohomology with support in `T`.** This is the filtered colimit of [Stacks, Tag 0EF1]. -/
private theorem isIso_derivedSectionsWithSupportIn_map_of_closed
    (hT : StableUnderSpecialization T)
    {X Y : DerivedCategory (ModuleCat.{max u v} A)} (f : X ⟶ Y)
    (hf : ∀ I : Ideal A, PrimeSpectrum.zeroLocus (I : Set A) ⊆ T →
      IsIso ((Dualizing.localCohomologyFunctor.{u, max u v} A I
        (Ideal.fg_of_isNoetherianRing I)).map f)) :
    IsIso ((derivedSectionsWithSupportIn.{u, v} A T).map f) := by
  have hclosed : ∀ I : Ideal A, PrimeSpectrum.zeroLocus (I : Set A) ⊆ T →
      IsIso ((derivedSectionsWithSupportIn.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).map f) := by
    intro I hI
    have hcomp : IsIso ((Dualizing.localCohomologyFunctor.{u, max u v} A I
        (Ideal.fg_of_isNoetherianRing I) ⋙
        (Dualizing.derivedPowerTorsionProperty A I
          (Ideal.fg_of_isNoetherianRing I)).ι).map f) := by
      have := hf I hI
      show IsIso ((Dualizing.derivedPowerTorsionProperty A I
        (Ideal.fg_of_isNoetherianRing I)).ι.map
        ((Dualizing.localCohomologyFunctor.{u, max u v} A I
          (Ideal.fg_of_isNoetherianRing I)).map f))
      infer_instance
    have hnat := isIso_compareSectionsWithSupportLocalCohomology.{u, v} A I
      (Ideal.fg_of_isNoetherianRing I)
    have := hnat
    exact CechFormula.isIso_map_of_natIso
      (asIso (compareSectionsWithSupportLocalCohomology.{u, v} A I
        (Ideal.fg_of_isNoetherianRing I))) f hcomp
  rw [DerivedCategory.isIso_iff]
  intro n
  have hstage : ∀ J : ClosedSupportIdeal A T,
      IsIso (((closedSupportDiagram.{u, v} A T n).map f).app J) := by
    intro J
    have := hclosed (OrderDual.ofDual J).1 (OrderDual.ofDual J).2
    show IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
      ((derivedSectionsWithSupportIn.{u, v} A (ClosedSupportIdeal.support A J)).map f))
    infer_instance
  have hdiag : IsIso ((closedSupportDiagram.{u, v} A T n).map f) :=
    NatIso.isIso_of_isIso_app _
  have hcol : IsIso ((closedSupportDiagram.{u, v} A T n ⋙ colim).map f) := by
    have := hdiag
    show IsIso (colim.map ((closedSupportDiagram.{u, v} A T n).map f))
    infer_instance
  have hκ := colimitClosedSupportComparison_isIso.{u, v} A T hT n
  have hκX : IsIso ((colimitClosedSupportComparison.{u, v} A T n).app X) :=
    NatIso.isIso_app_of_isIso _ X
  have hgoal : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
        ((derivedSectionsWithSupportIn.{u, v} A T).map f) =
      CategoryTheory.inv ((colimitClosedSupportComparison.{u, v} A T n).app X) ≫
        ((closedSupportDiagram.{u, v} A T n ⋙ colim).map f ≫
          (colimitClosedSupportComparison.{u, v} A T n).app Y) :=
    (IsIso.eq_inv_comp _).mpr
      ((colimitClosedSupportComparison.{u, v} A T n).naturality f).symm
  rw [hgoal]
  infer_instance

end ClosedSupport

/-- Tensoring a morphism with an identity in the second variable is the bifunctor's action on
the corresponding pair. -/
private theorem bifunctorMap_fst (A : Type u) [CommRing A]
    {X Y : DerivedCategory (ModuleCat.{u} A)} (f : X ⟶ Y)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    (CechFormula.derivedTensorProductBifunctor A).map
        ((f, 𝟙 L) : (X, L) ⟶ (Y, L)) =
      ((canonicalDerivedTensorProductFunctor A).map f).app L := by
  show ((canonicalDerivedTensorProductFunctor A).map f).app L ≫
    ((canonicalDerivedTensorProductFunctor A).obj Y).map (𝟙 L) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- If a bifunctor map `G` inverts `φ` and local cohomology commutes with the tensor product up
to `G`, then local cohomology inverts the tensor product of `φ`. -/
private theorem isIso_localCohomologyFunctor_map_tensor_of_natIso (A : Type u) [CommRing A]
    (I : Ideal A)
    (hfg : I.FG) {X Y : DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)}
    (φ : X ⟶ Y) (G : DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A))
    (e : CechFormula.derivedTensorProductBifunctor A ⋙
        CechFormula.localCohomologyEndofunctor A I hfg ≅
      G ⋙ CechFormula.derivedTensorProductBifunctor A) (hG : IsIso (G.map φ)) :
    IsIso ((Dualizing.localCohomologyFunctor.{u, u} A I hfg).map
      ((CechFormula.derivedTensorProductBifunctor A).map φ)) := by
  have hB : IsIso ((G ⋙ CechFormula.derivedTensorProductBifunctor A).map φ) := by
    change IsIso ((CechFormula.derivedTensorProductBifunctor A).map (G.map φ))
    infer_instance
  have hiso : IsIso ((Dualizing.derivedPowerTorsionProperty A I hfg).ι.map
      ((Dualizing.localCohomologyFunctor.{u, u} A I hfg).map
        ((CechFormula.derivedTensorProductBifunctor A).map φ))) :=
    CechFormula.isIso_map_of_natIso e φ hB
  exact isIso_of_reflects_iso _ (Dualizing.derivedPowerTorsionProperty A I hfg).ι

section TensorFormula

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))

/-- **The comparison produced by the augmentation.** If a natural transformation has values in
`D_T(A)` at the source and is inverted by `RΓ_T`, then `RΓ_T` of the target is the source,
compatibly with the augmentation. -/
private theorem exists_supported_comparison {C : Type*} [Category C]
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤)
    (F G : C ⥤ DerivedCategory (ModuleCat.{max u v} A)) (τ : F ⟶ G)
    (hF : ∀ X, DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)) (F.obj X))
    (hτ : ∀ X, IsIso ((derivedSectionsWithSupportIn.{u, v} A T).map (τ.app X))) :
    ∃ e : G ⋙ derivedSectionsWithSupportIn.{u, v} A T ≅ F,
      e.hom ≫ τ = Functor.whiskerLeft G
        (derivedSectionsWithSupportInAugmentation.{u, v} A T) := by
  let R := derivedSectionsWithSupportIn.{u, v} A T
  let ε := derivedSectionsWithSupportInAugmentation.{u, v} A T
  let α : F ⋙ R ⟶ F := Functor.whiskerLeft F ε
  have hα : ∀ X, IsIso (α.app X) := fun X ↦
    isIso_augmentation_of_supported.{u, v} A T hT hdim _ (hF X)
  have _ : IsIso α := NatIso.isIso_of_isIso_app α
  have hτ' : ∀ X, IsIso ((Functor.whiskerRight τ R).app X) := hτ
  have _ : IsIso (Functor.whiskerRight τ R) := NatIso.isIso_of_isIso_app _
  refine ⟨(asIso (Functor.whiskerRight τ R)).symm ≪≫ asIso α, ?_⟩
  ext X
  dsimp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [NatIso.isIso_inv_app]
  show (CategoryTheory.inv (R.map (τ.app X)) ≫ ε.app (F.obj X)) ≫ τ.app X = ε.app (G.obj X)
  have hn : R.map (τ.app X) ≫ ε.app (G.obj X) = ε.app (F.obj X) ≫ τ.app X :=
    ε.naturality (τ.app X)
  rw [Category.assoc, ← hn, IsIso.inv_hom_id_assoc]

/-- Local cohomology on `D(A)` for the closed support `V(I) ⊆ T` inverts the augmentation. -/
private theorem isIso_localCohomologyEndofunctor_map_augmentation
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) (I : Ideal A)
    (hI : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T) (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((CechFormula.localCohomologyEndofunctor A I (Ideal.fg_of_isNoetherianRing I)).map
      ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app K)) := by
  have := isIso_localCohomologyFunctor_map_augmentation.{u, u} A T hT hdim I hI K
  change IsIso ((Dualizing.derivedPowerTorsionProperty A I
    (Ideal.fg_of_isNoetherianRing I)).ι.map
    ((Dualizing.localCohomologyFunctor.{u, u} A I (Ideal.fg_of_isNoetherianRing I)).map
      ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app K)))
  infer_instance

/-- The augmentation tensored with the identity in the second variable, as a natural
transformation of bifunctors. -/
private def tensorAugmentationLeft :
    (Functor.prod (derivedSectionsWithSupportIn.{u, u} A T) (𝟭 _)) ⋙
        CechFormula.derivedTensorProductBifunctor A ⟶
      CechFormula.derivedTensorProductBifunctor A where
  app X := (CechFormula.derivedTensorProductBifunctor A).map
    ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app X.1, 𝟙 X.2)
  naturality X Y g := by
    dsimp only [Functor.comp_map, Functor.prod_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (CechFormula.derivedTensorProductBifunctor A).map
      (Prod.ext ((derivedSectionsWithSupportInAugmentation.{u, u} A T).naturality g.1)
        ((Category.comp_id g.2).trans (Category.id_comp g.2).symm))

/-- **Local cohomology with support in `T` inverts the augmentation tensored with the
identity.** -/
private theorem isIso_map_tensorAugmentationLeft (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) (X : DerivedCategory (ModuleCat.{u} A) ×
      DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((derivedSectionsWithSupportIn.{u, u} A T).map
      ((tensorAugmentationLeft.{u} A T).app X)) := by
  refine isIso_derivedSectionsWithSupportIn_map_of_closed.{u, u} A T hT _ (fun I hI ↦ ?_)
  set hfg := Ideal.fg_of_isNoetherianRing (R := A) I
  set C := CechFormula.localCohomologyEndofunctor A I hfg
  have hεK := isIso_localCohomologyEndofunctor_map_augmentation.{u} A T hT hdim I hI X.1
  exact isIso_localCohomologyFunctor_map_tensor_of_natIso.{u} A I hfg
    (((derivedSectionsWithSupportInAugmentation.{u, u} A T).app X.1, 𝟙 X.2) :
      ((derivedSectionsWithSupportIn.{u, u} A T).obj X.1, X.2) ⟶ (X.1, X.2))
    (Functor.prod C (𝟭 _))
    (CechFormula.localCohomology_derivedTensorProduct_right A I hfg ≪≫
      CechFormula.localCohomology_derivedTensorProduct_left A I hfg)
    (Iso.prod (asIso (C.map ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app X.1)))
      (Iso.refl X.2)).isIso_hom

/-- The augmentation tensored with the identity in the first variable, as a natural
transformation of bifunctors. -/
private def tensorAugmentationRight :
    (Functor.prod (𝟭 _) (derivedSectionsWithSupportIn.{u, u} A T)) ⋙
        CechFormula.derivedTensorProductBifunctor A ⟶
      CechFormula.derivedTensorProductBifunctor A where
  app X := (CechFormula.derivedTensorProductBifunctor A).map
    (𝟙 X.1, (derivedSectionsWithSupportInAugmentation.{u, u} A T).app X.2)
  naturality X Y g := by
    dsimp only [Functor.comp_map, Functor.prod_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (CechFormula.derivedTensorProductBifunctor A).map
      (Prod.ext ((Category.comp_id g.1).trans (Category.id_comp g.1).symm)
        ((derivedSectionsWithSupportInAugmentation.{u, u} A T).naturality g.2))

/-- **Local cohomology with support in `T` inverts the identity tensored with the
augmentation.** -/
private theorem isIso_map_tensorAugmentationRight (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) (X : DerivedCategory (ModuleCat.{u} A) ×
      DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((derivedSectionsWithSupportIn.{u, u} A T).map
      ((tensorAugmentationRight.{u} A T).app X)) := by
  refine isIso_derivedSectionsWithSupportIn_map_of_closed.{u, u} A T hT _ (fun I hI ↦ ?_)
  set hfg := Ideal.fg_of_isNoetherianRing (R := A) I
  set C := CechFormula.localCohomologyEndofunctor A I hfg
  have hεL := isIso_localCohomologyEndofunctor_map_augmentation.{u} A T hT hdim I hI X.2
  exact isIso_localCohomologyFunctor_map_tensor_of_natIso.{u} A I hfg
    ((𝟙 X.1, (derivedSectionsWithSupportInAugmentation.{u, u} A T).app X.2) :
      (X.1, (derivedSectionsWithSupportIn.{u, u} A T).obj X.2) ⟶ (X.1, X.2))
    (Functor.prod (𝟭 _) C) (CechFormula.localCohomology_derivedTensorProduct_right A I hfg)
    (Iso.prod (Iso.refl X.1)
      (asIso (C.map ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app X.2)))).isIso_hom

/-- **Stacks 0EF7.** Over a Noetherian ring of finite dimension, the derived tensor product of
an object of `D_T(A)` with an arbitrary object of `D(A)` again lies in `D_T(A)`. -/
@[stacks 0EF7 "support, left factor"]
theorem derivedCategoryB_tensor_left (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{u} A)) K) :
    DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{u} A))
      ((CechFormula.derivedTensorProductBifunctor A).obj (K, L)) :=
  derivedCategoryB_tensor_of_left.{u, u}
    (CochainComplex.DerivedTensor.DerivedTensorProduct.toGeneral
      (canonicalDerivedTensorProduct A)) hT hdim K L hK

/-- **Stacks 0EF7.** Over a Noetherian ring of finite dimension, the derived tensor product of
an arbitrary object of `D(A)` with an object of `D_T(A)` again lies in `D_T(A)`. -/
@[stacks 0EF7 "support, right factor"]
theorem derivedCategoryB_tensor_right (hT : StableUnderSpecialization T)
    (hdim : ringKrullDim A < ⊤) (K L : DerivedCategory (ModuleCat.{u} A))
    (hL : DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{u} A)) L) :
    DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{u} A))
      ((CechFormula.derivedTensorProductBifunctor A).obj (K, L)) := by
  intro n
  refine (supportModuleProperty A T).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso (derivedTensorProductCommIso L K)) ?_
  exact derivedCategoryB_tensor_left A T hT hdim L K hL n

/-- **Stacks 0EF7.** Local cohomology with support in `T` of a derived tensor product is the
derived tensor product with local cohomology taken in the left factor, by an isomorphism of
bifunctors carrying the augmentation of the tensor product to the augmentation of the left
factor tensored with the identity. -/
@[stacks 0EF7 "tensor formula, left factor"]
theorem exists_derivedSectionsWithSupportIn_tensorIso_left
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) :
    ∃ e : CechFormula.derivedTensorProductBifunctor A ⋙
          derivedSectionsWithSupportIn.{u, u} A T ≅
        Functor.prod (derivedSectionsWithSupportIn.{u, u} A T) (𝟭 _) ⋙
          CechFormula.derivedTensorProductBifunctor A,
      ∀ K L : DerivedCategory (ModuleCat.{u} A),
        e.hom.app (K, L) ≫ (CechFormula.derivedTensorProductBifunctor A).map
            (((derivedSectionsWithSupportInAugmentation.{u, u} A T).app K, 𝟙 L) :
              ((derivedSectionsWithSupportIn.{u, u} A T).obj K, L) ⟶ (K, L)) =
          (derivedSectionsWithSupportInAugmentation.{u, u} A T).app
            ((CechFormula.derivedTensorProductBifunctor A).obj (K, L)) := by
  obtain ⟨e, he⟩ := exists_supported_comparison.{u, u} A T hT hdim
    (Functor.prod (derivedSectionsWithSupportIn.{u, u} A T) (𝟭 _) ⋙
      CechFormula.derivedTensorProductBifunctor A)
    (CechFormula.derivedTensorProductBifunctor A) (tensorAugmentationLeft.{u} A T)
    (fun X ↦ derivedCategoryB_tensor_left A T hT hdim _ _
      (derivedCategoryB_derivedSectionsWithSupportIn.{u, u} A T hT X.1))
    (isIso_map_tensorAugmentationLeft.{u} A T hT hdim)
  exact ⟨e, fun K L ↦ congrArg (fun α ↦ NatTrans.app α (K, L)) he⟩

/-- **Stacks 0EF7.** Local cohomology with support in `T` of a derived tensor product is the
derived tensor product with local cohomology taken in the right factor, by an isomorphism of
bifunctors carrying the augmentation of the tensor product to the identity tensored with the
augmentation of the right factor. -/
@[stacks 0EF7 "tensor formula, right factor"]
theorem exists_derivedSectionsWithSupportIn_tensorIso_right
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) :
    ∃ e : CechFormula.derivedTensorProductBifunctor A ⋙
          derivedSectionsWithSupportIn.{u, u} A T ≅
        Functor.prod (𝟭 _) (derivedSectionsWithSupportIn.{u, u} A T) ⋙
          CechFormula.derivedTensorProductBifunctor A,
      ∀ K L : DerivedCategory (ModuleCat.{u} A),
        e.hom.app (K, L) ≫ (CechFormula.derivedTensorProductBifunctor A).map
            ((𝟙 K, (derivedSectionsWithSupportInAugmentation.{u, u} A T).app L) :
              (K, (derivedSectionsWithSupportIn.{u, u} A T).obj L) ⟶ (K, L)) =
          (derivedSectionsWithSupportInAugmentation.{u, u} A T).app
            ((CechFormula.derivedTensorProductBifunctor A).obj (K, L)) := by
  obtain ⟨e, he⟩ := exists_supported_comparison.{u, u} A T hT hdim
    (Functor.prod (𝟭 _) (derivedSectionsWithSupportIn.{u, u} A T) ⋙
      CechFormula.derivedTensorProductBifunctor A)
    (CechFormula.derivedTensorProductBifunctor A) (tensorAugmentationRight.{u} A T)
    (fun X ↦ derivedCategoryB_tensor_right A T hT hdim _ _
      (derivedCategoryB_derivedSectionsWithSupportIn.{u, u} A T hT X.2))
    (isIso_map_tensorAugmentationRight.{u} A T hT hdim)
  exact ⟨e, fun K L ↦ congrArg (fun α ↦ NatTrans.app α (K, L)) he⟩

/-- **Stacks 0EF7.** Applying local cohomology with support in `T` in both tensor factors agrees
with applying it to the tensor product, again compatibly with the augmentations. -/
@[stacks 0EF7 "tensor formula, both factors"]
theorem exists_derivedSectionsWithSupportIn_tensorIso_both
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) :
    ∃ e : CechFormula.derivedTensorProductBifunctor A ⋙
          derivedSectionsWithSupportIn.{u, u} A T ≅
        Functor.prod (derivedSectionsWithSupportIn.{u, u} A T)
          (derivedSectionsWithSupportIn.{u, u} A T) ⋙
          CechFormula.derivedTensorProductBifunctor A,
      ∀ K L : DerivedCategory (ModuleCat.{u} A),
        e.hom.app (K, L) ≫ (CechFormula.derivedTensorProductBifunctor A).map
            (((derivedSectionsWithSupportInAugmentation.{u, u} A T).app K,
                (derivedSectionsWithSupportInAugmentation.{u, u} A T).app L) :
              ((derivedSectionsWithSupportIn.{u, u} A T).obj K,
                (derivedSectionsWithSupportIn.{u, u} A T).obj L) ⟶ (K, L)) =
          (derivedSectionsWithSupportInAugmentation.{u, u} A T).app
            ((CechFormula.derivedTensorProductBifunctor A).obj (K, L)) := by
  obtain ⟨a, ha⟩ := exists_derivedSectionsWithSupportIn_tensorIso_left A T hT hdim
  obtain ⟨b, hb⟩ := exists_derivedSectionsWithSupportIn_tensorIso_right A T hT hdim
  have hεR : ∀ X : DerivedCategory (ModuleCat.{u} A),
      IsIso ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app
        ((derivedSectionsWithSupportIn.{u, u} A T).obj X)) := fun X ↦
    isIso_augmentation_of_supported.{u, u} A T hT hdim _
      (derivedCategoryB_derivedSectionsWithSupportIn.{u, u} A T hT X)
  let δ : (CechFormula.derivedTensorProductBifunctor A ⋙
        derivedSectionsWithSupportIn.{u, u} A T) ⋙
        derivedSectionsWithSupportIn.{u, u} A T ≅
      CechFormula.derivedTensorProductBifunctor A ⋙
        derivedSectionsWithSupportIn.{u, u} A T :=
    NatIso.ofComponents
      (fun X ↦ @asIso _ _ _ _
        ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app
          ((derivedSectionsWithSupportIn.{u, u} A T).obj
            ((CechFormula.derivedTensorProductBifunctor A).obj X)))
        (hεR ((CechFormula.derivedTensorProductBifunctor A).obj X)))
      (fun f ↦ (derivedSectionsWithSupportInAugmentation.{u, u} A T).naturality
        ((derivedSectionsWithSupportIn.{u, u} A T).map
          ((CechFormula.derivedTensorProductBifunctor A).map f)))
  refine ⟨δ.symm ≪≫ Functor.isoWhiskerRight a (derivedSectionsWithSupportIn.{u, u} A T) ≪≫
    Functor.associator (Functor.prod (derivedSectionsWithSupportIn.{u, u} A T) (𝟭 _))
      (CechFormula.derivedTensorProductBifunctor A)
      (derivedSectionsWithSupportIn.{u, u} A T) ≪≫
    Functor.isoWhiskerLeft
      (Functor.prod (derivedSectionsWithSupportIn.{u, u} A T) (𝟭 _)) b ≪≫
    (Functor.associator (Functor.prod (derivedSectionsWithSupportIn.{u, u} A T) (𝟭 _))
      (Functor.prod (𝟭 _) (derivedSectionsWithSupportIn.{u, u} A T))
      (CechFormula.derivedTensorProductBifunctor A)).symm, fun K L ↦ ?_⟩
  have hsplit : (CechFormula.derivedTensorProductBifunctor A).map
        (((derivedSectionsWithSupportInAugmentation.{u, u} A T).app K,
            (derivedSectionsWithSupportInAugmentation.{u, u} A T).app L) :
          ((derivedSectionsWithSupportIn.{u, u} A T).obj K,
            (derivedSectionsWithSupportIn.{u, u} A T).obj L) ⟶ (K, L)) =
      (CechFormula.derivedTensorProductBifunctor A).map
          ((𝟙 ((derivedSectionsWithSupportIn.{u, u} A T).obj K),
              (derivedSectionsWithSupportInAugmentation.{u, u} A T).app L) :
            ((derivedSectionsWithSupportIn.{u, u} A T).obj K,
              (derivedSectionsWithSupportIn.{u, u} A T).obj L) ⟶
              ((derivedSectionsWithSupportIn.{u, u} A T).obj K, L)) ≫
        (CechFormula.derivedTensorProductBifunctor A).map
          (((derivedSectionsWithSupportInAugmentation.{u, u} A T).app K, 𝟙 L) :
            ((derivedSectionsWithSupportIn.{u, u} A T).obj K, L) ⟶ (K, L)) := by
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg (CechFormula.derivedTensorProductBifunctor A).map
      (Prod.ext (Category.id_comp _).symm (Category.comp_id _).symm)
  have hnat : (derivedSectionsWithSupportIn.{u, u} A T).map (a.hom.app (K, L)) ≫
        (derivedSectionsWithSupportInAugmentation.{u, u} A T).app
          ((CechFormula.derivedTensorProductBifunctor A).obj
            ((derivedSectionsWithSupportIn.{u, u} A T).obj K, L)) =
      (derivedSectionsWithSupportInAugmentation.{u, u} A T).app
          ((derivedSectionsWithSupportIn.{u, u} A T).obj
            ((CechFormula.derivedTensorProductBifunctor A).obj (K, L))) ≫
        a.hom.app (K, L) :=
    (derivedSectionsWithSupportInAugmentation.{u, u} A T).naturality (a.hom.app (K, L))
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatIso.ofComponents_inv_app,
    Functor.prod_obj, Functor.id_obj]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]
  rw [hsplit, ← Category.assoc (b.hom.app ((derivedSectionsWithSupportIn.{u, u} A T).obj K, L)),
    hb ((derivedSectionsWithSupportIn.{u, u} A T).obj K) L, reassoc_of% hnat]
  have hδ : δ.inv.app (K, L) = CategoryTheory.inv
      ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app
        ((derivedSectionsWithSupportIn.{u, u} A T).obj
          ((CechFormula.derivedTensorProductBifunctor A).obj (K, L)))) := rfl
  have := hεR ((CechFormula.derivedTensorProductBifunctor A).obj (K, L))
  rw [hδ, IsIso.inv_hom_id_assoc]
  exact ha K L

/-- **Stacks 0EF7.** Local cohomology with support in `T` is the derived tensor product with the
local cohomology of the ring, by an isomorphism whose inverse is the canonical map
`RΓ_T(A) ⊗^L_A K ⟶ A ⊗^L_A K ⟶ K`. -/
@[stacks 0EF7 "tensor formula"]
theorem exists_derivedSectionsWithSupportIn_isoTensorUnit
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) :
    ∃ e : derivedSectionsWithSupportIn.{u, u} A T ≅
        (canonicalDerivedTensorProductFunctor A).obj
          ((derivedSectionsWithSupportIn.{u, u} A T).obj (CechFormula.unitObject A)),
      ∀ K : DerivedCategory (ModuleCat.{u} A),
        e.hom.app K ≫
            (((canonicalDerivedTensorProductFunctor A).map
                ((derivedSectionsWithSupportInAugmentation.{u, u} A T).app
                  (CechFormula.unitObject A))).app K ≫
              (CechFormula.derivedTensorLeftUnitor A).hom.app K) =
          (derivedSectionsWithSupportInAugmentation.{u, u} A T).app K := by
  set U := CechFormula.unitObject A with hU
  set R := derivedSectionsWithSupportIn.{u, u} A T with hR
  set ε := derivedSectionsWithSupportInAugmentation.{u, u} A T with hε
  set F := canonicalDerivedTensorProductFunctor A with hF
  have hτ : ∀ K : DerivedCategory (ModuleCat.{u} A),
      IsIso (R.map ((F.map (ε.app U) ≫
        (CechFormula.derivedTensorLeftUnitor A).hom).app K)) := by
    intro K
    have hlam : IsIso (R.map ((CechFormula.derivedTensorLeftUnitor A).hom.app K)) :=
      Functor.map_isIso R _
    have hleft : IsIso (R.map ((F.map (ε.app U)).app K)) := by
      have h := isIso_map_tensorAugmentationLeft.{u} A T hT hdim (U, K)
      rwa [show (tensorAugmentationLeft.{u} A T).app (U, K) = (F.map (ε.app U)).app K from
        bifunctorMap_fst A (ε.app U) K] at h
    have := hlam
    have := hleft
    show IsIso (R.map ((F.map (ε.app U)).app K ≫
      (CechFormula.derivedTensorLeftUnitor A).hom.app K))
    rw [R.map_comp]
    infer_instance
  obtain ⟨e, he⟩ := exists_supported_comparison.{u, u} A T hT hdim (F.obj (R.obj U)) (𝟭 _)
    (F.map (ε.app U) ≫ (CechFormula.derivedTensorLeftUnitor A).hom)
    (fun K ↦ derivedCategoryB_tensor_left A T hT hdim _ _
      (derivedCategoryB_derivedSectionsWithSupportIn.{u, u} A T hT U))
    hτ
  exact ⟨e, fun K ↦ congrArg (fun α ↦ NatTrans.app α K) he⟩

end TensorFormula

end Stacks.LocalCohomology

end
