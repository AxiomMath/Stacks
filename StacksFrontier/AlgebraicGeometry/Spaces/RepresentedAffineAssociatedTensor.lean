module

public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.Devissage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.RingTheory.Flat.Lazard
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.DevissageNatTrans
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SheafTensorUnitIsoLeftMaps

/-!
# The associated module on an affine algebraic space is compatible with the tensor product

Let `U` be an object of the big fppf site whose underlying scheme is affine, with ring of global
functions `R`, and let `M ↦ M^~` be the associated-module functor
`AlgebraicGeometry.Space.representedAffineAssociated` from `R`-modules to `𝒪`-modules on the
small étale site of the algebraic space `yoneda.obj U`.  For a fixed `R`-module `N` there is an
isomorphism

`(M ⊗_R N)^~ ≅ M^~ ⊗_𝒪 N^~`,

natural in `M`, for the tensor product `Stacks.SheafOfModules.Tensor.sheafTensor` of the small
étale ringed site, which is the one the derived tensor product of the space is built from.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineAssociatedTensorIso`: the isomorphism of functors
  `(- ⊗_R N)^~ ≅ (-)^~ ⊗_𝒪 N^~`.

## Main results

* `AlgebraicGeometry.Space.isFlat_representedAffineAssociated_obj`: the associated module of a
  flat `R`-module is flat.

## Implementation notes

The comparison is built on the small étale site of `yoneda.obj U` from the adjunction
`M ↦ M^~ ⊣ Γ`. Writing `H(M) = Γ(M^~ ⊗ N^~)`, the rule `a ⊗ n ↦ H(a)(n)` is a natural map
`M ⊗_R N ⟶ H(M)` whose adjoint `(M ⊗_R N)^~ ⟶ M^~ ⊗ N^~` is invertible at `M = R`; both sides
commute with colimits in `M`, so it is invertible everywhere
(`Stacks.EilenbergWatts.isIso_app_of_isIso_app_unit`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The tensor product of `𝒪`-modules on the small étale site of `yoneda.obj U`, the bifunctor
the derived tensor product of the space is built from. -/
abbrev representedAffineTensor :
    Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
        Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u}
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O

/-- The associated module of `R` is the structure sheaf, the unit of the tensor product. -/
abbrev representedAffineAssociatedUnitIso :
    (representedAffineAssociated B S hS U).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O) :=
  representedAffineAssociatedObjUnitIso B S hS U

/-- The left unit constraint `𝒪 ⊗ 𝓜 ≅ 𝓜` on the small étale site of `yoneda.obj U`. -/
abbrev representedAffineLeftUnitor
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    ((representedAffineTensor B S hS U).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O))).obj
        M ≅ M :=
  Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft _ M

/-- The associated-module functor is full. -/
instance : (representedAffineAssociated B S hS U).Full :=
  (representedAffineAssociatedFullyFaithful B S hS U).full

/-- The associated-module functor is faithful. -/
instance : (representedAffineAssociated B S hS U).Faithful :=
  (representedAffineAssociatedFullyFaithful B S hS U).faithful

/-- The counit `Γ(𝓜)^~ ⟶ 𝓜` is invertible at a quasi-coherent `𝓜`. -/
theorem isIso_representedAffineAssociatedAdjunction_counit_app_tensor
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : M.IsQuasicoherentOnSite) :
    IsIso ((representedAffineAssociatedAdjunction B S hS U).counit.app M) :=
  (representedAffineAssociatedAdjunction B S hS U).isIso_counit_app_of_iso
    ((ObjectProperty.ι _).mapIso
        ((representedAffineAssoc B S hS U).counitIso.app ⟨M, hM⟩).symm ≪≫
      (representedAffineAssociatedIso B S hS U).app
        ((representedAffineAssoc B S hS U).inverse.obj ⟨M, hM⟩))

/-- Tensoring on the left with `R^~` is the identity, through `R^~ ≅ 𝒪` and the left unit
constraint, naturally in the second factor. -/
def representedAffineUnitTensorIso
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    ((representedAffineTensor B S hS U).obj ((representedAffineAssociated B S hS U).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))).obj M ≅ M :=
  ((representedAffineTensor B S hS U).mapIso (representedAffineAssociatedUnitIso B S hS U)).app M ≪≫
    representedAffineLeftUnitor B S hS U M

/-- The isomorphism `R^~ ⊗ 𝓜 ≅ 𝓜` is natural in `𝓜`. -/
@[reassoc]
theorem representedAffineUnitTensorIso_naturality
    {M M' : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
    (f : M ⟶ M') :
    ((representedAffineTensor B S hS U).obj ((representedAffineAssociated B S hS U).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))).map f ≫
        (representedAffineUnitTensorIso B S hS U M').hom =
      (representedAffineUnitTensorIso B S hS U M).hom ≫ f := by
  simp only [representedAffineUnitTensorIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, NatTrans.naturality, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·)
    (Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft_naturality _ f)

/-- The unit constraint `R^~ ⊗ 𝓝^~ ≅ 𝓝^~` as a natural transformation in `𝓝`. -/
def representedAffineUnitTensorNatTrans :
    representedAffineAssociated B S hS U ⋙ (representedAffineTensor B S hS U).obj
        ((representedAffineAssociated B S hS U).obj
          (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ⟶
      representedAffineAssociated B S hS U where
  app N := (representedAffineUnitTensorIso B S hS U _).hom
  naturality _ _ f := by
    rw [Functor.comp_map]
    exact representedAffineUnitTensorIso_naturality B S hS U _

/-- Multiplication by a scalar `r ∈ R`, as a natural endomorphism of the associated-module
functor. -/
def representedAffineAssociatedSmul (r : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    representedAffineAssociated B S hS U ⟶ representedAffineAssociated B S hS U where
  app N := (representedAffineAssociated B S hS U).map (r • 𝟙 N)
  naturality _ _ f := by
    simp only [← Functor.map_comp, Linear.comp_smul, Linear.smul_comp, Category.id_comp,
      Category.comp_id]

/-- **Scalars act through the left tensor factor.**  For `r ∈ R`, tensoring the multiplication by
`r` on `R^~` with `𝓝^~` is, through `R^~ ⊗ 𝓝^~ ≅ 𝓝^~`, the associated map of multiplication by
`r` on `𝓝`. -/
theorem representedAffine_map_smul_tensor (r : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((representedAffineTensor B S hS U).map ((representedAffineAssociated B S hS U).map
        (r • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))))).app
        ((representedAffineAssociated B S hS U).obj N) ≫
      (representedAffineUnitTensorIso B S hS U _).hom =
    (representedAffineUnitTensorIso B S hS U _).hom ≫
      (representedAffineAssociated B S hS U).map (r • 𝟙 N) := by
  have := (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  have := Stacks.SheafOfModules.preservesColimits_sheafTensorObj
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O
    ((representedAffineAssociated B S hS U).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
  suffices h : Functor.whiskerLeft (representedAffineAssociated B S hS U)
      ((representedAffineTensor B S hS U).map ((representedAffineAssociated B S hS U).map
        (r • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))))) ≫
        representedAffineUnitTensorNatTrans B S hS U =
      representedAffineUnitTensorNatTrans B S hS U ≫ representedAffineAssociatedSmul B S hS U r from
    congrArg (fun φ => φ.app N) h
  refine Stacks.EilenbergWatts.natTrans_ext_of_app_unit ?_
  change ((representedAffineTensor B S hS U).map ((representedAffineAssociated B S hS U).map
        (r • 𝟙 _))).app _ ≫ (representedAffineUnitTensorIso B S hS U _).hom =
    (representedAffineUnitTensorIso B S hS U _).hom ≫
      (representedAffineAssociated B S hS U).map (r • 𝟙 _)
  exact Stacks.SheafOfModules.Tensor.sheafTensorMap_app_comp_sheafTensorUnitIsoLeft_of_iso _
    (representedAffineAssociatedUnitIso B S hS U) _

variable (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))

/-- The functor `M ↦ Γ(M^~ ⊗ N^~)` on `R`-modules. -/
abbrev representedAffineTensorSections :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⥤
      ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  representedAffineAssociated B S hS U ⋙
    (representedAffineTensor B S hS U).flip.obj ((representedAffineAssociated B S hS U).obj N) ⋙
      representedAffineSections B S hS U

/-- The functor `M ↦ Γ(M^~ ⊗ N^~)` sends `f` to `Γ(f^~ ⊗ N^~)`. -/
theorem representedAffineTensorSections_map
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (f : M ⟶ M') :
    (representedAffineTensorSections B S hS U N).map f =
      (representedAffineSections B S hS U).map (((representedAffineTensor B S hS U).map
        ((representedAffineAssociated B S hS U).map f)).app
          ((representedAffineAssociated B S hS U).obj N)) := rfl

/-- On `Γ(R^~ ⊗ N^~)` the endomorphism induced by multiplication by `r` on `R` is multiplication
by `r`. -/
theorem representedAffineTensorSections_map_smul (r : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineTensorSections B S hS U N).map
        (r • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) =
      r • 𝟙 ((representedAffineTensorSections B S hS U N).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) := by
  have hb := congrArg (representedAffineSections B S hS U).map
    (representedAffine_map_smul_tensor B S hS U r N)
  rw [Functor.map_comp, Functor.map_comp] at hb
  have hη : (representedAffineSections B S hS U).map
      ((representedAffineAssociated B S hS U).map (r • 𝟙 N)) =
        r • 𝟙 ((representedAffineSections B S hS U).obj
          ((representedAffineAssociated B S hS U).obj N)) := by
    have h := (representedAffineAssociatedAdjunction B S hS U).unit.naturality (r • 𝟙 N)
    rw [← Iso.cancel_iso_hom_left
      (asIso ((representedAffineAssociatedAdjunction B S hS U).unit.app N)), asIso_hom]
    refine (h.symm.trans ?_)
    rw [Functor.id_map]
    ext x
    simp
  rw [hη] at hb
  rw [← Iso.cancel_iso_hom_right _ _ ((representedAffineSections B S hS U).mapIso
    (representedAffineUnitTensorIso B S hS U _)), Functor.mapIso_hom]
  refine hb.trans ?_
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

/-- `N ≅ Γ(R^~ ⊗ N^~)`, by the unit of `M ↦ M^~ ⊣ Γ` and the unit constraint. -/
def representedAffineTensorSectionsUnitIso :
    N ≅ (representedAffineTensorSections B S hS U N).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :=
  asIso ((representedAffineAssociatedAdjunction B S hS U).unit.app N) ≪≫
    (representedAffineSections B S hS U).mapIso (representedAffineUnitTensorIso B S hS U _).symm

/-- Tensoring on the right with a fixed `𝒪`-module is an additive functor. -/
instance additive_representedAffineTensor_flip_obj
    (X : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    ((representedAffineTensor B S hS U).flip.obj X).Additive where
  map_add {_ _ f g} := by
    simp only [Functor.flip_obj_map, Functor.map_add, NatTrans.app_add]

/-- The `R`-bilinear map `(a, n) ↦ H(a)(n)`, for `H(M) = Γ(M^~ ⊗ N^~)` and `a` read as the map
`R ⟶ M` it spans, through `N ≅ H(R)`. -/
def representedAffineTensorSectionsBilin
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    M →ₗ[Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)] N →ₗ[Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
      (representedAffineTensorSections B S hS U N).obj M :=
  LinearMap.mk₂ _
    (fun a n => ((representedAffineTensorSections B S hS U N).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton _ M a))).hom
        ((representedAffineTensorSectionsUnitIso B S hS U N).hom.hom n))
    (fun a₁ a₂ n => by
      simp only [LinearMap.toSpanSingleton_add, ModuleCat.ofHom_add, Functor.map_add,
        ModuleCat.hom_add, LinearMap.add_apply])
    (fun r a n => by
      have h : ModuleCat.ofHom (LinearMap.toSpanSingleton _ M (r • a)) =
          (r • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≫
            ModuleCat.ofHom (LinearMap.toSpanSingleton _ M a) := by
        ext
        simp [smul_smul]
      rw [h, Functor.map_comp, representedAffineTensorSections_map_smul]
      simp only [Linear.smul_comp, Category.id_comp]
      rfl)
    (fun a n₁ n₂ => by simp only [map_add])
    (fun r a n => by simp only [map_smul])

/-- The map `M ⊗_R N ⟶ Γ(M^~ ⊗ N^~)`, `a ⊗ n ↦ H(a)(n)`. -/
def representedAffineTensorSectionsMap
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    M ⊗ N ⟶ (representedAffineTensorSections B S hS U N).obj M :=
  ModuleCat.ofHom (X := TensorProduct Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) M N)
    (Y := (representedAffineTensorSections B S hS U N).obj M)
    (TensorProduct.lift (representedAffineTensorSectionsBilin B S hS U N M))

/-- The map `M ⊗_R N ⟶ Γ(M^~ ⊗ N^~)` sends `a ⊗ n` to `H(a)(n)`, for `H(M) = Γ(M^~ ⊗ N^~)`. -/
theorem representedAffineTensorSectionsMap_tmul
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (a : M) (n : N) :
    (representedAffineTensorSectionsMap B S hS U N M).hom (a ⊗ₜ n) =
      ((representedAffineTensorSections B S hS U N).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton _ M a))).hom
          ((representedAffineTensorSectionsUnitIso B S hS U N).hom.hom n) := rfl

/-- The map `M ⊗_R N ⟶ Γ(M^~ ⊗ N^~)` is natural in `M`. -/
theorem representedAffineTensorSectionsMap_naturality
    {M M' : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)} (f : M ⟶ M') :
    f ▷ N ≫ representedAffineTensorSectionsMap B S hS U N M' =
      representedAffineTensorSectionsMap B S hS U N M ≫
        (representedAffineTensorSections B S hS U N).map f := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun a n => ?_
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton _ M a) ≫ f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton _ M' (f.hom a)) := by
    ext
    simp
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, representedAffineTensorSectionsMap_tmul,
    representedAffineTensorSectionsMap_tmul, ← h, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]

/-- The natural map `M ⊗_R N ⟶ Γ(M^~ ⊗ N^~)`, `a ⊗ n ↦ H(a)(n)`. -/
def representedAffineTensorSectionsNatTrans :
    tensorRight N ⟶ representedAffineTensorSections B S hS U N where
  app M := representedAffineTensorSectionsMap B S hS U N M
  naturality _ _ f := representedAffineTensorSectionsMap_naturality B S hS U N f

/-- At `M = R` the map `R ⊗_R N ⟶ Γ(R^~ ⊗ N^~)` is the isomorphism `N ≅ Γ(R^~ ⊗ N^~)` after
`R ⊗_R N ≅ N`. -/
theorem representedAffineTensorSectionsNatTrans_app_unit :
    (representedAffineTensorSectionsNatTrans B S hS U N).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) =
      (λ_ N).hom ≫ (representedAffineTensorSectionsUnitIso B S hS U N).hom := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun a n => ?_
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton _ (ModuleCat.of Γ((BigFppfOver.toScheme
      B S hS).obj U, ⊤) Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) a) =
      a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) := by
    ext
    simp [mul_comm]
  change (representedAffineTensorSectionsMap B S hS U N _).hom (a ⊗ₜ n) = _
  rw [representedAffineTensorSectionsMap_tmul, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply, h, representedAffineTensorSections_map_smul,
    map_smul]
  rfl

/-- At `M = R` the map `R ⊗_R N ⟶ Γ(R^~ ⊗ N^~)` is an isomorphism. -/
instance isIso_representedAffineTensorSectionsNatTrans_app_unit :
    IsIso ((representedAffineTensorSectionsNatTrans B S hS U N).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) := by
  rw [representedAffineTensorSectionsNatTrans_app_unit]
  infer_instance

/-- The comparison `(M ⊗_R N)^~ ⟶ M^~ ⊗ N^~`, adjoint to `a ⊗ n ↦ H(a)(n)` through the
counit at the quasi-coherent module `M^~ ⊗ N^~`. -/
def representedAffineAssociatedTensorHom :
    tensorRight N ⋙ representedAffineAssociated B S hS U ⟶
      representedAffineAssociated B S hS U ⋙
        (representedAffineTensor B S hS U).flip.obj
          ((representedAffineAssociated B S hS U).obj N) where
  app M := (representedAffineAssociated B S hS U).map
      ((representedAffineTensorSectionsNatTrans B S hS U N).app M) ≫
    (representedAffineAssociatedAdjunction B S hS U).counit.app _
  naturality M M' f := by
    have h1 := congrArg (representedAffineAssociated B S hS U).map
      ((representedAffineTensorSectionsNatTrans B S hS U N).naturality f)
    have h2 := (representedAffineAssociatedAdjunction B S hS U).counit.naturality
      (((representedAffineTensor B S hS U).flip.obj
        ((representedAffineAssociated B S hS U).obj N)).map
          ((representedAffineAssociated B S hS U).map f))
    rw [Functor.map_comp, Functor.map_comp] at h1
    rw [Functor.comp_map, ← Category.assoc, h1, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) h2

/-- The tensor product `M^~ ⊗ N^~` of two associated modules is quasi-coherent. -/
theorem isQuasicoherentOnSite_representedAffineTensor_obj
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (((representedAffineTensor B S hS U).obj ((representedAffineAssociated B S hS U).obj M)).obj
      ((representedAffineAssociated B S hS U).obj N)).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.DerivedTensorProduct.isQuasicoherentOnSite_sheafTensor
    (X := smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) _ _
    (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U M)
    (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U N)

/-- The comparison `(M ⊗_R N)^~ ⟶ M^~ ⊗ N^~` is an isomorphism. -/
instance isIso_representedAffineAssociatedTensorHom :
    IsIso (representedAffineAssociatedTensorHom B S hS U N) := by
  have := (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  have := Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O
    ((representedAffineAssociated B S hS U).obj N)
  have : PreservesColimitsOfSize.{u, u}
      (tensorRight N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⥤ _) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have : IsIso ((representedAffineAssociatedTensorHom B S hS U N).app
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) := by
    have hc := isIso_representedAffineAssociatedAdjunction_counit_app_tensor B S hS U _
      (isQuasicoherentOnSite_representedAffineTensor_obj B S hS U N
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hc
  have : ∀ M, IsIso ((representedAffineAssociatedTensorHom B S hS U N).app M) :=
    Stacks.EilenbergWatts.isIso_app_of_isIso_app_unit _
  exact NatIso.isIso_of_isIso_app _

/-- **The associated module of a tensor product.**  For an `R`-module `N`,
`(M ⊗_R N)^~ ≅ M^~ ⊗_𝒪 N^~` naturally in the `R`-module `M`, on the small étale site of the
affine algebraic space `yoneda.obj U`. -/
def representedAffineAssociatedTensorIso :
    tensorRight N ⋙ representedAffineAssociated B S hS U ≅
      representedAffineAssociated B S hS U ⋙
        (representedAffineTensor B S hS U).flip.obj
          ((representedAffineAssociated B S hS U).obj N) :=
  asIso (representedAffineAssociatedTensorHom B S hS U N)

/-! ### Flatness -/

section Flat

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

omit N in
/-- The associated module of a projective `R`-module is flat. -/
theorem isFlat_representedAffineAssociated_obj_of_projective
    (P : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) [Projective P] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O)
      ((representedAffineAssociated B S hS U).obj P) := by
  have := (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  set X := smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  have hsum : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := X.O)
      ((representedAffineAssociated B S hS U).obj
        (∐ fun _ : P => ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) := by
    refine Stacks.SheafOfModules.FlatRetract.isFlat_of_iso X.O
      (PreservesCoproduct.iso (representedAffineAssociated B S hS U) _).symm ?_
    refine Stacks.SheafOfModules.FlatColimits.isFlat_coproduct (J := X.J) (O := X.O) _ fun _ => ?_
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso X.O
      (representedAffineAssociatedUnitIso B S hS U).symm
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := X))
  refine Stacks.SheafOfModules.FlatRetract.isFlat_of_retract X.O
    ((representedAffineAssociated B S hS U).map
      (Projective.factorThru (𝟙 P) (Stacks.EilenbergWatts.freeCover P)))
    ((representedAffineAssociated B S hS U).map (Stacks.EilenbergWatts.freeCover P)) ?_ hsum
  rw [← Functor.map_comp, Projective.factorThru_comp, CategoryTheory.Functor.map_id]

omit N in
/-- **The associated module of a flat `R`-module is flat.** -/
theorem isFlat_representedAffineAssociated_obj
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    [Module.Flat Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) M] :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O)
      ((representedAffineAssociated B S hS U).obj M) := by
  have := (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  set X := smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
  obtain ⟨ι, _, _, _, _, G, _, _, f, _, hfree, -, ⟨e⟩⟩ :=
    flat_exists_directLimit_free_finite (R := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) M
  have hc := isColimitOfPreserves (representedAffineAssociated B S hS U)
    (ModuleCat.directLimitIsColimit G f)
  have hG : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := X.O)
      (((ModuleCat.directLimitDiagram G f) ⋙ representedAffineAssociated B S hS U).obj i) :=
    fun i =>
      have : Projective ((ModuleCat.directLimitDiagram G f).obj i) :=
        ModuleCat.projective_of_free
          (M := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (G i))
          (Module.Free.chooseBasis Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (G i))
      isFlat_representedAffineAssociated_obj_of_projective B S hS U _
  refine Stacks.SheafOfModules.FlatRetract.isFlat_of_iso X.O
    ((IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc) ≪≫
      (representedAffineAssociated B S hS U).mapIso e.toModuleIso) ?_
  exact Stacks.SheafOfModules.FlatColimits.isFlat_colimit (J := X.J) (O := X.O) _ hG

end Flat

end AlgebraicGeometry.Space

end
