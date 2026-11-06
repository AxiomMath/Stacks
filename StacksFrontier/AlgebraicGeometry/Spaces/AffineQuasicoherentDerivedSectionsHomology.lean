module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel

/-!
# Derived sections of a represented affine algebraic space are t-exact on `D_QCoh`

Let `U` be an object of the big fppf site with affine underlying scheme, `R = Γ(U)`, and `E` an
object of `D_QCoh(𝒪_{h_U})`. Then `Hⁱ(RΓ(E))` is the module of sections of `Hⁱ(E)`, that is,
`Hⁱ(RΓ(E)) ≅ Γ(Hⁱ(E))` as `R`-modules.

## Main results

* `AlgebraicGeometry.Space.representedAffineDerivedSectionsHomologyIso`.
* `AlgebraicGeometry.Space.epi_representedAffineSections_map`: the sections functor is exact on
  quasi-coherent modules.
* `AlgebraicGeometry.Space.moduleFinite_representedAffineSections`: a quasi-coherent module whose
  sections over a final affine chart are finite over the ring of that chart has finite module of
  sections over `R`.

## Implementation notes

`E` is the associated object `Φ(RΓ(E))` by the counit of `Φ ⊣ RΓ`, the cohomology of `Φ(M)` is
the associated module of the cohomology of `M` since `Φ` is induced by an exact functor, and the
unit of the adjunction between associated modules and sections is invertible, the associated
module functor being fully faithful.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The unit of the adjunction between associated modules and sections is invertible. -/
instance isIso_representedAffineAssociatedAdjunction_unit :
    IsIso (representedAffineAssociatedAdjunction B S hS U).unit := by
  have := (representedAffineAssociatedFullyFaithful B S hS U).full
  have := (representedAffineAssociatedFullyFaithful B S hS U).faithful
  exact (representedAffineAssociatedAdjunction B S hS U).unit_isIso_of_L_fully_faithful

/-- **The derived sections of a represented affine algebraic space are t-exact on `D_QCoh`**:
`Hⁱ(RΓ(E)) ≅ Γ(Hⁱ(E))` for `E` with quasi-coherent cohomology sheaves. -/
def representedAffineDerivedSectionsHomologyIso
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ((representedAffineDerivedSections B S hS U).obj E) ≅
      (representedAffineSections B S hS U).obj ((DerivedCategory.homologyFunctor _ i).obj E) :=
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hE
  let M := (representedAffineDerivedSections B S hS U).obj E
  let c : (representedAffineDerivedAssociated B S hS U).obj M ≅ E :=
    asIso ((representedAffineDerivedAdjunction B S hS U).counit.app E)
  (asIso ((representedAffineAssociatedAdjunction B S hS U).unit.app
      ((DerivedCategory.homologyFunctor _ i).obj M))) ≪≫
    (representedAffineSections B S hS U).mapIso
      (((representedAffineAssociated B S hS U).mapDerivedCategoryHomologyIso i).app M).symm ≪≫
    (representedAffineSections B S hS U).mapIso ((DerivedCategory.homologyFunctor _ i).mapIso c)

/-- The sections functor, restricted to quasi-coherent modules, is the inverse of the equivalence
`Mod(R) ≌ QCoh(𝒪_{h_U})`. -/
def representedAffineAssocInverseIso :
    (representedAffineAssoc B S hS U).inverse ≅
      ObjectProperty.ι _ ⋙ representedAffineSections B S hS U :=
  (representedAffineAssoc B S hS U).toAdjunction.rightAdjointUniq
    (Adjunction.restrictFullyFaithful (representedAffineAssociatedAdjunction B S hS U)
      (Functor.FullyFaithful.id _) (ObjectProperty.fullyFaithfulι _)
      (Functor.leftUnitor _ ≪≫ (representedAffineAssociatedIso B S hS U).symm)
      (Functor.rightUnitor _).symm)

/-- **The sections functor is exact on quasi-coherent modules**: it carries an epimorphism of
quasi-coherent modules to a surjection. -/
theorem epi_representedAffineSections_map
    {M N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
    (g : M ⟶ N) [Epi g] (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    Epi ((representedAffineSections B S hS U).map g) := by
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).O))
  let g' : (⟨M, hM⟩ : P.FullSubcategory) ⟶ ⟨N, hN⟩ := ObjectProperty.homMk g
  have : Epi g' := (ObjectProperty.ι P).epi_of_epi_map ‹Epi g›
  have h := NatIso.naturality_1 (representedAffineAssocInverseIso B S hS U) g'
  have : (representedAffineAssoc B S hS U).inverse.IsLeftAdjoint :=
    (representedAffineAssoc B S hS U).symm.toAdjunction.isLeftAdjoint
  have := Functor.preservesEpimorphisms_of_isLeftAdjoint (representedAffineAssoc B S hS U).inverse
  have h₁ : Epi ((representedAffineAssoc B S hS U).inverse.map g') := Functor.map_epi _ _
  show Epi ((ObjectProperty.ι P ⋙ representedAffineSections B S hS U).map g')
  rw [← h]
  exact @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _
    (@epi_comp _ _ _ _ _ _ h₁ _ (IsIso.epi_of_iso _))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- Generators of the sections of a quasi-coherent module `N` over a final affine chart `T` give an
epimorphism from a finite free module onto `N`. -/
theorem epi_freeHomEquiv_symm_of_span_eq_top
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) (T : SmallEtale B S hS (yoneda.obj U)) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS (yoneda.obj U) T) {k : ℕ} (g : Fin k → N.val.obj (op T))
    (hg : Submodule.span (chartRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) T)
      (Set.range g) = ⊤) :
    Epi (N.freeHomEquiv.symm fun j : ULift.{u} (Fin k) =>
      (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hT).symm (g j.down)) := by
  let s : ULift.{u} (Fin k) → N.sections := fun j =>
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hT).symm (g j.down)
  have hφj : ∀ j, SheafOfModules.ιFree j ≫ N.freeHomEquiv.symm s = N.unitHomEquiv.symm (s j) :=
    fun j => by
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
  refine epi_of_surjective_val_app_of_isAffine
    (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) B S hS _ fun W hW => ?_
  rw [← LinearMap.range_eq_top, eq_top_iff]
  have hspan := (chartBaseChange_surjective_iff_span_eq_top N (hT.from W)).1
    ((isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) N hN) T W hTa hW (hT.from W)).2
  rw [← hspan, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (show y ∈ Submodule.span _ (Set.range g) by rw [hg]; trivial)
  show chartRestrictLinear N (hT.from W) (∑ i, c i • g i) ∈ _
  rw [map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [chartRestrictLinear_smul]
  refine ⟨((SheafOfModules.ιFree (R := (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O))
      (ULift.up j)).val.app (op W)).hom (chartRestrict (hT.from W) (c j)), ?_⟩
  have h₁ := congrArg (fun f => (f.val.app (op W)).hom (chartRestrict (hT.from W) (c j)))
    (hφj (ULift.up j))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply] at h₁
  exact h₁.trans (unitHomEquiv_symm_val_app (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    B S hS (s (ULift.up j)) (op W) _)

/-- **Finiteness of the sections of a quasi-coherent module on an affine represented space.** If
the sections of a quasi-coherent module `N` over a final affine chart `T` are a finite module over
the ring of `T`, then its module of sections over `R` is finite.

Generators over `T` give a map from a finite free module, surjective on the sections over every
affine chart by the base change property of quasi-coherent modules, hence an epimorphism; the
sections functor is exact on quasi-coherent modules, and the sections of the finite free module
are `R^n`. -/
theorem moduleFinite_representedAffineSections
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) (T : SmallEtale B S hS (yoneda.obj U)) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS (yoneda.obj U) T)
    (hfin : Module.Finite (chartRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) T)
      (N.val.obj (op T))) :
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((representedAffineSections B S hS U).obj N) := by
  classical
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := chartRing B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) T) (M := N.val.obj (op T))
  let φ : SheafOfModules.free (ULift.{u} (Fin k)) ⟶ N := N.freeHomEquiv.symm fun j =>
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hT).symm (g j.down)
  have hφ : Epi φ := epi_freeHomEquiv_symm_of_span_eq_top B S hS U N hN T hT hTa g hg
  let C : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    ∐ fun _ : ULift.{u} (Fin k) => ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let D := (representedAffineAssociated B S hS U).obj C
  let eD := representedAffineAssociatedSigmaUnitIso (B := B) (S := S) (hS := hS) (U := U) k
  have : Epi (eD.hom ≫ φ) :=
    epi_comp' (@IsIso.epi_of_iso _ _ _ _ eD.hom (Iso.isIso_hom eD)) hφ
  let eR : C ≅ (representedAffineSections B S hS U).obj D :=
    asIso ((representedAffineAssociatedAdjunction B S hS U).unit.app _)
  have : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) C :=
    Module.Finite.equiv ((ModuleCat.coprodIsoDirectSum _).toLinearEquiv.trans
      (DirectSum.linearEquivFunOnFintype _ _ _)).symm
  have : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((representedAffineSections B S hS U).obj D) := Module.Finite.equiv eR.toLinearEquiv
  exact Module.Finite.of_surjective _ ((ModuleCat.epi_iff_surjective _).1
    (epi_representedAffineSections_map B S hS U (eD.hom ≫ φ)
      (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U _) hN))

end AlgebraicGeometry.Space

end
