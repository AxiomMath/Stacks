module

public import StacksFrontier.AlgebraicGeometry.ProEtale.BoundedLocallyConstantReduction
public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantSheafMaps
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ConstantSheafGenerators
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionTower
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.BoundedAboveShriekComplex
import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
import StacksFrontier.Algebra.Homology.DerivedCategory.SingleExtension
import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantClopenPieces
import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantDerivedCompletion
import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteProetale
import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSectionsCriterion
import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Monoidal
import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.TopDegree
import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes
import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# Complexes of completed constant sheaves on a weakly contractible affine scheme

Let `X` be an affine scheme which is weakly contractible, `Λ` a Noetherian ring and `I ⊆ Λ` an
ideal. Let `K` be an object of the derived category of sheaves of `Λ`-modules on `X_proét`
satisfying `AlgebraicGeometry.ProEtale.HasBoundedLocallyConstantReduction X Λ I K a b`: `K` is
derived complete, has cohomology in `[a, b]`, its reduction `K ⊗_Λ^L \underline{Λ/I}` has Tor
amplitude in `[a, b]` and locally constant cohomology sheaves of finite type. Such a `K` is
represented by a complex of completed constant sheaves.

## Main results

* `AlgebraicGeometry.ProEtale.exists_distTriang_hasBoundedLocallyConstantReduction`: for `a < b`,
  a distinguished triangle `(\underline{Λ}^∧)^{⊕ t}[-b] ⟶ K ⟶ L ⟶ ⋯` with `L` satisfying the
  condition on `[a, b - 1]`.
* `AlgebraicGeometry.ProEtale.exists_complex_of_hasBoundedLocallyConstantReduction`: a complex
  `C` in degrees `[a, b]` representing `K` whose terms in degrees `≠ a` are finite sums of copies
  of `\underline{Λ}^∧`.

## References

* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
* [Stacks Project, Tag 09BY](https://stacks.math.columbia.edu/tag/09BY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Pretriangulated

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Sheaf.symmetricCategory Stacks.ModuleSheaf.derivedMonoidal Stacks.ModuleSheaf.derivedSymmetric

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ] {I : Ideal Λ}

section Quotient

variable {R : Type*} [CommRing R] (J : Ideal R)

/-- The quotient map `R → R/J`, as a map of `R`-modules into `R/J` read over `R`. -/
def unitModuleToQuotient :
    Functor.unitModule R ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj
      (ModuleCat.of (R ⧸ J) (R ⧸ J)) :=
  ModuleCat.ofHom
    { toFun := Ideal.Quotient.mk J
      map_add' := map_add _
      map_smul' := fun r x => map_mul (Ideal.Quotient.mk J) r x }

/-- The quotient map `R → R/J` is surjective. -/
theorem surjective_unitModuleToQuotient : Function.Surjective (unitModuleToQuotient J) :=
  Ideal.Quotient.mk_surjective

end Quotient

variable [IsNoetherianRing Λ]

variable (X Λ I) in
/-- The reduction `\underline{Λ} ⟶ \underline{Λ/I}` of constant sheaves of `Λ`-modules on
`X_proét`. -/
def constantSheafToQuotientConstantSheaf :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
      (Functor.unitModule Λ) ⟶ quotientConstantSheaf X Λ I :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map
    (unitModuleToQuotient I)

/-- The reduction `\underline{Λ} ⟶ \underline{Λ/I}` of constant sheaves is an epimorphism. -/
instance epi_constantSheafToQuotientConstantSheaf :
    Epi (constantSheafToQuotientConstantSheaf X Λ I) := by
  have : Epi (unitModuleToQuotient I) :=
    (ModuleCat.epi_iff_surjective _).2 (surjective_unitModuleToQuotient I)
  have : Epi ((Functor.const (Scheme.ProEt X)ᵒᵖ).map (unitModuleToQuotient I)) :=
    NatTrans.epi_of_epi_app _
  exact (presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).map_epi _

variable (X Λ I) in
/-- The map `𝟙 ≅ \underline{Λ}[0] ⟶ \underline{Λ/I}[0]` in the derived category of sheaves of
`Λ`-modules on `X_proét`. -/
def derivedUnitToQuotientConstantSheaf :
    𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I) :=
  (Stacks.ModuleSheaf.derivedTensorUnitIso _ Λ).hom ≫
    (DerivedCategory.singleFunctor _ 0).map (constantSheafToQuotientConstantSheaf X Λ I)

omit [IsNoetherianRing Λ] in
/-- **The reduction is surjective on top cohomology.** If `K` lies in degrees `≤ b`, the
reduction `K ⟶ K ⊗_Λ^L \underline{Λ/I}` is an epimorphism on `H^b`. -/
theorem epi_homologyFunctor_map_derivedUnitToQuotientConstantSheaf
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) (b : ℤ)
    [K.IsLE b] :
    Epi ((DerivedCategory.homologyFunctor _ b).map
      ((ρ_ K).inv ≫ K ◁ derivedUnitToQuotientConstantSheaf X Λ I)) := by
  obtain ⟨e⟩ := Stacks.ModuleSheaf.nonempty_homology_tensor_single_natIso_of_isLE K b
  let := Stacks.ModuleSheaf.monoidalClosed (Scheme.ProEt.topology X) Λ
  have h : (DerivedCategory.homologyFunctor _ b).map
      (K ◁ (DerivedCategory.singleFunctor _ 0).map (constantSheafToQuotientConstantSheaf X Λ I)) =
      e.hom.app _ ≫ (tensorLeft _).map (constantSheafToQuotientConstantSheaf X Λ I) ≫
        e.inv.app _ := by
    rw [← Category.assoc, ← e.hom.naturality]
    simp
  have : Epi ((tensorLeft ((DerivedCategory.homologyFunctor _ b).obj K)).map
      (constantSheafToQuotientConstantSheaf X Λ I)) := Functor.map_epi _ _
  rw [derivedUnitToQuotientConstantSheaf, MonoidalCategory.whiskerLeft_comp, Functor.map_comp,
    Functor.map_comp, h]
  refine @epi_comp _ _ _ _ _ _ inferInstance _
    (@epi_comp _ _ _ _ _ _ inferInstance _ (@epi_comp _ _ _ _ _ _ inferInstance _
      (@epi_comp _ _ _ _ _ _ this _ inferInstance)))


variable (I) in
/-- The reduction `K ≅ K ⊗_Λ^L \underline{Λ} ⟶ K ⊗_Λ^L \underline{Λ/I}` of an object of the
derived category of sheaves of `Λ`-modules on `X_proét`. -/
def toTensorQuotientConstantSheaf
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) :
    K ⟶ K ⊗ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I) :=
  (ρ_ K).inv ≫ K ◁ derivedUnitToQuotientConstantSheaf X Λ I

omit [IsNoetherianRing Λ] in
/-- The reduction `K ⟶ K ⊗_Λ^L \underline{Λ/I}` is natural in `K`. -/
theorem toTensorQuotientConstantSheaf_naturality
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
    (g : K ⟶ K') :
    g ≫ toTensorQuotientConstantSheaf I K' =
      toTensorQuotientConstantSheaf I K ≫ g ▷ _ := by
  rw [toTensorQuotientConstantSheaf, toTensorQuotientConstantSheaf, Category.assoc,
    whisker_exchange, rightUnitor_inv_naturality_assoc]

variable {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
  {a b : ℤ}

omit [IsNoetherianRing Λ] in
/-- Under the condition on `[a, b]`, `K` lies in degrees `≤ b`. -/
theorem HasBoundedLocallyConstantReduction.isLE
    (hK : HasBoundedLocallyConstantReduction X Λ I K a b) :
    K.IsLE b := by
  rw [DerivedCategory.isLE_iff]
  exact fun i hi => hK.2.1 i fun h => by have := h.2; omega

/-- Under the condition on `[a, b]`, `K` is derived complete along `I` as an object of the
`Λ`-linear derived category of sheaves of `Λ`-modules. -/
theorem HasBoundedLocallyConstantReduction.isDerivedComplete
    (hK : HasBoundedLocallyConstantReduction X Λ I K a b) : IsDerivedComplete I K :=
  DerivedCompleteRecurrence.isDerivedComplete_of_iso
    ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).unitIso.app K).symm
    (isDerivedComplete_derivedModuleEquiv_inverse_obj X I hK.1)

omit [IsNoetherianRing Λ] in
/-- **Lifting generators of the top cohomology of the reduction.** On a weakly contractible
affine `X`, if `K` satisfies the condition on `[a, b]`, there is a map
`\underline{Λ}^{⊕ t}[-b] ⟶ K` which is surjective on `H^b(- ⊗_Λ^L \underline{Λ/I})`. -/
theorem HasBoundedLocallyConstantReduction.exists_singleFunctor_hom_epi [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
    (hK : HasBoundedLocallyConstantReduction X Λ I K a b) :
    ∃ (t : ℕ) (s : (DerivedCategory.singleFunctor _ b).obj (⨁ fun _ : Fin t =>
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
          (Functor.unitModule Λ)) ⟶ K),
      Epi ((DerivedCategory.homologyFunctor _ b).map
        (s ▷ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I))) := by
  have := hK.isLE
  obtain ⟨t, φ, hφ⟩ := exists_epi_biproduct_constantSheaf_of_isFiniteTypeLocallyConstant hX
    (hK.2.2.2 b)
  have := projective_constantSheaf_unitModule (Λ := Λ) hX
  let P := ⨁ fun _ : Fin t => (constantSheaf (Scheme.ProEt.topology X)
    (ModuleCat.{max (u + 1) w} Λ)).obj (Functor.unitModule Λ)
  have : Projective P := ⟨fun f e _ => ⟨biproduct.desc fun i =>
    Projective.factorThru (biproduct.ι (fun _ : Fin t => (constantSheaf
      (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj (Functor.unitModule Λ)) i ≫ f) e,
    biproduct.hom_ext' _ _ fun i => by simp⟩⟩
  have : Epi ((DerivedCategory.homologyFunctor _ b).map (toTensorQuotientConstantSheaf I K)) :=
    epi_homologyFunctor_map_derivedUnitToQuotientConstantSheaf K b
  let τ := Projective.factorThru φ
    ((DerivedCategory.homologyFunctor _ b).map (toTensorQuotientConstantSheaf I K))
  obtain ⟨s, hs⟩ := (DerivedCategory.bijective_homologyFromSingle_of_projective P K b).2 τ
  refine ⟨t, s, ?_⟩
  have h : (((DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).inv.app P ≫
      (DerivedCategory.homologyFunctor _ b).map (toTensorQuotientConstantSheaf I _)) ≫
        (DerivedCategory.homologyFunctor _ b).map (s ▷ _)) = φ := by
    rw [Category.assoc, ← Functor.map_comp, ← toTensorQuotientConstantSheaf_naturality,
      Functor.map_comp, ← Category.assoc, ← DerivedCategory.homologyFromSingle_apply, hs,
      Projective.factorThru_comp]
  exact @epi_of_epi _ _ _ _ _ _ _ (h ▸ hφ)

/-- **Extending a map from `\underline{Λ}^{⊕ t}[-b]` to the completion.** A map
`\underline{Λ}^{⊕ t}[-b] ⟶ K` into a derived complete `K` factors through
`(\underline{Λ}^∧)^{⊕ t}[-b]`. -/
theorem exists_singleFunctor_biproduct_completedConstantSheaf_hom (b : ℤ) {t : ℕ}
    (hK : IsDerivedComplete I K)
    (s : (DerivedCategory.singleFunctor _ b).obj (⨁ fun _ : Fin t =>
        (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
          (Functor.unitModule Λ)) ⟶ K) :
    ∃ ŝ : (DerivedCategory.singleFunctor _ b).obj
        (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⟶ K,
      (DerivedCategory.singleFunctor _ b).map
        (biproduct.map fun _ => completedConstantSheafMap X I) ≫ ŝ = s := by
  let F := DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) b
  let cΛ := (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
    (Functor.unitModule Λ)
  choose ŝ hŝ using fun i : Fin t =>
    (bijective_comp_singleFunctor_map_completedConstantSheafMap b K hK).2
      (F.map (biproduct.ι (fun _ : Fin t => cΛ) i) ≫ s)
  let L := completedConstantSheaf X Λ I (Functor.unitModule Λ)
  have hι : ∀ i, F.map (biproduct.ι (fun _ : Fin t => L) i) ≫
      (F.mapBiproduct (fun _ : Fin t => L)).hom = biproduct.ι (F.obj ∘ fun _ : Fin t => L) i :=
    fun i => by
    rw [← cancel_mono (F.mapBiproduct (fun _ : Fin t => L)).inv, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Functor.mapBiproduct_inv, biproduct.ι_desc]
  refine ⟨(F.mapBiproduct _).hom ≫ biproduct.desc ŝ, ?_⟩
  rw [← cancel_epi (F.mapBiproduct (fun _ : Fin t => cΛ)).inv]
  ext i
  rw [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, biproduct.ι_desc_assoc,
    ← F.map_comp_assoc, biproduct.ι_map, F.map_comp_assoc, reassoc_of% hι, biproduct.ι_desc]
  exact hŝ i

/-- **The completed constant sheaf against sheaves killed by `I`.** For a sheaf `N` of
`Λ`-modules killed by `I`, `\underline{Λ}^∧ ⊗_Λ^L N ≅ N`. -/
theorem nonempty_singleFunctor_completedConstantSheaf_tensor_iso
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hN : ∀ x ∈ I, x • 𝟙 N = 0) :
    Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        (completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⊗
          (DerivedCategory.singleFunctor _ 0).obj N ≅
        (DerivedCategory.singleFunctor _ 0).obj N) := by
  have := isIso_whiskerRight_singleFunctor_map_completedConstantSheafMap 0 N hN
  exact ⟨(asIso ((DerivedCategory.singleFunctor _ 0).map (completedConstantSheafMap X I) ▷
      (DerivedCategory.singleFunctor _ 0).obj N)).symm ≪≫
    whiskerRightIso (Stacks.ModuleSheaf.derivedTensorUnitIso _ Λ).symm _ ≪≫ λ_ _⟩

/-- **Finite sums of completed constant sheaves against sheaves killed by `I`.** For a sheaf `N`
of `Λ`-modules killed by `I`, `(\underline{Λ}^∧)^{⊕ t}[-b] ⊗_Λ^L N ≅ N^{⊕ t}[-b]`. -/
theorem nonempty_singleFunctor_biproduct_completedConstantSheaf_tensor_iso (b : ℤ) (t : ℕ)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hN : ∀ x ∈ I, x • 𝟙 N = 0) :
    Nonempty ((DerivedCategory.singleFunctor _ b).obj
        (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⊗
          (DerivedCategory.singleFunctor _ 0).obj N ≅
      (DerivedCategory.singleFunctor _ b).obj (⨁ fun _ : Fin t => N)) := by
  obtain ⟨e⟩ := nonempty_singleFunctor_completedConstantSheaf_tensor_iso N hN
  obtain ⟨e₀⟩ := Stacks.ModuleSheaf.nonempty_singleFunctor_tensor_iso_shift
    (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ))
    ((DerivedCategory.singleFunctor _ 0).obj N) b
  obtain ⟨s, hs⟩ := Stacks.ModuleSheaf.exists_commShift_isTriangulated_tensorRight _ Λ
    ((DerivedCategory.singleFunctor _ 0).obj N)
  let := s
  let F₀ := DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) 0
  let e₁ : F₀.obj (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⊗
      F₀.obj N ≅ F₀.obj (⨁ fun _ : Fin t => N) :=
    whiskerRightIso (F₀.mapBiproduct _) _ ≪≫ (tensorRight (F₀.obj N)).mapBiproduct _ ≪≫
      biproduct.mapIso (fun _ => e) ≪≫ (F₀.mapBiproduct _).symm
  exact ⟨e₀ ≪≫ (shiftFunctor _ (-b)).mapIso e₁ ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso (-b) b 0 (by omega)).app _⟩

/-- For a sheaf `N` killed by `I`, `(\underline{Λ}^∧)^{⊕ t}[-b] ⊗_Λ^L N` has no cohomology outside
degree `b`. -/
theorem isZero_homology_singleFunctor_biproduct_completedConstantSheaf_tensor (b : ℤ) (t : ℕ)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hN : ∀ x ∈ I, x • 𝟙 N = 0) {i : ℤ} (hi : i ≠ b) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj ((DerivedCategory.singleFunctor _ b).obj
        (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⊗
          (DerivedCategory.singleFunctor _ 0).obj N)) := by
  obtain ⟨e⟩ := nonempty_singleFunctor_biproduct_completedConstantSheaf_tensor_iso b t N hN
  exact (Stacks.Homology.isZero_homologyFunctor_obj_singleFunctor_obj _ b i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e)

variable (X Λ I) in
omit [IsNoetherianRing Λ] in
/-- A finite sum of copies of `\underline{Λ/I}` is locally constant of finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_biproduct_quotientConstantSheaf (t : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
      max (u + 1) w, max (u + 1) w} (Scheme.ProEt.topology X) Λ
      (⨁ fun _ : Fin t => quotientConstantSheaf X Λ I) := by
  let M := (ModuleCat.restrictScalars.{max (u + 1) w} (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I))
  have : Module.Finite Λ M :=
    Module.Finite.of_surjective (unitModuleToQuotient I).hom (surjective_unitModuleToQuotient I)
  have : Module.Finite Λ (ModuleCat.of Λ (Fin t → M)) :=
    inferInstanceAs (Module.Finite Λ (Fin t → M))
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_constant _ _
    (E := ModuleCat.of Λ (Fin t → M)) this
    ((constantSheaf _ _).mapIso (ModuleCat.biproductIsoPi fun _ : Fin t => M).symm ≪≫
      (constantSheaf _ _).mapBiproduct _)

/-- The cohomology sheaves of `(\underline{Λ}^∧)^{⊕ t}[-b] ⊗_Λ^L \underline{Λ/I}` are locally
constant of finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_singleFunctor_biproduct_tensor
    (b : ℤ) (t : ℕ) (i : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
      max (u + 1) w, max (u + 1) w} (Scheme.ProEt.topology X) Λ
      ((DerivedCategory.homologyFunctor _ i).obj ((DerivedCategory.singleFunctor _ b).obj
        (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⊗
          (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I))) := by
  obtain ⟨e⟩ := nonempty_singleFunctor_biproduct_completedConstantSheaf_tensor_iso b t
    (quotientConstantSheaf X Λ I) fun _ hx => smul_id_quotientConstantSheaf_eq_zero I X hx
  refine ObjectProperty.prop_of_iso _ ((DerivedCategory.homologyFunctor _ i).mapIso e).symm ?_
  by_cases hi : i = b
  · subst hi
    exact ObjectProperty.prop_of_iso _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ i).app _).symm
      (isFiniteTypeLocallyConstantModuleSheaf_biproduct_quotientConstantSheaf X Λ I t)
  · exact ObjectProperty.prop_of_isZero _
      (Stacks.Homology.isZero_homologyFunctor_obj_singleFunctor_obj _ b i hi)

/-- A finite sum of copies of `\underline{Λ}^∧`, read over the constant ring sheaf
`\underline{Λ}`, is derived complete along `I·\underline{Λ}`. -/
theorem isDerivedComplete_constantCoefficientModuleEquiv_biproduct_completedConstantSheaf
    (t : ℕ) :
    RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj
          (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)))) := by
  have hI : I.FG := IsNoetherian.noetherian I
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let F := completedConstantCoefficientSheafFunctor.{u, max (u + 1) w, w} X Λ I
  let e : F.obj (⨁ fun _ : Fin t => Functor.unitModule Λ) ≅
      E.functor.obj (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) :=
    F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ =>
        ((constantCoefficientModuleEquivFunctorIso.{u, max (u + 1) w, w} X Λ).app _).symm) ≪≫
      (E.functor.mapBiproduct _).symm
  exact (RingedSite.isDerivedComplete_iff_of_iso _ _
    ((DerivedCategory.singleFunctor _ 0).mapIso e)).1
      (isDerivedComplete_completedConstantCoefficientSheaf X I hI _)

/-- `(\underline{Λ}^∧)^{⊕ t}[-b]` is derived complete along `I·\underline{Λ}`. -/
theorem isDerivedComplete_singleFunctor_biproduct_completedConstantSheaf (b : ℤ) (t : ℕ) :
    RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj
        ((DerivedCategory.singleFunctor _ b).obj
          (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)))) := by
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let P : ObjectProperty (RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)) := fun F =>
    RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj F)
  have : P.IsWeakSerreClass := derivedCompleteSheaves_isWeakSerreClass.{u, max (u + 1) w, w} X Λ
    (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
  let G := ⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)
  refine (isDerivedComplete_iff_homology.{u, max (u + 1) w, w} X Λ _ _).2 fun p => ?_
  let eH : (DerivedCategory.homologyFunctor _ p).obj
      (E.functor.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ b).obj G)) ≅
      E.functor.obj ((DerivedCategory.homologyFunctor _ p).obj
        ((DerivedCategory.singleFunctor _ b).obj G)) :=
    (E.functor.mapDerivedCategoryHomologyIso p).app _
  show P _
  by_cases hp : p = b
  · subst hp
    exact ObjectProperty.prop_of_iso P (E.functor.mapIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ p).app G).symm ≪≫ eH.symm)
      (isDerivedComplete_constantCoefficientModuleEquiv_biproduct_completedConstantSheaf t)
  · exact ObjectProperty.prop_of_isZero P (IsZero.of_iso
      (E.functor.map_isZero (Stacks.Homology.isZero_homologyFunctor_obj_singleFunctor_obj _ b p hp))
      eH)


omit [IsNoetherianRing Λ] in
/-- Derived completeness along `I·\underline{Λ}` passes to the third vertex of a distinguished
triangle in the derived category of sheaves of `Λ`-modules. -/
theorem isDerivedComplete_derivedModuleEquiv_functor_obj₃_of_distTriang
    (T : Triangle (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} Λ)))) (hT : T ∈ distTriang _)
    (h₁ : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj T.obj₁))
    (h₂ : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj T.obj₂)) :
    RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj T.obj₃) := by
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let P : ObjectProperty (RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)) := fun F =>
    RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj F)
  have : P.IsWeakSerreClass := derivedCompleteSheaves_isWeakSerreClass.{u, max (u + 1) w, w} X Λ
    (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
  let F := E.functor.mapDerivedCategory
  have hT' : F.mapTriangle.obj T ∈ distTriang _ := F.map_distinguished T hT
  have h₁' : ∀ i, P ((DerivedCategory.homologyFunctor _ i).obj (F.obj T.obj₁)) :=
    (isDerivedComplete_iff_homology.{u, max (u + 1) w, w} X Λ _ _).1 h₁
  have h₂' : ∀ i, P ((DerivedCategory.homologyFunctor _ i).obj (F.obj T.obj₂)) :=
    (isDerivedComplete_iff_homology.{u, max (u + 1) w, w} X Λ _ _).1 h₂
  have h₃' := @Stacks.Homology.prop_homology_obj₃_of_distTriang _ _ _ P this
    (F.mapTriangle.obj T) hT' h₁' h₂'
  exact (isDerivedComplete_iff_homology.{u, max (u + 1) w, w} X Λ _ _).2 h₃'


omit [IsNoetherianRing Λ] in
/-- For a sheaf `P` of `Λ`-modules, if `P ⊗_Λ \underline{Λ/I} = 0` then `P ⊗_Λ Λ/I = 0` as a
sheaf of `Λ/I`-modules. -/
theorem isZero_extendScalars_of_isZero_tensor_quotientConstantSheaf
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hP : IsZero (P ⊗ quotientConstantSheaf X Λ I)) :
    IsZero ((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
      (Ideal.Quotient.mk I)).obj P) := by
  let R := Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk I)
  let e : R.obj ((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
      (Ideal.Quotient.mk I)).obj P) ≅ P ⊗ quotientConstantSheaf X Λ I :=
    R.mapIso (λ_ _).symm ≪≫
      (Stacks.ModuleSheaf.restrictScalarsTensorExtendScalarsIso _ (Ideal.Quotient.mk I)).app
        (𝟙_ _, P) ≪≫
      whiskerRightIso ((Stacks.ModuleSheaf.restrictScalarsConstantSheafIso _
        (Ideal.Quotient.mk I)).app (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I))) P ≪≫ β_ _ _
  rw [IsZero.iff_id_eq_zero]
  exact R.map_injective ((hP.of_iso e).eq_of_src _ _)
section Cone

variable {t : ℕ}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
  {f : (DerivedCategory.singleFunctor _ b).obj
      (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⟶ K}
  {g : K ⟶ L}
  {h : L ⟶ ((DerivedCategory.singleFunctor _ b).obj
      (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)))⟦(1 : ℤ)⟧}

omit [IsNoetherianRing Λ] in
/-- The cone of a map `(\underline{Λ}^∧)^{⊕ t}[-b] ⟶ K` has no cohomology above `b` or below `a`
when `K` has none outside `[a, b]` and `a < b`. -/
theorem HasBoundedLocallyConstantReduction.isZero_homology_cone (hab : a < b)
    (hK : HasBoundedLocallyConstantReduction X Λ I K a b) (hT : Triangle.mk f g h ∈ distTriang _)
    {i : ℤ} (hi : b < i ∨ i < a) : IsZero ((DerivedCategory.homologyFunctor _ i).obj L) :=
  Stacks.Homology.isZero_homology_obj₃_of_distTriang _ hT i (i + 1) rfl
    ((hK.2.1 i (by rintro ⟨h₁, h₂⟩; omega)).eq_of_src _ _)
    (Stacks.Homology.isZero_homologyFunctor_obj_singleFunctor_obj _ b (i + 1) (by omega))

/-- The reduction of the cone of `f` vanishes in degree `b` when `f` is surjective on
`H^b(- ⊗_Λ^L \underline{Λ/I})`. -/
theorem isZero_homology_cone_tensor_quotientConstantSheaf (hT : Triangle.mk f g h ∈ distTriang _)
    (hf : Epi ((DerivedCategory.homologyFunctor _ b).map
      (f ▷ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I)))) :
    IsZero ((DerivedCategory.homologyFunctor _ b).obj
      (L ⊗ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I))) := by
  obtain ⟨δq, hTq⟩ := Stacks.ModuleSheaf.exists_distTriang_whiskerRight _ hT
    ((DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I))
  refine Stacks.Homology.isZero_homology_obj₃_of_distTriang _ hTq b (b + 1) rfl ?_
    (isZero_homology_singleFunctor_biproduct_completedConstantSheaf_tensor b t _
      (fun _ hx => smul_id_quotientConstantSheaf_eq_zero I X hx) (by omega))
  have h₀ := comp_distTriang_mor_zero₁₂ _ hTq
  have h₁ : (DerivedCategory.homologyFunctor _ b).map
      (f ▷ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I)) ≫
        (DerivedCategory.homologyFunctor _ b).map
          (g ▷ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I)) = 0 := by
    rw [← Functor.map_comp]
    exact (congrArg (DerivedCategory.homologyFunctor _ b).map h₀).trans (Functor.map_zero _ _ _)
  exact (cancel_epi _).1 (h₁.trans comp_zero.symm)

/-- **Nakayama for the top cohomology.** If `L` lies in degrees `≤ b`, is derived complete
along `I·\underline{Λ}`, and its reduction vanishes in degree `b`, then `H^b(L) = 0`. -/
theorem isZero_homology_of_isZero_homology_tensor_quotientConstantSheaf [L.IsLE b]
    (hc : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj L))
    (hL : IsZero ((DerivedCategory.homologyFunctor _ b).obj
      (L ⊗ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I)))) :
    IsZero ((DerivedCategory.homologyFunctor _ b).obj L) := by
  have hI : I.FG := IsNoetherian.noetherian I
  obtain ⟨eT⟩ := Stacks.ModuleSheaf.nonempty_homology_tensor_single_iso_of_isLE L b
    (quotientConstantSheaf X Λ I)
  have h₁ := isZero_extendScalars_of_isZero_tensor_quotientConstantSheaf _ (hL.of_iso eT.symm)
  have h₂ := idealPowerProduct_eq_top_of_isZero_extendScalars _ h₁
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₃ := (isDerivedComplete_iff_homology.{u, max (u + 1) w, w} X Λ _ _).1 hc b
  have h₄ : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        (E.functor.obj ((DerivedCategory.homologyFunctor _ b).obj L))) :=
    (RingedSite.isDerivedComplete_iff_of_iso _ _ ((DerivedCategory.singleFunctor _ 0).mapIso
      ((E.functor.mapDerivedCategoryHomologyIso b).app L))).1 h₃
  have h₅ := isZero_of_isDerivedComplete_of_constantCoefficientIdealSheaf.{u, max (u + 1) w, w}
    X Λ I hI _ h₄ h₂
  exact (E.inverse.map_isZero h₅).of_iso (E.unitIso.app _)

/-- The cone of `f` has Tor amplitude in `[a, b - 1]` against sheaves killed by `I`, once it lies
in degrees `≤ b - 1`. -/
theorem HasBoundedLocallyConstantReduction.isZero_homology_cone_tensor (hab : a < b)
    (hK : HasBoundedLocallyConstantReduction X Λ I K a b) (hT : Triangle.mk f g h ∈ distTriang _)
    [L.IsLE (b - 1)] (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hN : ∀ x ∈ I, x • 𝟙 N = 0) {i : ℤ} (hi : i ∉ Set.Icc a (b - 1)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (L ⊗ (DerivedCategory.singleFunctor _ 0).obj N)) := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · obtain ⟨δN, hTN⟩ := Stacks.ModuleSheaf.exists_distTriang_whiskerRight _ hT
      ((DerivedCategory.singleFunctor _ 0).obj N)
    exact Stacks.Homology.isZero_homology_obj₃_of_distTriang _ hTN i (i + 1) rfl
      ((hK.2.2.1 N hN i (by simp only [Set.mem_Icc]; omega)).eq_of_src _ _)
      (isZero_homology_singleFunctor_biproduct_completedConstantSheaf_tensor b t N hN
        (by omega))
  · have : (L ⊗ (DerivedCategory.singleFunctor _ 0).obj N).IsLE (b - 1 + 0) :=
      Stacks.ModuleSheaf.isLE_tensor L ((DerivedCategory.singleFunctor _ 0).obj N) (b - 1) 0
    exact DerivedCategory.isZero_of_isLE _ (b - 1 + 0) i (by omega)

/-- The cohomology sheaves of the reduction of the cone of `f` are locally constant of finite
type. -/
theorem HasBoundedLocallyConstantReduction.isFiniteTypeLocallyConstantModuleSheaf_homology_cone
    (hK : HasBoundedLocallyConstantReduction X Λ I K a b) (hT : Triangle.mk f g h ∈ distTriang _)
    (i : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
      max (u + 1) w, max (u + 1) w} (Scheme.ProEt.topology X) Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (L ⊗ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I))) := by
  obtain ⟨δq, hTq⟩ := Stacks.ModuleSheaf.exists_distTriang_whiskerRight _ hT
    ((DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I))
  exact @Stacks.Homology.prop_homology_obj₃_of_distTriang _ _ _ _
    (Stacks.ConstantSheaf.isWeakSerreClass_isFiniteTypeLocallyConstantModuleSheaf _ _) _ hTq
    (isFiniteTypeLocallyConstantModuleSheaf_homology_singleFunctor_biproduct_tensor b t)
    hK.2.2.2 i

/-- **The cone of a lift of generators keeps the condition on a smaller range.** Let `K` satisfy
the condition on `[a, b]` with `a < b`, and let `f : (\underline{Λ}^∧)^{⊕ t}[-b] ⟶ K` be surjective
on `H^b(- ⊗_Λ^L \underline{Λ/I})`. Then the cone of `f` satisfies the condition on `[a, b - 1]`. -/
theorem HasBoundedLocallyConstantReduction.of_distTriang (hab : a < b)
    (hK : HasBoundedLocallyConstantReduction X Λ I K a b) (hT : Triangle.mk f g h ∈ distTriang _)
    (hf : Epi ((DerivedCategory.homologyFunctor _ b).map
      (f ▷ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I)))) :
    HasBoundedLocallyConstantReduction X Λ I L a (b - 1) := by
  have hc := isDerivedComplete_derivedModuleEquiv_functor_obj₃_of_distTriang _ hT
    (isDerivedComplete_singleFunctor_biproduct_completedConstantSheaf b t) hK.1
  have : L.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => hK.isZero_homology_cone hab hT (Or.inl hi)
  have hb := isZero_homology_of_isZero_homology_tensor_quotientConstantSheaf (L := L) hc
    (isZero_homology_cone_tensor_quotientConstantSheaf hT hf)
  have hL : ∀ i, i ∉ Set.Icc a (b - 1) → IsZero ((DerivedCategory.homologyFunctor _ i).obj L) := by
    intro i hi
    by_cases hib : i = b
    · exact hib ▸ hb
    · exact hK.isZero_homology_cone hab hT
        (by simp only [Set.mem_Icc] at hi; omega)
  have : L.IsLE (b - 1) := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => hL i (by simp only [Set.mem_Icc]; omega)
  exact ⟨hc, hL, fun N hN i hi => hK.isZero_homology_cone_tensor hab hT N hN hi,
    hK.isFiniteTypeLocallyConstantModuleSheaf_homology_cone hT⟩

end Cone

/-- On a weakly contractible affine scheme `X`, if `K` satisfies the condition on `[a, b]` with
`a < b`, there is a distinguished triangle
`(\underline{Λ}^∧)^{⊕ t}[-b] ⟶ K ⟶ L ⟶ (\underline{Λ}^∧)^{⊕ t}[-b + 1]` with `L` satisfying the
condition on `[a, b - 1]`. -/
theorem exists_distTriang_hasBoundedLocallyConstantReduction [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X) (hab : a < b)
    (hK : HasBoundedLocallyConstantReduction X Λ I K a b) :
    ∃ (t : ℕ) (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} Λ)))
      (f : (DerivedCategory.singleFunctor _ b).obj
        (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)) ⟶ K)
      (g : K ⟶ L)
      (h : L ⟶ ((DerivedCategory.singleFunctor _ b).obj
        (⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ)))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ ∧ HasBoundedLocallyConstantReduction X Λ I L a (b - 1) := by
  obtain ⟨t, s, hs⟩ := hK.exists_singleFunctor_hom_epi hX
  obtain ⟨ŝ, hŝ⟩ := exists_singleFunctor_biproduct_completedConstantSheaf_hom b
    hK.isDerivedComplete s
  obtain ⟨L, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle ŝ
  refine ⟨t, L, ŝ, g, h, hT, hK.of_distTriang hab hT ?_⟩
  rw [← hŝ, comp_whiskerRight, Functor.map_comp] at hs
  exact epi_of_epi ((DerivedCategory.homologyFunctor _ b).map
    ((DerivedCategory.singleFunctor _ b).map
      (biproduct.map fun _ => completedConstantSheafMap X I) ▷ _)) _

variable (X Λ I) in
/-- **A complex of completed constant sheaves.** On a weakly contractible affine scheme `X`, an
object `K` satisfying the condition on `[a, b]` is represented by a complex
`C` vanishing outside `[a, b]` whose terms in degrees `≠ a` are finite sums of copies of
`\underline{Λ}^∧`, and whose term in degree `a`, placed in degree `a`, satisfies the condition
on `[a, a]`. -/
theorem exists_complex_of_hasBoundedLocallyConstantReduction [IsAffine X]
    (hX : ProetaleWContractible.IsWeaklyContractibleObj X) (n : ℕ) :
    ∀ (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
      (a b : ℤ), b - a = n → HasBoundedLocallyConstantReduction X Λ I K a b →
      ∃ C : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ,
        C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧ Nonempty (K ≅ DerivedCategory.Q.obj C) ∧
        (∀ k : ℤ, k ≠ a → ∃ t : ℕ,
          Nonempty (C.X k ≅
            ⨁ fun _ : Fin t => completedConstantSheaf X Λ I (Functor.unitModule Λ))) ∧
        HasBoundedLocallyConstantReduction X Λ I
          ((DerivedCategory.singleFunctor _ a).obj (C.X a)) a a := by
  have hz : IsZero (⨁ fun _ : Fin 0 => completedConstantSheaf X Λ I (Functor.unitModule Λ)) :=
    (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ (fun j : Fin 0 => j.elim0))
  induction n with
  | zero =>
    intro K a b hn hK
    obtain rfl : a = b := by omega
    obtain ⟨e⟩ := hK.nonempty_iso_singleFunctor_homology
    let F := (DerivedCategory.homologyFunctor _ a).obj K
    refine ⟨(HomologicalComplex.single _ _ a).obj F, inferInstance, inferInstance,
      ⟨e ≪≫ (DerivedCategory.singleFunctorIsoCompQ _ a).app F⟩, fun k hk => ⟨0, ⟨?_⟩⟩, ?_⟩
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk).iso hz
    · exact (hK.of_iso e).of_iso ((DerivedCategory.singleFunctor _ a).mapIso
        (HomologicalComplex.singleObjXSelf _ a F).symm)
  | succ n ih =>
    intro K a b hn hK
    obtain ⟨t, L, f, g, h, hT, hL⟩ :=
      exists_distTriang_hasBoundedLocallyConstantReduction hX (by omega) hK
    obtain ⟨C', hGE, hLE, ⟨e⟩, hfree, hbase⟩ := ih L a (b - 1) (by omega) hL
    obtain ⟨C, h1, h2, h3, h4, h5⟩ :=
      DerivedCategory.exists_complex_of_distTriang_single b _ f g h hT a (by omega) C' e
    refine ⟨C, h1, h2, h3, fun k hk => ?_, ?_⟩
    · by_cases hkb : k ≤ b - 1
      · obtain ⟨t', ⟨e'⟩⟩ := hfree k hk
        obtain ⟨e''⟩ := h4 k hkb
        exact ⟨t', ⟨e'' ≪≫ e'⟩⟩
      · by_cases hkb' : k = b
        · subst hkb'
          exact ⟨t, h5⟩
        · exact ⟨0, ⟨(C.isZero_of_isStrictlyLE b k (by omega)).iso hz⟩⟩
    · obtain ⟨e'⟩ := h4 a (by omega)
      exact hbase.of_iso ((DerivedCategory.singleFunctor _ a).mapIso e'.symm)

end AlgebraicGeometry.ProEtale
