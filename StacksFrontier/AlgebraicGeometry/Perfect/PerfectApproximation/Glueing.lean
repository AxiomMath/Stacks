module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.PerfectLift
public import StacksFrontier.Homology.DerivedCategory.PerfectApproximation
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# Extending a perfect complex from a quasi-compact open across an affine open

Let `X = U ∪ V` with `V` affine, let `W ⊆ X` be an open containing `U` with `V ∩ W`
quasi-compact, and let `a : A ⟶ E|_W` be a morphism from a perfect object of `D(𝒪_W)` to the
restriction of an object `E` of `D(𝒪_X)` with quasi-coherent cohomology. Then there are a perfect
object `R` of `D(𝒪_X)`, an isomorphism `R|_W ≅ A ⊕ A[1]` and a morphism `R ⟶ E` restricting to
`a` on the summand `A`.

## Main results

* `AlgebraicGeometry.PerfectApproximation.exists_isPerfect_glueing`: given `a : A ⟶ E|_W` as
  above, a perfect `R` with `R|_W ≅ A ⊕ A[1]` and a morphism `R ⟶ E` restricting to `a` on `A`.
* `AlgebraicGeometry.PerfectApproximation.isZero_stalk_homology_biprod_shift`: the cohomology
  stalks of `K ⊕ L[1]` vanish wherever those of `K` and `L` do.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Duality.QcqsGeneration Stacks.Duality.SupportedGeneration

universe w u

namespace AlgebraicGeometry.PerfectApproximation

open Stacks.Duality.OpenImmersion (derivedRestrict derivedRestrictPushforwardAdjunction)

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- A compact open of an open subscheme. -/
private theorem isCompact_preimage_ι {X : Scheme.{u}} (V : X.Opens) (O : X.Opens)
    (h : IsCompact ((O : Set X) ∩ V)) : IsCompact ((V.ι ⁻¹ᵁ O : V.toScheme.Opens) :
      Set V.toScheme) := by
  rw [V.ι.isOpenEmbedding.isInducing.isCompact_iff]
  have : V.ι.base '' ((V.ι ⁻¹ᵁ O : V.toScheme.Opens) : Set V.toScheme) = (O : Set X) ∩ V := by
    rw [TopologicalSpace.Opens.map_coe, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  rwa [this]

/-- The stalks of the cohomology sheaves of `K ⊕ L[1]` vanish wherever those of `K` and `L` do. -/
theorem isZero_stalk_homology_biprod_shift {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{w} (_root_.SheafOfModules.{u} O)]
    (K L : DerivedCategory (_root_.SheafOfModules.{u} O)) (x : X)
    (hK : ∀ i : ℤ, IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor _ i).obj K).val.presheaf) x))
    (hL : ∀ i : ℤ, IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor _ i).obj L).val.presheaf) x)) (i : ℤ) :
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor _ i).obj (K ⊞ L⟦(1 : ℤ)⟧)).val.presheaf) x) := by
  let F := SheafOfModules.stalkFunctor O x
  let S := DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i ⋙ F
  have : S.Additive := Functor.instAdditiveComp _ _
  rw [← SheafOfModules.isZero_stalkFunctor_obj_iff]
  have hK' : IsZero (S.obj K) := (SheafOfModules.isZero_stalkFunctor_obj_iff _ _ _).2 (hK i)
  have hL' : IsZero (S.obj (L⟦(1 : ℤ)⟧)) :=
    ((SheafOfModules.isZero_stalkFunctor_obj_iff _ _ _).2 (hL (i + 1))).of_iso
      (F.mapIso ((DerivedCategory.homologyShiftIso
        (C := _root_.SheafOfModules.{u} O) i).app L))
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hK', hL'⟩) (S.mapBiprod _ _)

/-- Let `X = W ∪ V` with `V` affine and `V ∩ W` quasi-compact, let `E` be an object of `D(𝒪_X)`
with quasi-coherent cohomology and let `a : A ⟶ E|_W` be a morphism from a perfect object of
`D(𝒪_W)`. Then there are a perfect object `R` of `D(𝒪_X)`, an isomorphism `R|_W ≅ A ⊕ A[1]` and
a morphism `φ : R ⟶ E` whose restriction to `W` is `a` on the first summand and zero on the
second. -/
theorem exists_isPerfect_glueing {X : Scheme.{u}} (W V : X.Opens) (hWV : W ⊔ V = ⊤)
    (hV : IsAffineOpen V) (hWVc : IsCompact ((W : Set X) ∩ V)) (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (A : DerivedCategory W.toScheme.Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toScheme.toRingedSpace) A)
    (a : A ⟶ (derivedRestrict W.ι).obj E) :
    ∃ (R : DerivedCategory X.Modules) (f : (derivedRestrict W.ι).obj R ≅ A ⊞ A⟦(1 : ℤ)⟧)
      (φ : R ⟶ E), Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) R ∧
        (derivedRestrict W.ι).map φ = f.hom ≫ biprod.fst ≫ a := by
  have : IsAffine V.toScheme := hV
  let W₂ : V.toScheme.Opens := V.ι ⁻¹ᵁ W
  let iU : W₂.toScheme ⟶ W.toScheme := V.ι ∣_ W
  let iV := W₂.ι
  have hsq : IsPullback iU iV W.ι V.ι := isPullback_morphismRestrict V.ι W
  have hcov : ∀ y : X, (∃ x, W.ι x = y) ∨ (∃ x, V.ι x = y) := fun y => by
    rcases (hWV ▸ trivial : y ∈ W ⊔ V) with h | h
    exacts [Or.inl ⟨⟨y, h⟩, rfl⟩, Or.inr ⟨⟨y, h⟩, rfl⟩]
  have hW₂ : IsCompact (W₂ : Set V.toScheme) := isCompact_preimage_ι V W hWVc
  have : CompactSpace W₂.toScheme := isCompact_iff_compactSpace.mp hW₂
  have : QuasiSeparatedSpace W₂.toScheme := W₂.ι.isOpenEmbedding.quasiSeparatedSpace
  let adjU := derivedRestrictPushforwardAdjunction W.ι
  let adjV := derivedRestrictPushforwardAdjunction V.ι
  let adjV' := derivedRestrictPushforwardAdjunction iV
  let : (Stacks.Duality.derivedPushforward V.ι).CommShift ℤ := adjV.rightAdjointCommShift ℤ
  let : adjV.CommShift ℤ := adjV.commShift_of_leftAdjoint ℤ
  let : adjV.IsTriangulated := Adjunction.IsTriangulated.mk' adjV
  have := adjV.isTriangulated_rightAdjoint
  have : (Stacks.Duality.derivedPushforward V.ι).Additive := adjV.right_adjoint_additive
  have : (Stacks.Duality.derivedPushforward W.ι).Additive := adjU.right_adjoint_additive
  let B := (derivedRestrict iU).obj A
  have hB : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W₂.toScheme.toRingedSpace) B :=
    Stacks.DerivedQCoh.isPerfect_derivedRestrict_of_isOpenImmersion_of_model iU A hA
  obtain ⟨c, e, -, hc, -⟩ := Stacks.Duality.OpenImmersion.exists_isPerfect_lift iV B hB
    ((derivedRestrict V.ι).obj E)
    (fun i => Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict V.ι E hE i) 0
  let φ₀ : (derivedRestrict iU).obj (A ⊞ A⟦(1 : ℤ)⟧) ≅ (derivedRestrict iV).obj c :=
    (derivedRestrict iU).mapBiprod _ _ ≪≫
      biprod.mapIso (Iso.refl _) (((derivedRestrict iU).commShiftIso (1 : ℤ)).app A) ≪≫ e.symm
  obtain ⟨R₀, ⟨fU⟩, ⟨fV⟩⟩ := exists_glue adjU adjV adjV'
    (fun A' => baseChangeIso W.ι iU V.ι iV hsq A')
    (fun Q' => baseChangeIso V.ι iV W.ι iU hsq.flip Q') (A ⊞ A⟦(1 : ℤ)⟧) c φ₀
  let x : (derivedRestrict W.ι).obj R₀ ⟶ (derivedRestrict W.ι).obj E := fU.hom ≫ biprod.fst ≫ a
  let η := adjU.unit.app E
  obtain ⟨C₂, π, δ, hT₂⟩ := distinguished_cocone_triangle η
  have hC₂W : IsZero ((derivedRestrict W.ι).obj C₂) :=
    Triangle.isZero₃_of_isIso₁ _ ((derivedRestrict W.ι).map_distinguished _ hT₂)
      (CategoryTheory.ObjectProperty.isIso_map_unit_of_isIso_counit adjU E inferInstance)
  have hunit : IsIso (adjV.unit.app C₂) :=
    Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_unit_of_isZero_restrict
      V.ι W.ι iV iU hsq.flip (fun y => (hcov y).symm) C₂ hC₂W
  let o := adjU.homEquiv _ _ x ≫ π
  let o' := (adjV.homEquiv _ _).symm (o ≫ adjV.unit.app C₂)
  have hR₀V : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := V.toScheme.toRingedSpace)
      ((derivedRestrict V.ι).obj R₀) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso fV.symm hc
  have hEW : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W₂.toScheme.Modules i).obj
      ((derivedRestrict iU).obj ((derivedRestrict W.ι).obj E))).IsQuasicoherent := fun i =>
    Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict iU _
      (Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict W.ι E hE) i
  have hM : DerivedCategoryB.derivedCategoryB (A := V.toScheme.Modules)
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf)
      ((derivedRestrict V.ι).obj ((Stacks.Duality.derivedPushforward W.ι).obj
        ((derivedRestrict W.ι).obj E))) := fun i =>
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (baseChangeIso W.ι iU V.ι iV hsq _)).symm
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs iV ⟨_, hEW⟩ i)
  let T₂V := (derivedRestrict V.ι).mapTriangle.obj (Triangle.mk η π δ)
  have hT₂V : T₂V.rotate ∈ distTriang (DerivedCategory V.toScheme.Modules) :=
    rot_of_distTriang _ ((derivedRestrict V.ι).map_distinguished _ hT₂)
  have hEV : DerivedCategoryB.derivedCategoryB (A := V.toScheme.Modules)
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) T₂V.rotate.obj₃ :=
    DerivedCategoryB.derivedCategoryB_shift_mem _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre V.toScheme) 1
      (Stacks.Duality.OpenImmersion.derivedCategoryB_derivedRestrict V.ι E hE)
  have hC₂V : DerivedCategoryB.derivedCategoryB (A := V.toScheme.Modules)
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) T₂V.rotate.obj₂ :=
    DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre V.toScheme)
      T₂V.rotate hT₂V hM hEV
  let c₀ : Stacks.Duality.quasiCoherentDerivedCategory V.toScheme :=
    ⟨(derivedRestrict V.ι).obj R₀, isQuasicoherentDerived_of_isPseudoCoherent V.toScheme _
      (show RingedSpace.IsPerfect (X := V.toScheme.toRingedSpace) _ from hR₀V).isPseudoCoherent⟩
  let K₂ : Stacks.Duality.quasiCoherentDerivedCategory V.toScheme :=
    ⟨(derivedRestrict V.ι).obj C₂, hC₂V⟩
  have : IsCompactObject.{u} c₀ :=
    Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect _ c₀ hR₀V
  have hK₂ : IsZero ((Stacks.Duality.OpenImmersion.restrictedDerivedRestrict iV).obj K₂) :=
    CategoryTheory.ObjectProperty.isZero_fullSubcategory_of_isZero_obj
      (isZero_derivedRestrict_comp_of_isZero iV iU V.ι W.ι hsq.w.symm hC₂W)
  obtain ⟨I, Z, u₀, v, w₀, hT₃, hZc, hZ0, huo⟩ :=
    exists_distTriang_comp_eq_zero iV hK₂ (ObjectProperty.homMk (P := _) (X := c₀) (Y := K₂) o')
  obtain ⟨o₂, ho₂⟩ := Triangle.yoneda_exact₂ _ hT₃
    (ObjectProperty.homMk (P := _) (X := c₀) (Y := K₂) o') huo
  have ho' : o' = v.hom ≫ o₂.hom := congrArg (fun g => g.hom) ho₂
  let ζ : R₀ ⟶ (Stacks.Duality.derivedPushforward V.ι).obj Z.obj := adjV.homEquiv _ _ v.hom
  obtain ⟨R, ρ, ε, hT₄⟩ := distinguished_cocone_triangle₁ ζ
  have : (Stacks.Duality.derivedPushforward iU).IsRightAdjoint := inferInstance
  have hZW :
      IsZero ((derivedRestrict W.ι).obj ((Stacks.Duality.derivedPushforward V.ι).obj Z.obj)) :=
    IsZero.of_iso ((Stacks.Duality.derivedPushforward iU).map_isZero
      ((ObjectProperty.ι _).map_isZero hZ0)) (baseChangeIso V.ι iV W.ι iU hsq.flip Z.obj)
  have hρW : IsIso ((derivedRestrict W.ι).map ρ) :=
    (Triangle.isZero₃_iff_isIso₁ _ ((derivedRestrict W.ι).map_distinguished _ hT₄)).1 hZW
  have hρV : (derivedRestrict V.ι).map ρ ≫ o' = 0 := by
    have hv : v.hom = (derivedRestrict V.ι).map ζ ≫ adjV.counit.app Z.obj := by
      simp [ζ, ← Adjunction.homEquiv_counit]
    have h0 : ρ ≫ ζ = 0 := comp_distTriang_mor_zero₁₂ _ hT₄
    rw [ho', hv, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, h0, Functor.map_zero,
      zero_comp, zero_comp]
  have hρo : ρ ≫ o = 0 := by
    rw [← cancel_mono (adjV.unit.app C₂), zero_comp, Category.assoc]
    apply (adjV.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm]
    refine hρV.trans ?_
    rw [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  obtain ⟨β, hβ⟩ := Triangle.coyoneda_exact₂ _ hT₂ (ρ ≫ adjU.homEquiv _ _ x)
    (by rwa [Category.assoc])
  have hβW : (derivedRestrict W.ι).map β = (derivedRestrict W.ι).map ρ ≫ x := by
    have h₂ : (derivedRestrict W.ι).map (adjU.homEquiv _ _ x) ≫
        adjU.counit.app ((derivedRestrict W.ι).obj E) = x := by
      simp [← Adjunction.homEquiv_counit]
    have h₃ : (derivedRestrict W.ι).map ρ ≫ (derivedRestrict W.ι).map (adjU.homEquiv _ _ x) =
        (derivedRestrict W.ι).map β ≫ (derivedRestrict W.ι).map η := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (derivedRestrict W.ι).map hβ
    calc (derivedRestrict W.ι).map β
        = (derivedRestrict W.ι).map β ≫ (derivedRestrict W.ι).map η ≫
            adjU.counit.app ((derivedRestrict W.ι).obj E) := by
          rw [adjU.left_triangle_components E]; exact (Category.comp_id _).symm
      _ = (derivedRestrict W.ι).map ρ ≫ x := by
          rw [← Category.assoc, ← h₃, Category.assoc, h₂]
  refine ⟨R, asIso ((derivedRestrict W.ι).map ρ) ≪≫ fU, β, ?_, ?_⟩
  · refine Stacks.Duality.OpenImmersion.isPerfect_of_isPerfect_derivedRestrict_two W.ι V.ι hcov
      R ?_ ?_
    · exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        (asIso ((derivedRestrict W.ι).map ρ) ≪≫ fU).symm
        (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished _
          (binaryBiproductTriangle_distinguished A (A⟦(1 : ℤ)⟧)) hA
          (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hA 1))
    · exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished _
        ((derivedRestrict V.ι).map_distinguished _ hT₄) hR₀V
        (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
          (asIso (adjV.counit.app Z.obj)).symm (Stacks.Duality.isPerfect_of_isCompactObject Z hZc))
  · rw [hβW]
    simp [x]

end AlgebraicGeometry.PerfectApproximation

end
