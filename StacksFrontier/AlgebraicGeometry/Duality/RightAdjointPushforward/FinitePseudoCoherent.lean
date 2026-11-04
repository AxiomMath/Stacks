module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.DerivedInternalHomSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FiniteMorphism
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor

/-!
# `R ℰom(f₊ 𝒪_Y, -)` for a finite pseudo-coherent morphism

Let `f : Y ⟶ X` be a finite pseudo-coherent morphism of schemes. Then
`R ℰom(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(f₊ 𝒪_Y)` carries `D⁺_QCoh(𝒪_X)` into `D⁺_QCoh(f₊ 𝒪_Y)`
(Stacks, Tag 0AX2, first assertion).

`f₊ 𝒪_Y` is a pseudo-coherent `𝒪_X`-module (Tag 0AVX), so `R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)` has
quasi-coherent cohomology for `K ∈ D⁺_QCoh(𝒪_X)` (Tag 0A6H); read over `𝒪_X`, the functor
`R ℰom(f₊ 𝒪_Y, -)` is that derived internal Hom (Tag 0BV1), and an `f₊ 𝒪_Y`-module is
quasi-coherent when it is so over `𝒪_X` (Tag 01SB). Boundedness below comes from the adjunction
of Tag 0BV0 with the t-exact functor of restriction of scalars.

## Main results

* `AlgebraicGeometry.derivedCategoryBPlus_derivedHomSheaf_obj`: Tag 0AX2, first assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- `R ℰom(f₊ 𝒪_Y, -)` carries an object living in degrees `≥ c` to one living in degrees `≥ c`:
it is right adjoint to restriction of scalars, which preserves `D^{≤ c - 1}`. -/
theorem isGE_derivedHomSheaf_obj (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (c : ℤ) (hK : K.IsGE c) : ((derivedHomSheaf f).obj K).IsGE c := by
  obtain ⟨adj⟩ := derivedRestriction_adj_derivedHomSheaf f
  refine (DerivedCategory.TStructure.t.isGE_iff_orthogonal (c - 1) c (by omega) _).2
    fun Z g hZ ↦ ?_
  let := restrictScalars_additive f
  let := restrictionPreservesFiniteLimits f.toRingCatSheafHom
  let := restrictScalars_preservesFiniteColimits f
  have hZ' : DerivedCategory.IsLE Z (c - 1) := hZ
  have hRZ : ((derivedRestrictionOfScalars f).obj Z).IsLE (c - 1) :=
    Stacks.Homology.isLE_mapDerivedCategory_obj
      (SheafOfModules.restrictScalars f.toRingCatSheafHom) Z (c - 1)
  have h0 : ∀ g₁ g₂ : (derivedRestrictionOfScalars f).obj Z ⟶ K, g₁ = g₂ := fun g₁ g₂ ↦ by
    rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₁ (c - 1) c (by omega) hRZ hK,
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₂ (c - 1) c (by omega) hRZ hK]
  exact (adj.homEquiv Z K).symm.injective (h0 _ _)

/-- **Stacks, Tag 0AX2, first assertion.** For a finite pseudo-coherent morphism of schemes
`f : Y ⟶ X`, the functor `R ℰom(f₊ 𝒪_Y, -) : D(𝒪_X) ⥤ D(f₊ 𝒪_Y)` maps `D⁺_QCoh(𝒪_X)` into
`D⁺_QCoh(f₊ 𝒪_Y)`. -/
theorem derivedCategoryBPlus_derivedHomSheaf_obj [IsFinite f] [PseudoCoherent f]
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : DerivedCategoryB.derivedCategoryBPlus (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      K) :
    DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherent (pushforwardRingCatSheaf f)) ((derivedHomSheaf f).obj K) := by
  refine ⟨?_, fun n ↦ ?_⟩
  · obtain ⟨n₀, hn₀⟩ := hK.1
    have hge : K.IsGE n₀ := (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hn₀ i hi
    have := isGE_derivedHomSheaf_obj f K n₀ hge
    exact ⟨n₀, fun n hn ↦ DerivedCategory.isZero_of_isGE _ n₀ n hn⟩
  · let := restrictScalars_additive f
    let := restrictionPreservesFiniteLimits f.toRingCatSheafHom
    let := restrictScalars_preservesFiniteColimits f
    obtain ⟨e, -⟩ := derivedHomSheaf_comp_derivedRestriction_iso f
    have hE := (pseudoCoherent_iff_isPseudoCoherent_pushforward_unit f).1 inferInstance
    have hq := derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X _ K hE hK n
    have e' : (DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).obj
        ((derivedRestrictionOfScalars f).obj ((derivedHomSheaf f).obj K)) ≅
          (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
            ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (pushforwardRingCatSheaf f)) n).obj
              ((derivedHomSheaf f).obj K)) :=
      ((SheafOfModules.restrictScalars f.toRingCatSheafHom).mapDerivedCategoryHomologyIso n).app _
    refine (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff f
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (pushforwardRingCatSheaf f)) n).obj
        ((derivedHomSheaf f).obj K))).1 ?_
    refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((DerivedCategory.homologyFunctor _ n).mapIso
        (e.app K ≪≫ derivedInternalHomPushforwardObjIso f K)).symm ≪≫ e') hq

end AlgebraicGeometry
