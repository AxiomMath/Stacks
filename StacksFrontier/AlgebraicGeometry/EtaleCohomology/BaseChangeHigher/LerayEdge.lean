module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.HigherBaseChangeDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.PositiveDegreeInjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity

/-!
# The Leray edge map of a composite of direct images

Let `v : A' ⟶ A` and `g₀ : A ⟶ B` be morphisms of schemes and `g₁ = v ≫ g₀`. The commutative
square `g₁ ≫ 𝟙 = v ≫ g₀` has a base change map `𝟙⁻¹ R^r g₀_* ⟶ R^r g₁_* v⁻¹` on higher direct
images of abelian sheaves on the small étale sites ([Stacks, Tag 0F02]). At `v_* K`, followed by
`R^r g₁_*` of the counit `v⁻¹ v_* K ⟶ K`, it is a map `𝟙⁻¹ R^r g₀_*(v_* K) ⟶ R^r g₁_* K`: the
edge map of the relative Leray spectral sequence for `g₁ = v ≫ g₀` ([Stacks, Tag 0734]). Read
this way it inherits the compatibilities of base change maps (naturality, connecting morphisms,
pasting), so no spectral sequence is needed.

This file defines it and proves that it is invertible in degree zero, where it is the comparison
`g₀_* v_* ≅ g₁_*` of direct images.

## Main definitions

* `Stacks.EtaleCohomology.lerayEdge` — the Leray edge map.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_id_app_comp` — the underived base change map of
  the square, followed by a map out of `v⁻¹ N`, transposed.
* `Stacks.EtaleCohomology.isIso_lerayEdge_zero` — the Leray edge map is invertible in degree
  zero.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb_app_comp_map_eq` — the base change map followed
  by `R^r g₁_*` of `τ : v⁻¹ N ⟶ K` factors through the Leray edge map at `K`.

## References

* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section

variable {A A' B : Scheme.{u}} (g₀ : A ⟶ B) (g₁ : A' ⟶ B) (v : A' ⟶ A)
  (w : g₁ ≫ 𝟙 B = v ≫ g₀)

/-- **The underived base change map of a Leray square, followed by a map out of the inverse
image.** -/
theorem smallEtaleBaseChangeAb_id_app_comp {N : Sheaf (smallEtaleTopology A) Ab.{u + 1}}
    {K : Sheaf (smallEtaleTopology A') Ab.{u + 1}} (τ : (smallEtalePullbackAb v).obj N ⟶ K) :
    (smallEtaleBaseChangeAb (𝟙 B) g₀ g₁ v w).app N ≫ (smallEtalePushforwardAb g₁).map τ =
      ((smallEtaleAdjunctionAb (𝟙 B)).homEquiv _ _).symm ((smallEtalePushforwardAb g₀).map
        ((smallEtaleAdjunctionAb v).homEquiv _ _ τ) ≫
          (smallEtaleSquarePushforwardIso (𝟙 B) g₀ g₁ v w).hom.app K) := by
  rw [smallEtaleBaseChangeAb_eq_mate]
  have hn := (smallEtaleSquarePushforwardIso (𝟙 B) g₀ g₁ v w).hom.naturality τ
  have hc := (smallEtaleAdjunctionAb (𝟙 B)).counit_naturality ((smallEtalePushforwardAb g₁).map τ)
  rw [Stacks.Cohomology.BaseChange.mate_app, Adjunction.homEquiv_counit, Adjunction.homEquiv_unit]
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map] at hn hc ⊢
  rw [Category.assoc, Category.assoc, ← hc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  refine congrArg (fun z => (smallEtalePullbackAb (𝟙 B)).map z ≫
    (smallEtaleAdjunctionAb (𝟙 B)).counit.app ((smallEtalePushforwardAb g₁).obj K)) ?_
  rw [Functor.map_comp, Category.assoc, Category.assoc, hn]

/-- The counit of the adjunction along a morphism known to be the identity, through the two
identifications of inverse and direct image with the identity functor. -/
theorem smallEtaleAdjunctionAb_counit_app_of_eq_id {Y : Scheme.{u}} (b : Y ⟶ Y) (hb : b = 𝟙 Y)
    (M : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtaleAdjunctionAb b).counit.app M =
      (smallEtalePullbackAb b).map ((smallEtalePushforwardAbIdOf b hb).hom.app M) ≫
        (smallEtalePullbackAbIdOf b hb).hom.app M := by
  simp [smallEtalePullbackAbIdOf, Adjunction.leftAdjointIdIso_hom_app, ← Functor.map_comp_assoc]

/-- The identification `g_* ⟶ R⁰g_*` of a direct image with its degree-zero right derived
functor. -/
abbrev zeroUnit {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtalePushforwardAb g).obj F ⟶ ((smallEtalePushforwardAb g).rightDerived 0).obj F :=
  Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) F ≫
    (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.app F

/-- The identification `g_* ⟶ R⁰g_*` is an isomorphism. -/
instance isIso_zeroUnit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) : IsIso (zeroUnit g F) := by
  have : PreservesFiniteLimits (smallEtalePushforwardAb g) :=
    have := (smallEtaleAdjunctionAb g).rightAdjoint_preservesLimits
    inferInstance
  have := Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit (smallEtalePushforwardAb g) F
  infer_instance

/-- The identification `g_* ⟶ R⁰g_*` is natural in the sheaf. -/
theorem zeroUnit_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G) :
    (smallEtalePushforwardAb g).map φ ≫ zeroUnit g G =
      zeroUnit g F ≫ ((smallEtalePushforwardAb g).rightDerived 0).map φ := by
  rw [← Category.assoc, Stacks.DerivedFunctor.rightDerivedZeroUnit_naturality, Category.assoc,
    Category.assoc]
  congr 1
  exact ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.naturality φ)

/-- **The Leray edge map in degree zero is invertible.** For a commutative square
`g₁ ≫ 𝟙 = v ≫ g₀`, the base change map in degree `0` at `v_* K`, followed by the direct image
along `g₁` of the counit `v⁻¹v_*K ⟶ K`, is an isomorphism `𝟙⁻¹ R⁰g₀_*(v_*K) ≅ R⁰g₁_* K`: in
degree zero it is the comparison `g₀_* v_* ≅ g₁_*` of direct images. -/
theorem isIso_lerayEdge_zero (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    IsIso ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 0).app ((smallEtalePushforwardAb v).obj K) ≫
      ((smallEtalePushforwardAb g₁).rightDerived 0).map
        ((smallEtaleAdjunctionAb v).counit.app K)) := by
  have key := map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero (𝟙 B) g₀ g₁ v w
    ((smallEtalePushforwardAb v).obj K)
  have hz := zeroUnit_naturality g₁ ((smallEtaleAdjunctionAb v).counit.app K)
  have hb := smallEtaleBaseChangeAb_id_app_comp g₀ g₁ v w ((smallEtaleAdjunctionAb v).counit.app K)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit,
    (smallEtaleAdjunctionAb v).right_triangle_components, CategoryTheory.Functor.map_id,
    Category.id_comp,
    smallEtaleAdjunctionAb_counit_app_of_eq_id (𝟙 B) rfl] at hb
  have e : (higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 0).app ((smallEtalePushforwardAb v).obj K) ≫
      ((smallEtalePushforwardAb g₁).rightDerived 0).map ((smallEtaleAdjunctionAb v).counit.app K) =
      inv ((smallEtalePullbackAb (𝟙 B)).map (zeroUnit g₀ ((smallEtalePushforwardAb v).obj K))) ≫
        ((smallEtaleBaseChangeAb (𝟙 B) g₀ g₁ v w).app ((smallEtalePushforwardAb v).obj K) ≫
          (smallEtalePushforwardAb g₁).map ((smallEtaleAdjunctionAb v).counit.app K)) ≫
        zeroUnit g₁ K := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, key]
    exact (Category.assoc _ _ _).trans ((congrArg _ hz.symm).trans (Category.assoc _ _ _).symm)
  rw [e, hb]
  infer_instance

/-- **The Leray edge map** of a commutative square `g₁ ≫ 𝟙 = v ≫ g₀` in degree `r`:
the base change map of the square at `v_* K`, followed by `R^r g₁_*` of the counit
`v⁻¹v_* K ⟶ K`, a map `𝟙⁻¹ R^r g₀_*(v_* K) ⟶ R^r g₁_* K`. It is the edge map of the relative
Leray spectral sequence for `g₁ = v ≫ g₀`. -/
def lerayEdge (r : ℕ) (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    (smallEtalePullbackAb (𝟙 B)).obj
        (((smallEtalePushforwardAb g₀).rightDerived r).obj ((smallEtalePushforwardAb v).obj K)) ⟶
      ((smallEtalePushforwardAb g₁).rightDerived r).obj K :=
  (higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w r).app ((smallEtalePushforwardAb v).obj K) ≫
    ((smallEtalePushforwardAb g₁).rightDerived r).map ((smallEtaleAdjunctionAb v).counit.app K)

/-- **The base change map of a Leray square, followed by a map out of the inverse image,
factors through the Leray edge map**: for `τ : v⁻¹N ⟶ K` with adjoint `τ♭ : N ⟶ v_* K`, the
composite is `𝟙⁻¹ R^r g₀_*(τ♭)` followed by the Leray edge map at `K`. -/
theorem higherBaseChangeMapAb_app_comp_map_eq {N : Sheaf (smallEtaleTopology A) Ab.{u + 1}}
    {K : Sheaf (smallEtaleTopology A') Ab.{u + 1}} (r : ℕ)
    (τ : (smallEtalePullbackAb v).obj N ⟶ K) :
    (higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w r).app N ≫
        ((smallEtalePushforwardAb g₁).rightDerived r).map τ =
      (smallEtalePullbackAb (𝟙 B)).map (((smallEtalePushforwardAb g₀).rightDerived r).map
          ((smallEtaleAdjunctionAb v).homEquiv _ _ τ)) ≫ lerayEdge g₀ g₁ v w r K := by
  have hn := (higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w r).naturality
    ((smallEtaleAdjunctionAb v).homEquiv _ _ τ)
  simp only [Functor.comp_map] at hn
  rw [lerayEdge, reassoc_of% hn, ← Functor.map_comp]
  congr 2
  rw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

/-- **The Leray edge map in degree zero is invertible.** In degree zero it is the comparison
`g₀_* v_* ≅ g₁_*` of direct images, read through `𝟙⁻¹ ≅ 𝟭` and `g_* ≅ R⁰g_*`. -/
instance isIso_lerayEdge_zero' (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    IsIso (lerayEdge g₀ g₁ v w 0 K) :=
  isIso_lerayEdge_zero g₀ g₁ v w K

/-- The direct image `g_*` of abelian sheaves on the small étale sites preserves limits. -/
instance smallEtalePushforwardAb_preservesLimits {X Y : Scheme.{u}} (g : X ⟶ Y) :
    PreservesLimits (smallEtalePushforwardAb g) :=
  (smallEtaleAdjunctionAb g).rightAdjoint_preservesLimits

/-- The direct image `g_*` of an injective abelian sheaf on the small étale site is injective. -/
instance injective_smallEtalePushforwardAb_obj {X Y : Scheme.{u}} (g : X ⟶ Y)
    (I : Sheaf (smallEtaleTopology X) Ab.{u + 1}) [Injective I] :
    Injective ((smallEtalePushforwardAb g).obj I) :=
  (smallEtaleAdjunctionAb g).map_injective I inferInstance

/-- Higher direct images vanish on injective sheaves. -/
theorem isZero_rightDerived_succ_of_injective {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)
    (I : Sheaf (smallEtaleTopology X) Ab.{u + 1}) [Injective I] :
    IsZero (((smallEtalePushforwardAb g).rightDerived (n + 1)).obj I) :=
  Functor.isZero_rightDerived_obj_injective_succ _ n I

/-- `R⁰g_*` preserves monomorphisms, being isomorphic to the left exact `g_*`. -/
theorem mono_rightDerived_zero_map {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G) [Mono φ] :
    Mono (((smallEtalePushforwardAb g).rightDerived 0).map φ) := by
  rw [← mono_comp_iff_of_isIso (zeroUnit g F), ← zeroUnit_naturality]
  infer_instance

/-- If `R⁰g_*` maps `φ` to an epimorphism, then so does `g_*`. -/
theorem epi_map_of_epi_rightDerived_zero_map {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G)
    [Epi (((smallEtalePushforwardAb g).rightDerived 0).map φ)] :
    Epi ((smallEtalePushforwardAb g).map φ) := by
  rw [← epi_comp_iff_of_isIso _ (zeroUnit g G), zeroUnit_naturality]
  infer_instance

end

end Stacks.EtaleCohomology
