module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.PreimageUniformBound
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardBounds
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Upper cohomological bounds for the derived direct image along a qcqs morphism

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y`
quasi-compact, and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent.
There is an integer `N = N(X, Y, f)`, depending on neither `E` nor the degree, such that `Rf_*E`
lives in degrees `≤ b + N` as soon as `E` lives in degrees `≤ b`. This is part (2) of
[Stacks, Tag 08D5].

The cohomology sheaf `H ⁱ(Rf_*E)` is the sheafification of the presheaf `V ↦ H ⁱ(f⁻¹V, E)`
([Stacks, Tag 0D66]), so it vanishes as soon as `H ⁱ(f⁻¹V, E)` vanishes for `V` in a basis of
the topology of `Y`. There is one basis of affine opens and one `N` with `H ᵖ(f⁻¹V, ℱ) = 0` for
every member `V`, every quasi-coherent `ℱ` and every `p ≥ N`, and part (3) of
[Stacks, Tag 08D4] at the functor `Γ(f⁻¹V, -)` then bounds `RΓ(f⁻¹V, E)` by `b + N - 1`.

## Main results

* `AlgebraicGeometry.isZero_rightDerivedPlus_preimageSections_of_isZero_hgroup`: the uniform
  cohomology vanishing over `f⁻¹V`, read as vanishing of the higher right derived functors of
  `Γ(f⁻¹V, -) : Mod(𝒪_X) ⥤ Mod(Γ(V, 𝒪_Y))`.
* `AlgebraicGeometry.isLE_derivedPreimageSections_obj_of_isZero_hgroup`: [Stacks, Tag 08D4]
  part (3) at `Γ(f⁻¹V, -)` with a general `N`: `RΓ(f⁻¹V, E)` lives in degrees `≤ b + N - 1`.
* `AlgebraicGeometry.exists_isLE_derivedPushforward_obj`: [Stacks, Tag 08D5] part (2) for a
  quasi-compact quasi-separated morphism with quasi-compact target.
* `AlgebraicGeometry.exists_isIso_homologyFunctor_map_derivedPushforward_truncGEπ`: the
  truncation comparison, [Stacks, Tag 08D4] part (2) read at `Rf_*`.

## Implementation notes

`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` is stated with source
category `SheafOfModules Y.ringCatSheaf` while `Γ(f⁻¹V, -)` is stated with source
`SheafOfModules (structureSheafRing Y.toRingedSpace)`, and instance search does not cross the two
definitionally equal spellings, so three of its instances are supplied positionally.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedPreimageSections derivedPreimageSectionsUnit preimageSections)

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnboundedHigherDirectImage.isGrothendieckAbelian_moduleSheaves

variable {X Y : Scheme.{u}}

/-! ### Uniform vanishing for the sections over an inverse image -/

/-- **Uniform vanishing for `Γ(f⁻¹V, -)`.** Suppose the cohomology `H ᵖ(f⁻¹V, ℱ)` vanishes for
every quasi-coherent `𝒪_X`-module `ℱ` and every `p ≥ N`. Then the right derived functors of
`Γ(f⁻¹V, -) : Mod(𝒪_X) ⥤ Mod(Γ(V, 𝒪_Y))` vanish on quasi-coherent modules in every degree
`≥ N`. -/
public theorem isZero_rightDerivedPlus_preimageSections_of_isZero_hgroup (f : X ⟶ Y)
    (V : Y.Opens) (N : ℕ)
    (hvan : ∀ F : X.Modules, F.IsQuasicoherent → ∀ q : ℕ, N ≤ q →
      IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) q F))
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (hM : M.IsQuasicoherent)
    (p : ℤ) (hp : (N : ℤ) ≤ p) :
    IsZero (((preimageSections f.toLRSHom.toShHom V).rightDerivedPlus p).obj M) := by
  have hM' : (M : X.Modules).IsQuasicoherent := hM
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
    ⟨p.toNat, (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg N) hp)).symm⟩
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (preimageSections f.toLRSHom.toShHom V) (rfl : ((n : ℕ) : ℤ) = ((n : ℕ) : ℤ)) M).2 ?_
  have hAb := @hvan M hM' n (by exact_mod_cast hp)
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero
    (hAb.of_iso (((preimageSections f.toLRSHom.toShHom V).rightDerivedCompIso
      (forget₂ (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V)))
        AddCommGrpCat.{u}) n).app M).symm))

/-- **[Stacks, Tag 08D4] part (3) at the functor `Γ(f⁻¹V, -)`.** Let `V ⊆ Y` be an open over
whose inverse image the cohomology of every quasi-coherent `𝒪_X`-module vanishes in all degrees
`≥ N`, and let `E` be an object of `D(𝒪_X)` with quasi-coherent cohomology sheaves living in
degrees `≤ b`. Then the hypercohomology `RΓ(f⁻¹V, E)` lives in degrees `≤ b + N - 1`. -/
public theorem isLE_derivedPreimageSections_obj_of_isZero_hgroup (f : X ⟶ Y) (V : Y.Opens)
    (N : ℕ)
    (hvan : ∀ F : X.Modules, F.IsQuasicoherent → ∀ q : ℕ, N ≤ q →
      IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) q F))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) :
    ((derivedPreimageSections f.toLRSHom.toShHom V).obj E).IsLE (b + (N : ℤ) - 1) := by
  have hirdf : (derivedPreimageSections f.toLRSHom.toShHom V).IsRightDerivedFunctor
      (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) := inferInstance
  exact @isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus X _ _ _ _ _ _
    (preimageSections f.toLRSHom.toShHom V)
    (Stacks.Cohomology.DerivedSectionsLeray.preimageSections_additive _ _)
    (preservesLimitsOfShape_discrete_nat_preimageSections f V)
    (derivedPreimageSections f.toLRSHom.toShHom V)
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V) hirdf N
    (fun M hM p hp ↦ isZero_rightDerivedPlus_preimageSections_of_isZero_hgroup f V N hvan M hM
      p hp) E hcoh b hE

/-! ### The bound on the derived direct image -/

/-- **[Stacks, Tag 08D5] part (2).** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated
morphism of schemes with `Y` quasi-compact. There is an integer `N = N(X, Y, f)` such that for
every object `E` of `D(𝒪_X)` with quasi-coherent cohomology sheaves living in degrees `≤ b`, the
derived direct image `Rf_*E` lives in degrees `≤ b + N`. -/
@[ega "III 1.4.12" "more general"]
public theorem exists_isLE_derivedPushforward_obj (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    ∃ N : ℕ, ∀ E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent) →
      ∀ b : ℤ, E.IsLE b →
        ((derivedPushforward f.toLRSHom.toShHom).obj E).IsLE (b + (N : ℤ)) := by
  obtain ⟨N, B, hB, _, hvan⟩ :=
    Stacks.Cohomology.AffineCover.exists_isZero_hgroup_preimage_of_isBasis f
  refine ⟨N, fun E hcoh b hE ↦ ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine Stacks.Cohomology.UnboundedHigherDirectImage.isZero_homologyDerivedPushforward_of_isBasis
    f.toLRSHom.toShHom hB E i fun V hV ↦ ?_
  have hvan' : ∀ F : X.Modules, F.IsQuasicoherent → ∀ q : ℕ, N + 1 ≤ q →
      IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) q F) :=
    fun F hF q hq ↦ hvan V hV F hF q (by omega)
  have := isLE_derivedPreimageSections_obj_of_isZero_hgroup f V (N + 1) hvan' E hcoh b hE
  refine DerivedCategory.isZero_of_isLE _ (b + ((N + 1 : ℕ) : ℤ) - 1) i ?_
  push_cast
  omega

/-- **The derived direct image does not see a truncation from below in high degrees.** For a
quasi-compact quasi-separated `f` with quasi-compact target there is an `N` such that for every
object `E` of `D(𝒪_X)` with quasi-coherent cohomology sheaves and every `b`, the canonical map
`H ⁱ(Rf_*E) ⟶ H ⁱ(Rf_*(τ_{≥ b}E))` is an isomorphism for every `i ≥ b + N`.

This is [Stacks, Tag 08D4] part (2) read at `Rf_*`. -/
public theorem exists_isIso_homologyFunctor_map_derivedPushforward_truncGEπ (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] :
    ∃ N : ℕ, ∀ E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) i).obj E).IsQuasicoherent) →
      ∀ b i : ℤ, b + (N : ℤ) ≤ i →
        IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map
          ((derivedPushforward f.toLRSHom.toShHom).map
            ((DerivedCategory.TStructure.t.truncGEπ b).app E))) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj f
  refine ⟨N + 1, fun E hcoh b i hi ↦ ?_⟩
  have hP := containsZero_isQuasicoherent X
  have _ := SheafOfModules.isGrothendieckAbelianU.{u, u, u} (structureSheafRing X.toRingedSpace)
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) ℤ
  have _ : (derivedPushforward f.toLRSHom.toShHom).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated
      (modulePushforward f.toLRSHom.toShHom) _ (derivedPushforwardUnit f.toLRSHom.toShHom)
  let T := (derivedPushforward f.toLRSHom.toShHom).mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E)
  have hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :=
    (derivedPushforward f.toLRSHom.toShHom).map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E)
  have hl : T.obj₁.IsLE (b - 1 + (N : ℤ)) :=
    hN _ (@Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj _ _ _ _
        (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)) _ hP E hcoh (b - 1))
      (b - 1) (DerivedCategory.TStructure.t.isLE_truncLE_obj E (b - 1) (b - 1) le_rfl)
  have hz : ∀ j : ℤ, i ≤ j → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) j).obj T.obj₁) :=
    fun j hj ↦ T.obj₁.isZero_of_isLE (b - 1 + (N : ℤ)) j (by push_cast at hi ⊢; omega)
  have : Mono ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂) :=
    (Functor.homologySequence_mono_shift_map_mor₂_iff (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0) T hT i).2
      ((hz i le_rfl).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂) :=
    (Functor.homologySequence_epi_shift_map_mor₂_iff (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) 0) T hT i (i + 1) rfl).2
      ((hz _ (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).map T.mor₂)

end AlgebraicGeometry

end
