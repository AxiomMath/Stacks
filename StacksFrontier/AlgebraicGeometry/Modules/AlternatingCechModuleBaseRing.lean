module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex

/-!
# The structural ring maps of a base change form a pushout square

Let `f : X ⟶ Spec A` be a scheme over an affine base, let `φ : A → A'` be a ring map and let
`f' : X' ⟶ Spec A'` be the base change of `f` along `Spec φ`, with projection `g : X' ⟶ X`,
presented as an arbitrary cartesian square. For an affine open `W` of `X` the preimage
`g ⁻¹ᵁ W` is again affine and the four structural ring maps form a pushout square of rings:
`Γ(X', g ⁻¹ᵁ W) = A' ⊗_A Γ(X, W)`. We also show that base change of modules is transitive across
a pushout square of rings.

## Main results

* `Stacks.Cech.isBaseChange_restrictScalars_of_isPushout`: base change of modules is transitive
  across a pushout square of rings.
* `Stacks.Cech.baseRingHom_comp_app`: the structural ring maps commute with `φ` and `g`.
* `Stacks.Cech.isAffineOpen_preimage_of_isPullback`: `g ⁻¹ᵁ W` is affine when `W` is.
* `Stacks.Cech.isPushout_baseRingHom`: the structural square is a pushout of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.Cech

/-! ### Transitivity of base change across a pushout of rings -/

/-- **Base change is transitive across a pushout of rings.** If `S` is the pushout of
`A → A'` and `A → R` and `c : M →ₗ[R] N` exhibits `N` as `S ⊗[R] M`, then `c` exhibits `N`
as `A' ⊗[A] M`. -/
theorem isBaseChange_restrictScalars_of_isPushout
    {A A' R S : Type u} [CommRing A] [CommRing A'] [CommRing R] [CommRing S]
    [Algebra A A'] [Algebra A R] [Algebra R S] [Algebra A' S] [Algebra A S]
    [IsScalarTower A R S] [IsScalarTower A A' S] [Algebra.IsPushout A A' R S]
    {M N : Type u} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
    [AddCommGroup N] [Module A N] [Module A' N] [Module R N] [Module S N]
    [IsScalarTower A A' N] [IsScalarTower A R N] [IsScalarTower A' S N] [IsScalarTower R S N]
    (c : M →ₗ[R] N) (hc : IsBaseChange S c) :
    IsBaseChange A' (c.restrictScalars A) :=
  IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange A A' R S M).symm ≪≫ₗ hc.equiv.restrictScalars A')
    fun m => by
      have h : (Algebra.IsPushout.cancelBaseChange A A' R S M).symm (1 ⊗ₜ[A] m)
          = (1 : S) ⊗ₜ[R] m :=
        (LinearEquiv.symm_apply_eq _).mpr
          (Algebra.IsPushout.cancelBaseChange_tmul A A' R S M m).symm
      simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h,
        IsBaseChange.equiv_tmul, one_smul, LinearMap.restrictScalars_apply]

/-! ### The structural square of a base change of schemes -/

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)

/-- The `A`-algebra structure on `Γ(X, W)` through the structural map of `f`. -/
@[instance_reducible]
def baseAlgebra (W : X.Opens) : Algebra A Γ(X, W) :=
  (baseRingHom f W).hom.toAlgebra

/-- The structural ring map of `Stacks.Cech.baseRingHom`, written with the canonical
identification `Γ(Spec A, ⊤) ≅ A` rather than with `AlgebraicGeometry.toSpecΓ`. -/
private theorem baseRingHom_eq_ΓSpecIso_inv_appLE (W : X.Opens) (h : W ≤ f ⁻¹ᵁ ⊤) :
    baseRingHom f W = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ W h :=
  rfl

/-- The structural ring maps of the two schemes commute with `φ` and with `g`. -/
theorem baseRingHom_comp_app
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) (W : X.Opens) :
    baseRingHom f W ≫ g.app W = CommRingCat.ofHom φ ≫ baseRingHom f' (g ⁻¹ᵁ W) := by
  have hWT : W ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have hWT' : g ⁻¹ᵁ W ≤ f' ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A')).Opens) := by simp
  rw [baseRingHom_eq_ΓSpecIso_inv_appLE f W hWT,
    baseRingHom_eq_ΓSpecIso_inv_appLE f' (g ⁻¹ᵁ W) hWT', Category.assoc,
    Scheme.Hom.app_eq_appLE (f := g) (U := W), Scheme.Hom.appLE_comp_appLE]
  simp only [hsq.w, Scheme.Hom.comp_appLE, Scheme.Hom.preimage_top,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]

/-- The top open of `Spec A'` lies over the top open of `Spec A`. -/
private theorem top_le_preimage_top :
    (⊤ : (Spec (CommRingCat.of A')).Opens)
      ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens) :=
  le_top

/-- `g ⁻¹ᵁ W` is its intersection with the preimage under `f'` of the top open of `Spec A'`. -/
private theorem preimage_eq_inf_preimage_top (W : X.Opens) :
    g ⁻¹ᵁ W = g ⁻¹ᵁ W ⊓ f' ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A')).Opens) :=
  (inf_eq_left.2 le_top).symm

/-- **The preimage of an affine open under a base change of an affine base is affine.** -/
theorem isAffineOpen_preimage_of_isPullback
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {W : X.Opens} (hW : IsAffineOpen W) : IsAffineOpen (g ⁻¹ᵁ W) := by
  have h1 : IsAffine ((⊤ : (Spec (CommRingCat.of A)).Opens)).toScheme :=
    isAffineOpen_top (Spec (CommRingCat.of A))
  have h2 : IsAffine ((⊤ : (Spec (CommRingCat.of A')).Opens)).toScheme :=
    isAffineOpen_top (Spec (CommRingCat.of A'))
  have h3 : IsAffine W.toScheme := hW
  exact .of_isIso (Scheme.Hom.isPullback_resLE hsq (top_le_preimage_top φ) le_top
    (preimage_eq_inf_preimage_top f' g W)).isoPullback.hom

/-- **The structural ring maps of a base change form a pushout square.** For a cartesian
square over an affine base and an affine open `W` of `X`, the ring of functions on
`g ⁻¹ᵁ W` is `A' ⊗_A Γ(X, W)`. -/
theorem isPushout_baseRingHom
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {W : X.Opens} (hW : IsAffineOpen W) :
    IsPushout (baseRingHom f W) (CommRingCat.ofHom φ)
      (g.app W) (baseRingHom f' (g ⁻¹ᵁ W)) := by
  have hpo := (isIso_pushoutSection_iff hsq (top_le_preimage_top φ) le_top
      (preimage_eq_inf_preimage_top f' g W)).mp
    (isIso_pushoutSection_of_isAffineOpen hsq (top_le_preimage_top φ) le_top
      (preimage_eq_inf_preimage_top f' g W) (isAffineOpen_top (Spec (CommRingCat.of A)))
      (isAffineOpen_top (Spec (CommRingCat.of A'))) hW)
  refine hpo.of_iso' (Scheme.ΓSpecIso (CommRingCat.of A)).symm (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of A')).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact (baseRingHom_eq_ΓSpecIso_inv_appLE f W le_top).symm
  · simp only [Iso.symm_hom]
    exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, Scheme.Hom.appLE_eq_app]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact (baseRingHom_eq_ΓSpecIso_inv_appLE f' (g ⁻¹ᵁ W) le_top).symm

end Stacks.Cech

end

end
