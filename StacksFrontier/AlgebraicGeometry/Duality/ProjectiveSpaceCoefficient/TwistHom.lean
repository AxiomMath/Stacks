module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.CoefficientTopDegree
public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Equivalence
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSum
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# Maps out of the negative twists of projective space

On `ℙⁿ_R`, morphisms `𝒪(-i)[0]⟦q⟧ ⟶ F[0]⟦k⟧` in the derived category are computed by the
cohomology of `F ⊗ 𝒪(i)` in degree `k - q`: tensoring with `𝒪(i)` is an autoequivalence, it
carries `𝒪(-i)` to `𝒪`, and `Ext` out of `𝒪` is sheaf cohomology. Together with the
acyclicity of `(𝒪(d) ⊗ p^*M~) ⊗ 𝒪(i)` for `-n ≤ d + i ≤ -1`, this gives the vanishing of the
morphisms from the generators `𝒪(-1), …, 𝒪(-n)` into the candidate twisted inverse image
`(𝒪(-n-1) ⊗ p^*M~)[n]` of [Stacks, Tag 0A9W].

## Main results

* `Stacks.Duality.ProjCoeff.hom_twist_eq_zero`: every map `𝒪(-i)[0]⟦q⟧ ⟶ F[0]⟦k⟧` vanishes
  when `F ⊗ 𝒪(i)` has no cohomology in degree `k - q`.
* `Stacks.Duality.ProjCoeff.isZero_H_Ttw`: `(𝒪(d) ⊗ p^*M~) ⊗ 𝒪(i)` has no cohomology when
  `-n ≤ d + i ≤ -1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

variable (R : Type u) [CommRing R] (n : ℕ)

/-- `𝒪(-i) ⊗ 𝒪(i) ≅ 𝒪`. -/
def twistInvTensorIso (i : ℤ) :
    (tensorRightModules (P R n) (O R n i)).obj (O R n (-i)) ≅
      SheafOfModules.unit (P R n).ringCatSheaf :=
  Stacks.AlgebraicGeometry.ProjTwistRank.tensorTwistingSheafIso R n (-i) i ≪≫
    eqToIso (congrArg (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n))
      (neg_add_cancel i)) ≪≫
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading R n)

/-- `M ↦ (𝒪(d) ⊗ p^*M~) ⊗ 𝒪(i)`. -/
abbrev Ttw (d i : ℤ) : ModuleCat.{u} R ⥤ (P R n).Modules :=
  T R n d ⋙ tensorRightModules (P R n) (O R n i)

/-- Tensoring on the right by `𝒪(i)` is an equivalence of `𝒪_{ℙⁿ_R}`-modules. -/
instance (i : ℤ) : (tensorRightModules (P R n) (O R n i)).IsEquivalence :=
  Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule _ _

/-- `(𝒪(d) ⊗ p^*R~) ⊗ 𝒪(i) ≅ 𝒪(d + i)`. -/
def TtwObjIso₁ (d i : ℤ) :
    (tensorRightModules (P R n) (O R n i)).obj ((T R n d).obj (.of R R)) ≅
    (tensorRightModules (P R n) (O R n i)).obj (O R n d) :=
  (tensorRightModules (P R n) (O R n i)).mapIso
    (geometricFactorFormulaObjSelfIso R (W R n) (O R n d))

/-- `𝒪(d) ⊗ 𝒪(i) ≅ 𝒪(d + i)`. -/
def TtwObjIso₂ (d i : ℤ) : (tensorRightModules (P R n) (O R n i)).obj (O R n d) ≅
    O R n (d + i) :=
  Stacks.AlgebraicGeometry.ProjTwistRank.tensorTwistingSheafIso R n d i

/-- `(𝒪(d) ⊗ p^*R~) ⊗ 𝒪(i) ≅ 𝒪(d + i)`, the value of `Ttw` on `R`. -/
def TtwObjIso (d i : ℤ) : (Ttw R n d i).obj (.of R R) ≅ O R n (d + i) :=
  TtwObjIso₁ R n d i ≪≫ TtwObjIso₂ R n d i

/-- **`(𝒪(d) ⊗ p^*M~) ⊗ 𝒪(i)` has no cohomology when `-n ≤ d + i ≤ -1`.** -/
theorem isZero_H_Ttw (d i : ℤ) (h₁ : -(n : ℤ) ≤ d + i) (h₂ : d + i < 0) (q : ℕ)
    (L : ModuleCat.{u} R) : IsZero ((H R n q).obj ((Ttw R n d i).obj L)) := by
  have hT : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) (Ttw R n d i) := fun J => by
    have := preservesColimitsOfShape_T R n d J
    have : (tensorRightModules (P R n) (O R n i)).IsLeftAdjoint :=
      ((tensorRightModules (P R n) (O R n i)).asEquivalence.toAdjunction).isLeftAdjoint
    exact comp_preservesColimitsOfShape _ _
  have hqc : ∀ L, ((Ttw R n d i).obj L).IsQuasicoherent := fun L =>
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent (P R n).toRingedSpace _ _
      (isQuasicoherent_T R n d L)
      (Stacks.ProjectiveCohomology.isQuasicoherent_twistingSheaf R n i)
  exact isZero_H_of_forall R n (Ttw R n d i) hT hqc (fun p => (isZero_H_O_iff R n _ p |>.2
    (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_of_neg_le R n _ h₁ h₂ p)).of_iso
    ((H R n p).mapIso (TtwObjIso R n d i))) q L

section ExtGroup

attribute [local instance] HasExt.standard

/-- `Ext^j(𝒪, F)` vanishes as soon as `Hʲ(ℙⁿ_R, F)` does, as an abstract `Ext` group. -/
theorem subsingleton_ext_unit (F : (P R n).Modules) (j : ℕ)
    (h : IsZero ((H R n j).obj F)) :
    Subsingleton (Abelian.Ext.{u + 1} (SheafOfModules.unit (P R n).ringCatSheaf) F j) := by
  let := HasDerivedCategory.standard (SheafOfModules (P R n).ringCatSheaf)
  have : Subsingleton (((_root_.SheafOfModules.evaluation (P R n).ringCatSheaf
      (op ⊤)).rightDerived j).obj F) := ModuleCat.isZero_iff_subsingleton.1 h
  have := (Stacks.Cohomology.SpaceModules.derivedHomEquivModuleCohomology
    (P R n).ringCatSheaf F j).injective.subsingleton
  exact (Abelian.Ext.homEquiv.{u + 1, u + 1} (C := SheafOfModules (P R n).ringCatSheaf)
    (X := SheafOfModules.unit (P R n).ringCatSheaf) (Y := F) (n := j)).injective.subsingleton

end ExtGroup

section Hom

universe w

variable [HasDerivedCategory.{w} (P R n).Modules]

attribute [local instance] HasExt.standard

/-- Tensoring on the right by `𝒪(i)` is an equivalence of `𝒪_{ℙⁿ_R}`-modules. -/
instance (i : ℤ) : (tensorRightModules (P R n) (O R n i)).IsEquivalence :=
  Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule _ _

/-- `Ext^j(𝒪, F)` vanishes as soon as `Hʲ(ℙⁿ_R, F)` does. -/
theorem subsingleton_zExt_unit (F : (P R n).Modules) (j : ℕ)
    (h : IsZero ((H R n j).obj F)) :
    Subsingleton (Abelian.zExt (C := (P R n).Modules) (SheafOfModules.unit (P R n).ringCatSheaf) F
      (j : ℤ)) :=
  (Equiv.subsingleton_congr (Abelian.Ext.homEquiv.{w, u + 1} (C := (P R n).Modules)
    (X := SheafOfModules.unit (P R n).ringCatSheaf) (Y := F) (n := j))).1
    (subsingleton_ext_unit R n F j h)

/-- `Ext^j(𝒪(-i), F)` vanishes as soon as `Hʲ(ℙⁿ_R, F ⊗ 𝒪(i))` does. -/
theorem subsingleton_zExt_twist (i : ℤ) (F : (P R n).Modules) (j : ℕ)
    (h : IsZero ((H R n j).obj ((tensorRightModules (P R n) (O R n i)).obj F))) :
    Subsingleton (Abelian.zExt (O R n (-i)) F (j : ℤ)) := by
  have : (tensorRightModules (P R n) (O R n i)).Additive :=
    Functor.additive_of_isEquivalence _
  have := subsingleton_zExt_unit R n _ j h
  exact ((Abelian.zExt.mapAddEquiv (tensorRightModules (P R n) (O R n i)) (O R n (-i)) F j).trans
    (Abelian.zExt.congrAddEquiv (twistInvTensorIso R n i)
      (Iso.refl ((tensorRightModules (P R n) (O R n i)).obj F)) j)).injective.subsingleton

/-- Morphisms into a negative shift of a module in degree zero from a module in degree zero
vanish. -/
theorem shiftedHom_single_eq_zero_of_neg {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (X Y : C) (m : ℤ) (hm : m < 0)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦m⟧) : f = 0 := by
  have : (((DerivedCategory.singleFunctor C 0).obj Y)⟦m⟧).IsGE (-m) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 m (-m) (by omega)
  exact DerivedCategory.TStructure.t.zero f 0 (-m) (by omega)

/-- **Maps from a shifted negative twist into a shifted module.** If `F ⊗ 𝒪(i)` has no
cohomology in degree `k - q`, every map `𝒪(-i)[0]⟦q⟧ ⟶ F[0]⟦k⟧` vanishes. -/
theorem hom_twist_eq_zero (i : ℤ) (F : (P R n).Modules) (q k : ℤ)
    (h : ∀ j : ℕ, (j : ℤ) = k - q →
      IsZero ((H R n j).obj ((tensorRightModules (P R n) (O R n i)).obj F)))
    (f : ((DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n (-i)))⟦q⟧ ⟶
      ((DerivedCategory.singleFunctor (P R n).Modules 0).obj F)⟦k⟧) : f = 0 := by
  let X := (DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n (-i))
  let Y := (DerivedCategory.singleFunctor (P R n).Modules 0).obj F
  let e : (Y⟦k - q⟧)⟦q⟧ ≅ Y⟦k⟧ :=
    (shiftFunctorAdd' (DerivedCategory (P R n).Modules) (k - q) q k (by omega)).symm.app Y
  have hg : (shiftFunctor _ q).preimage (f ≫ e.inv) = 0 := by
    rcases lt_or_ge (k - q) 0 with hlt | hge
    · exact shiftedHom_single_eq_zero_of_neg _ _ _ hlt _
    · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hge
      have : Subsingleton (X ⟶ Y⟦k - q⟧) := by
        rw [hj]
        exact subsingleton_zExt_twist R n i F j (h j hj.symm)
      exact Subsingleton.elim _ _
  have hfe : f ≫ e.inv = 0 := by
    rw [← (shiftFunctor (DerivedCategory (P R n).Modules) q).map_preimage (f ≫ e.inv), hg,
      Functor.map_zero]
  simpa using hfe =≫ e.hom

end Hom

end Stacks.Duality.ProjCoeff
