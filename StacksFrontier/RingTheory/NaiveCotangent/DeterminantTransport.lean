module

public import StacksFrontier.Homology.TwoTermComplex.DeterminantLineBaseChange
public import StacksFrontier.RingTheory.NaiveCotangent.DeterminantSquare

/-!
# Transport of determinant lines along quasi-isomorphisms of two-term complexes

For a two-term complex `C = (C₁ → C₀)` of finite projective modules, the cochain complex
`twoTermComplex C` (the differential placed in degrees `-1` and `0`) is a two-term presentation of
its class in the derived category, and its determinant line is that of the linear map
`C₁ → C₀` (`NaiveCotangent.doubleEquiv`). A quasi-isomorphism `g : C ⟶ D` induces an
equivalence `detTransport g` of determinant lines: the quotient of the equivalences of
Stacks 0FJJ of the two legs of the surjective span `C ← C ⊕ (D₁ = D₁) → D`. It computes the
comparison of the determinant of Stacks 0FJM between any two presentations related by `g`, it
does not depend on the span, and it commutes with base change.

## Main definitions

* `NaiveCotangent.ofTwoTerm C e`: the two-term presentation `twoTermComplex C` of an object `K`
  of the derived category with `e : K ≅ C`.
* `NaiveCotangent.doubleEquiv C`: the determinant line of `twoTermComplex C` is that of `C`.
* `NaiveCotangent.ChainMap.toHom g`: a chain map as a morphism of two-term complexes.
* `NaiveCotangent.detTransport g`: the equivalence of determinant lines along a
  quasi-isomorphism.

## Main results

* `NaiveCotangent.detPresentationIso_ofTwoTerm`: `detTransport g` computes the comparison of
  the determinant of Stacks 0FJM between two presentations related by `g`.
* `NaiveCotangent.detTransport_eq_of_span`: `detTransport g` is computed by any surjective span.
* `NaiveCotangent.detTransport_baseChange`: `detTransport` commutes with base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra TwoTermDeterminant
open scoped TensorProduct

namespace NaiveCotangent

universe u

attribute [local instance] HasDerivedCategory.standard

variable {B : Type u} [CommRing B]

/-! ### The cochain complex of a two-term complex -/

section Double

variable (C : TwoTerm.{u, u, u} B)

/-- Degree `-1` of `twoTermComplex C` is `C₁`. -/
def doubleNegEquiv : (Deformation.Artin.twoTermComplex C).X (-1) ≃ₗ[B] C.X₁ :=
  (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom C.d)
    ComplexShape.upIntRelNegOneZero).toLinearEquiv

/-- Degree `0` of `twoTermComplex C` is `C₀`. -/
def doubleZeroEquiv : (Deformation.Artin.twoTermComplex C).X 0 ≃ₗ[B] C.X₀ :=
  (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom C.d)
    ComplexShape.upIntRelNegOneZero (by decide)).toLinearEquiv

/-- The differential of `twoTermComplex C` from degree `-1` to degree `0` is `C.d`, read through
the identifications of the two terms. -/
theorem doubleZeroEquiv_d (x : (Deformation.Artin.twoTermComplex C).X (-1)) :
    doubleZeroEquiv C (((Deformation.Artin.twoTermComplex C).d (-1) 0).hom x) =
      C.d (doubleNegEquiv C x) := by
  show (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom C.d)
      ComplexShape.upIntRelNegOneZero (by decide)).hom.hom
        (((HomologicalComplex.double (ModuleCat.ofHom C.d)
          ComplexShape.upIntRelNegOneZero).d (-1) 0).hom x) = _
  rw [HomologicalComplex.double_d (ModuleCat.ofHom C.d) ComplexShape.upIntRelNegOneZero
    (by decide)]
  simp [doubleNegEquiv]
  rfl

/-- The identification of the differential of `twoTermComplex C` with `C.d`, as a morphism of
two-term complexes bijective in both degrees. -/
def doubleHom : TwoTermComplex.Hom ((Deformation.Artin.twoTermComplex C).d (-1) 0).hom C.d where
  neg := (doubleNegEquiv C).toLinearMap
  zero := (doubleZeroEquiv C).toLinearMap
  comm := LinearMap.ext fun x => doubleZeroEquiv_d C x

/-- `doubleHom` is bijective in degree `-1`. -/
theorem bijective_doubleHom_neg : Function.Bijective (doubleHom C).neg :=
  (doubleNegEquiv C).bijective

/-- `doubleHom` is bijective in degree `0`. -/
theorem bijective_doubleHom_zero : Function.Bijective (doubleHom C).zero :=
  (doubleZeroEquiv C).bijective

/-- The inverse of `doubleHom C`. -/
def doubleHomInv : TwoTermComplex.Hom C.d ((Deformation.Artin.twoTermComplex C).d (-1) 0).hom where
  neg := (doubleNegEquiv C).symm.toLinearMap
  zero := (doubleZeroEquiv C).symm.toLinearMap
  comm := LinearMap.ext fun x => (doubleZeroEquiv C).injective (by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply, doubleZeroEquiv_d])

/-- `doubleHomInv` is bijective in degree `-1`. -/
theorem bijective_doubleHomInv_neg : Function.Bijective (doubleHomInv C).neg :=
  (doubleNegEquiv C).symm.bijective

/-- `doubleHomInv` is bijective in degree `0`. -/
theorem bijective_doubleHomInv_zero : Function.Bijective (doubleHomInv C).zero :=
  (doubleZeroEquiv C).symm.bijective

/-- `doubleHom` is degreewise surjective. -/
private theorem isDegreewiseSurjective_doubleHom : (doubleHom C).IsDegreewiseSurjective :=
  .of_bijective (bijective_doubleHom_neg C) (bijective_doubleHom_zero C)

/-- `doubleHom` is a quasi-isomorphism. -/
private theorem isQuasiIso_doubleHom : (doubleHom C).IsQuasiIso :=
  TwoTermComplex.Hom.isQuasiIso_of_bijective _ (bijective_doubleHom_neg C)
    (bijective_doubleHom_zero C)

/-- `doubleHomInv` is a quasi-isomorphism. -/
private theorem isQuasiIso_doubleHomInv : (doubleHomInv C).IsQuasiIso :=
  TwoTermComplex.Hom.isQuasiIso_of_bijective _ (bijective_doubleHomInv_neg C)
    (bijective_doubleHomInv_zero C)

variable [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀]

/-- The degree `-1` term of `twoTermComplex C` is finite. -/
instance finite_twoTermComplex_X_negOne :
    Module.Finite B ((Deformation.Artin.twoTermComplex C).X (-1)) :=
  Module.Finite.equiv (doubleNegEquiv C).symm

/-- The degree `-1` term of `twoTermComplex C` is projective. -/
instance projective_twoTermComplex_X_negOne :
    Module.Projective B ((Deformation.Artin.twoTermComplex C).X (-1)) :=
  Module.Projective.of_equiv (doubleNegEquiv C).symm

/-- The degree `0` term of `twoTermComplex C` is finite. -/
instance finite_twoTermComplex_X_zero :
    Module.Finite B ((Deformation.Artin.twoTermComplex C).X 0) :=
  Module.Finite.equiv (doubleZeroEquiv C).symm

/-- The degree `0` term of `twoTermComplex C` is projective. -/
instance projective_twoTermComplex_X_zero :
    Module.Projective B ((Deformation.Artin.twoTermComplex C).X 0) :=
  Module.Projective.of_equiv (doubleZeroEquiv C).symm

/-- The terms of `twoTermComplex C` are finite projective. -/
theorem twoTermComplex_finite_projective (i : ℤ) :
    Module.Finite B ((Deformation.Artin.twoTermComplex C).X i) ∧
      Module.Projective B ((Deformation.Artin.twoTermComplex C).X i) := by
  by_cases h₁ : i = -1
  · subst h₁; exact ⟨inferInstance, inferInstance⟩
  · by_cases h₀ : i = 0
    · subst h₀; exact ⟨inferInstance, inferInstance⟩
    · have hz := HomologicalComplex.isZero_double_X (ModuleCat.ofHom C.d)
        ComplexShape.upIntRelNegOneZero i h₁ h₀
      have : Subsingleton ((Deformation.Artin.twoTermComplex C).X i) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact ⟨inferInstance, inferInstance⟩

/-- **The determinant line of `twoTermComplex C` is that of `C`.** -/
def doubleEquiv :
    TwoTermComplex.determinantLine ((Deformation.Artin.twoTermComplex C).d (-1) 0).hom ≃ₗ[B]
      TwoTermComplex.determinantLine C.d :=
  (doubleHom C).detEquiv (.of_bijective (bijective_doubleHom_neg C) (bijective_doubleHom_zero C))
    (TwoTermComplex.Hom.isQuasiIso_of_bijective _ (bijective_doubleHom_neg C)
      (bijective_doubleHom_zero C))

omit [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀] in
/-- `twoTermComplex C` has rank zero when `C` has. -/
theorem isRankZero_double (hC : TwoTermComplex.IsRankZero C.d) :
    TwoTermComplex.IsRankZero ((Deformation.Artin.twoTermComplex C).d (-1) 0).hom := fun q =>
  (congrFun (Module.rankAtStalk_eq_of_equiv (doubleNegEquiv C)) q).trans
    ((hC q).trans (congrFun (Module.rankAtStalk_eq_of_equiv (doubleZeroEquiv C)) q).symm)

/-- `doubleEquiv` carries the canonical element to the canonical element. -/
theorem doubleEquiv_delta (hC : TwoTermComplex.IsRankZero C.d) :
    doubleEquiv C (TwoTermComplex.delta _ (isRankZero_double C hC)) =
      TwoTermComplex.delta C.d hC :=
  TwoTermComplex.Hom.detEquiv_delta _ _ _ _ _

/-- **`twoTermComplex C` as a two-term presentation** of an object `K` of the derived category
together with an isomorphism `K ≅ twoTermComplex C`. -/
def ofTwoTerm {K : DerivedCategory (ModuleCat.{u} B)}
    (e : K ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex C)) :
    TwoTermPresentation K where
  complex := Deformation.Artin.twoTermComplex C
  finite i := (twoTermComplex_finite_projective C i).1
  projective i := (twoTermComplex_finite_projective C i).2
  strictlyGE := (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi =>
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)
  strictlyLE := (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)
  iso := e

end Double

/-! ### Chain maps as morphisms of two-term complexes -/

section ChainMap

variable {C D E : TwoTerm.{u, u, u} B}

/-- A chain map of two-term complexes, as a morphism `TwoTermComplex.Hom` of the differentials. -/
def ChainMap.toHom (g : ChainMap C D) : TwoTermComplex.Hom C.d D.d where
  neg := g.f₁
  zero := g.f₀
  comm := g.comm.symm

/-- The degree `-1` component of `ChainMap.toHom g` is `g.f₁`. -/
@[simp] theorem ChainMap.toHom_neg (g : ChainMap C D) : g.toHom.neg = g.f₁ := rfl

/-- The degree `0` component of `ChainMap.toHom g` is `g.f₀`. -/
@[simp] theorem ChainMap.toHom_zero (g : ChainMap C D) : g.toHom.zero = g.f₀ := rfl

/-- The composite of chain maps is the composite of the morphisms of two-term complexes. -/
theorem ChainMap.toHom_comp (h : ChainMap D E) (g : ChainMap C D) :
    (h.comp g).toHom = h.toHom.comp g.toHom := rfl

/-- A chain map of two-term complexes is a quasi-isomorphism exactly when it is one as a morphism
of the differentials. -/
private theorem isQuasiIso_toHom_iff {g : ChainMap C D} : g.toHom.IsQuasiIso ↔ IsQuasiIso g := by
  have h₁ : (g.toHom.hMinus : LinearMap.ker C.d → LinearMap.ker D.d) = g.onH₁ := by
    funext x
    exact Subtype.ext rfl
  have h₀ : (g.toHom.hZero : C.X₀ ⧸ LinearMap.range C.d → D.X₀ ⧸ LinearMap.range D.d) =
      g.onH₀ := by
    funext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  exact ⟨fun h => ⟨h₁ ▸ h.1, h₀ ▸ h.2⟩, fun h => ⟨h₁ ▸ h.1, h₀ ▸ h.2⟩⟩

/-- A quasi-isomorphism of two-term complexes is a quasi-isomorphism of the differentials. -/
theorem ChainMap.isQuasiIso_toHom {g : ChainMap C D} (hg : IsQuasiIso g) :
    g.toHom.IsQuasiIso :=
  isQuasiIso_toHom_iff.2 hg

/-- Degreewise surjectivity of a chain map, as a morphism of the differentials. -/
theorem ChainMap.isDegreewiseSurjective_toHom {g : ChainMap C D}
    (h₁ : Function.Surjective g.f₁) (h₀ : Function.Surjective g.f₀) :
    g.toHom.IsDegreewiseSurjective :=
  ⟨h₁, h₀⟩

end ChainMap

/-- Morphisms of two-term complexes are determined by their two components. -/
theorem _root_.TwoTermComplex.Hom.ext_neg_zero {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module B K₁] [AddCommGroup K₀] [Module B K₀]
    [AddCommGroup L₁] [Module B L₁] [AddCommGroup L₀] [Module B L₀]
    {K : K₁ →ₗ[B] K₀} {L : L₁ →ₗ[B] L₀} {a b : TwoTermComplex.Hom K L}
    (h₁ : a.neg = b.neg) (h₀ : a.zero = b.zero) : a = b := by
  cases a
  cases b
  simp only at h₁ h₀
  subst h₁ h₀
  rfl

/-! ### The comparison of the determinant along a surjective quasi-isomorphism -/

section Comparison

variable {C D : TwoTerm.{u, u, u} B}
  [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀]
  [Module.Finite B D.X₁] [Module.Projective B D.X₁] [Module.Finite B D.X₀]
  [Module.Projective B D.X₀]

/-- The morphism of cochain complexes induced by a chain map, read on the differentials through
the identifications of `doubleEquiv`, is the chain map itself. -/
theorem doubleHom_comp_hom (g : ChainMap C D) {K L : DerivedCategory (ModuleCat.{u} B)}
    (eC : K ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex C))
    (eD : L ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex D)) :
    (doubleHom D).comp ((ofTwoTerm C eC).hom (ofTwoTerm D eD) (Deformation.Artin.twoTermHom g)) =
      g.toHom.comp (doubleHom C) := by
  have h₁ : ((doubleHom D).comp ((ofTwoTerm C eC).hom (ofTwoTerm D eD)
      (Deformation.Artin.twoTermHom g))).neg = (g.toHom.comp (doubleHom C)).neg := by
    refine LinearMap.ext fun x => ?_
    show (doubleNegEquiv D) (((Deformation.Artin.twoTermHom g).f (-1)).hom x) =
      g.f₁ (doubleNegEquiv C x)
    rw [Deformation.Artin.twoTermHom_f_neg_one]
    exact (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom D.d)
      ComplexShape.upIntRelNegOneZero).inv_hom_id_apply _
  have h₀ : ((doubleHom D).comp ((ofTwoTerm C eC).hom (ofTwoTerm D eD)
      (Deformation.Artin.twoTermHom g))).zero = (g.toHom.comp (doubleHom C)).zero := by
    refine LinearMap.ext fun x => ?_
    show (doubleZeroEquiv D) (((Deformation.Artin.twoTermHom g).f 0).hom x) =
      g.f₀ (doubleZeroEquiv C x)
    rw [Deformation.Artin.twoTermHom_f_zero]
    exact (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom D.d)
      ComplexShape.upIntRelNegOneZero (by decide)).inv_hom_id_apply _
  cases h : (doubleHom D).comp ((ofTwoTerm C eC).hom (ofTwoTerm D eD)
    (Deformation.Artin.twoTermHom g))
  cases h' : g.toHom.comp (doubleHom C)
  rw [h] at h₁ h₀
  rw [h'] at h₁ h₀
  simp only at h₁ h₀
  subst h₁ h₀
  rfl

/-- `TwoTermComplex.Hom.detEquiv` depends only on the morphism. -/
theorem _root_.TwoTermComplex.Hom.detEquiv_congr {K₁ K₀ L₁ L₀ : Type u}
    [AddCommGroup K₁] [Module B K₁] [Module.Finite B K₁] [Module.Projective B K₁]
    [AddCommGroup K₀] [Module B K₀] [Module.Finite B K₀] [Module.Projective B K₀]
    [AddCommGroup L₁] [Module B L₁] [Module.Finite B L₁] [Module.Projective B L₁]
    [AddCommGroup L₀] [Module B L₀] [Module.Finite B L₀] [Module.Projective B L₀]
    {K : K₁ →ₗ[B] K₀} {L : L₁ →ₗ[B] L₀} {a a' : TwoTermComplex.Hom K L} (h : a = a')
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) (ha' : a'.IsDegreewiseSurjective)
    (hqa' : a'.IsQuasiIso) : a.detEquiv ha hqa = a'.detEquiv ha' hqa' := by
  subst h
  rfl

/-- **The determinant of Stacks 0FJM, compared along a surjective quasi-isomorphism.** If two
two-term presentations `twoTermComplex C` and `twoTermComplex D` of `K` are related by a
degreewise-surjective quasi-isomorphism `g : C ⟶ D` compatible with the two isomorphisms to
`K`, then their identifications with the determinant of `K` differ by the equivalence of
determinant lines of Stacks 0FJJ attached to `g`. -/
theorem doubleEquiv_detPresentationIso (K : PerfectTwoTermComplex B)
    (eC : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex C))
    (eD : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex D))
    (g : ChainMap C D) (hg : eC.hom ≫ DerivedCategory.Q.map (Deformation.Artin.twoTermHom g) =
      eD.hom)
    (h₁ : Function.Surjective g.f₁) (h₀ : Function.Surjective g.f₀) (hq : IsQuasiIso g)
    (x : ((TwoTermDeterminant.det B).obj ⟨K⟩).of.obj) :
    doubleEquiv D (detPresentationIso K (ofTwoTerm D eD) x) =
      g.toHom.detEquiv (g.isDegreewiseSurjective_toHom h₁ h₀) (ChainMap.isQuasiIso_toHom hq)
        (doubleEquiv C (detPresentationIso K (ofTwoTerm C eC) x)) := by
  have hQ : DerivedCategory.Q.map (Deformation.Artin.twoTermHom g) = eC.inv ≫ eD.hom := by
    rw [← hg, Iso.inv_hom_id_assoc]
  have hiso : IsIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom g)) := by
    rw [hQ]; exact ⟨⟨eD.inv ≫ eC.hom, by simp, by simp⟩⟩
  let := (ofTwoTerm C eC).finite (-1)
  let := (ofTwoTerm C eC).projective (-1)
  let := (ofTwoTerm C eC).finite 0
  let := (ofTwoTerm C eC).projective 0
  let := (ofTwoTerm D eD).finite (-1)
  let := (ofTwoTerm D eD).projective (-1)
  let := (ofTwoTerm D eD).finite 0
  let := (ofTwoTerm D eD).projective 0
  have hcomp := doubleHom_comp_hom g eC eD
  have hn : ∀ w, doubleNegEquiv D (((ofTwoTerm C eC).hom (ofTwoTerm D eD)
      (Deformation.Artin.twoTermHom g)).neg w) = g.f₁ (doubleNegEquiv C w) :=
    fun w => LinearMap.congr_fun (congrArg TwoTermComplex.Hom.neg hcomp) w
  have hz : ∀ w, doubleZeroEquiv D (((ofTwoTerm C eC).hom (ofTwoTerm D eD)
      (Deformation.Artin.twoTermHom g)).zero w) = g.f₀ (doubleZeroEquiv C w) :=
    fun w => LinearMap.congr_fun (congrArg TwoTermComplex.Hom.zero hcomp) w
  have hq' : ((ofTwoTerm C eC).hom (ofTwoTerm D eD)
      (Deformation.Artin.twoTermHom g)).IsQuasiIso := by
    have he : (ofTwoTerm C eC).hom (ofTwoTerm D eD) (Deformation.Artin.twoTermHom g) =
        (doubleHomInv D).comp (g.toHom.comp (doubleHom C)) := by
      refine TwoTermComplex.Hom.ext_neg_zero ?_ ?_
      · refine LinearMap.ext fun w => (doubleNegEquiv D).injective ?_
        rw [hn]
        exact ((doubleNegEquiv D).apply_symm_apply _).symm
      · refine LinearMap.ext fun w => (doubleZeroEquiv D).injective ?_
        rw [hz]
        exact ((doubleZeroEquiv D).apply_symm_apply _).symm
    rw [he]
    exact (isQuasiIso_doubleHomInv D).comp ((ChainMap.isQuasiIso_toHom hq).comp
      (isQuasiIso_doubleHom C))
  have hs' : ((ofTwoTerm C eC).hom (ofTwoTerm D eD)
      (Deformation.Artin.twoTermHom g)).IsDegreewiseSurjective := by
    refine ⟨fun y => ?_, fun y => ?_⟩
    · obtain ⟨z, hz'⟩ := h₁ (doubleNegEquiv D y)
      refine ⟨(doubleNegEquiv C).symm z, (doubleNegEquiv D).injective ?_⟩
      exact (hn _).trans ((congrArg g.f₁ (LinearEquiv.apply_symm_apply _ z)).trans hz')
    · obtain ⟨z, hz'⟩ := h₀ (doubleZeroEquiv D y)
      refine ⟨(doubleZeroEquiv C).symm z, (doubleZeroEquiv D).injective ?_⟩
      exact (hz _).trans ((congrArg g.f₀ (LinearEquiv.apply_symm_apply _ z)).trans hz')
  have hf : (ofTwoTerm C eC).iso.hom ≫ DerivedCategory.Q.map (Deformation.Artin.twoTermHom g) ≫
      (ofTwoTerm D eD).iso.inv =
      (𝟙 (⟨K⟩ : Core (PerfectTwoTermComplex B)) : _ ⟶ _).iso.hom.hom := by
    show eC.hom ≫ DerivedCategory.Q.map (Deformation.Artin.twoTermHom g) ≫ eD.inv = 𝟙 _
    rw [← Category.assoc, hg, Iso.hom_inv_id]
  have key := detPresentationIso_det_map K K (ofTwoTerm C eC) (ofTwoTerm D eD) (𝟙 _)
    (Deformation.Artin.twoTermHom g) hf hs' hq' x
  have hid : ((TwoTermDeterminant.det B).map (𝟙 (⟨K⟩ : Core (PerfectTwoTermComplex B)))).iso.hom
      x = x := by
    have h := (TwoTermDeterminant.det B).map_id (⟨K⟩ : Core (PerfectTwoTermComplex B))
    rw [h]
    rfl
  rw [hid] at key
  rw [show detPresentationIso K (ofTwoTerm D eD) x = ((ofTwoTerm C eC).hom (ofTwoTerm D eD)
    (Deformation.Artin.twoTermHom g)).detEquiv hs' hq'
      (detPresentationIso K (ofTwoTerm C eC) x) from key]
  have hg₁ := g.isDegreewiseSurjective_toHom h₁ h₀
  have hgq := ChainMap.isQuasiIso_toHom hq
  have e₁ := TwoTermComplex.Hom.detEquiv_comp (doubleHom D) _ (isDegreewiseSurjective_doubleHom D)
    (isQuasiIso_doubleHom D) hs' hq' ((isDegreewiseSurjective_doubleHom D).comp hs')
    ((isQuasiIso_doubleHom D).comp hq')
  have e₂ := TwoTermComplex.Hom.detEquiv_comp g.toHom (doubleHom C) hg₁ hgq
    (isDegreewiseSurjective_doubleHom C) (isQuasiIso_doubleHom C)
    (hg₁.comp (isDegreewiseSurjective_doubleHom C)) (hgq.comp (isQuasiIso_doubleHom C))
  have e₃ := TwoTermComplex.Hom.detEquiv_congr hcomp
    ((isDegreewiseSurjective_doubleHom D).comp hs') ((isQuasiIso_doubleHom D).comp hq')
    (hg₁.comp (isDegreewiseSurjective_doubleHom C)) (hgq.comp (isQuasiIso_doubleHom C))
  exact congrArg (fun e => e (detPresentationIso K (ofTwoTerm C eC) x))
    (e₁.symm.trans (e₃.trans e₂))

end Comparison

/-! ### Transport along a quasi-isomorphism -/

section Transport

variable {C D : TwoTerm.{u, u, u} B}
  [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀]
  [Module.Finite B D.X₁] [Module.Projective B D.X₁] [Module.Finite B D.X₀]
  [Module.Projective B D.X₀]

omit [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀] [Module.Finite B D.X₁] [Module.Projective B D.X₁]
  [Module.Finite B D.X₀] [Module.Projective B D.X₀] in
/-- A chain map of two-term complexes is a quasi-isomorphism exactly when it is one as a morphism
of the differentials. -/
theorem ChainMap.isQuasiIso_of_toHom {g : ChainMap C D} (hg : g.toHom.IsQuasiIso) :
    IsQuasiIso g :=
  isQuasiIso_toHom_iff.1 hg

/-- **The transport of determinant lines along a quasi-isomorphism** `g : C ⟶ D` of two-term
complexes of finite projective modules: the equivalences of Stacks 0FJJ of the two legs of the
surjective span `C ← C ⊕ (D₁ = D₁) → D`. -/
def detTransport (g : ChainMap C D) (hg : IsQuasiIso g) :
    TwoTermComplex.determinantLine C.d ≃ₗ[B] TwoTermComplex.determinantLine D.d :=
  ((spanLeft C D).toHom.detEquiv
      ((spanLeft C D).isDegreewiseSurjective_toHom (spanLeft_surjective₁ C D)
        (spanLeft_surjective₀ C D))
      (ChainMap.isQuasiIso_toHom (isQuasiIso_of_isHomotopyEquiv
        (spanLeft_isHomotopyEquiv C D)))).symm.trans
    ((spanRight g).toHom.detEquiv
      ((spanRight g).isDegreewiseSurjective_toHom (spanRight_surjective₁ g)
        (spanRight_surjective₀ g hg))
      (ChainMap.isQuasiIso_toHom (spanRight_isQuasiIso g hg)))

omit [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀] [Module.Finite B D.X₁] [Module.Projective B D.X₁]
  [Module.Finite B D.X₀] [Module.Projective B D.X₀] in
/-- `twoTermHom` of a homotopy equivalence becomes an isomorphism in the derived category. -/
theorem isIso_Q_map_twoTermHom_of_isQuasiIso {g : ChainMap C D} (hg : IsQuasiIso g) :
    IsIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom g)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (Stacks.TwoTermDoubleQuasiIso.quasiIso_mapDouble ComplexShape.upIntRelNegOneZero hg)

/-- **`detTransport` computes the determinant of Stacks 0FJM**: if two presentations
`twoTermComplex C` and `twoTermComplex D` of `K` are related by a quasi-isomorphism `g`, their
identifications with the determinant of `K` differ by `detTransport g`. -/
theorem doubleEquiv_detPresentationIso_of_isQuasiIso (K : PerfectTwoTermComplex B)
    (eC : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex C))
    (eD : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex D))
    (g : ChainMap C D) (hq : IsQuasiIso g)
    (hg : eC.hom ≫ DerivedCategory.Q.map (Deformation.Artin.twoTermHom g) = eD.hom)
    (x : ((TwoTermDeterminant.det B).obj ⟨K⟩).of.obj) :
    doubleEquiv D (detPresentationIso K (ofTwoTerm D eD) x) =
      detTransport g hq (doubleEquiv C (detPresentationIso K (ofTwoTerm C eC) x)) := by
  have hl : IsIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom (spanLeft C D))) :=
    Deformation.Artin.isIso_Q_map_twoTermHom (spanLeft_isHomotopyEquiv C D)
  let eS : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex (spanTwoTerm C D)) :=
    eC ≪≫ (asIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom (spanLeft C D)))).symm
  have hL : eS.hom ≫ DerivedCategory.Q.map (Deformation.Artin.twoTermHom (spanLeft C D)) =
      eC.hom := by
    simp [eS]
  have hR : eS.hom ≫ DerivedCategory.Q.map (Deformation.Artin.twoTermHom (spanRight g)) =
      eD.hom := by
    have hh : DerivedCategory.Q.map (Deformation.Artin.twoTermHom (spanRight g)) =
        DerivedCategory.Q.map (Deformation.Artin.twoTermHom (spanLeft C D)) ≫
          DerivedCategory.Q.map (Deformation.Artin.twoTermHom g) := by
      rw [← Functor.map_comp, ← Deformation.Artin.twoTermHom_comp]
      exact Deformation.Artin.Q_map_twoTermHom_eq_of_homotopic (spanRight_homotopic g)
    rw [hh, ← Category.assoc, hL, hg]
  have e₁ := doubleEquiv_detPresentationIso K eS eC (spanLeft C D) hL
    (spanLeft_surjective₁ C D) (spanLeft_surjective₀ C D)
    (isQuasiIso_of_isHomotopyEquiv (spanLeft_isHomotopyEquiv C D)) x
  have e₂ := doubleEquiv_detPresentationIso K eS eD (spanRight g) hR
    (spanRight_surjective₁ g) (spanRight_surjective₀ g hq) (spanRight_isQuasiIso g hq) x
  rw [e₂, e₁]
  simp only [detTransport, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end Transport

/-! ### Independence of the span, and base change -/

section SpanIndependence

variable {C D : TwoTerm.{u, u, u} B}
  [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀]
  [Module.Finite B D.X₁] [Module.Projective B D.X₁] [Module.Finite B D.X₀]
  [Module.Projective B D.X₀]

/-- A two-term complex of finite projective modules is a perfect object of Tor-amplitude in
`[-1, 0]`. -/
theorem perfectTwoTermComplexProperty_twoTermComplex (C : TwoTerm.{u, u, u} B)
    [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
    [Module.Projective B C.X₀] :
    perfectTwoTermComplexProperty B
      (DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex C)) := by
  let T := ofTwoTerm C (Iso.refl _)
  refine ⟨⟨T.complex, -1, 0, T.strictlyGE, T.strictlyLE, T.finite, T.projective, ⟨T.iso⟩⟩,
    ⟨T.complex, fun i => ?_, T.strictlyGE, T.strictlyLE, ⟨T.iso⟩⟩⟩
  have := T.projective i
  infer_instance

/-- **`detTransport` is computed by any surjective span**: if `l : S ⟶ C` and `r : S ⟶ D` are
degreewise-surjective quasi-isomorphisms with `r = g ∘ l` in the derived category, then
`detTransport g` is the equivalence of `r` composed with the inverse of that of `l`. -/
theorem detTransport_eq_of_span {S : TwoTerm.{u, u, u} B}
    [Module.Finite B S.X₁] [Module.Projective B S.X₁] [Module.Finite B S.X₀]
    [Module.Projective B S.X₀]
    (g : ChainMap C D) (hg : IsQuasiIso g) (l : ChainMap S C) (r : ChainMap S D)
    (hl₁ : Function.Surjective l.f₁) (hl₀ : Function.Surjective l.f₀) (hl : IsQuasiIso l)
    (hr₁ : Function.Surjective r.f₁) (hr₀ : Function.Surjective r.f₀) (hr : IsQuasiIso r)
    (hlr : DerivedCategory.Q.map (Deformation.Artin.twoTermHom r) =
      DerivedCategory.Q.map (Deformation.Artin.twoTermHom l) ≫
        DerivedCategory.Q.map (Deformation.Artin.twoTermHom g))
    (φ : TwoTermComplex.determinantLine C.d) :
    detTransport g hg φ =
      r.toHom.detEquiv (r.isDegreewiseSurjective_toHom hr₁ hr₀) (ChainMap.isQuasiIso_toHom hr)
        ((l.toHom.detEquiv (l.isDegreewiseSurjective_toHom hl₁ hl₀)
          (ChainMap.isQuasiIso_toHom hl)).symm φ) := by
  have := isIso_Q_map_twoTermHom_of_isQuasiIso hg
  have := isIso_Q_map_twoTermHom_of_isQuasiIso hl
  let K : PerfectTwoTermComplex B :=
    ⟨_, perfectTwoTermComplexProperty_twoTermComplex C⟩
  let eC : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex C) := Iso.refl _
  let eD : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex D) :=
    asIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom g))
  let eS : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex S) :=
    (asIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom l))).symm
  obtain ⟨x, rfl⟩ := (doubleEquiv C).surjective φ
  obtain ⟨x, rfl⟩ := (detPresentationIso K (ofTwoTerm C eC)).surjective x
  have h₁ := doubleEquiv_detPresentationIso_of_isQuasiIso K eC eD g hg (by simp [eC, eD]) x
  have h₂ := doubleEquiv_detPresentationIso K eS eC l (by simp [eS, eC]) hl₁ hl₀ hl x
  have h₃ := doubleEquiv_detPresentationIso K eS eD r (by simp [eS, eD, hlr]) hr₁ hr₀ hr x
  rw [← h₁, h₃, h₂, LinearEquiv.symm_apply_apply]

/-- **`detTransport` is functorial**: the transport along a composite of quasi-isomorphisms is
the composite of the transports. -/
theorem detTransport_comp {E : TwoTerm.{u, u, u} B} [Module.Finite B E.X₁]
    [Module.Projective B E.X₁] [Module.Finite B E.X₀] [Module.Projective B E.X₀]
    (g : ChainMap C D) (g' : ChainMap D E) (hg : IsQuasiIso g) (hg' : IsQuasiIso g')
    (hgg : IsQuasiIso (g'.comp g)) (φ : TwoTermComplex.determinantLine C.d) :
    detTransport (g'.comp g) hgg φ = detTransport g' hg' (detTransport g hg φ) := by
  have := isIso_Q_map_twoTermHom_of_isQuasiIso hg
  have := isIso_Q_map_twoTermHom_of_isQuasiIso hgg
  let K : PerfectTwoTermComplex B :=
    ⟨_, perfectTwoTermComplexProperty_twoTermComplex C⟩
  let eC : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex C) := Iso.refl _
  let eD : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex D) :=
    asIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom g))
  let eE : K.obj ≅ DerivedCategory.Q.obj (Deformation.Artin.twoTermComplex E) :=
    asIso (DerivedCategory.Q.map (Deformation.Artin.twoTermHom (g'.comp g)))
  obtain ⟨x, rfl⟩ := (doubleEquiv C).surjective φ
  obtain ⟨x, rfl⟩ := (detPresentationIso K (ofTwoTerm C eC)).surjective x
  have h₁ := doubleEquiv_detPresentationIso_of_isQuasiIso K eC eD g hg (by simp [eC, eD]) x
  have h₂ := doubleEquiv_detPresentationIso_of_isQuasiIso K eD eE g' hg' (by
    simp only [eD, eE, asIso_hom]
    rw [← Functor.map_comp, ← Deformation.Artin.twoTermHom_comp]) x
  have h₃ := doubleEquiv_detPresentationIso_of_isQuasiIso K eC eE (g'.comp g) hgg
    (by simp [eC, eE]) x
  rw [← h₃, h₂, h₁]

end SpanIndependence

section BaseChange

variable {C D : TwoTerm.{u, u, u} B}
  [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀]
  [Module.Finite B D.X₁] [Module.Projective B D.X₁] [Module.Finite B D.X₀]
  [Module.Projective B D.X₀]
  (B' : Type u) [CommRing B'] [Algebra B B']

/-- The base change of a finite degree `-1` term is finite. -/
instance TwoTerm.finite_baseChange_X₁ (E : TwoTerm.{u, u, u} B) [Module.Finite B E.X₁] :
    Module.Finite B' (E.baseChange B').X₁ :=
  inferInstanceAs (Module.Finite B' (B' ⊗[B] E.X₁))

/-- The base change of a finite degree `0` term is finite. -/
instance TwoTerm.finite_baseChange_X₀ (E : TwoTerm.{u, u, u} B) [Module.Finite B E.X₀] :
    Module.Finite B' (E.baseChange B').X₀ :=
  inferInstanceAs (Module.Finite B' (B' ⊗[B] E.X₀))

/-- The base change of a projective degree `-1` term is projective. -/
instance TwoTerm.projective_baseChange_X₁ (E : TwoTerm.{u, u, u} B) [Module.Projective B E.X₁] :
    Module.Projective B' (E.baseChange B').X₁ :=
  inferInstanceAs (Module.Projective B' (B' ⊗[B] E.X₁))

/-- The base change of a projective degree `0` term is projective. -/
instance TwoTerm.projective_baseChange_X₀ (E : TwoTerm.{u, u, u} B) [Module.Projective B E.X₀] :
    Module.Projective B' (E.baseChange B').X₀ :=
  inferInstanceAs (Module.Projective B' (B' ⊗[B] E.X₀))

/-- The base change `det(C) → det(C ⊗_B B')` of the determinant line of a two-term complex of
finite projective modules, `TwoTermComplex.determinantLineBaseChangeMap` read at the base change
`C.baseChange B'` of the two-term complex, as a semilinear map along `B → B'`. -/
def TwoTerm.detBaseChange (E : TwoTerm.{u, u, u} B) [Module.Finite B E.X₁]
    [Module.Projective B E.X₁] [Module.Finite B E.X₀] [Module.Projective B E.X₀] :
    TwoTermComplex.determinantLine E.d →ₛₗ[algebraMap B B']
      TwoTermComplex.determinantLine (E.baseChange B').d where
  toFun := TwoTermComplex.determinantLineBaseChangeMap B' E.d
  map_add' := map_add _
  map_smul' b φ := (map_smul (TwoTermComplex.determinantLineBaseChangeMap B' E.d) b φ).trans
    (algebraMap_smul B' b _).symm

/-- `TwoTerm.detBaseChange` is the base change map of determinant lines. -/
theorem TwoTerm.detBaseChange_apply (E : TwoTerm.{u, u, u} B) [Module.Finite B E.X₁]
    [Module.Projective B E.X₁] [Module.Finite B E.X₀] [Module.Projective B E.X₀]
    (φ : TwoTermComplex.determinantLine E.d) :
    E.detBaseChange B' φ = TwoTermComplex.determinantLineBaseChangeMap B' E.d φ := rfl

/-- The base change of determinant lines carries the canonical element to the canonical element. -/
theorem TwoTerm.detBaseChange_delta (E : TwoTerm.{u, u, u} B) [Module.Finite B E.X₁]
    [Module.Projective B E.X₁] [Module.Finite B E.X₀] [Module.Projective B E.X₀]
    (hE : TwoTermComplex.IsRankZero E.d) (hE' : TwoTermComplex.IsRankZero (E.baseChange B').d) :
    E.detBaseChange B' (TwoTermComplex.delta E.d hE) = TwoTermComplex.delta _ hE' :=
  TwoTermComplex.determinantLineBaseChangeMap_delta B' E.d hE hE'

omit [Module.Finite B C.X₁] [Module.Projective B C.X₁] [Module.Finite B C.X₀]
  [Module.Projective B C.X₀] [Module.Finite B D.X₁] [Module.Projective B D.X₁]
  [Module.Finite B D.X₀] [Module.Projective B D.X₀] in
/-- The base change of a chain map is the base change of the morphism of differentials. -/
theorem ChainMap.toHom_baseChange (g : ChainMap C D) :
    (g.baseChange B').toHom = g.toHom.baseChange B' := rfl

/-- **`detTransport` commutes with base change**, for a quasi-isomorphism whose base change is
again a quasi-isomorphism (for instance a homotopy equivalence). -/
theorem detTransport_baseChange (g : ChainMap C D) (hq : IsQuasiIso g)
    (hq' : IsQuasiIso (g.baseChange B')) (φ : TwoTermComplex.determinantLine C.d) :
    detTransport (g.baseChange B') hq' (C.detBaseChange B' φ) =
      D.detBaseChange B' (detTransport g hq φ) := by
  rw [TwoTerm.detBaseChange_apply, TwoTerm.detBaseChange_apply]
  set l := spanLeft C D
  set r := spanRight g
  have hl := isQuasiIso_of_isHomotopyEquiv (spanLeft_isHomotopyEquiv C D)
  have hr := spanRight_isQuasiIso g hq
  have hls := l.isDegreewiseSurjective_toHom (spanLeft_surjective₁ C D) (spanLeft_surjective₀ C D)
  have hrs := r.isDegreewiseSurjective_toHom (spanRight_surjective₁ g) (spanRight_surjective₀ g hq)
  have hlq := ChainMap.isQuasiIso_toHom hl
  have hrq := ChainMap.isQuasiIso_toHom hr
  have hlq' := ChainMap.isQuasiIso_of_toHom (g := l.baseChange B') (hlq.baseChange B' hls)
  have hrq' := ChainMap.isQuasiIso_of_toHom (g := r.baseChange B') (hrq.baseChange B' hrs)
  have hlr : DerivedCategory.Q.map (Deformation.Artin.twoTermHom (r.baseChange B')) =
      DerivedCategory.Q.map (Deformation.Artin.twoTermHom (l.baseChange B')) ≫
        DerivedCategory.Q.map (Deformation.Artin.twoTermHom (g.baseChange B')) := by
    rw [← Functor.map_comp, ← Deformation.Artin.twoTermHom_comp, ← ChainMap.baseChange_comp]
    exact Deformation.Artin.Q_map_twoTermHom_eq_of_homotopic
      ((spanRight_homotopic g).baseChange B')
  refine (detTransport_eq_of_span (g.baseChange B') _ (l.baseChange B') (r.baseChange B')
    hls.baseChange.1 hls.baseChange.2 hlq' hrs.baseChange.1 hrs.baseChange.2 hrq' hlr _).trans ?_
  obtain ⟨ψ, rfl⟩ := (l.toHom.detEquiv hls hlq).surjective φ
  have e₁ := TwoTermComplex.Hom.detEquiv_baseChange B' l.toHom hls hlq ψ
  have e₂ := TwoTermComplex.Hom.detEquiv_baseChange B' r.toHom hrs hrq ψ
  have e₃ : ((l.baseChange B').toHom.detEquiv
      ((l.baseChange B').isDegreewiseSurjective_toHom hls.baseChange.1 hls.baseChange.2)
      (ChainMap.isQuasiIso_toHom hlq')).symm
      (TwoTermComplex.determinantLineBaseChangeMap B' C.d (l.toHom.detEquiv hls hlq ψ)) =
      TwoTermComplex.determinantLineBaseChangeMap B' (spanTwoTerm C D).d ψ :=
    (LinearEquiv.symm_apply_eq _).mpr e₁.symm
  refine (congrArg _ e₃).trans (e₂.trans ?_)
  congr 1
  simp only [detTransport, LinearEquiv.trans_apply]
  rw [LinearEquiv.symm_apply_apply]

end BaseChange

end NaiveCotangent

end
