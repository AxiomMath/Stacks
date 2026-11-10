/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.SquareModel
public import StacksFrontier.RingTheory.Fitting.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponents

/-!
# The Fitting ideal of `H¹` of a family of invertible modules on a curve

Let `X` be a proper scheme over a field `k` covered by two affine opens `U₀, U₁`, let `A` be a
`k`-algebra and `M` an invertible module on a base change `X_A = X ×_k Spec A`. Then `H¹(X_A, M)`
is the cokernel of the two-term Čech differential `d` of `M` for the covering `U_A`, and this
cokernel is a finite `A`-module (`d` has a finite projective model). Its zeroth Fitting ideal
`Fit₀(H¹(X_A, M)) ⊆ A` commutes with arbitrary base change `A ⟶ A'`: the Čech differential commutes
with base change, the cokernel is right exact, and Fitting ideals commute with base change
([Stacks, Tag 07ZA]). For a family `M` on `X ×_k T` these ideals glue to an ideal sheaf on `T`,
which commutes with base change along `T' ⟶ T` and is unchanged by twisting `M` by a class pulled
back from `T`.

This is the ideal cutting out the theta divisor of a curve, in the construction of the
polarization used in the proof of [Stacks, Tag 03U1].

## Main definitions

* `Stacks.FamilyFitting.fittingCoker`: the zeroth Fitting ideal of the cokernel of a linear map
  with a finite projective model.
* `Stacks.FamilyFitting.cechFitting`: `Fit₀(H¹(X_A, M))` for an invertible module `M` on `X_A`.
* `Stacks.FamilyFitting.familyFitting`: the ideal sheaf on `T` whose ideal on an affine open `V`
  is `Fit₀(H¹(X ×_k V, M))`.

## Main results

* `Stacks.FamilyFitting.cokerBaseChangeEquiv`: `coker (d ⊗ A') ≃ A' ⊗ coker d`.
* `Stacks.FamilyFitting.cechFitting_baseChange`: `Fit₀(H¹(X_A, M))` commutes with base change.
* `Stacks.FamilyFitting.familyFitting_comap`: the inverse image of the family Fitting ideal sheaf
  along `T' ⟶ T` is the family Fitting ideal sheaf of the pulled-back family.
* `Stacks.FamilyFitting.familyFitting_rep_add_pullback`: twisting by a class from the base does
  not change the family Fitting ideal sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace Stacks.FamilyFitting

section Linear

variable {R : Type u} [CommRing R] {C₀ C₁ : Type u} [AddCommGroup C₀] [AddCommGroup C₁]
  [Module R C₀] [Module R C₁]

/-- The cokernel of a linear map. -/
abbrev coker (d : C₀ →ₗ[R] C₁) : Type u := C₁ ⧸ LinearMap.range d

/-- The range of the base change `S ⊗ d` is the image of `S ⊗ range d` in `S ⊗ C₁`. -/
theorem range_baseChange_eq (d : C₀ →ₗ[R] C₁) (S : Type u) [CommRing S] [Algebra R S] :
    LinearMap.range (d.baseChange S) = LinearMap.range
      (TensorProduct.AlgebraTensorModule.lTensor S S ((LinearMap.range d).subtype)) := by
  refine SetLike.ext' ?_
  have h1 : (⇑(d.baseChange S) : S ⊗[R] C₀ → S ⊗[R] C₁) = ⇑(LinearMap.lTensor S d) :=
    LinearMap.baseChange_eq_lTensor d
  have h2 : (⇑(TensorProduct.AlgebraTensorModule.lTensor S S ((LinearMap.range d).subtype)) :
      S ⊗[R] (LinearMap.range d) → S ⊗[R] C₁) =
      ⇑(LinearMap.lTensor S (LinearMap.range d).subtype) :=
    rfl
  have h3 := congrArg (fun N : Submodule R (S ⊗[R] C₁) => (N : Set (S ⊗[R] C₁)))
    (LinearMap.lTensor_range (Q := S) (g := d))
  simp only [LinearMap.coe_range] at h3 ⊢
  rw [h1, h2]
  exact h3

/-- **The cokernel commutes with base change**: `coker (A' ⊗ d) ≃ A' ⊗ coker d`. -/
def cokerBaseChangeEquiv (d : C₀ →ₗ[R] C₁) (S : Type u) [CommRing S] [Algebra R S] :
    coker (d.baseChange S) ≃ₗ[S] S ⊗[R] coker d :=
  (Submodule.quotEquivOfEq _ _ (range_baseChange_eq d S)).trans
    (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S (LinearMap.range d)).symm

/-- The cokernel of a map with a finite projective model is a finite module. -/
theorem module_finite_coker_of_model {d : C₀ →ₗ[R] C₁}
    (h : Stacks.TwoTermComplex.HasFiniteProjectiveModel d) : Module.Finite R (coker d) := by
  obtain ⟨K₀, K₁, _, _, _, _, _, _, hK₁, _, δ, φ₀, φ₁, hsq⟩ := h
  exact Module.Finite.equiv hsq.cokerEquiv

/-- The zeroth Fitting ideal of the cokernel of a map with a finite projective model. -/
def fittingCoker (d : C₀ →ₗ[R] C₁) (h : Stacks.TwoTermComplex.HasFiniteProjectiveModel d) :
    Ideal R :=
  haveI := module_finite_coker_of_model h
  fittingIdeal (R := R) (M := coker d) ((0 : ℕ) : ℤ)

/-- Maps identified by linear equivalences of source and target have equal Fitting ideals of
their cokernels. -/
theorem fittingCoker_congr {d : C₀ →ₗ[R] C₁} {D₀ D₁ : Type u} [AddCommGroup D₀] [AddCommGroup D₁]
    [Module R D₀] [Module R D₁] {d' : D₀ →ₗ[R] D₁}
    (h : Stacks.TwoTermComplex.HasFiniteProjectiveModel d)
    (h' : Stacks.TwoTermComplex.HasFiniteProjectiveModel d') (e₀ : C₀ ≃ₗ[R] D₀) (e₁ : C₁ ≃ₗ[R] D₁)
    (he : e₁.toLinearMap ∘ₗ d = d' ∘ₗ e₀.toLinearMap) : fittingCoker d h = fittingCoker d' h' := by
  have := module_finite_coker_of_model h
  have := module_finite_coker_of_model h'
  exact fittingIdeal_eq_of_linearEquiv
    (Stacks.TwoAffineCech.cokerEquivOfComm d d' e₀ e₁ he) 0

/-- **The Fitting ideal of a cokernel commutes with base change.** -/
theorem fittingCoker_baseChange (d : C₀ →ₗ[R] C₁)
    (h : Stacks.TwoTermComplex.HasFiniteProjectiveModel d)
    (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R C₁] :
    fittingCoker (d.baseChange S) (h.baseChange S) =
      Ideal.map (algebraMap R S) (fittingCoker d h) := by
  have := module_finite_coker_of_model h
  have := module_finite_coker_of_model (h.baseChange S)
  rw [fittingCoker, fittingCoker,
    fittingIdeal_eq_of_linearEquiv (cokerBaseChangeEquiv d S) 0]
  exact (fittingIdeal_basic_properties.{u, u, u, u} (R := R) (M := coker d)).2.2.1 S 0

end Linear

/-! ### The Fitting ideal of `H¹` of a family over an affine base -/

section Family

open Stacks.TwoAffineCech

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- **`Fit₀(H¹(X_A, M))`** for an invertible module `M` on a base change `X_A` of `X` to an affine
scheme, computed on the two-affine cover pulled back from `X`. -/
def cechFitting {A : Type u} [CommRing A] [Algebra k A] {XA : Scheme.{u}} (gA : XA ⟶ X)
    (fA : XA ⟶ Spec (.of A))
    (hA : IsPullback gA fA fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (M : XA.Modules) [Stacks.Ample.IsInvertibleModule XA M] : Ideal A :=
  fittingCoker (cechD fA (sqCover U gA) M)
    (hasFiniteProjectiveModel_of_isPullback fX U hU hUaff gA fA hA M)

include hU in
/-- **The Fitting ideal of `H¹` commutes with base change.** -/
theorem cechFitting_baseChange {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] (φ : A →+* A') {XA XA' : Scheme.{u}} (gA : XA ⟶ X) (fA : XA ⟶ Spec (.of A))
    (hA : IsPullback gA fA fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (gA' : XA' ⟶ X) (fA' : XA' ⟶ Spec (.of A'))
    (hA' : IsPullback gA' fA' fX (Spec.map (CommRingCat.ofHom (algebraMap k A'))))
    (g : XA' ⟶ XA) (hsq : IsPullback g fA' fA (Spec.map (CommRingCat.ofHom φ)))
    (hg : g ≫ gA = gA') (M : XA.Modules) [Stacks.Ample.IsInvertibleModule XA M]
    (M' : XA'.Modules) [Stacks.Ample.IsInvertibleModule XA' M']
    (e : (Scheme.Modules.pullback g).obj M ≅ M') :
    cechFitting fX U hU hUaff gA' fA' hA' M' =
      Ideal.map φ (cechFitting fX U hU hUaff gA fA hA M) := by
  let : Algebra A A' := φ.toAlgebra
  have : M.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule M
  have : IsSeparated fA := isSeparated_of_isPullback' fX gA fA hA
  have := flat_cech_of_isPullback fX U hUaff gA fA hA M 1
  have hmodel := hasFiniteProjectiveModel_of_isPullback fX U hU hUaff gA fA hA M
  have hcover : (fun i => g ⁻¹ᵁ (sqCover U gA i)) = sqCover U gA' := by
    funext i
    rw [sqCover, sqCover, ← Scheme.Hom.comp_preimage, hg]
  have hcomm := baseChangeEquiv_comm φ fA fA' g hsq (sqCover U gA) M
    (isAffineOpen_sqCover fX U hUaff gA fA hA)
  have hcongr := cechD_congr fA' (fun i => g ⁻¹ᵁ (sqCover U gA i)) e
  rw [cechFitting, cechFitting]
  change _ = Ideal.map (algebraMap A A') _
  rw [← fittingCoker_baseChange _ hmodel A']
  have h1 := (hmodel.baseChange A').of_linearEquiv _ _ _ hcomm
  have h2 := h1.of_linearEquiv _ _ _ hcongr
  have key : ∀ (V : Cover.{u} → XA'.Opens) (hV : V = sqCover U gA')
      (h : Stacks.TwoTermComplex.HasFiniteProjectiveModel (cechD fA' V M')),
      fittingCoker (cechD fA' V M') h = fittingCoker (cechD fA' (sqCover U gA') M')
        (hasFiniteProjectiveModel_of_isPullback fX U hU hUaff gA' fA' hA' M') := by
    intro V hV h
    subst hV
    rfl
  rw [← key _ hcover h2]
  exact (fittingCoker_congr h1 h2 _ _ hcongr).symm.trans
    (fittingCoker_congr (hmodel.baseChange A') h1 _ _ hcomm).symm

/-! ### Charts of a family over an arbitrary base -/

variable {T : Scheme.{u}} (tT : T ⟶ Spec (.of k))

/-- The `k`-algebra structure on `A` for a morphism `Spec A ⟶ T` over `k`. -/
abbrev chartAlgebra {A : CommRingCat.{u}} (j : Spec A ⟶ T) : Algebra k A :=
  (Spec.preimage (j ≫ tT)).hom.toAlgebra

/-- For the `k`-algebra structure `chartAlgebra tT j`, the morphism `Spec A ⟶ Spec k` is
`j ≫ tT`. -/
theorem specMap_chartAlgebra {A : CommRingCat.{u}} (j : Spec A ⟶ T) :
    letI := chartAlgebra tT j
    Spec.map (CommRingCat.ofHom (algebraMap k A)) = j ≫ tT := by
  let := chartAlgebra tT j
  change Spec.map (CommRingCat.ofHom (Spec.preimage (j ≫ tT)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

omit [IsProper fX] in
/-- `X ×_k Spec A` with its two projections is a pullback of `X ⟶ Spec k` along
`Spec A ⟶ Spec k`. -/
theorem isPullback_chart {A : CommRingCat.{u}} (j : Spec A ⟶ T) :
    letI := chartAlgebra tT j
    IsPullback (pullback.fst fX (j ≫ tT)) (pullback.snd fX (j ≫ tT)) fX
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  let := chartAlgebra tT j
  rw [specMap_chartAlgebra]
  exact IsPullback.of_hasPullback _ _

/-- The base change map `X ×_k Spec A ⟶ X ×_k T` of a chart. -/
abbrev chartMap {A : CommRingCat.{u}} (j : Spec A ⟶ T) :
    pullback fX (j ≫ tT) ⟶ pullback fX tT :=
  pullback.map fX (j ≫ tT) fX tT (𝟙 _) j (𝟙 _) (by simp) (by simp)

variable (M : (pullback fX tT).Modules) [Stacks.Ample.IsInvertibleModule _ M]

/-- The pullback of an invertible module along `chartMap fX tT j` is invertible. -/
instance isInvertibleModule_chart {A : CommRingCat.{u}} (j : Spec A ⟶ T) :
    Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback (chartMap fX tT j)).obj M) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback _ M

/-- **The Fitting ideal of `H¹` of the family `M` on a chart `Spec A ⟶ T`.** -/
def chartFitting {A : CommRingCat.{u}} (j : Spec A ⟶ T) : Ideal A :=
  letI := chartAlgebra tT j
  cechFitting fX U hU hUaff (pullback.fst fX (j ≫ tT)) (pullback.snd fX (j ≫ tT))
    (isPullback_chart fX tT j) ((Scheme.Modules.pullback (chartMap fX tT j)).obj M)

include hU in
/-- **The chart Fitting ideals are compatible with base change** along a morphism of bases
`h : T' ⟶ T` and a compatible ring map of charts. -/
theorem chartFitting_baseChange {T' : Scheme.{u}} (tT' : T' ⟶ Spec (.of k)) (h : T' ⟶ T)
    (htT : h ≫ tT = tT') (M' : (pullback fX tT').Modules) [Stacks.Ample.IsInvertibleModule _ M']
    (e : (Scheme.Modules.pullback (pullback.map fX tT' fX tT (𝟙 _) h (𝟙 _) (by simp)
      (by rw [Category.comp_id, htT]))).obj M ≅ M')
    {A A' : CommRingCat.{u}} (j : Spec A ⟶ T) (j' : Spec A' ⟶ T') (φ : A ⟶ A')
    (hφ : Spec.map φ ≫ j = j' ≫ h) :
    chartFitting fX U hU hUaff tT' M' j' = Ideal.map φ.hom (chartFitting fX U hU hUaff tT M j) := by
  let := chartAlgebra tT j
  let := chartAlgebra tT' j'
  have hw : Spec.map φ ≫ j ≫ tT = j' ≫ tT' := by rw [← Category.assoc, hφ, Category.assoc, htT]
  set g : pullback fX (j' ≫ tT') ⟶ pullback fX (j ≫ tT) :=
    pullback.map fX (j' ≫ tT') fX (j ≫ tT) (𝟙 _) (Spec.map φ) (𝟙 _) (by simp) (by simp [hw])
  have hg : g ≫ pullback.fst fX (j ≫ tT) = pullback.fst fX (j' ≫ tT') := by
    simp only [g, pullback.lift_fst, Category.comp_id]
  have hsq : IsPullback g (pullback.snd fX (j' ≫ tT')) (pullback.snd fX (j ≫ tT)) (Spec.map φ) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback fX (j ≫ tT))
    rw [hg, hw]
    exact IsPullback.of_hasPullback _ _
  have hmap : g ≫ chartMap fX tT j = chartMap fX tT' j' ≫
      pullback.map fX tT' fX tT (𝟙 _) h (𝟙 _) (by simp) (by rw [Category.comp_id, htT]) := by
    apply pullback.hom_ext
    · simp only [g, chartMap, Category.assoc, pullback.lift_fst,
        Category.comp_id]
    · simp only [g, chartMap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [hφ]
  let e' : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback (chartMap fX tT j)).obj M) ≅
      (Scheme.Modules.pullback (chartMap fX tT' j')).obj M' :=
    (Scheme.Modules.pullbackComp g (chartMap fX tT j)).app M ≪≫
      (Scheme.Modules.pullbackCongr hmap).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback (chartMap fX tT' j')).mapIso e
  exact cechFitting_baseChange fX U hU hUaff φ.hom _ _ (isPullback_chart fX tT j) _ _
    (isPullback_chart fX tT' j') g (by rw [CommRingCat.ofHom_hom]; exact hsq) hg _ _ e'

omit [IsProper fX] in
/-- The map `X ×_k T ⟶ X ×_k T` induced by identities is the identity. -/
theorem pullbackMap_id_eq :
    pullback.map fX tT fX tT (𝟙 _) (𝟙 T) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- **The Fitting ideal sheaf of `H¹` of a family**: the ideal sheaf on `T` whose ideal on an
affine open `V` is `Fit₀(H¹(X ×_k V, M))`. -/
def familyFitting : T.IdealSheafData where
  ideal V := chartFitting fX U hU hUaff tT M V.2.fromSpec
  map_ideal_basicOpen V f := by
    have e : (Scheme.Modules.pullback (pullback.map fX tT fX tT (𝟙 _) (𝟙 T) (𝟙 _) (by simp)
        (by rw [Category.comp_id, Category.id_comp]))).obj M ≅ M :=
      (Scheme.Modules.pullbackCongr (pullbackMap_id_eq fX tT)).app M ≪≫
        (Scheme.Modules.pullbackId _).app M
    exact (chartFitting_baseChange fX U hU hUaff tT M tT (𝟙 T) (Category.id_comp _) M e
      V.2.fromSpec (T.affineBasicOpen f).2.fromSpec _
      (by rw [Category.comp_id]; exact IsAffineOpen.map_fromSpec V.2
            (T.affineBasicOpen f).2 _)).symm

/-- The ideal of `familyFitting` on an affine open `V` is the chart Fitting ideal of `V ⟶ T`. -/
theorem familyFitting_ideal (V : T.affineOpens) :
    (familyFitting fX U hU hUaff tT M).ideal V = chartFitting fX U hU hUaff tT M V.2.fromSpec :=
  rfl

end Family

/-! ### Inverse images of ideal sheaves on affine opens -/

section Comap

/-- **The inverse image of an ideal sheaf on an affine open mapping into an affine open**: for
`h : X ⟶ Y`, affine opens `V ⊆ Y` and `V' ⊆ h⁻¹ V`, the ideal of `I.comap h` on `V'` is generated
by the image of the ideal of `I` on `V`. -/
theorem ideal_comap_of_le {X Y : Scheme.{u}} (I : Y.IdealSheafData) (h : X ⟶ Y)
    (V : Y.affineOpens) (V' : X.affineOpens) (hle : V'.1 ≤ h ⁻¹ᵁ V.1) :
    (I.comap h).ideal V' = Ideal.map (h.appLE V.1 V'.1 hle).hom (I.ideal V) := by
  have hV : IsAffine V.1.toScheme := V.2
  have hV' : IsAffine V'.1.toScheme := V'.2
  set r := h.resLE V.1 V'.1 hle
  have hcomap : (I.comap V.1.ι).comap r = (I.comap h).comap V'.1.ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Scheme.Hom.resLE_comp_ι]
  have key := Stacks.IdealSheaf.ideal_comap_top_of_isAffine (I.comap V.1.ι) r
  have e1 := (congrArg (fun K : V'.1.toScheme.IdealSheafData =>
      K.ideal ⟨⊤, isAffineOpen_top V'.1.toScheme⟩) hcomap).trans
    (Stacks.IdealSheaf.ideal_comap_ι_top (I.comap h) V'.2 _)
  have e2 := Stacks.IdealSheaf.ideal_comap_ι_top I V.2 (isAffineOpen_top V.1.toScheme)
  have hgtop : r.appTop = V.1.topIso.hom ≫ h.appLE V.1 V'.1 hle ≫ V'.1.topIso.inv := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  have main : Ideal.map V'.1.topIso.inv.hom ((I.comap h).ideal V') =
      Ideal.map V'.1.topIso.inv.hom (Ideal.map (h.appLE V.1 V'.1 hle).hom (I.ideal V)) := by
    simp only at e1
    rw [← e1, key, e2, Ideal.map_map, ← CommRingCat.hom_comp, hgtop, Iso.inv_hom_id_assoc,
      CommRingCat.hom_comp, ← Ideal.map_map]
  exact Stacks.IdealSheaf.ideal_map_hom_injective V'.1.topIso.symm main

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))
  {T : Scheme.{u}} (tT : T ⟶ Spec (.of k)) (M : (pullback fX tT).Modules)
  [Stacks.Ample.IsInvertibleModule _ M]

/-- **The Fitting ideal sheaf of `H¹` commutes with base change**: its inverse image along
`h : T' ⟶ T` is the Fitting ideal sheaf of the pulled-back family. -/
theorem familyFitting_comap {T' : Scheme.{u}} (tT' : T' ⟶ Spec (.of k)) (h : T' ⟶ T)
    (htT : h ≫ tT = tT') (M' : (pullback fX tT').Modules) [Stacks.Ample.IsInvertibleModule _ M']
    (e : (Scheme.Modules.pullback (pullback.map fX tT' fX tT (𝟙 _) h (𝟙 _) (by simp)
      (by rw [Category.comp_id, htT]))).obj M ≅ M') :
    (familyFitting fX U hU hUaff tT M).comap h = familyFitting fX U hU hUaff tT' M' := by
  let ι := {p : T.affineOpens × T'.affineOpens // p.2.1 ≤ h ⁻¹ᵁ p.1.1}
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := ι) (fun p => p.1.2) ?_ ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (h x)) isOpen_univ
    obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'le⟩ :=
      T'.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ h ⁻¹ᵁ V from hxV)
        (h ⁻¹ᵁ V).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, ⟨V', hV'⟩), hV'le⟩, hxV'⟩
  · intro p
    rw [ideal_comap_of_le _ h p.1.1 p.1.2 p.2, familyFitting_ideal, familyFitting_ideal]
    exact (chartFitting_baseChange fX U hU hUaff tT M tT' h htT M' e p.1.1.2.fromSpec
      p.1.2.2.fromSpec (h.appLE p.1.1.1 p.1.2.1 p.2)
      (IsAffineOpen.SpecMap_appLE_fromSpec h p.1.1.2 p.1.2.2 p.2)).symm

end Comap

/-! ### Twisting by a class from the base -/

section Twist

/-- **A Picard class is trivial on a neighbourhood of every point**, on an affine open. -/
theorem exists_affineOpen_schemePullbackClass_fromSpec_eq_zero {T : Scheme.{u}}
    (N : Stacks.Picard.ofScheme T) (t : T) :
    ∃ V : T.affineOpens, t ∈ V.1 ∧ Stacks.Picard.schemePullbackClass V.2.fromSpec N = 0 := by
  obtain ⟨W, htW, hW⟩ := Stacks.Divisors.exists_isTrivial_restrict_preimage_of_isFinite (𝟙 T)
    (Stacks.PicardCurve.rep N) t
  have hW' : Stacks.Picard.schemePullbackClass ((𝟙 T) ⁻¹ᵁ W).ι N = 0 := by
    obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso ((𝟙 T) ⁻¹ᵁ W).ι N
    have e' := e ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback _).app _).symm
    have hinv : Stacks.SheafOfModules.IsInvertible ((𝟙 T) ⁻¹ᵁ W).toScheme.presheaf
        (Stacks.RingedSpace.structureIsSheaf ((𝟙 T) ⁻¹ᵁ W).toScheme.toRingedSpace)
        ((Stacks.PicardCurve.rep N).restrict ((𝟙 T) ⁻¹ᵁ W).ι) := by
      have : Stacks.SheafOfModules.IsInvertible ((𝟙 T) ⁻¹ᵁ W).toScheme.presheaf
          (Stacks.RingedSpace.structureIsSheaf ((𝟙 T) ⁻¹ᵁ W).toScheme.toRingedSpace)
          (Stacks.PicardCurve.rep (Stacks.Picard.schemePullbackClass ((𝟙 T) ⁻¹ᵁ W).ι N)) :=
        (Stacks.Picard.picardRepresentative _ _).property
      exact Stacks.SheafOfModules.isInvertible_of_iso _ _ e'
    have h0 := (AlgebraicGeometry.Scheme.picardClass_eq_zero_iff _ _ hinv).2 hW
    rw [← Stacks.Picard.classOf_picardRepresentative _
      (Stacks.Picard.schemePullbackClass ((𝟙 T) ⁻¹ᵁ W).ι N)]
    refine Eq.trans ?_ h0
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e'⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, hVW⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (show t ∈ (𝟙 T) ⁻¹ᵁ W from htW)
      ((𝟙 T) ⁻¹ᵁ W).isOpen
  have hV' : IsAffineOpen V := hV
  refine ⟨⟨V, hV⟩, htV, ?_⟩
  have hVW' : V ≤ (𝟙 T) ⁻¹ᵁ W := hVW
  have hfac : hV'.fromSpec = (hV'.isoSpec.inv ≫ T.homOfLE hVW') ≫ ((𝟙 T) ⁻¹ᵁ W).ι := by
    rw [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
  change Stacks.Picard.schemePullbackClass hV'.fromSpec N = 0
  rw [hfac, ← Stacks.Picard.schemePullbackClass_comp, hW']
  exact (Stacks.Picard.schemePullbackClassHom (hV'.isoSpec.inv ≫ T.homOfLE hVW')).map_zero

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i)) {T : Scheme.{u}} (tT : T ⟶ Spec (.of k))

/-- `Fit₀(H¹)` of a family over an affine base depends on the module only up to isomorphism. -/
theorem cechFitting_congr {A : Type u} [CommRing A] [Algebra k A] {XA : Scheme.{u}} (gA : XA ⟶ X)
    (fA : XA ⟶ Spec (.of A))
    (hA : IsPullback gA fA fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (M M' : XA.Modules) [Stacks.Ample.IsInvertibleModule XA M]
    [Stacks.Ample.IsInvertibleModule XA M'] (e : Nonempty (M ≅ M')) :
    cechFitting fX U hU hUaff gA fA hA M = cechFitting fX U hU hUaff gA fA hA M' := by
  obtain ⟨e⟩ := e
  exact fittingCoker_congr _ _ _ _ (Stacks.TwoAffineCech.cechD_congr fA _ e)

omit [IsProper fX] in
/-- If a Picard class `n` on `T` pulls back to zero along `j : Spec A ⟶ T`, then adding the
pullback of `n` to `x` does not change the pullback of `x` along `chartMap fX tT j`. -/
theorem schemePullbackClass_chartMap_add {A : CommRingCat.{u}} (j : Spec A ⟶ T)
    (x : Stacks.Picard.ofScheme (pullback fX tT)) (n : Stacks.Picard.ofScheme T)
    (hn : Stacks.Picard.schemePullbackClass j n = 0) :
    Stacks.Picard.schemePullbackClass (chartMap fX tT j)
        (x + Stacks.Picard.schemePullbackClass (pullback.snd fX tT) n) =
      Stacks.Picard.schemePullbackClass (chartMap fX tT j) x := by
  have h1 := Stacks.Picard.schemePullbackClass_add (chartMap fX tT j) x
    (Stacks.Picard.schemePullbackClass (pullback.snd fX tT) n)
  have h2 := Stacks.Picard.schemePullbackClass_comp (chartMap fX tT j) (pullback.snd fX tT) n
  have h3 : chartMap fX tT j ≫ pullback.snd fX tT = pullback.snd fX (j ≫ tT) ≫ j :=
    pullback.lift_snd _ _ _
  have h4 := Stacks.Picard.schemePullbackClass_comp (pullback.snd fX (j ≫ tT)) j n
  have h5 : Stacks.Picard.schemePullbackClass (pullback.snd fX (j ≫ tT))
      (0 : Stacks.Picard.ofScheme (Spec A)) = 0 :=
    (Stacks.Picard.schemePullbackClassHom (pullback.snd fX (j ≫ tT))).map_zero
  rw [h1, h2, h3, ← h4, hn, h5, add_zero]

/-- **The family Fitting ideal sheaf only depends on the point of the Picard functor**: twisting
by a class from the base does not change it. -/
theorem familyFitting_rep_add_pullback (x : Stacks.Picard.ofScheme (pullback fX tT))
    (n : Stacks.Picard.ofScheme T) :
    familyFitting fX U hU hUaff tT
        (Stacks.PicardCurve.rep (x + Stacks.Picard.schemePullbackClass (pullback.snd fX tT) n)) =
      familyFitting fX U hU hUaff tT (Stacks.PicardCurve.rep x) := by
  let ι := {V : T.affineOpens // Stacks.Picard.schemePullbackClass V.2.fromSpec n = 0}
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := ι) (fun V => V.1) ?_ ?_
  · refine eq_top_iff.2 fun t _ => ?_
    obtain ⟨V, htV, hV⟩ := exists_affineOpen_schemePullbackClass_fromSpec_eq_zero n t
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, htV⟩
  · intro V
    rw [familyFitting_ideal, familyFitting_ideal, chartFitting, chartFitting]
    let := chartAlgebra tT V.1.2.fromSpec
    refine cechFitting_congr fX U hU hUaff (pullback.fst fX (V.1.2.fromSpec ≫ tT))
      (pullback.snd fX (V.1.2.fromSpec ≫ tT)) (isPullback_chart fX tT V.1.2.fromSpec) _ _ ?_
    have hcl := schemePullbackClass_chartMap_add fX tT V.1.2.fromSpec x n V.2
    obtain ⟨e₁⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso
      (chartMap fX tT V.1.2.fromSpec) (x + Stacks.Picard.schemePullbackClass (pullback.snd fX tT) n)
    obtain ⟨e₂⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso
      (chartMap fX tT V.1.2.fromSpec) x
    exact ⟨e₁.symm ≪≫ eqToIso (congrArg Stacks.PicardCurve.rep hcl) ≪≫ e₂⟩

end Twist

end Stacks.FamilyFitting
