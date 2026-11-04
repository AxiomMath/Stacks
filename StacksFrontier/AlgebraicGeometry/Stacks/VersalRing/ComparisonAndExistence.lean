module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing.ChartIndependence

/-!
# Versal rings: comparison and existence at a point (Stacks 0DQX)

Any two versal rings at a finite-type field-valued point are comparable by a power series ring,
and a versal ring exists once the predeformation category is a deformation category with
finite-dimensional tangent space.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

attribute [local implicit_reducible] rebaseArtinianAlgebra rebaseCompleteLocalAlgebra
  rebaseArtinianAlgebraCanonical rebaseArtinianFunctorCanonical
  Deformation.AdicTruncation.obj

attribute [local implicit_reducible] completeOpenRebase completeOpenRebaseFunctor

attribute [local implicit_reducible] chartChangeFormalFunctor
  formalObjectRebaseFunctor formalObjectOfRebasedTruncations

/-! ## Comparison of two versal rings at one point (Stacks 0DQX, second assertion)

Two versal rings `A`, `A'` to `𝒳` at a finite-type field-valued point `x₀` are comparable: one is a
formal power series ring in finitely many variables over the other, over the base scheme `S`. The
compatibility with `S` is recorded as an equality of the two induced morphisms from the spectrum
of the power series ring to `S`.
-/

universe q uF vF

/-! ### Shrinking the chart so that the residue field becomes a finite module -/

/-- The residue field of a point of `𝒳` is of finite type over the affine chart presenting it. -/
private theorem affineChartFieldMap_finiteType
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    RingHom.FiniteType (algebraMap Λ k) := by
  let : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := hfinite
  have hmap : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k))) := by
    let : LocallyOfFiniteType iΛ := inferInstance
    exact locallyOfFiniteType_of_comp
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k))) iΛ
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hmap
  change RingHom.FiniteType (algebraMap Λ k) at hmap
  exact hmap

/-- **Stacks 00FY.** A field of finite type over a ring becomes a finite module over a principal
localization of that ring. -/
private theorem finite_localization_of_finiteType_fieldMap
    {R k : Type u} [CommRing R] [Field k] (φ : R →+* k)
    (hφ : RingHom.FiniteType φ) :
    ∃ r : R, φ r ≠ 0 ∧
      ∀ (B : Type u) [CommRing B] [Algebra R B]
        [IsLocalization.Away r B] (ψ : B →+* k),
        ψ.comp (algebraMap R B) = φ → RingHom.Finite ψ := by
  let : Algebra R k := φ.toAlgebra
  let : Algebra R φ.range := φ.rangeRestrict.toAlgebra
  let : Algebra φ.range k := φ.range.subtype.toAlgebra
  let : IsScalarTower R φ.range k := .of_algebraMap_eq fun _ => rfl
  let : Algebra.FiniteType R k := hφ
  let : Algebra.FiniteType φ.range k :=
    .of_restrictScalars_finiteType R _ _
  obtain ⟨a, -, alg, tower, finite⟩ :=
    exists_isField_localizationAway_and_finite_of_finiteType φ.range k Subtype.val_injective
  let := alg
  let := tower
  let := finite
  obtain ⟨r, hr⟩ := φ.rangeRestrict_surjective a
  subst a
  have hrUnit : IsUnit (φ r) := by
    change IsUnit (algebraMap φ.range k (φ.rangeRestrict r))
    rw [IsScalarTower.algebraMap_apply φ.range
      (Localization.Away (φ.rangeRestrict r)) k]
    exact (IsLocalization.Away.algebraMap_isUnit (φ.rangeRestrict r)).map _
  refine ⟨r, hrUnit.ne_zero, ?_⟩
  intro B _ _ _ ψ hψ
  let q := IsLocalization.Away.map B
    (Localization.Away (φ.rangeRestrict r)) φ.rangeRestrict r
  have hq : Function.Surjective q := by
    apply (IsLocalization.Away.map_surjective_iff _ _ _ _).mpr
    intro a
    obtain ⟨b, rfl⟩ := φ.rangeRestrict_surjective a
    exact ⟨b, 0, by simp⟩
  have heq : ψ = (algebraMap
      (Localization.Away (φ.rangeRestrict r)) k).comp q := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    have hx := RingHom.congr_fun hψ x
    dsimp only [RingHom.comp_apply]
    rw [show q ((algebraMap R B) x) =
        algebraMap φ.range
          (Localization.Away (φ.rangeRestrict r)) (φ.rangeRestrict x) by
      simp [q, IsLocalization.Away.map, IsLocalization.map_eq]]
    rwa [← IsScalarTower.algebraMap_apply]
  rw [heq]
  exact (RingHom.finite_algebraMap.mpr finite).comp
    (.of_surjective q hq)

/-- An affine chart presenting a point of `𝒳` can be shrunk to a principal open over which the
residue field is a finite module. -/
theorem exists_finite_localized_affineChart
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ r : Λ, algebraMap Λ k r ≠ 0 ∧
      ∃ ψ : Localization.Away r →+* k,
        ψ.comp (algebraMap Λ (Localization.Away r)) = algebraMap Λ k ∧
          RingHom.Finite ψ := by
  let φ := algebraMap Λ k
  obtain ⟨r, hr, hfinite⟩ := finite_localization_of_finiteType_fieldMap φ
    (affineChartFieldMap_finiteType iΛ hfinite)
  let : IsLocalization.Away r (Localization.Away r) := Localization.isLocalization
  have hu : IsUnit (algebraMap Λ k r) := isUnit_iff_ne_zero.mpr hr
  let ψ : Localization.Away r →+* k := IsLocalization.Away.lift r hu
  have hψ : ψ.comp (algebraMap Λ (Localization.Away r)) = algebraMap Λ k := by
    ext x
    dsimp [RingHom.comp_apply, ψ]
    rw [IsLocalization.Away.lift_eq]
  exact ⟨r, hr, ψ, hψ, hfinite _ ψ hψ⟩

/-- The point of `𝒳` is still of finite type and quasi-compact over the shrunken chart. -/
theorem finiteTypeAfterAwayLocalization
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (r : Λ) (ψ : Localization.Away r →+* k)
    (hψfinite : RingHom.Finite ψ) :
    LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom ψ) ≫
          (Spec.map (CommRingCat.ofHom
            (algebraMap Λ (Localization.Away r))) ≫ iΛ)) ∧
      QuasiCompact
        (Spec.map (CommRingCat.ofHom ψ) ≫
          (Spec.map (CommRingCat.ofHom
            (algebraMap Λ (Localization.Away r))) ≫ iΛ)) := by
  let : IsLocalization.Away r (Localization.Away r) := Localization.isLocalization
  let : Algebra (Localization.Away r) k := ψ.toAlgebra
  have hmodule : Module.Finite (Localization.Away r) k :=
    RingHom.finite_algebraMap.mp hψfinite
  let : Module.Finite (Localization.Away r) k := hmodule
  have hloc : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom ψ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change RingHom.FiniteType ψ
    exact RingHom.FiniteType.of_finite hψfinite
  have hqc : QuasiCompact (Spec.map (CommRingCat.ofHom ψ)) := by
    have hfinite : IsFinite (Spec.map (CommRingCat.ofHom ψ)) :=
      (IsFinite.SpecMap_iff _).mpr hψfinite
    infer_instance
  let iΛr := Spec.map (CommRingCat.ofHom
      (algebraMap Λ (Localization.Away r))) ≫ iΛ
  have hiΛr : IsOpenImmersion iΛr := by
    dsimp [iΛr]
    infer_instance
  let : LocallyOfFiniteType iΛr := inferInstance
  let : QuasiCompact iΛr := inferInstance
  constructor
  · exact locallyOfFiniteType_comp _ _
  · exact AlgebraicGeometry.quasiCompact_comp _ _

/-- The shrunken chart presents the same morphism `Spec k ⟶ S`. -/
theorem awayChart_point_map_eq
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) (r : Λ)
    (ψ : Localization.Away r →+* k)
    (hψ : ψ.comp (algebraMap Λ (Localization.Away r)) = algebraMap Λ k) :
    Spec.map (CommRingCat.ofHom ψ) ≫
        (Spec.map (CommRingCat.ofHom
          (algebraMap Λ (Localization.Away r))) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  exact RingHom.congr_fun hψ x

/-- An element of the chart which is nonzero in the residue field is a unit in a complete local
algebra with that residue field. -/
theorem coefficientElement_isUnit_in_completeLocal
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k) (r : Λ)
    (hr : algebraMap Λ k r ≠ 0) : IsUnit (algebraMap Λ A r) := by
  have hres : residue A (algebraMap Λ A r) ≠ 0 := by
    intro hz
    have hcomm := A.residueEquiv.commutes' r
    rw [IsScalarTower.algebraMap_apply Λ A (ResidueField A) r] at hcomm
    rw [IsLocalRing.ResidueField.algebraMap_eq] at hcomm
    rw [hz] at hcomm
    have hzero : A.residueEquiv.toFun 0 = 0 := map_zero A.residueEquiv.toAlgHom
    rw [hzero] at hcomm
    exact hr hcomm.symm
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres

/-- The same complete local algebra, viewed over the shrunken chart. -/
abbrev localizeCompleteLocalAlgCat
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (r : Λ)
    [Algebra (Localization.Away r) k]
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (hA : IsUnit (algebraMap Λ A r)) (hk : IsUnit (algebraMap Λ k r))
    (hkMap : ∀ x : Localization.Away r,
      algebraMap (Localization.Away r) k x = IsLocalization.Away.lift r hk x) :
    Deformation.CompleteLocalAlgCat.{u, u, u} (Localization.Away r) k := by
  letI : IsLocalization.Away r (Localization.Away r) := Localization.isLocalization
  let ψA : Localization.Away r →+* A := IsLocalization.Away.lift r hA
  let ψk : Localization.Away r →+* k := IsLocalization.Away.lift r hk
  letI : Algebra (Localization.Away r) A := ψA.toAlgebra
  letI : IsScalarTower Λ (Localization.Away r) A :=
    .of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hA x).symm
  letI : IsScalarTower Λ (Localization.Away r) k :=
    .of_algebraMap_eq fun x => by
      rw [hkMap]
      exact (IsLocalization.Away.lift_eq r hk x).symm
  have hres : (A.residueEquiv.toRingEquiv.toRingHom).comp
      (algebraMap (Localization.Away r) (ResidueField A)) =
        algebraMap (Localization.Away r) k := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    change A.residueEquiv
        (algebraMap (Localization.Away r) (ResidueField A)
          (algebraMap Λ (Localization.Away r) x)) =
      algebraMap (Localization.Away r) k (algebraMap Λ (Localization.Away r) x)
    rw [← IsScalarTower.algebraMap_apply Λ (Localization.Away r)
      (ResidueField A) x]
    rw [← IsScalarTower.algebraMap_apply Λ (Localization.Away r) k x]
    exact A.residueEquiv.commutes' x
  let resEq : ResidueField A ≃ₐ[Localization.Away r] k :=
    AlgEquiv.ofRingEquiv (f := A.residueEquiv.toRingEquiv)
      (fun x => by
        have hx := RingHom.congr_fun hres x
        change A.residueEquiv
          ((algebraMap (Localization.Away r) (ResidueField A)) x) = _ at hx
        exact hx)
  exact {
    carrier := A.carrier
    commRing := A.commRing
    algebra := inferInstance
    completeLocal := A.completeLocal
    residueEquiv := resEq
  }

/-! ### Power series algebra isomorphisms -/

/-- A power series ring in one variable is functorial in its coefficient algebra. -/
private def powerSeriesMapAlgEquiv
    {R A B : Type q} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] (e : A ≃ₐ[R] B) :
    PowerSeries A ≃ₐ[R] PowerSeries B where
  toFun := PowerSeries.mapAlgHom e.toAlgHom
  invFun := PowerSeries.mapAlgHom e.symm.toAlgHom
  left_inv f := by
    ext n
    change PowerSeries.coeff n
      (PowerSeries.map e.symm.toRingHom (PowerSeries.map e.toRingHom f)) = _
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.symm_apply_apply _
  right_inv f := by
    ext n
    change PowerSeries.coeff n
      (PowerSeries.map e.toRingHom (PowerSeries.map e.symm.toRingHom f)) = _
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.apply_symm_apply _
  map_mul' f g := (PowerSeries.mapAlgHom e.toAlgHom).map_mul f g
  map_add' f g := (PowerSeries.mapAlgHom e.toAlgHom).map_add f g
  commutes' r := by
    rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
    rw [PowerSeries.mapAlgHom_apply, PowerSeries.map_C]
    exact congrArg PowerSeries.C (e.commutes r)

/-- A power series ring is functorial in its coefficient algebra. -/
@[sga "7 XXII 4.4"]
private def mvPowerSeriesMapAlgEquiv
    (σ : Type) {R : Type u} {A B : Type q} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [CommSemiring B] [Algebra R B] (e : A ≃ₐ[R] B) :
    MvPowerSeries σ A ≃ₐ[R] MvPowerSeries σ B where
  toFun := MvPowerSeries.mapAlgHom e.toAlgHom
  invFun := MvPowerSeries.mapAlgHom e.symm.toAlgHom
  left_inv f := by
    ext x
    simp [MvPowerSeries.mapAlgHom_apply, MvPowerSeries.coeff_map]
  right_inv f := by
    ext x
    simp [MvPowerSeries.mapAlgHom_apply, MvPowerSeries.coeff_map]
  map_mul' f g := (MvPowerSeries.mapAlgHom e.toAlgHom).map_mul f g
  map_add' f g := (MvPowerSeries.mapAlgHom e.toAlgHom).map_add f g
  commutes' r := by
    simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.mapAlgHom_apply,
      MvPowerSeries.map_C]

/-- A power series ring in `n + m` variables is a power series ring in `n` variables over a
power series ring in `m` variables. -/
private def mvPowerSeriesStackEquiv (n m : ℕ) (R : Type q) [CommSemiring R] :
    MvPowerSeries (Fin (n + m)) R ≃ₐ[R]
      MvPowerSeries (Fin n) (MvPowerSeries (Fin m) R) := by
  induction n with
  | zero =>
      let e : MvPowerSeries (Fin (0 + m)) R ≃+*
          MvPowerSeries (Fin 0) (MvPowerSeries (Fin m) R) :=
        (MvPowerSeries.renameEquiv R (finCongr (by omega))).toRingEquiv.trans
          (MvPowerSeries.isEmptyEquiv (Fin 0) (MvPowerSeries (Fin m) R)).toRingEquiv.symm
      exact AlgEquiv.ofRingEquiv (f := e) (fun r => by
        simp [MvPowerSeries.algebraMap_apply, e])
  | succ n ih =>
      have h : (n + 1) + m = (n + m) + 1 := by omega
      exact
        (MvPowerSeries.renameEquiv R (finCongr h)).trans
          ((MvPowerSeries.finSuccEquiv R (n + m)).trans
            ((powerSeriesMapAlgEquiv ih).trans
              ((MvPowerSeries.finSuccEquiv (MvPowerSeries (Fin m) R) n).symm
                |>.restrictScalars R)))

/-- An isomorphism of complete local algebras is an algebra isomorphism of the underlying
algebras. -/
private def completeLocalAlgIsoAlgEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : Deformation.CompleteLocalAlgCat.{u, max v w, w} Λ k} (i : A ≅ B) :
    A ≃ₐ[Λ] B := by
  have hcompAB : i.inv.hom.comp i.hom.hom = AlgHom.id Λ A := by
    have hh := congrArg (fun g : A ⟶ A => g.hom) i.hom_inv_id
    change i.inv.hom.comp i.hom.hom = AlgHom.id Λ A at hh
    exact hh
  have hcompBA : i.hom.hom.comp i.inv.hom = AlgHom.id Λ B := by
    have hh := congrArg (fun g : B ⟶ B => g.hom) i.inv_hom_id
    change i.hom.hom.comp i.inv.hom = AlgHom.id Λ B at hh
    exact hh
  refine AlgEquiv.ofBijective i.hom.hom ⟨fun x y hxy => ?_, fun y => ⟨i.inv.hom y, ?_⟩⟩
  · have hx := congrArg (fun g : A →ₐ[Λ] A => g x) hcompAB
    have hy := congrArg (fun g : A →ₐ[Λ] A => g y) hcompAB
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at hx hy
    rw [← hx, ← hy, hxy]
  · have hy := congrArg (fun g : B →ₐ[Λ] B => g y) hcompBA
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hy

/-- If `Y = Y₀[[t₁,…,tₙ]]` and `X = X₀[[t₁,…,tₘ]]` with `X₀ ≅ Y₀` and `m ≤ n`, then `Y` is a power
series ring in `n - m` variables over `X`. -/
private theorem nonempty_algEquiv_mvPowerSeries_sub
    {Λ : Type u} {X X₀ Y Y₀ : Type q} [CommSemiring Λ] [CommSemiring X] [CommSemiring X₀]
    [CommSemiring Y] [CommSemiring Y₀] [Algebra Λ X] [Algebra Λ X₀] [Algebra Λ Y] [Algebra Λ Y₀]
    {m n : ℕ} (hmn : m ≤ n) (eX : MvPowerSeries (Fin m) X₀ ≃ₐ[Λ] X)
    (eY : MvPowerSeries (Fin n) Y₀ ≃ₐ[Λ] Y) (e₀ : X₀ ≃ₐ[Λ] Y₀) :
    Nonempty (Y ≃ₐ[Λ] MvPowerSeries (Fin (n - m)) X) := by
  exact ⟨eY.symm.trans <|
    (mvPowerSeriesMapAlgEquiv (Fin n) (R := Λ) e₀.symm).trans <|
      ((MvPowerSeries.renameEquiv X₀
        (finCongr (Nat.sub_add_cancel hmn).symm)).restrictScalars Λ).trans
        (((mvPowerSeriesStackEquiv (n - m) m X₀).restrictScalars Λ).trans
          (mvPowerSeriesMapAlgEquiv (Fin (n - m)) (R := Λ) eX))⟩

/-! ### Comparison of two versal formal objects -/

/-- Two versal formal objects of a predeformation category have comparable bases: one is a power
series ring in finitely many variables over the other. This is **Stacks 0DQX**, second assertion,
at the level of formal objects. -/
private theorem versalFormalObjects_powerSeries_comparison
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ Deformation.ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : Deformation.IsPredeformationCategory p)
    (ξ η : Deformation.FormalObject p)
    (hξ : Deformation.IsVersal hp.cofibered ξ)
    (hη : Deformation.IsVersal hp.cofibered η) :
    (∃ n : ℕ, Nonempty (ξ.base ≃ₐ[Λ] MvPowerSeries (Fin n) η.base)) ∨
      (∃ n : ℕ, Nonempty (η.base ≃ₐ[Λ] MvPowerSeries (Fin n) ξ.base)) := by
  obtain ⟨ξ₀, -, hξ₀, -, m, eξ, -⟩ :=
    Deformation.exists_minimalVersal_powerSeries hp ξ hξ
  obtain ⟨η₀, -, hη₀, -, n, eη, -⟩ :=
    Deformation.exists_minimalVersal_powerSeries hp η hη
  obtain ⟨i⟩ := Deformation.isomorphic_of_isMinimalVersal hp ξ₀ η₀ hξ₀ hη₀
  let i₀ : ξ₀.base ≅ η₀.base :=
    { hom := i.hom.base
      inv := i.inv.base
      hom_inv_id := congrArg (fun f : ξ₀ ⟶ ξ₀ => f.base) i.hom_inv_id
      inv_hom_id := congrArg (fun f : η₀ ⟶ η₀ => f.base) i.inv_hom_id }
  let e₀ : ξ₀.base ≃ₐ[Λ] η₀.base := completeLocalAlgIsoAlgEquiv i₀
  by_cases hmn : m ≤ n
  · exact Or.inr ⟨n - m, nonempty_algEquiv_mvPowerSeries_sub hmn eξ eη e₀⟩
  · exact Or.inl ⟨m - n, nonempty_algEquiv_mvPowerSeries_sub (Nat.le_of_not_ge hmn) eη eξ e₀.symm⟩

/-! ### Comparison of two versal rings -/

/-- Composing two `Spec` maps of ring homomorphisms with a morphism out of the target composes the
ring homomorphisms. -/
private theorem spec_map_ofHom_comp_assoc {X : Scheme.{u}} {A B C : Type u} [CommRing A]
    [CommRing B] [CommRing C] (f : B →+* A) (g : C →+* B) (i : Spec (.of C) ⟶ X) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g) ≫ i =
      Spec.map (CommRingCat.ofHom (f.comp g)) ≫ i := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The constant-coefficient inclusion `A → A[[t₁,…,tᵣ]]` is compatible with the structure maps
from `Λ`, after composing with a morphism `Spec Λ ⟶ X`. -/
private theorem spec_map_C_comp_algebraMap {X : Scheme.{u}} {Λ A : Type u} [CommRing Λ]
    [CommRing A] [Algebra Λ A] (r : ℕ) (i : Spec (.of Λ) ⟶ X) :
    Spec.map (CommRingCat.ofHom (MvPowerSeries.C : A →+* MvPowerSeries (Fin r) A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ i =
      Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPowerSeries (Fin r) A))) ≫ i := by
  rw [spec_map_ofHom_comp_assoc]
  congr 3
  ext a
  simp [MvPowerSeries.algebraMap_apply]

/-- Two versal rings at a field-valued point of an algebraic stack are isomorphic over the base
after adjoining finitely many formal variables to one of them. -/
@[stacks 0DQX "the comparison of any two versal rings at x₀: A ≅ A'[[t₁,…,t_r]] or \
A' ≅ A[[t₁,…,t_r]]"]
theorem versalRing_powerSeries_comparison
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : IsOpenImmersion iΛ')
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (A' : Deformation.CompleteLocalAlgCat.{u, u, u} Λ' k)
    (hA : AlgebraicGeometry.Stack.IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A)
    (hA' : AlgebraicGeometry.Stack.IsVersalRingAt D iΛ' hiΛ' x₀ hx₀' hfinite' A') :
    (∃ r : ℕ, ∃ e : A ≃+* MvPowerSeries (Fin r) A',
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom
        (algebraMap Λ' (MvPowerSeries (Fin r) A'))) ≫ iΛ') ∨
    (∃ r : ℕ, ∃ e : A' ≃+* MvPowerSeries (Fin r) A,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ' =
      Spec.map (CommRingCat.ofHom
        (algebraMap Λ (MvPowerSeries (Fin r) A))) ≫ iΛ) := by
  have : IsLocallyNoetherian (Spec (.of Λ)) :=
    isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsLocallyNoetherian (Spec (.of Λ')) :=
    isLocallyNoetherian_of_isOpenImmersion iΛ'
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  have : IsNoetherianRing Λ' :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ')).mp inferInstance
  let : IsOpenImmersion iΛ := hiΛ
  let : IsOpenImmersion iΛ' := hiΛ'
  obtain ⟨r₀, hr₀, ψ₀, hψ₀, hψ₀finite⟩ :=
    exists_finite_localized_affineChart iΛ hfinite.1
  let R := Localization.Away r₀
  let : IsLocalization.Away r₀ R := Localization.isLocalization
  let : Algebra R k := ψ₀.toAlgebra
  let iR : Spec (.of R) ⟶ D.S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ
  have hiR : IsOpenImmersion iR := by
    dsimp [iR]
    infer_instance
  have hpointR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom ψ₀) ≫ iR) :=
    hx₀.trans (congrArg Over.mk (awayChart_point_map_eq iΛ r₀ ψ₀ hψ₀).symm)
  have hfiniteR := finiteTypeAfterAwayLocalization iΛ r₀ ψ₀ hψ₀finite
  have : IsNoetherianRing R := inferInstance
  let C := Deformation.Artin.predeformationCategory iR
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hpointR
  let : Category C.carrier := C.category
  have hpC : Deformation.IsPredeformationCategory C.projection :=
    Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iR D.𝒳.val.val.p x₀ hpointR D.𝒳.val.property
  have hAunit := coefficientElement_isUnit_in_completeLocal A r₀ hr₀
  have hkunit : IsUnit (algebraMap Λ k r₀) := isUnit_iff_ne_zero.mpr hr₀
  have hψ₀lift : ψ₀ = IsLocalization.Away.lift r₀ hkunit := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r₀)
    ext x
    have hx := RingHom.congr_fun hψ₀ x
    change ψ₀ (algebraMap Λ R x) = algebraMap Λ k x at hx
    exact hx.trans (IsLocalization.Away.lift_eq r₀ hkunit x).symm
  have : Module.Finite R k := RingHom.finite_algebraMap.mp hψ₀finite
  let AR := localizeCompleteLocalAlgCat r₀ A hAunit hkunit
    (fun x => by
      change ψ₀ x = IsLocalization.Away.lift r₀ hkunit x
      exact DFunLike.congr_fun hψ₀lift x)
  let : Algebra R A := (IsLocalization.Away.lift r₀ hAunit).toAlgebra
  let : IsScalarTower Λ R A := .of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq r₀ hAunit x).symm
  let eA : (A : Type u) ≃+* (AR : Type u) := RingEquiv.refl _
  have hringA : (algebraMap R A).comp (algebraMap Λ R) = algebraMap Λ A := by
    ext x
    change IsLocalization.Away.lift r₀ hAunit (algebraMap Λ R x) = algebraMap Λ A x
    exact IsLocalization.Away.lift_eq r₀ hAunit x
  have hSAR : Spec.map (CommRingCat.ofHom (algebraMap R AR)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
    change Spec.map (CommRingCat.ofHom
        (algebraMap R A)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ) = _
    calc
      _ = Spec.map (CommRingCat.ofHom
          ((algebraMap R A).comp (algebraMap Λ R))) ≫ iΛ := by
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      _ = _ := by rw [hringA]
  have hekA : ∀ a : A,
      AR.residueEquiv (residue AR (eA a)) = A.residueEquiv (residue A a) := by
    intro a
    rfl
  have hringEA : eA.toRingHom.comp (algebraMap Λ A) = algebraMap Λ A := by
    ext x
    rfl
  have hmapEA : Spec.map (CommRingCat.ofHom eA.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hringEA]
  have heSA : Spec.map (CommRingCat.ofHom eA.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap R AR)) ≫ iR := by
    calc
      _ = Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ :=
            congrArg (fun f : Spec (.of AR) ⟶ Spec (.of Λ) => f ≫ iΛ) hmapEA
      _ = _ := hSAR.symm
  have hAR : AlgebraicGeometry.Stack.IsVersalRingAt D iR hiR x₀ hpointR hfiniteR AR :=
    (AlgebraicGeometry.Stack.isVersalRingAt_iff_of_affineOpenPresentation
      D iΛ hiΛ iR hiR x₀ hx₀ hpointR hfinite hfiniteR A AR eA heSA hekA).mp hA
  have hclosedR := closedPointCharts_eq iR iΛ'
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hpointR hx₀'
  obtain ⟨g, hg, hS⟩ := completeLocalOpenLift_data
    iΛ' iR hiR hclosedR.symm A'
  let : Algebra R A' := g.toAlgebra
  let A'R := rebaseCompleteLocalAlgebra A' g hg
  have hmapg : algebraMap R A'R = g := rfl
  let eA' : (A' : Type u) ≃+* (A'R : Type u) := RingEquiv.refl _
  have hcompA' : eA'.toRingHom.comp g = algebraMap R A'R := by
    ext x
    rfl
  have heSA' : Spec.map (CommRingCat.ofHom eA'.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ' =
      Spec.map (CommRingCat.ofHom (algebraMap R A'R)) ≫ iR := by
    calc
      _ = Spec.map (CommRingCat.ofHom eA'.toRingHom) ≫
          Spec.map (CommRingCat.ofHom g) ≫ iR :=
            congrArg (fun f : Spec (.of A') ⟶ D.S =>
              Spec.map (CommRingCat.ofHom eA'.toRingHom) ≫ f) hS.symm
      _ = _ := by
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcompA']
  have hekA' : ∀ a : A',
      A'R.residueEquiv (residue A'R (eA' a)) = A'.residueEquiv (residue A' a) := by
    intro a
    rfl
  have hA'R : AlgebraicGeometry.Stack.IsVersalRingAt D iR hiR x₀ hpointR hfiniteR A'R :=
    (AlgebraicGeometry.Stack.isVersalRingAt_iff_of_affineOpenPresentation
      D iΛ' hiΛ' iR hiR x₀ hx₀' hpointR hfinite' hfiniteR A' A'R eA' heSA' hekA').mp hA'
  rcases hAR with ⟨ξ, hξA, hξ⟩
  rcases hA'R with ⟨ξ', hξ'A, hξ'⟩
  rcases versalFormalObjects_powerSeries_comparison hpC ξ ξ' hξ hξ' with
    ⟨r, ⟨e⟩⟩ | ⟨r, ⟨e⟩⟩
  · rw [hξA, hξ'A] at e
    refine Or.inl ⟨r, e.toRingEquiv, ?_⟩
    have he : e.toRingHom.comp (algebraMap R AR) =
        (MvPowerSeries.C (σ := Fin r)).comp (algebraMap R A'R) := by
      apply RingHom.ext
      intro a
      change e (algebraMap R AR a) =
        MvPowerSeries.C (σ := Fin r) (algebraMap R A'R a)
      rw [e.commutes]
      rw [MvPowerSeries.algebraMap_apply]
    calc
      _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R AR)) ≫ iR := by rw [hSAR]
      _ = Spec.map (CommRingCat.ofHom ((MvPowerSeries.C (σ := Fin r)).comp g)) ≫ iR := by
          rw [spec_map_ofHom_comp_assoc, he, hmapg]
      _ = Spec.map (CommRingCat.ofHom (MvPowerSeries.C : A' →+* MvPowerSeries (Fin r) A')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ' := by
          rw [← hS]
          exact (spec_map_ofHom_comp_assoc _ _ _).symm
      _ = _ := spec_map_C_comp_algebraMap r iΛ'
  · rw [hξ'A, hξA] at e
    refine Or.inr ⟨r, e.toRingEquiv, ?_⟩
    have he : e.toRingHom.comp (algebraMap R A'R) =
        algebraMap R (MvPowerSeries (Fin r) AR) := by
      apply RingHom.ext
      intro a
      change e (algebraMap R A'R a) =
        algebraMap R (MvPowerSeries (Fin r) AR) a
      exact e.commutes a
    calc
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ' A')) ≫ iΛ' =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R A'R)) ≫ iR :=
            congrArg (fun f : Spec (.of A') ⟶ D.S =>
              Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f) hS.symm
      _ = Spec.map (CommRingCat.ofHom (algebraMap R (MvPowerSeries (Fin r) AR))) ≫ iR := by
          rw [spec_map_ofHom_comp_assoc, he]
      _ = Spec.map (CommRingCat.ofHom (MvPowerSeries.C : A →+* MvPowerSeries (Fin r) A)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R AR)) ≫ iR :=
        (spec_map_C_comp_algebraMap (A := AR) r iR).symm
      _ = Spec.map (CommRingCat.ofHom (MvPowerSeries.C : A →+* MvPowerSeries (Fin r) A)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by rw [hSAR]
      _ = _ := spec_map_C_comp_algebraMap r iΛ


/-! ## Existence of a versal ring at a point (Stacks 0DQX, first assertion)

A versal ring at `x₀` exists once the predeformation category of `x₀` is a deformation category
with finite-dimensional tangent space (**Stacks 0DQW**).
-/

/-- **Stacks 0DQX**, first assertion, from **Stacks 0DQW**: if the predeformation category of a
finite-type field-valued point `x₀` at every affine-open chart of `S` with `Λ' → k` finite is a
deformation category with finite-dimensional tangent space, then a versal ring to `𝒳` at `x₀`
exists, presented over any given affine-open chart. -/
theorem exists_isVersalRingAt_of_deformationCategory
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hdef : ∀ {Λ' : Type u} [CommRing Λ'] [Algebra Λ' k] [Module.Finite Λ' k]
      (iΛ' : Spec (.of Λ') ⟶ D.S),
      IsOpenImmersion iΛ' →
      ∀ hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'),
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
        QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') →
      let C := Deformation.Artin.predeformationCategory iΛ'
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀'
      letI := C.category
      ∃ hp : Deformation.IsDeformationCategory C.projection,
        letI : Fact (Deformation.IsPredeformationCategory
            (BasedCategory.ofFunctor C.projection).p) := ⟨hp.predeformation⟩
        letI : Fact (Deformation.SchlessingerConditionS2 (CategoryOfElements.π
            (Deformation.isomorphismClasses (BasedCategory.ofFunctor C.projection)
              hp.predeformation.cofibered))) :=
          ⟨Deformation.schlessingerConditionS2_of_isIsomorphismClasses
            (BasedCategory.ofFunctor C.projection) hp.predeformation.cofibered
            (Deformation.schlessingerConditionS2_of_satisfiesRS hp.satisfiesRS)
            (Or.inl hp.predeformation)⟩
        FiniteDimensional k (Deformation.tangentSpaceArtinian Λ' k
          (Deformation.isomorphismClasses (BasedCategory.ofFunctor C.projection)
            hp.predeformation.cofibered))) :
    ∃ A : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k,
      AlgebraicGeometry.Stack.IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite A := by
  have : IsLocallyNoetherian (Spec (.of Λ)) :=
    isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  let : IsOpenImmersion iΛ := hiΛ
  obtain ⟨r₀, -, ψ₀, hψ₀, hψ₀finite⟩ :=
    exists_finite_localized_affineChart iΛ hfinite.1
  let R := Localization.Away r₀
  let : Algebra R k := ψ₀.toAlgebra
  let iR : Spec (.of R) ⟶ D.S :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ
  have hiR : IsOpenImmersion iR := by
    dsimp [iR]
    infer_instance
  have hpointR : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ iR) :=
    hx₀.trans (congrArg Over.mk (awayChart_point_map_eq iΛ r₀ ψ₀ hψ₀).symm)
  have hfiniteR := finiteTypeAfterAwayLocalization iΛ r₀ ψ₀ hψ₀finite
  have : IsNoetherianRing R := inferInstance
  have : Module.Finite R k := RingHom.finite_algebraMap.mp hψ₀finite
  obtain ⟨hp, hT⟩ := hdef iR hiR hpointR hfiniteR
  let C := Deformation.Artin.predeformationCategory iR
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hpointR
  let : Category C.carrier := C.category
  obtain ⟨ξ, hξ⟩ := Deformation.exists_versalFormalObject R k
    (BasedCategory.ofFunctor C.projection) hp.predeformation
    (Deformation.schlessingerConditionS1_of_satisfiesRS hp.satisfiesRS)
    (Deformation.schlessingerConditionS2_of_satisfiesRS hp.satisfiesRS) hT
  have hAR : AlgebraicGeometry.Stack.IsVersalRingAt D iR hiR x₀ hpointR hfiniteR ξ.base :=
    ⟨ξ, rfl, hξ⟩
  have hclosed := closedPointCharts_eq iR iΛ
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hpointR hx₀
  obtain ⟨g, hg, hS⟩ := completeLocalOpenLift_data iR iΛ hiΛ hclosed ξ.base
  let A := rebaseCompleteLocalAlgebra ξ.base g hg
  let e : (ξ.base : Type u) ≃+* (A : Type u) := RingEquiv.refl _
  have hcomp : e.toRingHom.comp (algebraMap R ξ.base) = algebraMap R ξ.base := by
    ext x
    rfl
  have hmapg : algebraMap Λ A = g := rfl
  have heS : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R ξ.base)) ≫ iR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
    rw [hmapg, hS, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  refine ⟨A, (AlgebraicGeometry.Stack.isVersalRingAt_iff_of_affineOpenPresentation
    D iR hiR iΛ hiΛ x₀ hpointR hx₀ hfiniteR hfinite ξ.base A e heS fun a => rfl).mp hAR⟩

/-! ### Moving a versal formal object to another chart, keeping its objects of `𝒳` -/

/-- **A versal formal object can be moved to another affine-open presentation without changing its
objects of `𝒳` or the identification of its residue field.** Besides the conclusion of
`AlgebraicGeometry.Stack.exists_isVersal_ofPredeformation_eq_of_affineOpenPresentation`, the
residue field identifications `κ(η.base) ≅ k` and `κ(ξ.base) ≅ k` agree along the identification
of the two complete local bases. -/
theorem exists_isVersal_ofPredeformation_eq_residue_of_affineOpenPresentation
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : IsOpenImmersion iΛ')
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ) :
    ∃ η : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection,
      Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
        D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered η ∧
      ∃ hEq : Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀
          hx₀' hfinite' η =
        Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
          hfinite ξ,
        ∀ a : ξ.base, η.base.residueEquiv (residue η.base
            (cast (congrArg (fun A : Deformation.Artin.FormalBase D.S => A.R)
              (congrArg Deformation.Artin.FormalObject.base hEq)).symm a)) =
          ξ.base.residueEquiv (residue ξ.base a) := by
  let q := D.𝒳.val.val.p ⋙ Over.post D.B.inclusion
  let hp := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered
  let hp' := (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered
  let C := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let C' := Deformation.Artin.predeformationCategory iΛ' q x₀ hx₀'
  have hEq : Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀
      hx₀' hfinite' ((chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj ξ) =
      Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite ξ := ?_
  · exact ⟨(chartChangeFormalFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj ξ,
      isVersal_chartChange iΛ iΛ' hiΛ hiΛ' q x₀ hx₀ hx₀' hp hp' ξ hξ, hEq, fun _ => rfl⟩
  have hl : ∀ n, (C'.objects ((chartChangePredeformationFunctor iΛ iΛ' hiΛ' q x₀ hx₀ hx₀').obj
      (ξ.level n))).point = (C.objects (ξ.level n)).point := fun n =>
    congrArg Deformation.Artin.DeformationObject.point
      (chartChange_objects iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (ξ.level n))
  refine Deformation.Artin.FormalObject.ext_of_level ?_ hl ?_
  · change Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite'
        (completeOpenRebase iΛ iΛ' hiΛ' (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀') ξ.base) =
      Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base
    have hfac := completeOpenRebase_fac iΛ iΛ' hiΛ' (closedPointCharts_eq iΛ iΛ' q x₀ hx₀ hx₀')
      ξ.base
    unfold Deformation.Artin.completeLocalAlgFormalBase
    congr 1
  · intro n
    exact chartChange_arrow iΛ iΛ' hiΛ' q x₀ hx₀ hx₀' (ξ.transition n)

/-- **A versal formal object can be moved to another affine-open presentation without changing its
objects of `𝒳`.** In the versal situation, a versal formal object `ξ` of the predeformation
category of `x₀` presented over `Spec Λ ⟶ S` gives a versal formal object `η` of the
predeformation category of `x₀` presented over another affine open `Spec Λ' ⟶ S` containing the
image of `Spec k`, with the same formal object over the site: the same complete local base as a
ring over `S`, the same levels and the same transitions. -/
theorem exists_isVersal_ofPredeformation_eq_of_affineOpenPresentation
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k]
    [Algebra Λ k] [Algebra Λ' k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : IsOpenImmersion iΛ')
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite' : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ) :
    ∃ η : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection,
      Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
        D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered η ∧
      Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀ hx₀'
          hfinite' η =
        Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
          hfinite ξ := by
  obtain ⟨η, hη, hEq, -⟩ := exists_isVersal_ofPredeformation_eq_residue_of_affineOpenPresentation
    D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite hfinite' ξ hξ
  exact ⟨η, hη, hEq⟩

end AlgebraicGeometry.Stack

end
