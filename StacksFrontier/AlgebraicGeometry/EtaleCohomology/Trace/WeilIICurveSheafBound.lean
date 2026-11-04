module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FlatStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveCompactificationIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTorsionFree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDevissage

/-!
# The weight bound of Weil II for lisse sheaves on a curve

The curve case of the weight bound of Weil II (Deligne, Weil II 3.2.3,
`Stacks.EtaleCohomology.WeilIICurveBound`) is stated for the sheaf `ℱ_ρ` of a continuous
representation `ρ` of the fundamental group.  The reduction of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) to curves meets lisse ℓ-adic sheaves, which
are isogenous to such sheaves (the correspondence between lisse sheaves and representations).
Isogenous ℓ-adic sheaves have the same rational stalks and the same rational compactly supported
cohomology, with the same Frobenius actions up to conjugation, so mixedness, realizability and the
weight bound transfer along an isogeny.

## Main results

The following declarations are in the namespace `Stacks.EtaleCohomology.LAdicSheaf`.

* `charpoly_rationalStalkEnd_of_isogeny`: isogenous sheaves have the same characteristic
  polynomials on rational stalks.
* `isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff_of_isogeny`:
  isogenous sheaves have the same Frobenius weights on `Hⁱ_c`.
* `satisfiesWeightBound_of_isCurve`: on a smooth curve the weight bound may be checked on one
  compactification (Tag 0F7I for curves).
* `satisfiesWeightBound_of_weilIICurveBound`: the weight bound for lisse sheaves on a smooth
  geometrically connected curve, from the curve case for representations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section Isogeny

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **Isogenous ℓ-adic sheaves have the same characteristic polynomials on rational stalks**: an
isogeny `φ`, `ψ` (with `φ ≫ ψ` and `ψ ≫ φ` multiplication by `ℓᴺ`) induces an isomorphism of
rational stalks conjugating the actions of every endomorphism of the geometric point. -/
theorem LAdicSheaf.charpoly_rationalStalkEnd_of_isogeny {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F) (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G)
    {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    (LAdicSheaf.rationalStalkEnd B X ℓ F a).charpoly =
      (LAdicSheaf.rationalStalkEnd B X ℓ G a).charpoly := by
  have hc : ((ℓ ^ N : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have hcomp : ∀ {F' G' : LAdicSheaf B X ℓ} (α : F' ⟶ G') (β : G' ⟶ F'),
      α ≫ β = (ℓ ^ N) • 𝟙 F' →
        LAdicSheaf.rationalStalkMap β s ∘ₗ LAdicSheaf.rationalStalkMap α s =
          ((ℓ ^ N : ℕ) : ℚ_[ℓ]) • LinearMap.id := by
    intro F' G' α β h
    rw [← LAdicSheaf.rationalStalkMap_nsmul_id, ← h]
    simp only [LAdicSheaf.rationalStalkMap, LAdicSheaf.stalkMap_comp, LinearMap.baseChange_comp]
  let e : LAdicSheaf.rationalStalkLeft B X ℓ F s ≃ₗ[ℚ_[ℓ]] LAdicSheaf.rationalStalkLeft B X ℓ G s :=
    LinearEquiv.ofLinear (LAdicSheaf.rationalStalkMap φ s)
      (((ℓ ^ N : ℕ) : ℚ_[ℓ])⁻¹ • LAdicSheaf.rationalStalkMap ψ s)
      (by rw [LinearMap.comp_smul, hcomp ψ φ h₂, smul_smul, inv_mul_cancel₀ hc, one_smul])
      (by rw [LinearMap.smul_comp, hcomp φ ψ h₁, smul_smul, inv_mul_cancel₀ hc, one_smul])
  have hconj : LAdicSheaf.rationalStalkEnd B X ℓ G a =
      e.conj (LAdicSheaf.rationalStalkEnd B X ℓ F a) := by
    rw [LinearEquiv.conj_apply]
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    show LAdicSheaf.rationalStalkEnd B X ℓ G a (LAdicSheaf.rationalStalkMap φ s y) =
      e (LAdicSheaf.rationalStalkEnd B X ℓ F a (e.symm (e y)))
    rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun (LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap φ a) y
  rw [hconj, LinearEquiv.charpoly_conj]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Isogenous ℓ-adic sheaves have the same Frobenius weights on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`**: the
isomorphism of rational cohomology induced by the isogeny intertwines the geometric Frobenius
endomorphisms, so their characteristic polynomials agree. -/
theorem LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff_of_isogeny
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G i)]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ} :
    IsCharpolyNormMixedOfWeightLE q' ι b
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i).hom ↔
      IsCharpolyNormMixedOfWeightLE q' ι b
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          G i).hom := by
  let e := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
    h₁ h₂ i
  have hcomm := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback B X
    ℓ f j kbar φ ψ N h₁ h₂ i
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)
  have hconj : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
      G i).hom = e.toLinearEquiv.conj
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          F i).hom := by
    rw [LinearEquiv.conj_apply]
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
    have := congrArg (fun g => g.hom y) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact this
  have hpoly : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
      G i).hom.charpoly = (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p
        q hcard F i).hom.charpoly := by
    rw [hconj, LinearEquiv.charpoly_conj]
  simp only [IsCharpolyNormMixedOfWeightLE, hpoly]

end Isogeny

section Curve

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] {kbar : Type u} [Field kbar] [Algebra k kbar]
  {p q : ℕ} [Fact p.Prime] [CharP k p] {hcard : Fintype.card k = p ^ q} {ι : ℚ_[ℓ] →+* ℂ}

/-- **On a smooth curve the weight bound may be checked on one compactification**: the Frobenius
characteristic polynomials on `Hⁱ_c` do not depend on the compactification (Tag 0F7I for curves,
`LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isCurve`), given the finite
dimensionality of the cohomology. -/
theorem LAdicSheaf.satisfiesWeightBound_of_isCurve (U : B.Scheme) [IsNoetherian U.1]
    [ConnectedSpace U.1] (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] [IsCurve k f] [Smooth f] (j₀ : CompactificationOf (Over.mk f))
    (hfin : LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar U f)
    (h₀ : ∀ (F : LAdicSheaf.{u, u + 1} B U ℓ) (w : ℤ), F.IsLisse →
      LAdicSheaf.IsPointwiseMixedOfWeightLE B U ℓ f F (p ^ q) ι w →
      LAdicSheaf.IsIotaRealizable B U ℓ f F ι →
      ∀ (i : ℤ) [FiniteDimensional ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j₀ kbar F i)],
        IsCharpolyNormMixedOfWeightLE (p ^ q) ι (w + i)
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j₀ kbar p q hcard
            F i).hom) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U f := by
  intro j F w hl hm hr i _
  have := (hfin j₀ F i).1
  have h := h₀ F w hl hm hr i
  have hpoly := LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isCurve B ℓ
    f kbar p q hcard j j₀ F i
  simp only [IsCharpolyNormMixedOfWeightLE, hpoly] at h ⊢
  exact h

/-- **The weight bound for lisse sheaves from the weight bound for representations.**  On a
connected noetherian `U` separated of finite type over `k`, if the weight bound holds for the
sheaves `ℱ_ρ` of the continuous representations `ρ` of `π₁(U, x̄)` which are pointwise `ι`-mixed
and `ι`-realizable, then it holds for lisse sheaves: every lisse ℓ-adic sheaf is isogenous to the
sheaf `ℱ_ρ` of a continuous representation
(`Stacks.EtaleCohomology.LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse`), with the same
Frobenius characteristic polynomials at closed points and on `Hⁱ_c`. -/
theorem LAdicSheaf.satisfiesWeightBound_of_forall_representationSheaf
    (U : B.Scheme) [IsNoetherian U.1] [ConnectedSpace U.1] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (x : GeometricPoint U.1)
    (hU : ∀ (j : CompactificationOf (Over.mk f)) {r : ℕ}
      (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ) (w : ℤ),
      Stacks.EtaleCohomology.IsPointwiseMixedOfWeightLE f x (p ^ q) ι w ρ →
      Stacks.EtaleCohomology.IsIotaRealizable f x ι ρ →
      ∀ (i : ℤ) [FiniteDimensional ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
            (LAdicSheaf.representationSheaf B U x ρ hρ) i)],
        IsCharpolyNormMixedOfWeightLE (p ^ q) ι (w + i)
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p q hcard
            (LAdicSheaf.representationSheaf B U x ρ hρ) i).hom) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U f := by
  intro j F w hl hm hr i _
  obtain ⟨r, ρ, hρ, φ, ψ, N, h₁, h₂⟩ :=
    LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse ℓ (B := B) (X := U) (x := x)
      (F := F) hl
  obtain ⟨F', hF'l, hF'tr⟩ := hr
  obtain ⟨r', ρ', hρ', φ', ψ', N', h₁', h₂'⟩ :=
    LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse ℓ (B := B) (X := U) (x := x)
      (F := F') hF'l
  have hcp : ∀ (G : LAdicSheaf.{u, u + 1} B U ℓ) {s : ℕ}
      (σ : EtaleFundamentalGroup U.1 x →* GL (Fin s) ℚ_[ℓ]) (hσ : Continuous σ)
      (α : G ⟶ LAdicSheaf.representationSheaf B U x σ hσ)
      (β : LAdicSheaf.representationSheaf B U x σ hσ ⟶ G) (M : ℕ)
      (_ : α ≫ β = (ℓ ^ M) • 𝟙 _) (_ : β ≫ α = (ℓ ^ M) • 𝟙 _) (y : closedPoints U.1),
      (LAdicSheaf.rationalStalkFrobenius B U ℓ G y.1 (finite_residueField f y.1 y.2)).charpoly =
        (σ (geometricFrobeniusFamily f x y)).val.charpoly := by
    intro G s σ hσ α β M hαβ hβα y
    have := finite_residueField f y.1 y.2
    exact (LAdicSheaf.charpoly_rationalStalkEnd_of_isogeny B U ℓ α β M hαβ hβα
      (frobeniusPointHom U.1 y.1)).trans
      (charpoly_rationalStalkFrobenius_representationSheaf_eq B U x f σ hσ y)
  -- `ρ` is pointwise mixed and realizable
  have hmρ : Stacks.EtaleCohomology.IsPointwiseMixedOfWeightLE f x (p ^ q) ι w ρ := fun y z hz =>
    hm y z (by rw [hcp F ρ hρ φ ψ N h₁ h₂ y]; exact hz)
  have hrρ : Stacks.EtaleCohomology.IsIotaRealizable f x ι ρ := by
    refine ⟨r', ρ', hρ', fun y n => ?_⟩
    have h := (coeff_charpoly_mul_mem_range_ofReal_iff ι
      (LAdicSheaf.rationalStalkFrobenius B U ℓ F y.1 (finite_residueField f y.1 y.2))
      (LAdicSheaf.rationalStalkFrobenius B U ℓ F' y.1 (finite_residueField f y.1 y.2))).2
      (fun m hm => hF'tr y m hm) n
    rwa [hcp F ρ hρ φ ψ N h₁ h₂ y, hcp F' ρ' hρ' φ' ψ' N' h₁' h₂' y] at h
  -- the weight bound for `ℱ_ρ`, transported along the isogeny
  let e := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B U ℓ f j kbar φ ψ N
    h₁ h₂ i
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
      f j kbar (LAdicSheaf.representationSheaf B U x ρ hρ) i) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv
  have hG : IsCharpolyNormMixedOfWeightLE (p ^ q) ι (w + i)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p q hcard
        (LAdicSheaf.representationSheaf B U x ρ hρ) i).hom :=
    hU j ρ hρ w hmρ hrρ i
  exact (isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff_of_isogeny
    B U ℓ f j kbar p q hcard φ ψ N h₁ h₂ i).2 hG

/-- **The weight bound for lisse sheaves on a curve.**  On a smooth separated geometrically
connected curve `U` over `k`, given the curve case for representations
(`Stacks.EtaleCohomology.WeilIICurveBound`), the weight bound holds for lisse sheaves, since every
lisse ℓ-adic sheaf is isogenous to the sheaf `ℱ_ρ` of a continuous representation
(`Stacks.EtaleCohomology.LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse`):
a lisse `F`, pointwise `ι`-mixed and `ι`-realizable with witness `F'`, is isogenous to `ℱ_ρ`, with
`F'` isogenous to `ℱ_{ρ'}`; the Frobenius characteristic polynomials of `F`, `F'` at closed points
are those of `ρ(F_y)`, `ρ'(F_y)`, so `ρ` is pointwise mixed and realizable with witness `ρ'`, and
the weights of `Hⁱ_c(U_k̄, F)` are those of `Hⁱ_c(U_k̄, ℱ_ρ)`. -/
theorem LAdicSheaf.satisfiesWeightBound_of_weilIICurveBound (hcurve : WeilIICurveBound.{u})
    (U : B.Scheme) [IsNoetherian U.1] [ConnectedSpace U.1] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (hℓ : ℓ ≠ p) (x : GeometricPoint U.1) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U f :=
  LAdicSheaf.satisfiesWeightBound_of_forall_representationSheaf U f x
    fun j _ ρ hρ w hm hr i _ => hcurve B U ℓ k f j kbar p q hcard hℓ x ρ hρ ι w hm hr i

end Curve

end Stacks.EtaleCohomology
