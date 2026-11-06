module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLevelTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDctfFinal

/-!
# The dual coefficients of `ℱ_ρ`

Let `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` be continuous, with integral model `ρ₀ : π₁(X, x̄) → GL_r(ℤ_ℓ)`
(`Stacks.EtaleCohomology.integralModel`), so that `ℱ_ρ` is the ℓ-adic sheaf of `ρ₀`. The dual
coefficients of the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) are the
ℓ-adic sheaf `ℱ_{ρ₀^∨}` of the contragredient `ρ₀^∨ = (ρ₀ᵀ)⁻¹` of that same integral model: its
levels pair with those of `ℱ_ρ` (`Stacks.EtaleCohomology.representationLevelTensorPairing`).

This file proves the properties of `ℱ_{ρ₀^∨}` that do not involve the pairing: it is lisse with
flat levels, the complexes `RΓ_c(X_k̄, -)` of the levels of the sheaf of every continuous
`ℤ_ℓ`-representation (so of `ℱ_ρ` and `ℱ_{ρ₀^∨}`) are perfect, and the geometric Frobenius at a
closed point acts on the stalks of `ℱ_{ρ₀^∨}` with the characteristic polynomial of `ρ^∨(F_y)`, so
that `ℱ_{ρ₀^∨}` is pointwise `ι`-mixed of weights `≤ 0` and `ι`-realizable when `ρ` satisfies the
conclusions of Deligne's conjecture.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.representationDualSheaf`: the ℓ-adic sheaf `ℱ_{ρ₀^∨}`.

## Main results

* `isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf`.
* `Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkFrobenius_representationDualSheaf`.
* `Stacks.EtaleCohomology.LAdicSheaf.isPointwiseMixedOfWeightLE_representationDualSheaf`,
  `Stacks.EtaleCohomology.LAdicSheaf.isIotaRealizable_representationDualSheaf`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.ZModPrimePower

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Perfectness of `RΓ_c` of the levels -/

section Perfect

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable [ConnectedSpace X.1] (x : GeometricPoint X.1) {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The levels of the ℓ-adic sheaf of a continuous `ℤ_ℓ`-representation are constructible
flat** on Mathlib's small étale site: they are constructible, and their stalks are pow-exact,
hence flat over `ℤ/ℓⁿ⁺¹`. -/
theorem isConstructibleFlatEtaleModule_etaleLevel_representationLAdicSheaf (n : ℕ) :
    IsConstructibleFlatEtaleModule B X (ZMod (ℓ ^ (n + 1))) (LAdicSheaf.etaleLevel B X ℓ
      (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ₀ hρ₀) n) := by
  have h0 : IsConstructibleFlatModuleSheaf B X (ZMod (ℓ ^ (n + 1)))
      ((representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ₀ hρ₀).level n) :=
    isConstructibleFlatModuleSheaf_of_flat_etaleModuleStalk B X _ _
      ((representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ₀ hρ₀).constructible n)
      (fun s => flat_of_isPowExact (LAdicSheaf.isPowExact_finiteLevelStalk _ s n
        (powExact_representationLevelSheaf B X x ρ₀ hρ₀ n)))
  exact isConstructibleFlatModuleSheaf_congr B X _
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unitIso.app
      _) h0

omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The levels of the ℓ-adic sheaf of a continuous `ℤ_ℓ`-representation lie in `D_ctf`**. -/
theorem isCtf_levelComplex_representationLAdicSheaf (n : ℕ) :
    IsCtf B X (ZMod (ℓ ^ (n + 1)))
      (DerivedCategory.Q.obj (LAdicSheaf.levelComplex B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n).obj) := by
  let G := LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n
  refine IsRepresentedByConstructibleFlatEtaleComplex.isCtf B (ZMod (ℓ ^ (n + 1)))
    ⟨(CochainComplex.singleFunctor _ 0).obj G, 0, 0, inferInstance, inferInstance,
      fun i => ?_, ⟨Iso.refl _⟩⟩
  by_cases hi : i = 0
  · subst hi
    exact (isConstructibleFlatEtaleModule_etaleLevel_representationLAdicSheaf B X ℓ x ρ₀ hρ₀
      n).of_iso B X _ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm
  · exact isConstructibleFlatEtaleModule_of_isZero B _ X
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G i hi)

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

include hcard in
omit [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The complexes `RΓ_c(X_k̄, Fₙ)` of the levels of the ℓ-adic sheaf `F` of a continuous
`ℤ_ℓ`-representation are perfect**, for `ℓ ≠ p`, by [Stacks, Tag 03V3] at the levels (`R π_*`
preserving `D_ctf` along proper morphisms being
`Stacks.EtaleCohomology.properDirectImageCtfInput`). -/
theorem isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf
    [Algebra.IsAlgebraic k kbar] (hℓp : ℓ ≠ p) (n : ℕ) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n))) := by
  let : Fintype (rationalPoints f) := @Fintype.ofFinite _ (finite_rationalPoints f)
  exact
    (perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf_of_isSeparated_of_properDirectImageCtfInput
    (kbar := kbar) (p := p) (q := q) (hcard := hcard)
    (natCard_zmod_pow_ne_zero_of_ne_char ℓ p hℓp n)
    (properDirectImageCtfInput B (ZMod (ℓ ^ (n + 1)))) f j _ X.property
    (isCtf_levelComplex_representationLAdicSheaf B X ℓ x ρ₀ hρ₀ n)).choose_spec.choose

end Perfect

/-! ### The sheaf of the contragredient of the integral model -/

section Dual

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)

/-- **The dual coefficients `ℱ_{ρ₀^∨}` of `ℱ_ρ`**: the ℓ-adic sheaf of the contragredient
`ρ₀^∨ = (ρ₀ᵀ)⁻¹` of the integral model `ρ₀` of `ρ` whose sheaf is `ℱ_ρ`
(`Stacks.EtaleCohomology.LAdicSheaf.representationSheaf`). -/
public def LAdicSheaf.representationDualSheaf : LAdicSheaf.{u, u + 1} B X ℓ :=
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
    (contragredient (integralModel ρ hρ))
    (continuous_contragredient (continuous_integralModel ρ hρ))

/-- `ℱ_{ρ₀^∨}` is lisse. -/
public theorem LAdicSheaf.representationDualSheaf_isLisse :
    (LAdicSheaf.representationDualSheaf B X x ρ hρ).IsLisse :=
  have := compactSpace_etaleFundamentalGroup X.1 x
  representationLAdicSheaf_isLisse B X x _ _ _

/-- The levels of `ℱ_{ρ₀^∨}` are pow-exact on Mathlib's small étale site. -/
public theorem LAdicSheaf.powExact_etaleLevel_representationDualSheaf (n : ℕ) :
    PowExact ℓ (n + 1)
      (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.representationDualSheaf B X x ρ hρ) n) :=
  have := compactSpace_etaleFundamentalGroup X.1 x
  powExact_etaleLevel_representationLAdicSheaf B X x _ _ n

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- Over `ℚ_ℓ`, the contragredient of the integral model at `g` has the characteristic polynomial
of `ρ^∨(g)`. -/
public theorem charpoly_contragredient_integralModel [CompactSpace (EtaleFundamentalGroup X.1 x)]
    (g : EtaleFundamentalGroup X.1 x) :
    ((contragredient (integralModel ρ hρ) g).val.charpoly).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      (contragredient ρ g).val.charpoly := by
  rw [contragredient_val, contragredient_val, Matrix.charpoly_transpose,
    Matrix.charpoly_transpose, ← map_inv, ← map_inv]
  exact charpoly_integralModel ρ hρ g⁻¹

variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The geometric Frobenius at a closed point `y` acts on the stalks of `ℱ_{ρ₀^∨}` and of
`ℱ_{ρ^∨}` with the same characteristic polynomial**, that of `ρ^∨(F_y)`. -/
public theorem LAdicSheaf.charpoly_rationalStalkFrobenius_representationDualSheaf
    (y : closedPoints X.1) :
    (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.representationDualSheaf B X x ρ hρ) y.1
        (finite_residueField f y.1 y.2)).charpoly =
      (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.representationSheaf B X x
        (contragredient ρ) (continuous_contragredient hρ)) y.1
        (finite_residueField f y.1 y.2)).charpoly := by
  have := finite_residueField f y.1 y.2
  have := compactSpace_etaleFundamentalGroup X.1 x
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso X.1 (geometricPointAt X.1 y.1) x
  rw [charpoly_rationalStalkFrobenius_representationSheaf B X x _ _ y t]
  have h := charpoly_rationalStalkEnd_representationLAdicSheaf B X x
    (contragredient (integralModel ρ hρ))
    (continuous_contragredient (continuous_integralModel ρ hρ))
    t (frobeniusPointHom X.1 y.1) ((frobeniusDataOfPath x y t).localElement⁻¹)
    (inv_localElement_hom x y t)
  have he : etaleFundamentalGroupMulEquiv t (frobeniusDataOfPath x y t).localElement⁻¹ =
      (frobeniusDataOfPath x y t).element⁻¹ :=
    MulEquiv.map_inv (etaleFundamentalGroupMulEquiv t) _
  rw [he] at h
  exact h.trans (charpoly_contragredient_integralModel B X x ρ hρ _)

/-- **`ℱ_{ρ₀^∨}` is pointwise `ι`-mixed of weights `≤ 0`** when `ρ` satisfies the conclusions of
Deligne's conjecture along `ι`: so does `ρ^∨`, whose Frobenius characteristic polynomials are
those of `ℱ_{ρ₀^∨}`. -/
public theorem LAdicSheaf.isPointwiseMixedOfWeightLE_representationDualSheaf {p : ℕ} (q : ℕ)
    {ι : ℚ_[ℓ] →+* ℂ} (h : HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f (LAdicSheaf.representationDualSheaf B X x ρ hρ)
      q ι 0 := by
  have h' := LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_of_hasDeligneConclusions
    B X ℓ f x (contragredient ρ) (continuous_contragredient hρ) q h.contragredient
  intro y z hz
  rw [LAdicSheaf.charpoly_rationalStalkFrobenius_representationDualSheaf B X x ρ hρ f y] at hz
  exact h' y z hz

/-- **`ℱ_{ρ₀^∨}` is `ι`-realizable** when `ρ` satisfies the conclusions of Deligne's conjecture
along `ι`: so does `ρ^∨`, which is therefore `ι`-realizable, and its sheaf has the Frobenius
characteristic polynomials of `ℱ_{ρ₀^∨}`. -/
public theorem LAdicSheaf.isIotaRealizable_representationDualSheaf {p : ℕ}
    {ι : ℚ_[ℓ] →+* ℂ} (h : HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    LAdicSheaf.IsIotaRealizable B X ℓ f (LAdicSheaf.representationDualSheaf B X x ρ hρ) ι := by
  have h' := (LAdicSheaf.isIotaRealizable_iff_charpoly B X ℓ f _ ι).1
    (LAdicSheaf.isIotaRealizable_representationSheaf B X ℓ f x (contragredient ρ)
      (continuous_contragredient hρ)
      (h.contragredient.isIotaRealizable (continuous_contragredient hρ)))
  obtain ⟨F'', hF'', hreal⟩ := h'
  refine (LAdicSheaf.isIotaRealizable_iff_charpoly B X ℓ f _ ι).2 ⟨F'', hF'', fun y j => ?_⟩
  rw [LAdicSheaf.charpoly_rationalStalkFrobenius_representationDualSheaf B X x ρ hρ f y]
  exact hreal y j

end Dual

end Stacks.EtaleCohomology

end
