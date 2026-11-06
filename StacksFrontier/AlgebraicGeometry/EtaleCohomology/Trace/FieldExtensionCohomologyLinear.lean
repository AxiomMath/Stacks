module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFieldExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCommutantCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageCoefficient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationChangeCoefficients

/-!
# `Hⁱ_c` after a finite extension of the base field, `E`-linearly

Let `X` be separated of finite type over a finite field `k` with `q = p ^ f` elements, `k'` a
finite extension with `q ^ (m + 1)` elements, `X' = X ×_k k'` with the projection `g : X' ⟶ X`, and
`F` an ℓ-adic sheaf on `X` with coefficients in a `ℤ_ℓ`-algebra `O`, `E = O[1/ℓ]`. The
identification `Hⁱ_c(X'_k̄, g⁻¹F ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` of
`Stacks.EtaleCohomology.LAdicSheaf.rationalFieldExtensionCohomologyIso` is natural in `F`, so it
commutes with the actions of `O` and is `E`-linear; it carries the Frobenius of `X'` over `k'` to
`(π_X^*) ^ (m + 1)`. This is the base change step (BC) of the identification of the stalk at the
origin in Laumon's degeneration ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `LAdicSheaf.CoefficientSheaf.rationalLinearEquivOfCommute`: a `ℚ_ℓ`-linear isomorphism of
  rational compactly supported cohomologies commuting with the actions of `O` is `E`-linear.
* `LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyLinearEquiv`.

## Main results

* `LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyLinearEquiv_frobenius`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Linear

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X X' : B.Scheme} [IsNoetherian X.1] [IsNoetherian X'.1]
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
  (F : LAdicSheaf.CoefficientSheaf B X ℓ O) (F' : LAdicSheaf.CoefficientSheaf B X' ℓ O)
  {k k' : Type u} [Field k] [Fintype k] [Field k'] [Fintype k']
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (f' : X'.1 ⟶ Spec (.of k')) [LocallyOfFiniteType f'] [QuasiCompact f'] [IsSeparated f']
  (j : CompactificationOf (Over.mk f)) (j' : CompactificationOf (Over.mk f'))
  (kbar kbar' : Type u) [Field kbar] [Algebra k kbar] [Field kbar'] [Algebra k' kbar'] (i i' : ℤ)
  (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

/-- **A `ℚ_ℓ`-linear isomorphism commuting with the actions of `O` is `E`-linear**: if
`c : Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) ≃ Hⁱ'_c(X'_k̄', F' ⊗ ℚ_ℓ)` commutes with the actions of every `o ∈ O`,
it commutes with the actions of `E = O[1/ℓ]`. -/
public def LAdicSheaf.CoefficientSheaf.rationalLinearEquivOfCommute
    (c : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        F.toLAdicSheaf i ≃ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ f' j' kbar'
        F'.toLAdicSheaf i')
    (hc : ∀ (o : O) (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        F.toLAdicSheaf i),
      c (F.rationalIntegralRingHom f j kbar i o v) =
        F'.rationalIntegralRingHom f' j' kbar' i' o (c v)) :
    letI := F.rationalCohomologyModule f j kbar i E
    letI := F'.rationalCohomologyModule f' j' kbar' i' E
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ f' j' kbar'
        F'.toLAdicSheaf i' :=
  letI := F.rationalCohomologyModule f j kbar i E
  letI := F'.rationalCohomologyModule f' j' kbar' i' E
  { toFun := c
    map_add' := c.map_add
    map_smul' := fun e v => by
      change c (F.rationalRingHom f j kbar i E e v) = F'.rationalRingHom f' j' kbar' i' E e (c v)
      have hO : (c.conjRingEquiv.toRingHom.comp (F.rationalRingHom f j kbar i E)).comp
          (algebraMap O E) = (F'.rationalRingHom f' j' kbar' i' E).comp (algebraMap O E) := by
        refine RingHom.ext fun o => ?_
        simp only [RingHom.comp_apply]
        rw [LAdicSheaf.CoefficientSheaf.rationalRingHom_algebraMap_apply,
          LAdicSheaf.CoefficientSheaf.rationalRingHom_algebraMap_apply]
        refine LinearMap.ext fun w => ?_
        change c (F.rationalIntegralRingHom f j kbar i o (c.symm w)) = _
        rw [hc, LinearEquiv.apply_symm_apply]
      have h := LinearMap.congr_fun
        (RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (ℓ : O)) hO) e) (c v)
      refine Eq.trans ?_ h
      change _ = c (F.rationalRingHom f j kbar i E e (c.symm (c v)))
      rw [LinearEquiv.symm_apply_apply]
    invFun := c.symm
    left_inv := c.left_inv
    right_inv := c.right_inv }

omit [Algebra ℚ_[ℓ] E] in
/-- The `E`-linear isomorphism `rationalLinearEquivOfCommute c hc` acts as `c`. -/
@[simp]
public theorem LAdicSheaf.CoefficientSheaf.rationalLinearEquivOfCommute_apply
    (c : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        F.toLAdicSheaf i ≃ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ f' j' kbar'
        F'.toLAdicSheaf i')
    (hc : ∀ (o : O) (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        F.toLAdicSheaf i),
      c (F.rationalIntegralRingHom f j kbar i o v) =
        F'.rationalIntegralRingHom f' j' kbar' i' o (c v))
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    F.rationalLinearEquivOfCommute F' f f' j j' kbar kbar' i i' E c hc v = c v :=
  rfl

end Linear

section FieldExtension

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]
  [IsNoetherian X.1] [IsNoetherian (fieldExtensionScheme B X f k').1]
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O) (i : ℤ)
  (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

/-- Intertwining `a ≫ e.hom = e.hom ≫ b` also gives `e.inv (b w) = a (e.inv w)`. -/
private theorem iso_inv_conj_apply {R : Type*} [Ring R] {M N : ModuleCat.{u + 1} R} (e : M ≅ N)
    (a : M ⟶ M) (b : N ⟶ N) (h : a ≫ e.hom = e.hom ≫ b) (w : N) :
    e.inv.hom (b w) = a (e.inv.hom w) :=
  (congrArg e.inv.hom (iso_conj_apply e a b h w)).symm.trans (Iso.hom_inv_id_apply e _)

/-- The rational field extension isomorphism commutes with the actions of `O`. -/
public theorem
    LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyIso_inv_rationalIntegralRingHom
    (o : O) (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (compactificationFieldBaseChange f j k') kbar
      (LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f k') F).toLAdicSheaf i) :
    (LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F.toLAdicSheaf i).inv.hom
        ((LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f k')
            F).rationalIntegralRingHom (pullback.snd f (specAlgebraMap k k'))
          (compactificationFieldBaseChange f j k') kbar i o v) =
      F.rationalIntegralRingHom f j kbar i o
        ((LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar
          F.toLAdicSheaf i).inv.hom v) := by
  have h := congrArg (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.fieldExtensionCohomologyIso_hom_naturality B X ℓ f j k' kbar i (F.act o).asHom)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact iso_inv_conj_apply _ _ _ h v

variable (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
  (hcard : Fintype.card k = p ^ q) (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * (m + 1)))

/-- **`Hⁱ_c(X'_k̄, g⁻¹F ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`, `E`-linearly**, for `X' = X ×_k k'` and
the projection `g : X' ⟶ X`. -/
public def LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyLinearEquiv :
    letI := (LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f k')
      F).rationalCohomologyModule (pullback.snd f (specAlgebraMap k k'))
        (compactificationFieldBaseChange f j k') kbar i E
    letI := F.rationalCohomologyModule f j kbar i E
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f k')
          F).toLAdicSheaf i ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i :=
  LAdicSheaf.CoefficientSheaf.rationalLinearEquivOfCommute _ F _ f _ j kbar kbar i i E
    (LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar
      F.toLAdicSheaf i).toLinearEquiv.symm
    (LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyIso_inv_rationalIntegralRingHom
      B X ℓ f j k' kbar F i)

omit [Algebra ℚ_[ℓ] E] in
/-- **The `E`-linear field extension isomorphism carries the Frobenius of `X'` over `k'` to
`(π_X^*) ^ (m + 1)`**, `#k' = q ^ (m + 1)`. -/
public theorem LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyLinearEquiv_frobenius
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
        (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f k') F).toLAdicSheaf i) :
    LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyLinearEquiv B X ℓ f j k' kbar F i E
        ((LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f k')
          F).rationalGeometricCompactlySupportedFrobenius (pullback.snd f (specAlgebraMap k k'))
            (compactificationFieldBaseChange f j k') kbar i E p (q * (m + 1)) hcard' v) =
      ((F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard) ^ (m + 1))
        (LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyLinearEquiv B X ℓ f j k' kbar
          F i E v) := by
  let R := LAdicSheaf.rationalFieldExtensionCohomologyIso B X ℓ f j k' kbar F.toLAdicSheaf i
  let πX := LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
    F.toLAdicSheaf i
  let πX' := LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
    (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
    (compactificationFieldBaseChange f j k') kbar p (q * (m + 1)) hcard'
    (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F.toLAdicSheaf) i
  have h := congrArg (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.fieldExtensionCohomologyIso_comm B X ℓ f j k' kbar F.toLAdicSheaf i p q hcard m
      hcard')
  rw [Functor.map_comp, Functor.map_comp] at h
  have hpow : (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      ((End.of (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        F.toLAdicSheaf i)) ^ (m + 1)).asHom = ((End.of πX) ^ (m + 1)).asHom :=
    congrArg End.asHom
      (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).mapEnd _).map_pow _ _)
  have hp : ((End.of πX) ^ (m + 1)).asHom.hom = πX.hom ^ (m + 1) := by
    have h₀ := map_pow (ModuleCat.endRingEquiv
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i))
      (End.of πX) (m + 1)
    simp only [ModuleCat.endRingEquiv_apply] at h₀
    exact h₀
  let := (LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f k')
    F).rationalCohomologyModule (pullback.snd f (specAlgebraMap k k'))
      (compactificationFieldBaseChange f j k') kbar i E
  let := F.rationalCohomologyModule f j kbar i E
  have hπ : ∀ w, ((F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard) ^ (m + 1))
      w = (πX.hom ^ (m + 1)) w := by
    intro w
    rw [Module.End.pow_apply, Module.End.pow_apply]
    rfl
  have hP : ∀ w, ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      ((End.of (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        F.toLAdicSheaf i)) ^ (m + 1)).asHom).hom w = (πX.hom ^ (m + 1)) w := by
    intro w
    rw [hpow]
    exact LinearMap.congr_fun hp w
  show R.inv.hom (πX'.hom v) = _
  exact (iso_inv_conj_apply R _ _ h v).trans ((hP _).trans (hπ _).symm)

end FieldExtension

end Stacks.EtaleCohomology

end
