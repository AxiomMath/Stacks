module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLimitWeights

/-!
# Short exact sequences of ℓ-adic sheaves and weights of `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`

Let `0 → F₁ → F₂ → F₃ → 0` be a sequence of ℓ-adic sheaves on `X` which is short exact at every
finite level.  The distinguished triangles of `RΓ_c(X_k̄, -)` give, at every level `n`, exact
sequences `Hⁱ_c(X_k̄, F₁,ₙ) → Hⁱ_c(X_k̄, F₂,ₙ) → Hⁱ_c(X_k̄, F₃,ₙ)`; when the first terms are finite
they pass to the limit and, `ℚ_ℓ` being flat over `ℤ_ℓ`, to the rational limit:

`Hⁱ_c(X_k̄, F₁ ⊗ ℚ_ℓ) → Hⁱ_c(X_k̄, F₂ ⊗ ℚ_ℓ) → Hⁱ_c(X_k̄, F₃ ⊗ ℚ_ℓ)`

is exact, and its maps commute with the geometric Frobenius `π_X^*`.  Hence a bound on the
absolute values of the Frobenius characteristic roots on the outer terms gives the same bound on
the middle term.

## Main results

* `Stacks.EtaleCohomology.exact_geometricCompactSupportPadicCohomology_map`: exactness in the
  middle of `Hⁱ_c(X_k̄, -)` on a short exact sequence of sheaves of `ℤ_ℓ`-modules.
* `Stacks.EtaleCohomology.LAdicSheaf.exact_rationalGeometricCompactlySupportedCohomologyMap`: the
  rational sequence above is exact.
* `Stacks.EtaleCohomology.LAdicSheaf.isCharpolyNormMixedOfWeightLE_of_shortExact`: weights pass
  from the outer terms to the middle one.

## References

* Kedlaya, *Fourier transforms and p-adic Weil II*, Theorem 6.6.2
* Deligne, *La conjecture de Weil II*, 3.2
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}

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

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f] in
/-- **`Hⁱ_c(X_k̄, -)` is exact in the middle** on a short exact sequence of sheaves of
`ℤ_ℓ`-modules on the small étale site of `X`. -/
public theorem exact_geometricCompactSupportPadicCohomology_map [Finite k]
    {S : ShortComplex (Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ]))}
    (hS : S.ShortExact) (i : ℤ) :
    Function.Exact ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map S.f).hom
      ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map S.g).hom := by
  have := Fintype.ofFinite k
  have hS₁ := hS.map_of_exact (SmallEtale.sheafEquiv B X.1 X.property
    (ModuleCat.{u + 1} ℤ_[ℓ])).functor
  have hS₂ := hS₁.map_of_exact (HomologicalComplex.single (EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (ComplexShape.up ℤ) 0)
  have hge : ∀ T : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ_[ℓ]),
      ∃ n, CochainComplex.IsStrictlyGE ((HomologicalComplex.single
        (EtaleModules.{u, 0} ℤ_[ℓ] X.1) (ComplexShape.up ℤ) 0).obj
          ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj T)) n :=
    fun _ => ⟨0, inferInstance⟩
  exact exact_homology_compactSupportFrobeniusFunctor_map ℤ_[ℓ] f j kbar hS₂
    (hge S.X₁) (hge S.X₂) (hge S.X₃) i

variable {f j kbar}

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Exactness of `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` in the middle.**  For morphisms `φ : F₁ ⟶ F₂` and
`ψ : F₂ ⟶ F₃` of ℓ-adic sheaves which form a short exact sequence at every finite level, and with
every `Hⁱ_c(X_k̄, F₁,ₙ)` finite,
`Hⁱ_c(X_k̄, F₁ ⊗ ℚ_ℓ) → Hⁱ_c(X_k̄, F₂ ⊗ ℚ_ℓ) → Hⁱ_c(X_k̄, F₃ ⊗ ℚ_ℓ)` is exact. -/
public theorem LAdicSheaf.exact_rationalGeometricCompactlySupportedCohomologyMap [Finite k]
    {F₁ F₂ F₃ : LAdicSheaf B X ℓ} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)
    (hw : ∀ n, LAdicSheaf.padicLevelMap φ n ≫ LAdicSheaf.padicLevelMap ψ n = 0)
    (hS : ∀ n, (ShortComplex.mk _ _ (hw n)).ShortExact) (i : ℤ)
    (hfin : ∀ n, Finite ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F₁ n))) :
    Function.Exact
      ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i)).hom
      ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i)).hom :=
  exact_rationalLimMap_of_finite
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar φ i)
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar ψ i)
    (fun n => exact_geometricCompactSupportPadicCohomology_map f j kbar (hS n.unop) i)
    (fun n => hfin n.unop)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Weights along a short exact sequence of ℓ-adic sheaves.**  For morphisms `φ : F₁ ⟶ F₂` and
`ψ : F₂ ⟶ F₃` of ℓ-adic sheaves which form a short exact sequence at every finite level, with every
`Hⁱ_c(X_k̄, F₁,ₙ)` finite: if the complex roots, read along `ι`, of the characteristic polynomials
of `π_X^*` on `Hⁱ_c(X_k̄, F₁ ⊗ ℚ_ℓ)` and on `Hⁱ_c(X_k̄, F₃ ⊗ ℚ_ℓ)` have absolute values
`q' ^ (w / 2)` with `w ≤ b`, so do those on `Hⁱ_c(X_k̄, F₂ ⊗ ℚ_ℓ)`. -/
public theorem LAdicSheaf.isCharpolyNormMixedOfWeightLE_of_shortExact
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    {F₁ F₂ F₃ : LAdicSheaf B X ℓ} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)
    (hw : ∀ n, LAdicSheaf.padicLevelMap φ n ≫ LAdicSheaf.padicLevelMap ψ n = 0)
    (hS : ∀ n, (ShortComplex.mk _ _ (hw n)).ShortExact) (i : ℤ)
    (hfin : ∀ n, Finite ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F₁ n)))
    [h₁ : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F₁ i)]
    [h₂ : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F₂ i)]
    [h₃ : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F₃ i)]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (hF₁ : IsCharpolyNormMixedOfWeightLE q' ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F₁ i).hom)
    (hF₃ : IsCharpolyNormMixedOfWeightLE q' ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F₃ i).hom) :
    IsCharpolyNormMixedOfWeightLE q' ι b (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius
      B X ℓ f j kbar p q hcard F₂ i).hom := by
  have hcomm : ∀ {G₁ G₂ : LAdicSheaf B X ℓ} (χ : G₁ ⟶ G₂),
      LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar G₁ i
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) ≫
        LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar χ i =
      LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar χ i ≫
        LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar G₂ i
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) := by
    intro G₁ G₂ χ
    ext n : 2
    induction n using Opposite.rec with
    | op n =>
      exact ((geometricCompactSupportPadicCohomologyPullback B X ℓ f j kbar i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).naturality
          (LAdicSheaf.padicLevelMap χ n)).symm
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
    (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F₁ i)) := h₁
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
    (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F₂ i)) := h₂
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
    (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F₃ i)) := h₃
  exact isCharpolyNormMixedOfWeightLE_rationalLimMap_of_exact
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar φ i)
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar ψ i)
    (fun n => exact_geometricCompactSupportPadicCohomology_map f j kbar (hS n.unop) i)
    (fun n => hfin n.unop)
    _ _ _ (hcomm φ) (hcomm ψ) hF₁ hF₃

end Stacks.EtaleCohomology

end
