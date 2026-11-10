module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLisseFibre

/-!
# The lisse locus of the Fourier family from Laumon's local theory

The line-by-line lisseness `Stacks.EtaleCohomology.LaumonFourierLineLisseFibreInput` of the
Fourier family `G_V = R¹g'_!(pr₁^*ℱ_σ ⊗ L_ψ'(a xⁿ + x t))`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) follows from the two statements of Laumon's
local theory of the Fourier transform (Laumon, *Transformation de Fourier, constantes d'équations
fonctionnelles et conjecture de Weil*, 2.4.3; Katz, *Gauss sums, Kloosterman sums, and monodromy
groups*, 8.5):

* `Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`: there is `N` such that for `n > N`
  prime to `p` and `a ≠ 0` the family is lisse over every open of the `t`-line. For `n` larger than
  the slopes of `σ` at `∞`, `ℱ_σ ⊗ L_ψ'(a xⁿ)` is totally wild at `∞` with all slopes `n > 1`, and
  the Fourier transform of such a sheaf is lisse on all of `𝔸¹` (with `R⁰ = R² = 0`; the same holds
  for the reductions of every lattice modulo `ℓᵐ`, the slopes being those of the `ℚ_ℓ`-sheaf).
* `Stacks.EtaleCohomology.LaumonFourierLineLisseZeroInput`: on the line `a = 0` (the Fourier
  transform of `σ` itself) the family is lisse off the zeros of one nonzero `D₀ ∈ k[t]`, over every
  finite extension of `k`: the singular points are the `t` for which `ℱ_σ ⊗ L_ψ(t x)` has a slope
  `≤ 1` part at `∞`, a finite set stable under `Gal(k̄/k)`.

Then `h_m = D₀(t)` serves for every `m`
(`Stacks.EtaleCohomology.laumonFourierLineLisseFibreInput_of_away_zero`), whence
`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`
(`Stacks.EtaleCohomology.laumonFourierLineLisseInput_of_away_zero`).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineLisseAway`: the Fourier family is lisse over every open
  of the `t`-line for `a ≠ 0`.
* `Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`: Laumon's local theory away from
  `a = 0`.
* `Stacks.EtaleCohomology.LaumonFourierLineLisseZeroInput`: Laumon's local theory on the line
  `a = 0`.

## Main results

* `Stacks.EtaleCohomology.laumonFourierLineLisseFibreInput_of_away_zero`: the two local statements
  imply the line-by-line lisseness.
* `Stacks.EtaleCohomology.laumonFourierLineLisseInput_of_away_zero`: the two local statements imply
  `Stacks.EtaleCohomology.LaumonFourierLineLisseInput`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

section Algebra

open Polynomial

variable {k : Type*} [Field k]

/-- `m(a)` restricted to the line `a = a₀` is the constant `m(a₀)`. -/
public theorem eval₂_laumonLine_aeval_X_zero {k' : Type*} [Field k'] [Algebra k k'] (a : k')
    (mk : Polynomial k) :
    MvPolynomial.eval₂ (C.comp (algebraMap k k')) ![C a, X]
      (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) mk) =
        C (Polynomial.aeval a mk) := by
  rw [Polynomial.aeval_def, ← MvPolynomial.coe_eval₂Hom, Polynomial.hom_eval₂, Polynomial.aeval_def,
    Polynomial.hom_eval₂]
  congr 1
  · ext r
    simp [MvPolynomial.algebraMap_eq]
  · simp

/-- `D₀(t)` restricted to the line `a = a₀` is `D₀` over `k'`. -/
public theorem eval₂_laumonLine_aeval_X_one {k' : Type*} [Field k'] [Algebra k k'] (a : k')
    (D₀ : Polynomial k) :
    MvPolynomial.eval₂ (C.comp (algebraMap k k')) ![C a, X]
      (Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) D₀) =
        D₀.map (algebraMap k k') := by
  rw [Polynomial.aeval_def, ← MvPolynomial.coe_eval₂Hom, Polynomial.hom_eval₂, Polynomial.map]
  congr 1
  · ext r
    simp [MvPolynomial.algebraMap_eq]
  · simp

/-- **`m(a)` does not divide a nonzero `D₀(t)`**, for `m` with a root `a₀` in some field. -/
public theorem not_aeval_X_zero_dvd_aeval_X_one {k' : Type*} [Field k'] [Algebra k k'] (a : k')
    {mk : Polynomial k} (hmk : Polynomial.aeval a mk = 0) {D₀ : Polynomial k} (hD₀ : D₀ ≠ 0) :
    ¬ Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) mk ∣
      Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) D₀ := by
  rintro ⟨q, hq⟩
  have h1 := congrArg (MvPolynomial.eval₂ (C.comp (algebraMap k k')) ![C a, X]) hq
  rw [eval₂_laumonLine_aeval_X_one, MvPolynomial.eval₂_mul, eval₂_laumonLine_aeval_X_zero, hmk,
    map_zero, zero_mul] at h1
  exact Polynomial.map_ne_zero hD₀ h1

end Algebra

section Family

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] [ConnectedSpace U.1]
  (k : Type u) [Field k] [Fintype k] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
  (x : GeometricPoint U.1) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
  (ψ : AddChar k E) (n : ℕ)

/-- **The Fourier family is lisse over every open of the `t`-line, for `a ≠ 0`**: for every
finite extension `k'` of `k`, `a ∈ k'ˣ`, all the data of the family, every open `V'` of the
`t`-line, `U' = pr₂⁻¹(V')` and any compactification of `g' : U' → V'`, `G_V` is lisse. -/
public def LaumonFourierLineLisseAway : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k'), a ≠ 0 →
    ∀ (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (pz : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1]
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
    IsOpenImmersion (B.inclusion.map jV') →
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b
      (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁ jU g'
        jg').toLAdicSheaf.IsLisse

end Family

/-- **Laumon's local theory, away from `a = 0`**: under the hypotheses of
`Stacks.EtaleCohomology.LaumonFourierLineLisseInput` there is `N` such that for `n > N` prime to
`p` the Fourier family is lisse over every open of the `t`-line for every `a ≠ 0`
(`Stacks.EtaleCohomology.LaumonFourierLineLisseAway`): `ℱ_σ ⊗ L_ψ'(a xⁿ)` has all its slopes at
`∞` equal to `n > 1`, and the Fourier transform of such a sheaf is lisse on `𝔸¹`. -/
public def LaumonFourierLineLisseAwayInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p], Fintype.card k = p ^ n → ℓ ≠ p →
    ∀ (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      LaumonFourierLineLisseAway B U ℓ k e x E b σ ψ n

/-- **Laumon's local theory on the line `a = 0`**: under the hypotheses of
`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`, for every `n` there is a nonzero `D₀ ∈ k[t]`
such that on the line `a = 0` (the Fourier transform of `σ`) the family is lisse over every open of
the `t`-line inside `D(D₀)`, over every finite extension of `k`
(`Stacks.EtaleCohomology.LaumonFourierLineLisseOn` for `m = a` and `h = D₀(t)`). -/
public def LaumonFourierLineLisseZeroInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p], Fintype.card k = p ^ n → ℓ ≠ p →
    ∀ (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
          f j kbar (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∀ n : ℕ, ∃ D₀ : Polynomial k, D₀ ≠ 0 ∧
      LaumonFourierLineLisseOn B U ℓ k e x E b σ ψ n Polynomial.X
        (Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) D₀)

/-- **The line-by-line lisseness from Laumon's local theory**: with `D₀` from
`Stacks.EtaleCohomology.LaumonFourierLineLisseZeroInput`, `h_m = D₀(t)` is not divisible by
`m(a)` (evaluate at a root of `m`) and the family is lisse over every open inside `D(D₀)` on every
line: by `Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput` for `a ≠ 0`, and by the choice of
`D₀` for `a = 0`. -/
public theorem laumonFourierLineLisseFibreInput_of_away_zero
    (ha : LaumonFourierLineLisseAwayInput.{u}) (hb : LaumonFourierLineLisseZeroInput.{u}) :
    LaumonFourierLineLisseFibreInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ hef j kbar _ _ _ _ p q _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hstab hζ ι' β hV hpure ψ hψ
  obtain ⟨N, hN⟩ := ha B U ℓ k f e hef j kbar p q hcard hℓp x E b σ hσ K hirr hstab hζ ι' β hpure
    ψ hψ
  refine ⟨N, fun n hn hpn mk hmk => ?_⟩
  obtain ⟨D₀, hD₀, hZ⟩ := hb B U ℓ k f e hef j kbar p q hcard hℓp x E b σ hσ K hirr hstab hζ ι' β
    hpure ψ hψ n
  refine ⟨Polynomial.aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) D₀, ?_, ?_⟩
  · rcases hmk with rfl | hirr'
    · exact not_aeval_X_zero_dvd_aeval_X_one (0 : k) (by simp) hD₀
    · have := Fact.mk hirr'
      exact not_aeval_X_zero_dvd_aeval_X_one (AdjoinRoot.root mk)
        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) hD₀
  · intro k' _ _ _ a _ hS hL z hz pz hσ₁ V' U' _ _ jV' jU g' _ _ _ jg' hopen hrange hpb
    by_cases ha0 : a = 0
    · subst ha0
      exact hZ k' 0 (by simp) hS hL z hz pz hσ₁ V' U' jV' jU g' jg' hopen hrange hpb
    · exact hN n hn hpn k' a ha0 hS hL z hz pz hσ₁ V' U' jV' jU g' jg' hopen hpb

/-- **The lisse locus of the Fourier family with all its data, from Laumon's local theory**:
`Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput` and
`Stacks.EtaleCohomology.LaumonFourierLineLisseZeroInput` imply
`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`. -/
public theorem laumonFourierLineLisseInput_of_away_zero
    (ha : LaumonFourierLineLisseAwayInput.{u}) (hb : LaumonFourierLineLisseZeroInput.{u}) :
    LaumonFourierLineLisseInput.{u} :=
  laumonFourierLineLisseInput_of_fibre (laumonFourierLineLisseFibreInput_of_away_zero ha hb)

end Stacks.EtaleCohomology

end
