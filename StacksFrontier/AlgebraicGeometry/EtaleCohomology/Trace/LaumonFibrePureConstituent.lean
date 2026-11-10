module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreStableReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepCohomologyDecomposition

/-!
# The fibres of a direct sum are pure off the product of the curves

The statement `Stacks.EtaleCohomology.LaumonFibrePureConstituentInput` of Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): if after the extension of scalars to `E'`
the representation `σ` is conjugate to a block sum of `σᵢ`, each with fibres pure off `Dᵢ = 0`,
then the fibres of `σ` are pure off `∏ Dᵢ = 0`. At a fibre, the twist of `σ ⊗ E'` by the
Artin–Schreier character is conjugate to the block sum of the twists of the `σᵢ`, so the
`E'`-linear Frobenius characteristic polynomial of `σ ⊗ E'` is the product of those of the `σᵢ`
(`Stacks.EtaleCohomology.restrictScalarsRepFrobeniusCharpoly_eq_prod`), and it is the image of the
`E`-linear one of `σ` (`Stacks.EtaleCohomology.restrictScalarsRepFrobeniusCharpoly_map`); a root
along `ι' = ι'' ∘ (E → E')` is therefore a root of one of the factors along `ι''`.
## Main results

* `Stacks.EtaleCohomology.isRoot_charpoly_twist_of_blockConj`.
* `Stacks.EtaleCohomology.laumonFibrePureConstituentInput`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Twist

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (i : ℤ)
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  {E E' : Type} [Field E] [Field E'] [Algebra ℚ_[ℓ] E] [Algebra ℚ_[ℓ] E'] [Algebra E E']
  [IsScalarTower ℚ_[ℓ] E E'] {d d' : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
  (b' : Module.Basis (Fin d') ℚ_[ℓ] E')

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Roots of the Frobenius characteristic polynomial of a twisted representation which becomes
a block sum over `E'`.**  If `M ((σ ⊗ E') ⊗ eqv) M⁻¹ = ⨁ σₜ` and `χ' = χ ⊗ E'`, every root along
`ι'` of the `E`-linear Frobenius characteristic polynomial on `Hⁱ_c(ℱ_{Res_b (σ ⊗ χ)})` is a root
along `ι''` (extending `ι'`) of that of some `σₜ ⊗ χ'`, which has continuous `Res_{b'}` and
finite-dimensional cohomology. -/
theorem isRoot_charpoly_twist_of_blockConj {m : ℕ} (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
    (χ : EtaleFundamentalGroup X.1 x →* Eˣ) {r : ℕ} {ms : Fin r → ℕ}
    (σs : ∀ t, EtaleFundamentalGroup X.1 x →* GL (Fin (ms t)) E')
    (χ' : EtaleFundamentalGroup X.1 x →* E'ˣ) (hχ : ∀ g, (χ' g : E') = algebraMap E E' (χ g))
    (eqv : Fin m ≃ Σ t, Fin (ms t)) (M : GL (Σ t, Fin (ms t)) E')
    (hM : ∀ g, (M : Matrix (Σ t, Fin (ms t)) (Σ t, Fin (ms t)) E') *
        Matrix.reindex eqv eqv ((σ g).val.map (algebraMap E E')) *
        ((M⁻¹ : GL (Σ t, Fin (ms t)) E') : Matrix (Σ t, Fin (ms t)) (Σ t, Fin (ms t)) E') =
      Matrix.blockDiagonal' fun t => (σs t g).val)
    (hτ : Continuous (restrictScalarsRep b (characterTwist σ χ)))
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      j kbar (restrictScalarsRepCoefficientSheaf B X x b (characterTwist σ χ) hτ).toLAdicSheaf i)]
    (ι' : E →+* ℂ) (ι'' : E' →+* ℂ) (hι : ι''.comp (algebraMap E E') = ι') (P : ℂ → Prop)
    (hP : ∀ t (hτt : Continuous (restrictScalarsRep b' (characterTwist (σs t) χ')))
      [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
        j kbar (restrictScalarsRepCoefficientSheaf B X x b' (characterTwist (σs t) χ')
          hτt).toLAdicSheaf i)] (z : ℂ),
      ((restrictScalarsRepFrobeniusCharpoly B X x f j kbar i p q hcard b' _ hτt).map ι'').IsRoot z →
        P z) (z : ℂ)
    (hz : ((restrictScalarsRepFrobeniusCharpoly B X x f j kbar i p q hcard b _ hτ).map
      ι').IsRoot z) :
    P z := by
  have hτ' := continuous_restrictScalarsRep_map B X x b b' hτ
  have hM' : ∀ g, (M : Matrix (Σ t, Fin (ms t)) (Σ t, Fin (ms t)) E') * Matrix.reindex eqv eqv
      (((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp (characterTwist σ χ)) g).val *
      ((M⁻¹ : GL (Σ t, Fin (ms t)) E') : Matrix (Σ t, Fin (ms t)) (Σ t, Fin (ms t)) E') =
      Matrix.blockDiagonal' fun t => (characterTwist (σs t) χ' g).val := fun g => by
    have h1 : (((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp (characterTwist σ χ))
        g).val = (χ' g : E') • (σ g).val.map (algebraMap E E') := by
      change ((characterTwist σ χ g).val).map (algebraMap E E') = _
      rw [characterTwist_val, hχ]
      ext a a'
      simp
    have h2 : Matrix.reindex eqv eqv ((χ' g : E') • (σ g).val.map (algebraMap E E')) =
        (χ' g : E') • Matrix.reindex eqv eqv ((σ g).val.map (algebraMap E E')) := by
      ext a a'
      simp
    rw [h1, h2, Matrix.mul_smul, Matrix.smul_mul, hM g, ← Matrix.blockDiagonal'_smul]
    congr 1
    funext t
    rw [characterTwist_val]
    rfl
  have hτs := continuous_restrictScalarsRep_of_blockConj B X x b' hτ' eqv M hM'
  have := finiteDimensional_map B X x f j kbar i b b' hτ hτ'
  have := finiteDimensional_of_blockConj B X x f j kbar i b' hτ' eqv M hM' hτs
  have hprod := (restrictScalarsRepFrobeniusCharpoly_map B X x f j kbar i p q hcard b b' hτ
    hτ').symm.trans (restrictScalarsRepFrobeniusCharpoly_eq_prod B X x f j kbar i p q hcard b' hτ'
      eqv M hM' hτs)
  have hz' : ((∏ t, restrictScalarsRepFrobeniusCharpoly B X x f j kbar i p q hcard b'
      (characterTwist (σs t) χ') (hτs t)).map ι'').IsRoot z := by
    rw [← hprod, Polynomial.map_map, hι]
    exact hz
  rw [Polynomial.map_prod, Polynomial.IsRoot, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at hz'
  obtain ⟨t, -, ht⟩ := hz'
  exact hP t (hτs t) z ht

end Twist

/-- **The fibres of a direct sum are pure off the product of the curves** (Kedlaya, *Fourier
transforms and p-adic Weil II*, §6.4): `Stacks.EtaleCohomology.LaumonFibrePureConstituentInput`. -/
public theorem laumonFibrePureConstituentInput : LaumonFibrePureConstituentInput.{u} := by
  intro B U ℓ _ _ _ _ k _ _ e _ x E _ _ d b m σ ι' β ψ n E' _ _ _ _ d' b' ι'' hι r ms σs eqv M hM
    Ds hDs k' _ _ _ hX' _ _ x' hx' a c hD p₀ hτ _ _ _ j' kbar' _ _ _ p n' _ _ hcard' hV z hz
  have hD' : ∀ t, MvPolynomial.eval ![a, c] (MvPolynomial.map (algebraMap k k') (Ds t)) ≠ 0 := by
    intro t h
    apply hD
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ t) h
  let φ : EtaleFundamentalGroup _ x' →* EtaleFundamentalGroup U.1 x :=
    hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom
  exact isRoot_charpoly_twist_of_blockConj B
    (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
    x' (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) j' kbar' 1 p n' hcard' b b'
    (σ.comp φ)
    (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
      (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)
      (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀)
    (fun t => (σs t).comp φ)
    (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
      (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)
      (((algebraMap E E').toMonoidHom.compAddChar ψ).compAddMonoidHom
        (Algebra.trace k k').toAddMonoidHom) x' p₀)
    (fun g => rfl) eqv M (fun g => hM _) hτ (hV := hV) ι' ι'' hι _
    (fun t hτt hVt z hz => hDs t k' hX' x' hx' a c (hD' t) p₀ hτt j' kbar' p n' hcard' (hV := hVt)
      z hz) z hz

end Stacks.EtaleCohomology

end
