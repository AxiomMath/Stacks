module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierFamilyConjugateWild
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormStable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveDualTraceConjugationMultiset
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyConjugateProductReal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.UnramifiedTwistContinuity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreTwistPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreTopVanishingProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyFibreCharacter
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilySheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineProjectiveCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteCompactSupportCohomology
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.UnramifiedCharacter

/-!
# The real partner of the Fourier family in the totally wild range

This proves `Stacks.EtaleCohomology.LaumonFourierFamilyConjugateWildInput`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, proof of Theorem 6.4) from the identification of the fibres of the family over the
closed points of the `t`-line (`Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtensionInput`);
the vanishing of `H²_c` on the fibres is `Stacks.EtaleCohomology.laumonFibreTopVanishingInput`.

Let `τ`, `τ''` be the representations of `π₁(V', x̄_V)` attached to the Fourier family `G_V` of
`(σ, ψ)` and to that of `(σ^∨, ψ⁻¹)`, and `χ` the unramified character with
`χ(F_y) = q ^ (β deg y)`, `q = #k'`. At a closed point `y` of `V'` the characteristic polynomial of
`τ(F_y)` is that of the Frobenius of `κ(y)` on `H¹_c` of the fibre `ℱ_{τ_y}`,
`τ_y = σ ⊗ L_{ψ ∘ Tr}(a xⁿ + t(y) x)` over `κ(y)`
(`Stacks.EtaleCohomology.charpoly_laumonFourierFamily_eq_fieldExtension`), and that of `τ''(F_y)`
is the one on `H¹_c` of `ℱ_{τ_y^∨}`, since the fibre of the dual family is the contragredient
(`Stacks.EtaleCohomology.contragredient_characterTwist`,
`Stacks.ArtinSchreier.artinSchreierCharacter_inv`). The trace formula on `𝔸¹_{κ(y)}`
(`Stacks.EtaleCohomology.roots_filter_ne_zero_contragredient_eq_map_conj_of_curve`, with the
purity `Stacks.EtaleCohomology.laumonFibreTwistPurityInput`) makes the roots of `τ''(F_y)` the
`q_y ^ (-β) z̄`, `z` running over those of `τ(F_y)`, so that the roots of `(τ'' ⊗ χ)(F_y)` are
the `z̄`, and `τ ⊕ (τ'' ⊗ χ)` is real.

## Main results

* `Stacks.EtaleCohomology.contragredient_characterTwist`,
  `Stacks.ArtinSchreier.artinSchreierCharacter_inv`.
* `Stacks.EtaleCohomology.charpoly_laumonFourierFamily_eq_fieldExtension`.
* `Stacks.EtaleCohomology.laumonFourierFamilyConjugateWildInput_of_inputs`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **The contragredient of a twist is the twist of the contragredient by the inverse
character.** -/
public theorem contragredient_characterTwist {G : Type*} [Group G] {n : Type*} [Fintype n]
    [DecidableEq n] {O : Type} [CommRing O] (ρ : G →* GL n O) (χ : G →* Oˣ) :
    contragredient (characterTwist ρ χ) = characterTwist (contragredient ρ) (χ⁻¹ : G →* Oˣ) := by
  ext g : 2
  have hinv : (((characterTwist ρ χ g)⁻¹ : GL n O) : Matrix n n O) =
      ((χ g)⁻¹ : Oˣ).val • (((ρ g)⁻¹ : GL n O) : Matrix n n O) := by
    show (((ρ g * Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom (χ g))⁻¹ :
      GL n O) : Matrix n n O) = _
    rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  rw [contragredient_val, characterTwist_val, contragredient_val, hinv, Matrix.transpose_smul,
    MonoidHom.inv_apply]

/-- **The characteristic polynomial of `c • A` at `c X`** is `c ^ n` times that of `A`:
`det(c X - c A) = c ^ n det(X - A)`. -/
public theorem charpoly_smul_comp_C_mul_X {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (c : R) (A : Matrix n n R) :
    (c • A).charpoly.comp (Polynomial.C c * Polynomial.X) =
      Polynomial.C (c ^ Fintype.card n) * A.charpoly := by
  have hmat : (Polynomial.compRingHom (Polynomial.C c * Polynomial.X)).mapMatrix
      (charmatrix (c • A)) = Polynomial.C c • charmatrix A := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, charmatrix_apply,
      charmatrix_apply, Polynomial.coe_compRingHom_apply]
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal_apply_eq, Polynomial.sub_comp, mul_sub, Matrix.smul_apply]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.smul_apply]
  rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det, hmat, Matrix.det_smul,
    ← Matrix.charpoly, ← Polynomial.C_pow]

/-- **The roots of the characteristic polynomial of `c • A`** are `c` times those of `A`, with
multiplicity, for `c ≠ 0` in a field. -/
public theorem roots_charpoly_smul {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    {c : K} (hc : c ≠ 0) (A : Matrix n n K) :
    (c • A).charpoly.roots = A.charpoly.roots.map (c * ·) := by
  have h := congrArg Polynomial.roots (charpoly_smul_comp_C_mul_X c A)
  rw [Polynomial.roots_C_mul _ (pow_ne_zero _ hc),
    show Polynomial.C c * Polynomial.X = Polynomial.C c * Polynomial.X + Polynomial.C 0 by simp,
    Polynomial.roots_comp_C_mul_X_add_C _ _ _ (IsUnit.mk0 c hc)] at h
  rw [← h, Multiset.map_map]
  conv_lhs => rw [← Multiset.map_id (c • A).charpoly.roots]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp [Ring.inverse_eq_inv', hc]

/-- **The roots of the characteristic polynomial of `c • M` along `ι`** are `ι c` times those of
`M`, with multiplicity. -/
public theorem roots_charpoly_map_smul {E : Type*} [Field E] (ι : E →+* ℂ) {n : Type*}
    [Fintype n] [DecidableEq n] {c : E} (hc : c ≠ 0) (M : Matrix n n E) :
    ((c • M).charpoly.map ι).roots = (M.charpoly.map ι).roots.map (ι c * ·) := by
  have hmap : (c • M).map ι = ι c • M.map ι := by
    ext i j
    simp
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, hmap,
    roots_charpoly_smul ((map_ne_zero ι).2 hc)]

/-- **The roots of the characteristic polynomial of an invertible matrix are nonzero.** -/
public theorem ne_zero_of_mem_roots_charpoly_map {E : Type*} [Field E] (ι : E →+* ℂ) {n : Type*}
    [Fintype n] [DecidableEq n] (M : GL n E) {z : ℂ}
    (hz : z ∈ ((M : Matrix n n E).charpoly.map ι).roots) : z ≠ 0 := by
  rintro rfl
  have hroot := (Polynomial.mem_roots (Polynomial.map_monic_ne_zero
    (Matrix.charpoly_monic (M : Matrix n n E)))).1 hz
  rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
    map_eq_zero] at hroot
  have hdet := Matrix.det_eq_sign_charpoly_coeff (M : Matrix n n E)
  rw [hroot, mul_zero] at hdet
  exact (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit |>.ne_zero hdet

end Stacks.EtaleCohomology

namespace Stacks.ArtinSchreier

/-- **The Artin–Schreier character of `ψ⁻¹` is the inverse of that of `ψ`.** -/
public theorem artinSchreierCharacter_inv (k : Type u) [Field k] [Fintype k] (A : Type u)
    [CommRing A] [Algebra k A] (g : A) [ConnectedSpace (Spec (.of A))] {O : Type} [Field O]
    (ψ : AddChar k O) (x : GeometricPoint (Spec (.of A)))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k A g)) :
    artinSchreierCharacter k A g ψ⁻¹ x p₀ = (artinSchreierCharacter k A g ψ x p₀)⁻¹ := by
  ext γ
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, artinSchreierCharacter_apply,
    artinSchreierCharacter_apply, AddChar.inv_apply']

end Stacks.ArtinSchreier

namespace Stacks.EtaleCohomology

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

omit [Fintype k] in
/-- **The Frobenius of the Fourier family at a closed point `y` of `V'` is that of its fibre
over `κ(y)`**: for `τ` attached to the lisse family `G_V` (the data of
`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`) and every choice of the data of the
Fourier fibre over `κ(y)`, the characteristic polynomial of `τ(F_y)` is that of the Frobenius of
`κ(y)` on `H¹_c(𝔸¹_κ̄, ℱ_σ ⊗ L_ψ''(a xⁿ + t(y) x) ⊗ ℚ_ℓ)`: the stalk Frobenius of `G_V` at `y`
(`Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_eq_restrictScalarsRep_family`), `E`-linear
proper base change (`Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput`) and
the identification of the fibre (`Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtension`). -/
public theorem charpoly_laumonFourierFamily_eq_fieldExtension
    (hext : LaumonFourierFamilyFieldExtension B U ℓ k e x E b σ ψ n) [FiniteDimensional ℚ_[ℓ] E]
    (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (pz : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] [ConnectedSpace V'.1]
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
    (fV : V'.1 ⟶ Spec (.of k')) [LocallyOfFiniteType fV]
    (hjV' : IsOpenImmersion (B.inclusion.map jV'))
    (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV'))
    (xV : GeometricPoint V'.1) {r : ℕ}
    (ρ : EtaleFundamentalGroup V'.1 xV →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (φ : (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b
      (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁ jU g'
        jg').toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V' xV ρ hρ)
    (ψ₀ : LAdicSheaf.representationSheaf B V' xV ρ hρ ⟶ (laumonFourierRestrictedHigherDirectImage
      k' B hS ℓ b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁ jU g'
        jg').toLAdicSheaf) (N : ℕ)
    (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _) {mτ : ℕ}
    (τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) E)
    (P : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Q : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ])
    (hPQ : P * Q = 1)
    (hα : ∀ e' : E, Q * isogenyCoefficientAlgHom B V' xV (laumonFourierRestrictedHigherDirectImage
      k' B hS ℓ b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁ jU g'
        jg') ρ hρ φ ψ₀ N E hφψ hψφ (algebraMap_conjIntegralSubring_algebraMap _ _) e' * P =
          restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e'))
    (hτ : ∀ g : EtaleFundamentalGroup V'.1 xV,
      haveI := compactSpace_etaleFundamentalGroup V'.1 xV
      Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val)
    (hQP : Q * P = 1) (y : closedPoints V'.1) [Fintype (V'.1.residueField y.1)] (pv nv : ℕ)
    [Fact pv.Prime] [CharP (V'.1.residueField y.1) pv]
    (hcardv : Fintype.card (V'.1.residueField y.1) = pv ^ nv) :
    letI := laumonPointAlgebra jV' y.1 k
    ∀ (hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (V'.1.residueField y.1)))))
    [IsNoetherian (Spec (.of (Polynomial (V'.1.residueField y.1))))]
    [ConnectedSpace (Spec (.of (Polynomial (V'.1.residueField y.1))))]
    (x' : GeometricPoint (Spec (.of (Polynomial (V'.1.residueField y.1)))))
    (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
      (algebraMap k (V'.1.residueField y.1)))) ≫ inv e) = x)
    (p₀ : (finiteEtaleFiberFunctor x').obj
        (Stacks.ArtinSchreier.cover (V'.1.residueField y.1) (Polynomial (V'.1.residueField y.1))
          (Polynomial.C (laumonPointRingHom jV' y.1 (Polynomial.C a)) * Polynomial.X ^ n +
            Polynomial.C (laumonPointRingHom jV' y.1 Polynomial.X) * Polynomial.X)))
      (τf : EtaleFundamentalGroup (Spec (.of (Polynomial (V'.1.residueField y.1)))) x' →*
        GL (Fin m) E)
      (_ : τf = characterTwist
        (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k (V'.1.residueField y.1)))) ≫ inv e) x').toMonoidHom))
        (Stacks.ArtinSchreier.artinSchreierCharacter (V'.1.residueField y.1)
          (Polynomial (V'.1.residueField y.1))
          (Polynomial.C (laumonPointRingHom jV' y.1 (Polynomial.C a)) * Polynomial.X ^ n +
            Polynomial.C (laumonPointRingHom jV' y.1 Polynomial.X) * Polynomial.X)
          (ψ.compAddMonoidHom (Algebra.trace k (V'.1.residueField y.1)).toAddMonoidHom) x' p₀))
      (hτf : Continuous (restrictScalarsRep b τf))
      [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
        (Polynomial (V'.1.residueField y.1)))))]
      [QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
        (Polynomial (V'.1.residueField y.1)))))]
      [IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
        (Polynomial (V'.1.residueField y.1)))))]
      (j' : CompactificationOf (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (V'.1.residueField y.1) (Polynomial (V'.1.residueField y.1)))))))
      (kbar' : Type u) [Field kbar'] [Algebra (V'.1.residueField y.1) kbar']
      [IsAlgClosure (V'.1.residueField y.1) kbar']
      [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') ℓ
        (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
          (Polynomial (V'.1.residueField y.1))))) j' kbar'
        (LAdicSheaf.representationSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX')
          x' (restrictScalarsRep b τf) hτf) 1)],
      letI := (restrictScalarsRepCoefficientSheaf B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') x' b τf
          hτf).rationalCohomologyModule
          (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
            (Polynomial (V'.1.residueField y.1))))) j' kbar' 1 E
      haveI := (restrictScalarsRepCoefficientSheaf B
        (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') x' b τf
          hτf).rationalCohomologyModule_isScalarTower
        (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
          (Polynomial (V'.1.residueField y.1))))) j' kbar' 1 E
          (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
            (Polynomial (V'.1.residueField y.1))))) j' kbar'
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') x' b τf
              hτf).toLAdicSheaf 1) := hV
      haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') ℓ
          (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
            (Polynomial (V'.1.residueField y.1))))) j' kbar'
          (restrictScalarsRepCoefficientSheaf B
            (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') x' b τf
              hτf).toLAdicSheaf 1) :=
        Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      (τ (geometricFrobeniusFamily fV xV y)).val.charpoly =
        (LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B
          (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') x' b τf
            hτf).rationalGeometricCompactlySupportedFrobenius
          (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
            (Polynomial (V'.1.residueField y.1))))) j' kbar' 1 E pv nv hcardv)) := by
  intro hX' _ _ x' hx' p₀ τf hτfe hτf _ _ _ j' kbar' _ _ _ hV
  subst hτfe
  have ha := charpoly_rationalStalkFrobenius_eq_restrictScalarsRep_family B V' xV _ ρ hρ φ ψ₀ N
    hφψ hψφ E (algebraMap_conjIntegralSubring_algebraMap _ _) b fV τ P Q hPQ hα hτ hQP y
  have hfinS := finite_rationalStalkLeft_of_isogeny B V' xV _ ρ hρ φ ψ₀ N hφψ hψφ
    (geometricPointAt V'.1 y.1)
  refine coefficientHigherDirectImageStalkLinearInput B ℓ k' U' V' g' jg' fV y
    (AlgebraicClosure (V'.1.residueField y.1)) pv nv hcardv _ ?_
  intro Y _ i fY _ _ _ hpbY jY hY
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  obtain ⟨hfinY, heqb⟩ := hY (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (laumonFourierFamilySheaf k' B hS b (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom)
      n a z pz _ hσ₁)) 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have := hfinY
  have heqc := hext k' a hS hL z hz pz hσ₁ V' U' jV' jU g' hjV' hpb y.1 Y i fY hpbY jY
    (AlgebraicClosure (V'.1.residueField y.1)) pv nv hcardv hX' x' hx' p₀ hτf j' kbar'
  exact ha.symm.trans (heqb.trans heqc)

end Family

/-- **A partner of the Fourier family real along `ι'` in the totally wild range**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, proof of Theorem 6.4), from the identification of the fibres of the family over every
closed point of the `t`-line (`Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtensionInput`;
the vanishing of `H²_c` on the fibres is `Stacks.EtaleCohomology.laumonFibreTopVanishingInput`,
the purity of the fibres `Stacks.EtaleCohomology.laumonFibreTwistPurityInput`): the partner is the
representation of the Fourier family of `(σ^∨, ψ⁻¹)` twisted by the unramified character with
`F_y ↦ #k' ^ (β deg y)`. -/
public theorem laumonFourierFamilyConjugateWildInput_of_inputs
    (hext : LaumonFourierFamilyFieldExtensionInput.{u}) :
    LaumonFourierFamilyConjugateWildInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hst hζ ι' β _ hpure ψ hψ
  obtain ⟨N, hN⟩ := laumonFibreTopVanishingInput B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K
    hirr hζ ι' β hpure ψ hψ
  refine ⟨N, fun n₀ hn₀ hpn₀ => ?_⟩
  intro k' _ _ _ a ha hS hL z hz pz hσ₁ hσ₂ V' U' _ _ _ jV' jU g' _ _ _ jg' fV _ hjV' hfV hpb hlis₂
    xV r ρ hρ φ ψ₀ N' hφψ hψφ mτ τ P Q hPQ hα hτ hQP
  classical
  have : ∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := fun n T =>
    AlgebraicGeometry.hasWeakSheafify_smallEtale_of_scheme B _ T
  have hk'p : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  obtain ⟨n', -, hcard'⟩ := FiniteField.card k' p
  -- the representation `τ₂` of the dual family
  obtain ⟨r₂, ρ₂, hρ₂, φ₂, ψ₂, N₂, hφψ₂, hψφ₂, m₂, τ₂, P₂, Q₂, hτ₂c, hPQ₂, hQP₂, hα₂, hτ₂⟩ :=
    exists_restrictScalarsRep_of_isLisse B V' xV _ E
      (algebraMap_conjIntegralSubring_algebraMap _ _) b hlis₂
  -- the unramified character `χ` with `χ(F_y) = #k' ^ (β deg y)`
  have hpu : IsUnit (p : ℤ_[ℓ]) := PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
    ((Nat.coprime_primes (Fact.out : ℓ.Prime) (Fact.out : p.Prime)).2 hℓp))
  obtain ⟨χ, hχc, -, hχF⟩ := exists_unramifiedCharacter fV xV ℓ (hpu.unit ^ ((n' : ℤ) * β))
  refine ⟨m₂, characterTwist τ₂ (padicUnitsCharacter χ),
    continuous_restrictScalarsRep_characterTwist_padicUnitsCharacter b τ₂ hτ₂c χ hχc,
    fun y m' => ?_⟩
  -- the closed point `y` and its residue field `κ(y)`
  have : Finite (V'.1.residueField y.1) := finite_residueField fV y.1 y.2
  let : Fintype (V'.1.residueField y.1) := Fintype.ofFinite _
  let := laumonPointAlgebra jV' y.1 k
  have hinj : Function.Injective ((laumonPointRingHom jV' y.1).comp Polynomial.C) :=
    RingHom.injective _
  have : CharP (V'.1.residueField y.1) p := charP_of_injective_ringHom hinj p
  have hcardv : Fintype.card (V'.1.residueField y.1) = p ^ ((n' : ℕ) * residueDegree fV y.1) := by
    rw [← Nat.card_eq_fintype_card, natCard_residueField_eq_pow_residueDegree fV y.1, hcard',
      pow_mul]
  -- the fibre data over `κ(y)`
  have : Algebra.IsAlgebraic k (V'.1.residueField y.1) := inferInstance
  obtain ⟨x', hx'⟩ := exists_geometricPoint_polynomial_map_eq e (V'.1.residueField y.1) x
  obtain ⟨p₀⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiberFunctor_cover
    (V'.1.residueField y.1)
    (Polynomial.C (laumonPointRingHom jV' y.1 (Polynomial.C a)) * Polynomial.X ^ n₀ +
      Polynomial.C (laumonPointRingHom jV' y.1 Polynomial.X) * Polynomial.X) x'
  have hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (V'.1.residueField y.1)))) :=
    (schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).2 (Polynomial.cardinalMk_le_max.trans_lt
      (max_lt ((Cardinal.lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff) B.aleph0_lt_cutoff))
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
      (Polynomial (V'.1.residueField y.1))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have := Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_polynomial
    (V'.1.residueField y.1)
  have := Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_polynomial
    (V'.1.residueField y.1) (AlgebraicClosure (V'.1.residueField y.1))
  have hτ₀ := continuous_restrictScalarsRep_comp_etaleFundamentalGroupMap
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k (V'.1.residueField y.1)))) ≫
      inv e) x' hx' b σ hσ
  have hτf := continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter
    (V'.1.residueField y.1) (Polynomial (V'.1.residueField y.1))
    (Polynomial.C (laumonPointRingHom jV' y.1 (Polynomial.C a)) * Polynomial.X ^ n₀ +
      Polynomial.C (laumonPointRingHom jV' y.1 Polynomial.X) * Polynomial.X) b
    (ψ.compAddMonoidHom (Algebra.trace k (V'.1.residueField y.1)).toAddMonoidHom) x' p₀ _ hτ₀
  have hfin := LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ
  have hτc := continuous_restrictScalarsRep_contragredient b hτf
  have hV := fun (τf : EtaleFundamentalGroup (Spec (.of (Polynomial (V'.1.residueField y.1))))
      x' →* GL (Fin m) E) (h : Continuous (restrictScalarsRep b τf)) => (hfin
    (V'.1.residueField y.1) (AlgebraicClosure (V'.1.residueField y.1)) p
    ((n' : ℕ) * residueDegree fV y.1) hcardv hℓp
    (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX')
    (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
      (Polynomial (V'.1.residueField y.1)))))
    (affineLineProjectiveCompactification (V'.1.residueField y.1))
    (LAdicSheaf.representationSheaf B
      (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') x'
      (restrictScalarsRep b τf) h) 1).1
  -- the Frobenius of `τ` and of `τ₂` at `y` are those of the fibres over `κ(y)`
  have h1 := charpoly_laumonFourierFamily_eq_fieldExtension B U ℓ k e x E b σ ψ n₀
    (hext B U ℓ k e x E b σ ψ n₀) k' a hS hL z hz pz hσ₁ V' U' jV' jU g' jg' fV hjV' hpb xV ρ hρ
    φ ψ₀ N' hφψ hψφ τ P Q hPQ hα hτ hQP y p ((n' : ℕ) * residueDegree fV y.1) hcardv hX' x' hx'
    p₀ _ rfl hτf (affineLineProjectiveCompactification (V'.1.residueField y.1))
    (AlgebraicClosure (V'.1.residueField y.1)) (hV := hV _ hτf)
  have hψinv : (ψ⁻¹).compAddMonoidHom (Algebra.trace k (V'.1.residueField y.1)).toAddMonoidHom =
      (ψ.compAddMonoidHom (Algebra.trace k (V'.1.residueField y.1)).toAddMonoidHom)⁻¹ := by
    ext t
    simp
  have h2 := charpoly_laumonFourierFamily_eq_fieldExtension B U ℓ k e x E b (contragredient σ) ψ⁻¹
    n₀ (hext B U ℓ k e x E b (contragredient σ) ψ⁻¹ n₀) k' a hS hL z hz pz hσ₂ V' U' jV' jU g' jg'
    fV hjV' hpb xV ρ₂ hρ₂ φ₂ ψ₂ N₂ hφψ₂ hψφ₂ τ₂ P₂ Q₂ hPQ₂ hα₂ hτ₂ hQP₂ y p
    ((n' : ℕ) * residueDegree fV y.1) hcardv hX' x' hx' p₀ (contragredient _)
    (by
      -- the fibre of the dual family is the contragredient of the fibre
      rw [contragredient_characterTwist, ← Stacks.ArtinSchreier.artinSchreierCharacter_inv,
        ← hψinv]
      rfl)
    hτc
    (affineLineProjectiveCompactification (V'.1.residueField y.1))
    (AlgebraicClosure (V'.1.residueField y.1)) (hV := hV _ hτc)
  -- the trace formula on `𝔸¹_{κ(y)}`
  have hac : MvPolynomial.eval ![laumonPointRingHom jV' y.1 (Polynomial.C a),
      laumonPointRingHom jV' y.1 Polynomial.X]
      (MvPolynomial.map (algebraMap k (V'.1.residueField y.1)) (MvPolynomial.X 0)) ≠ 0 := by
    rw [MvPolynomial.map_X, MvPolynomial.eval_X, Matrix.cons_val_zero]
    exact (map_ne_zero_iff _ hinj).2 ha
  have hpur := laumonFibreTwistPurityInput B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr
    hζ ι' β hpure ψ hψ n₀ (V'.1.residueField y.1) hX' x' hx'
    (laumonPointRingHom jV' y.1 (Polynomial.C a)) (laumonPointRingHom jV' y.1 Polynomial.X) p₀ hτf
    (affineLineProjectiveCompactification (V'.1.residueField y.1))
    (AlgebraicClosure (V'.1.residueField y.1)) p ((n' : ℕ) * residueDegree fV y.1) hcardv
  have hv := hN n₀ hn₀ hpn₀ (V'.1.residueField y.1) hX' x' hx'
    (laumonPointRingHom jV' y.1 (Polynomial.C a)) (laumonPointRingHom jV' y.1 Polynomial.X) hac p₀
    hτf (affineLineProjectiveCompactification (V'.1.residueField y.1))
    (AlgebraicClosure (V'.1.residueField y.1)) p ((n' : ℕ) * residueDegree fV y.1) hcardv
  have hm := roots_filter_ne_zero_contragredient_eq_map_conj_of_curve B
    (Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField y.1)) B hX') ℓ
    (V'.1.residueField y.1) (Spec.map (CommRingCat.ofHom (algebraMap (V'.1.residueField y.1)
      (Polynomial (V'.1.residueField y.1)))))
    (affineLineProjectiveCompactification (V'.1.residueField y.1))
    (AlgebraicClosure (V'.1.residueField y.1)) p ((n' : ℕ) * residueDegree fV y.1) hcardv hℓp x' E
    b _ hτf ι' β hpur hv.1 hv.2 (hV := hV _ hτf) (hV' := hV _ hτc)
  have hR : (((τ₂ (geometricFrobeniusFamily fV xV y)).val.charpoly.map ι').roots.filter
      (· ≠ 0)) = ((((τ (geometricFrobeniusFamily fV xV y)).val.charpoly.map ι').roots.filter
        (· ≠ 0)).map fun z => (((p ^ ((n' : ℕ) * residueDegree fV y.1) : ℕ) : ℂ) ^ β)⁻¹ *
          starRingEnd ℂ z) := by
    refine (congrArg (fun P : Polynomial E => (P.map ι').roots.filter (· ≠ 0)) h2).trans ?_
    refine hm.trans ?_
    exact congrArg (fun P : Polynomial E => ((P.map ι').roots.filter (· ≠ 0)).map
      fun z => (((p ^ ((n' : ℕ) * residueDegree fV y.1) : ℕ) : ℂ) ^ β)⁻¹ * starRingEnd ℂ z)
      h1.symm
  rw [Multiset.filter_eq_self.2 fun z hz => ne_zero_of_mem_roots_charpoly_map ι' _ hz,
    Multiset.filter_eq_self.2 fun z hz => ne_zero_of_mem_roots_charpoly_map ι' _ hz] at hR
  -- the twist by `χ` multiplies the roots of `τ₂(F_y)` by `q_y ^ β`
  have hc : ι' ((padicUnitsCharacter χ (geometricFrobeniusFamily fV xV y) : Eˣ) : E) =
      ((p ^ ((n' : ℕ) * residueDegree fV y.1) : ℕ) : ℂ) ^ β := by
    rw [padicUnitsCharacter_apply, hχF y]
    have hval : (((hpu.unit ^ ((n' : ℤ) * β)) ^ residueDegree fV y.1 : ℤ_[ℓ]ˣ) : ℚ_[ℓ]) =
        ((p : ℚ_[ℓ]) ^ ((n' : ℤ) * β)) ^ residueDegree fV y.1 := by
      have h := Units.coe_map (PadicInt.Coe.ringHom (p := ℓ)).toMonoidHom
        ((hpu.unit ^ ((n' : ℤ) * β)) ^ residueDegree fV y.1)
      simp only [map_pow, map_zpow, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
        Units.coe_map, IsUnit.unit_spec] at h
      exact h.symm
    rw [hval]
    simp only [map_pow, map_zpow₀, map_natCast]
    rw [← zpow_natCast, ← _root_.zpow_mul, Nat.cast_pow, ← zpow_natCast (p : ℂ),
      ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  have hroots : (((characterTwist τ₂ (padicUnitsCharacter χ)
      (geometricFrobeniusFamily fV xV y)).val.charpoly.map ι').roots) =
      ((τ (geometricFrobeniusFamily fV xV y)).val.charpoly.map ι').roots.map (starRingEnd ℂ) := by
    rw [characterTwist_val, roots_charpoly_map_smul ι' (Units.ne_zero _), hR, Multiset.map_map]
    refine Multiset.map_congr rfl fun w _ => ?_
    have hq0 : (((p ^ ((n' : ℕ) * residueDegree fV y.1) : ℕ) : ℂ) ^ β) ≠ 0 :=
      zpow_ne_zero _ (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
    simp only [Function.comp_apply]
    rw [hc, mul_inv_cancel_left₀ hq0]
  exact coeff_mul_mem_range_ofReal_of_roots_eq_map_conj ι' (Matrix.charpoly_monic _)
    (Matrix.charpoly_monic _) hroots m'

end Stacks.EtaleCohomology

end
