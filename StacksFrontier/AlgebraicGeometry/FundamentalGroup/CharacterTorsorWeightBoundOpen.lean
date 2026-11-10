module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.CharacterTorsorWeightBound
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.OpenCurveKummerEigenBound
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilPairingFrobenius

/-!
# Frobenius-invariant characters of the geometric fundamental group of a smooth curve

Let `X` be a smooth curve over a finite field `k`, proper or not, `x` a geometric point,
`Γ = π₁(X, x)`, `H = π₁(X_k̄, x)` the kernel of `Γ → π₁(Spec k)`, `φ ∈ Γ` a lift of the inverse of
Frobenius, and `ℓ ≠ char k` a prime. For every open normal subgroup `U` of `Γ`, the locally
constant characters `χ : H ∩ U → ℤ/ℓᵉ` invariant under conjugation by `φ ^ [Γ : U]` are bounded in
number independently of `e`. This is the geometric input of Weil II 1.3.4 in the proof of
Tag 03VH, for every smooth curve.

The proof follows `AlgebraicGeometry.exists_forall_encard_invariant_zmod_le_of_isProper`, with the
cover `Y` of `X` with fibre `Γ ⧸ V` now an open subcurve of a smooth proper geometrically
irreducible curve `Ȳ` over a finite field `k₀`
(`AlgebraicGeometry.exists_compactification_constantField_of_finiteEtale`). The characters inject
(`AlgebraicGeometry.CharacterTorsorData.eq_of_baseTorsor_eq`) into `H¹(Y_K, μ_{ℓᵉ})`, `K = k̄₀`,
where they are eigenvectors of the twist by a power `Fᵐ` of Frobenius fixing the points of
`Ȳ_K ∖ Y_K` (`Stacks.Kummer.exists_galoisTwist_frobenius_pow_fixed`), with eigenvalue `#k₀ᵐ`
(`AlgebraicGeometry.CharacterTorsorData.rootsOfUnityPullbackMap_baseTorsor`). These eigenvectors
are bounded independently of `e` (`Stacks.Kummer.exists_forall_encard_eigen_h1RootsOfUnity_le`).

The Weil pairing on `Pic(Ȳ_K)[ℓⁿ]` is `Stacks.Picard.exists_weilPairing_frobeniusPicardHom`; the
statement has no further hypotheses.

## Main results

* `AlgebraicGeometry.exists_forall_encard_invariant_zmod_le`: the bound, for every smooth curve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  Stacks.Cohomology.Torsors Stacks.EtaleCohomology Stacks.Kummer

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Fintype k] (p N : ℕ) [Fact p.Prime] [CharP k p]
  (hq : Fintype.card k = p ^ N) {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
  [Smooth f] [IsCurve k f] (x : GeometricPoint X) (φ : EtaleFundamentalGroup X x)
  (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p N hq (x.map f))⁻¹)
  {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)

/-- The power `Fᵐ` of the Frobenius of `k̄` acts as `c ↦ c ^ (qᵐ)`. -/
theorem frobeniusAlgEquivOfAlgebraic_pow_apply (K₀ K : Type u) [Field K₀] [Fintype K₀] [Field K]
    [Algebra K₀ K] [Algebra.IsAlgebraic K₀ K] (m : ℕ) (c : K) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic K₀ K ^ m) c = c ^ (Fintype.card K₀ ^ m) := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- An open subscheme of a proper scheme over a field `k₀`, which is a curve over a subfield `k`
of `k₀`, is a curve over `k₀`. -/
theorem isCurve_comp_of_isOpenImmersion {k K₀ : Type u} [Field k] [Field K₀] {Y Ybar : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsCurve k g] (j : Y ⟶ Ybar) [IsOpenImmersion j]
    (r : Ybar ⟶ Spec (.of K₀)) [IsProper r] : IsCurve K₀ (j ≫ r) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiCompact (j ≫ r) := quasiCompact_of_compactSpace (j ≫ r)
  have : IsVariety K₀ (j ≫ r) := {}
  exact { topologicalKrullDim_eq_one := IsCurve.topologicalKrullDim_eq_one (k := k) (f := g) }

/-- The underlying space of a curve over a field is compact. -/
theorem compactSpace_of_isCurve {K₀ : Type u} [Field K₀] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K₀)) [IsCurve K₀ g] : CompactSpace Y :=
  QuasiCompact.compactSpace_of_compactSpace g

/-- The underlying space of a curve over a field is quasi-separated. -/
theorem quasiSeparatedSpace_of_isCurve {K₀ : Type u} [Field K₀] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K₀)) [IsCurve K₀ g] : QuasiSeparatedSpace Y :=
  quasiSeparatedSpace_of_quasiSeparated g

include hφ hℓ hℓp in
/-- **Frobenius-invariant characters of the geometric fundamental group of a smooth curve are
bounded** (the geometric input of Weil II 1.3.4). For a smooth curve `X` over a finite field `k`,
proper or not, `H = π₁(X_k̄)`, `φ` a lift of the inverse Frobenius and `ℓ ≠ char k` prime, for
every open normal `U ⊆ π₁(X, x)` the locally constant characters `H ∩ U → ℤ/ℓᵉ` invariant under
conjugation by `φ ^ [π₁ : U]` are at most `C` in number, `C` independent of `e`. -/
theorem exists_forall_encard_invariant_zmod_le :
    ∀ U : Subgroup (EtaleFundamentalGroup X x), U.Normal →
      IsOpen (U : Set (EtaleFundamentalGroup X x)) →
      ∃ C : ℕ, ∀ e : ℕ,
        {χ : ↥((etaleFundamentalGroupMap f x).toMonoidHom.ker ⊓ U) → ZMod (ℓ ^ e) |
          (∀ a b, χ (a * b) = χ a + χ b) ∧ IsLocallyConstant χ ∧
          ∀ a b : ↥((etaleFundamentalGroupMap f x).toMonoidHom.ker ⊓ U),
            (b : EtaleFundamentalGroup X x) = φ ^ U.index * a * (φ ^ U.index)⁻¹ →
              χ b = χ a}.encard ≤ C := by
  classical
  intro U hU hUo
  have := hU
  have : ∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y) := finite_finiteEtaleFiber x
  set H := (etaleFundamentalGroupMap f x).toMonoidHom.ker
  have hH := isClosed_ker_etaleFundamentalGroupMap f x
  have hdense := dense_ker_sup_zpowers_of_etaleFundamentalGroupMap_eq_inv p N hq f x φ hφ
  have hO := exists_isOpen_ker_le_zpow_mem_dvd p N hq f x φ hφ
  have hext := fun e : ℕ => Stacks.LAdic.isOpen_and_exists_extension (A := ZMod (ℓ ^ e)) hH
    hdense hO hUo
  have hVo := (hext 0).1
  obtain ⟨Y, eY, heY⟩ := exists_quotientCover hVo
  have := connectedSpace_of_quotient_equiv Y eY heY
  have hYc := isCurve_finiteEtale_comp k f Y
  obtain ⟨K₀, iF, iA, iM, Ybar, j, iJ, r, hr, iP, iS, iG, iC, -⟩ :=
    exists_compactification_constantField_of_finiteEtale k f Y
  have : Finite K₀ := Module.finite_of_finite k
  let : Fintype K₀ := Fintype.ofFinite K₀
  have : CharP K₀ p := charP_of_injective_algebraMap (algebraMap k K₀).injective p
  have : IsCurve K₀ (j ≫ r) := isCurve_comp_of_isOpenImmersion (Y.hom ≫ f) j r
  have : CompactSpace Y.left := compactSpace_of_isCurve (j ≫ r)
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_isCurve (j ≫ r)
  -- `ℓ` is invertible in `k₀`, and `#k₀` is prime to `ℓ`
  have hℓ0 : (ℓ : K₀) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K₀ p]
    intro hdvd
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).1 hdvd).symm
  have hℓK₀ : IsUnit (ℓ : K₀) := hℓ0.isUnit
  have : NeZero (ℓ : K₀) := ⟨hℓ0⟩
  have : IsProper (Over.mk r).hom := iP
  have : Smooth (Over.mk r).hom := iS
  have : GeometricallyIrreducible (Over.mk r).hom := iG
  have : IsCurve K₀ (Over.mk r).hom := iC
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Fintype.card K₀ = p ^ d := by
    obtain ⟨d, hp, hd⟩ := FiniteField.card K₀ p
    exact ⟨d, hd⟩
  have : ∀ e : ℕ, NeZero (ℓ ^ e) := fun e => ⟨pow_ne_zero _ hℓ.ne_zero⟩
  -- a power of Frobenius fixing the points at infinity
  obtain ⟨m, hm, hfixm⟩ := exists_galoisTwist_frobenius_pow_fixed r j
  have hcop : ∀ e : ℕ, Nat.Coprime (Fintype.card K₀ ^ m) (ℓ ^ e) := fun e => by
    rw [hd, ← pow_mul]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : p.Prime) hℓ).2 (Ne.symm hℓp))
  -- the geometric base `Y_K`
  set K := AlgebraicClosure K₀
  set r' := j ≫ r
  have hr' : r' ≫ Spec.map (CommRingCat.ofHom (algebraMap k K₀)) = Y.hom ≫ f := hr
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (pullback r' (spectrumMap K₀ K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse _
  let : HasExt.{u + 1}
      (Sheaf (pullback r' (spectrumMap K₀ K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  obtain ⟨C, hC⟩ := exists_forall_encard_eigen_h1RootsOfUnity_le r j hℓ hℓK₀ m hm hfixm
  choose ζ hζ using fun e : ℕ => HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (ℓ ^ e)
  -- the sets of invariant characters
  set S : ∀ e : ℕ, Set (↥(H ⊓ U) → ZMod (ℓ ^ e)) := fun e =>
    {χ | (∀ a b, χ (a * b) = χ a + χ b) ∧ IsLocallyConstant χ ∧
      ∀ a b : ↥(H ⊓ U), (b : EtaleFundamentalGroup X x) = φ ^ U.index * a * (φ ^ U.index)⁻¹ →
        χ b = χ a}
  -- their extensions to `V`, and the classes of the torsors of the extensions
  have hcls : ∀ (e : ℕ) (χ : ↥(H ⊓ U) → ZMod (ℓ ^ e)),
      ∃ c : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} (pullback r' (spectrumMap K₀ K)) (ℓ ^ e)) 1,
        χ ∈ S e → ∃ (χ' : ↥(H ⊓ U ⊔ (Subgroup.zpowers (φ ^ U.index)).topologicalClosure) →
            ZMod (ℓ ^ e)) (hadd : ∀ a b, χ' (a * b) = χ' a + χ' b)
          (D : CharacterTorsorData x χ' hadd Y eY),
          (∀ n : ↥(H ⊓ U), χ' ⟨n, Subgroup.mem_sup_left n.2⟩ = χ n) ∧
          c = torsorIsoClassesEquivH1 _ (Quotient.mk _ (D.baseTorsor (hζ e)
            (pullback.snd r' (spectrumMap K₀ K)) (pullback.fst r' (spectrumMap K₀ K)))) := by
    intro e χ
    by_cases hχ : χ ∈ S e
    · obtain ⟨χ', hadd', hχc', hres, -⟩ := (hext e).2 χ hχ.1 hχ.2.1 hχ.2.2
      obtain ⟨D⟩ := nonempty_characterTorsorData (χ := χ') (hadd := hadd') hVo hχc' Y eY heY
      exact ⟨_, fun _ => ⟨χ', hadd', D, hres, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hχ⟩
  choose c hc using hcls
  have hinj : ∀ e, Set.InjOn (c e) (S e) := by
    intro e χ₁ h₁ χ₂ h₂ h12
    obtain ⟨χ₁', hadd₁, D₁, hres₁, hc₁⟩ := hc e χ₁ h₁
    obtain ⟨χ₂', hadd₂, D₂, hres₂, hc₂⟩ := hc e χ₂ h₂
    rw [hc₁, hc₂] at h12
    have h := (torsorIsoClassesEquivH1 _).injective h12
    funext n
    rw [← hres₁ n, ← hres₂ n]
    refine CharacterTorsorData.eq_of_baseTorsor_eq f heY r' hr' (hζ e) D₁ D₂ h _ ?_
    exact (MonoidHom.mem_ker).1 n.2.1
  have heig : ∀ e, ∀ χ ∈ S e, rootsOfUnityPullbackMap.{u, 0, u + 1}
      (Stacks.Picard.galoisTwist K₀ K (Over.mk r')
        (FiniteField.frobeniusAlgEquivOfAlgebraic K₀ K ^ m)) (ℓ ^ e) 1 (c e χ) =
      ((Fintype.card K₀ : ℤ) ^ m) • c e χ := by
    intro e χ hχ
    obtain ⟨χ', hadd', D, -, hcD⟩ := hc e χ hχ
    set m' := ((((Fintype.card K₀ ^ m : ℕ)) : ZMod (ℓ ^ e))⁻¹).val
    have hqm : ((Fintype.card K₀ ^ m * m' : ℕ) : ZMod (ℓ ^ e)) = 1 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact ZMod.coe_mul_inv_eq_one _ (hcop e)
    have hσπ := Stacks.Picard.galoisTwist_comp_fst K₀ K (Over.mk r')
      (FiniteField.frobeniusAlgEquivOfAlgebraic K₀ K ^ m)
    have hσζ : (Stacks.Picard.galoisTwist K₀ K (Over.mk r')
        (FiniteField.frobeniusAlgEquivOfAlgebraic K₀ K ^ m)).appTop.hom
          (Stacks.Kummer.baseRingMap (pullback.snd r' (spectrumMap K₀ K)) (𝟙 _) (ζ e)) =
        Stacks.Kummer.baseRingMap (pullback.snd r' (spectrumMap K₀ K)) (𝟙 _) (ζ e) ^
          (Fintype.card K₀ ^ m) := by
      refine (galoisTwist_appTop_baseRingMap K₀ K (Over.mk r') _ (ζ e)).trans ?_
      rw [frobeniusAlgEquivOfAlgebraic_pow_apply, map_pow]
      rfl
    rw [hcD, D.rootsOfUnityPullbackMap_baseTorsor (hζ e) (pullback.snd r' (spectrumMap K₀ K))
      (pullback.fst r' (spectrumMap K₀ K)) _ hσπ (Fintype.card K₀ ^ m) m' hσζ hqm]
    rw [← natCast_zsmul]
    push_cast
    rfl
  refine ⟨C, fun e => ?_⟩
  calc (S e).encard = (c e '' S e).encard := ((hinj e).encard_image).symm
    _ ≤ _ := Set.encard_le_encard ?_
    _ ≤ C := hC e
  rintro _ ⟨χ, hχ, rfl⟩
  exact heig e χ hχ

end AlgebraicGeometry
