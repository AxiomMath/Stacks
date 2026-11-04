module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.CharacterTorsorPicardEigen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteFieldFrobeniusDense
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.Picard.BaseChangeCurveTorsionFinite

/-!
# Frobenius-invariant characters of the geometric fundamental group of a proper curve

Let `X` be a smooth proper curve over a finite field `k`, `x` a geometric point, `Γ = π₁(X, x)`,
`H = π₁(X_k̄, x)` the kernel of `Γ → π₁(Spec k)`, `φ ∈ Γ` a lift of the inverse of Frobenius, and
`ℓ ≠ char k` a prime. For every open normal subgroup `U` of `Γ`, the locally constant
characters `χ : H ∩ U → ℤ/ℓᵉ` invariant under conjugation by `φ ^ [Γ : U]` are bounded in number
independently of `e`. This is the geometric input of Weil II 1.3.4 in the proof of Tag 03VH.

The proof: such a `χ` extends to a character `χ'` of the open subgroup
`V = (H ∩ U) · closure ⟨φ ^ [Γ : U]⟩` killing `φ ^ [Γ : U]`
(`Stacks.LAdic.isOpen_and_exists_extension`). Let `Y` be the cover of `X` with fibre `Γ ⧸ V`, a
smooth proper geometrically irreducible curve over its constant field `k₀`
(`AlgebraicGeometry.exists_constantField_of_finiteEtale`), and `T_χ ⟶ Y` the `ℤ/ℓᵉ`-torsor cover
of `χ'`. Over `Ȳ = Y ×_{k₀} k̄₀` the cover `T_χ` is a `μ_{ℓᵉ}`-torsor, and its class in
`H¹(Ȳ, μ_{ℓᵉ})` maps injectively to `Pic(Ȳ)[ℓᵉ]`. The map `χ ↦ [T_χ]` is injective
(`AlgebraicGeometry.CharacterTorsorData.eq_of_baseTorsor_eq`), and its values are eigenvectors
of Frobenius with eigenvalue `#k₀`
(`AlgebraicGeometry.CharacterTorsorData.frobeniusPicardHom_h1RootsOfUnityToPicard_baseTorsor`).
These eigenvectors are bounded independently of `e`
(`Stacks.Picard.exists_forall_encard_le_of_injOn`).

## Input carried as a hypothesis

* `hWeil`: the Weil pairing on `Pic(Ȳ)[ℓⁿ]` for smooth proper geometrically irreducible curves
  over finite fields, as consumed by `Stacks.Picard.exists_forall_encard_le_of_injOn`.

## Main results

* `Stacks.Kummer.injective_h1RootsOfUnityToPicard_of_isProper`: `H¹(X, μ_n) → Pic(X)` is
  injective for `X` integral and proper over an algebraically closed field, `n` invertible.
* `AlgebraicGeometry.exists_forall_encard_invariant_zmod_le_of_isProper`: the bound.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  Stacks.Cohomology.Torsors Stacks.EtaleCohomology Stacks.Kummer

universe w v u

namespace Stacks.Kummer

/-- **`H¹(X, μ_n) → Pic(X)` is injective** for `X` integral and proper over an algebraically
closed field `K` and `n` invertible in `K`: global units are `n`-th powers. -/
theorem injective_h1RootsOfUnityToPicard_of_isProper (X : Scheme.{u}) (n : ℕ)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] {K : Type u}
    [Field K] [IsAlgClosed K] (g : X ⟶ Spec (.of K)) [IsProper g] [IsIntegral X]
    (hn : IsUnit (n : K)) : Function.Injective (h1RootsOfUnityToPicard.{w, v, u} X n) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  exact (etaleH1MultiplicativeAddEquivPicard.{w, v, u} X).injective.comp
    (injective_sheafH_map_rootsOfUnityι_one X hn0 (isUnit_natCast_globalSections X n g hn)
      (surjective_sheafH_map_powMap_zero X (n := n)
        (exists_pow_eq_globalUnit X n g (Nat.pos_of_ne_zero hn0))))

end Stacks.Kummer

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Fintype k] (p N : ℕ) [Fact p.Prime] [CharP k p]
  (hq : Fintype.card k = p ^ N) {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
  [IsProper f] [Smooth f] [IsCurve k f] (x : GeometricPoint X) (φ : EtaleFundamentalGroup X x)
  (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p N hq (x.map f))⁻¹)
  {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)

include hφ hℓ hℓp in
/-- **Frobenius-invariant characters of the geometric fundamental group of a proper curve are
bounded** (the geometric input of Weil II 1.3.4). For a smooth proper curve `X` over a finite
field `k`, `H = π₁(X_k̄)`, `φ` a lift of the inverse Frobenius and `ℓ ≠ char k` prime, for every
open normal `U ⊆ π₁(X, x)` the locally constant characters `H ∩ U → ℤ/ℓᵉ` invariant under
conjugation by `φ ^ [π₁ : U]` are at most `C` in number, `C` independent of `e`. The Weil pairing
(`hWeil`) is an input. -/
theorem exists_forall_encard_invariant_zmod_le_of_isProper
    (hWeil : ∀ (K₀ : Type u) [Field K₀] [Fintype K₀] (Y : Over (Spec (.of K₀))) [IsProper Y.hom]
      [Smooth Y.hom] [GeometricallyIrreducible Y.hom] [IsCurve K₀ Y.hom], IsUnit (ℓ : K₀) →
      ∀ n : ℕ, ∃ e : Submodule.torsionBy ℤ
          (Stacks.Picard.ofScheme (SchemeOver.baseChange K₀ (AlgebraicClosure K₀) Y))
          ((ℓ : ℤ) ^ n) →+
          Submodule.torsionBy ℤ
            (Stacks.Picard.ofScheme (SchemeOver.baseChange K₀ (AlgebraicClosure K₀) Y))
            ((ℓ : ℤ) ^ n) →+ ZMod (ℓ ^ n),
        (∀ a, (∀ b, e a b = 0) → a = 0) ∧
          ∀ a b, e (Stacks.Picard.torsionByRestrict (Stacks.Picard.frobeniusPicardHom Y) _ a)
            (Stacks.Picard.torsionByRestrict (Stacks.Picard.frobeniusPicardHom Y) _ b) =
              (Fintype.card K₀ : ℤ) • e a b) :
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
  have := connectedSpace_of_quotient_equiv hVo Y eY heY
  obtain ⟨K₀, iF, iA, iM, r, hr, iP, iS, iG, iC⟩ := exists_constantField_of_finiteEtale k f Y
  have : Finite K₀ := Module.finite_of_finite k
  let : Fintype K₀ := Fintype.ofFinite K₀
  have : CharP K₀ p := charP_of_injective_algebraMap (algebraMap k K₀).injective p
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace r
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated r
  have : IsProper (Over.mk r).hom := iP
  have : Smooth (Over.mk r).hom := iS
  have : GeometricallyIrreducible (Over.mk r).hom := iG
  have : IsCurve K₀ (Over.mk r).hom := iC
  -- `ℓ` is invertible in `k₀`, and `#k₀` is prime to `ℓ`
  have hℓ0 : (ℓ : K₀) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K₀ p]
    intro hdvd
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).1 hdvd).symm
  have hℓK₀ : IsUnit (ℓ : K₀) := hℓ0.isUnit
  have : NeZero (ℓ : K₀) := ⟨hℓ0⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Fintype.card K₀ = p ^ d := by
    obtain ⟨d, hp, hd⟩ := FiniteField.card K₀ p
    exact ⟨d, hd⟩
  have hcop : ∀ e : ℕ, Nat.Coprime (Fintype.card K₀) (ℓ ^ e) := fun e => by
    rw [hd]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : p.Prime) hℓ).2 (Ne.symm hℓp))
  have : ∀ e : ℕ, NeZero (ℓ ^ e) := fun e => ⟨pow_ne_zero _ hℓ.ne_zero⟩
  -- the geometric base `Ȳ`
  set K := AlgebraicClosure K₀
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (pullback r (spectrumMap K₀ K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse _
  let : HasExt.{u + 1}
      (Sheaf (pullback r (spectrumMap K₀ K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  have : GeometricallyReduced r := geometricallyReduced_of_smooth r
  have : GeometricallyIntegral r :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible r
  have : IsIntegral (pullback r (spectrumMap K₀ K)) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd r (spectrumMap K₀ K))
  have hℓK : ∀ e : ℕ, IsUnit ((ℓ ^ e : ℕ) : K) := fun e => by
    rw [Nat.cast_pow]
    exact (by simpa using hℓK₀.map (algebraMap K₀ K) : IsUnit (ℓ : K)).pow e
  choose ζ hζ using fun e : ℕ => HasEnoughRootsOfUnity.exists_primitiveRoot K (ℓ ^ e)
  -- the sets of invariant characters
  set S : ∀ e : ℕ, Set (↥(H ⊓ U) → ZMod (ℓ ^ e)) := fun e =>
    {χ | (∀ a b, χ (a * b) = χ a + χ b) ∧ IsLocallyConstant χ ∧
      ∀ a b : ↥(H ⊓ U), (b : EtaleFundamentalGroup X x) = φ ^ U.index * a * (φ ^ U.index)⁻¹ →
        χ b = χ a}
  -- their extensions to `V`, and the classes of the torsors of the extensions
  have hcls : ∀ (e : ℕ) (χ : ↥(H ⊓ U) → ZMod (ℓ ^ e)),
      ∃ c : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} (pullback r (spectrumMap K₀ K)) (ℓ ^ e)) 1,
        χ ∈ S e → ∃ (χ' : ↥(H ⊓ U ⊔ (Subgroup.zpowers (φ ^ U.index)).topologicalClosure) →
            ZMod (ℓ ^ e)) (hadd : ∀ a b, χ' (a * b) = χ' a + χ' b)
          (D : CharacterTorsorData x χ' hadd Y eY),
          (∀ n : ↥(H ⊓ U), χ' ⟨n, Subgroup.mem_sup_left n.2⟩ = χ n) ∧
          c = torsorIsoClassesEquivH1 _ (Quotient.mk _ (D.baseTorsor (hζ e)
            (pullback.snd r (spectrumMap K₀ K)) (pullback.fst r (spectrumMap K₀ K)))) := by
    intro e χ
    by_cases hχ : χ ∈ S e
    · obtain ⟨χ', hadd', hχc', hres, -⟩ := (hext e).2 χ hχ.1 hχ.2.1 hχ.2.2
      obtain ⟨D⟩ := nonempty_characterTorsorData (χ := χ') (hadd := hadd') hVo hχc' Y eY heY
      exact ⟨_, fun _ => ⟨χ', hadd', D, hres, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hχ⟩
  choose c hc using hcls
  set Φ : ∀ e : ℕ, (↥(H ⊓ U) → ZMod (ℓ ^ e)) →
      Stacks.Picard.ofScheme (SchemeOver.baseChange K₀ K (Over.mk r)) := fun e χ =>
    h1RootsOfUnityToPicard.{u + 1, 0, u} (pullback r (spectrumMap K₀ K)) (ℓ ^ e) (c e χ)
  have hinj : ∀ e, Set.InjOn (Φ e) (S e) := by
    intro e χ₁ h₁ χ₂ h₂ h12
    obtain ⟨χ₁', hadd₁, D₁, hres₁, hc₁⟩ := hc e χ₁ h₁
    obtain ⟨χ₂', hadd₂, D₂, hres₂, hc₂⟩ := hc e χ₂ h₂
    have h12' := injective_h1RootsOfUnityToPicard_of_isProper.{u + 1, 0, u} _ (ℓ ^ e)
      (pullback.snd r (spectrumMap K₀ K)) (hℓK e) h12
    rw [hc₁, hc₂] at h12'
    have h := (torsorIsoClassesEquivH1 _).injective h12'
    funext n
    rw [← hres₁ n, ← hres₂ n]
    refine CharacterTorsorData.eq_of_baseTorsor_eq f heY r hr (hζ e) D₁ D₂ h _ ?_
    exact (MonoidHom.mem_ker).1 n.2.1
  have htor : ∀ e, ∀ χ ∈ S e, ((ℓ : ℤ) ^ e) • Φ e χ = 0 := by
    intro e χ _
    show ((ℓ : ℤ) ^ e) • h1RootsOfUnityToPicard.{u + 1, 0, u} _ (ℓ ^ e) (c e χ) = 0
    rw [← map_zsmul, show ((ℓ : ℤ) ^ e) = ((ℓ ^ e : ℕ) : ℤ) by push_cast; rfl, natCast_zsmul,
      nsmul_sheafH_rootsOfUnity_eq_zero, map_zero]
  have heig : ∀ e, ∀ χ ∈ S e, Stacks.Picard.frobeniusPicardHom (Over.mk r) (Φ e χ) =
      (Fintype.card K₀ : ℤ) • Φ e χ := by
    intro e χ hχ
    obtain ⟨χ', hadd', D, -, hcD⟩ := hc e χ hχ
    show Stacks.Picard.frobeniusPicardHom (Over.mk r)
        (h1RootsOfUnityToPicard.{u + 1, 0, u} _ (ℓ ^ e) (c e χ)) =
      (Fintype.card K₀ : ℤ) • h1RootsOfUnityToPicard.{u + 1, 0, u} _ (ℓ ^ e) (c e χ)
    rw [hcD]
    exact D.frobeniusPicardHom_h1RootsOfUnityToPicard_baseTorsor r (hζ e) (hcop e)
  have hunit : ∀ n : ℕ, IsUnit ((Fintype.card K₀ : ℤ) : ZMod (ℓ ^ n)) := fun n => by
    rw [Int.cast_natCast, ZMod.isUnit_iff_coprime]
    exact hcop n
  exact Stacks.Picard.exists_forall_encard_le_of_injOn (Over.mk r) ℓ hℓ.ne_zero
    (Stacks.Picard.finite_torsionBy_ofScheme_baseChange_algebraicClosure (Over.mk r) hℓK₀)
    hunit (hWeil K₀ (Over.mk r) hℓK₀) S Φ hinj htor heig

end AlgebraicGeometry
