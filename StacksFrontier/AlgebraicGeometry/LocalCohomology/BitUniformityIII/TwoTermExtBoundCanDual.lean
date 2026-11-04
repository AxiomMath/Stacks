module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualSection
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwoTermExtBound

/-!
# Killing `Ext¹` out of a two-term complex over a `CanDualSituation`

The form of Stacks Tag 0GAD over a `CanDualSituation`, the carrier Tag 0GAC is stated on. The
algebraic ingredients (the two-term representative, `resMap`, `isANCModule_X_neg_one`) are in
`TwoTermExtBound`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.LocalCohomology.UniformityIII

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}

attribute [local instance] HasDerivedCategory.standard

/-- **The form of Stacks Tag 0GAD that the source's `d > 0` argument reaches**, over a
`CanDualSituation`. Tag 0GAD itself, at the printed target and on the blowup, is
`Stacks.LocalCohomology.UniformityIII.ext_one_powQuot_map_eq_zero_blowup`.

With `d = d(S)` and `q₀ = q(S)` as in Tag 0GA6, let
`n ≥ c ≥ 0` satisfy `n ≥ q₀ + (1 + d)c` and `n ≥ (2 + d)c`. Let `K` be an object of `D(A/Iⁿ)`
with `Hⁱ(K) = 0` for `i ≠ -1, 0`, with `Hⁱ(K)` finite for `i = -1, 0`, and such that
`Ext¹_{A/Iⁿ}(K, N)` is annihilated by `I^c/Iⁿ` for every finite `A/Iⁿ`-module `N`. Then the map

`Ext¹_{A/Iⁿ}(K, Iⁿ/I^{2n}) ⟶ Ext¹_{A/Iⁿ}(K, I^{n-(2+d)c}/I^{2n-(2+d)c})`

induced by the canonical map of coefficients is zero.

The levels are carried as parameters, exactly as in Tag 0GAC: `g + c = f` and
`f + (1 + d)c = n`, so that `f = n - (1 + d)c` and `g = n - (2 + d)c`. The source's two
numerical hypotheses are precisely the existence of `g` as a natural number (`n ≥ (2 + d)c`)
and `q₀ ≤ f` (`n ≥ q₀ + (1 + d)c`), and `c ≤ n` follows.

The source writes the annihilation hypothesis as `Ext¹_{A/I^c}(K, N)`, a typographical slip:
`K` is an object of `D(A/Iⁿ)` and the Ext group its proof uses, through More on Algebra,
Lemma 0G9F applied to the ideal `I^c/Iⁿ` of the ring `A/Iⁿ`, is `Ext¹_{A/Iⁿ}(K, N)`.

The proof is the case `d > 0` of the source, which is pure algebra: a finite two-term
representative `L⁻¹ → L⁰` of `K` with `L⁰` finite free and multiplication by `I^c/Iⁿ` on `L⁻¹`
factoring through the differential exists by Tag 0G9F, which makes `L⁻¹` an `(A, n, c)`-module;
a class in `Ext¹_{A/Iⁿ}(K, Iⁿ/I^{2n})` is a homomorphism `φ : L⁻¹ → Iⁿ/I^{2n}` by Tag 0ALN(1);
Tag 0GAC writes the twist of `φ` down to level `f` as `∑ aᵢψᵢ` with `aᵢ ∈ I^c` and
`ψᵢ : L⁻¹ → I^g/I^{g+n}`; and twisting once more down to level `g` turns `∑ aᵢψᵢ` into
`∑ aᵢ·ψᵢ`, which factors through the differential by way of maps `hᵢ : L⁰ → L⁻¹` with
`d ≫ hᵢ = aᵢ`.

**The carrier.** The Situation is a `CanDualSituation`, the carrier Tag 0GAC is stated on. The
source states this lemma "with `d = d(S)` and `q₀ = q(S)` as above", that is in the ambient
setting fixed at the start of Section 0GA6 — the same setting Tag 0GAC is stated and proved
in, and the one in which Remark 0GAB constructs `can : p^*(M^∨) → (p^*M)^∨` with kernel and
cokernel scheme theoretically supported on `Y_c` and Tag 0GA9 supplies the dotted arrows for
it. A lemma is not stated over less data than the lemma it cites. Over `DualSituation`, which
carries neither `(p^*M)^∨` nor any scheme, the duality step cannot be derived: the registered
clauses of Tag 0GAB are statements about a morphism of ringed sites, and a `DualSituation` has
none, so it had to be hypothesised instead. Nothing is lost by the change, since the only
`DualSituation` in the development, `affineDualSituation`, is the one
`principalCanDualSituation` upgrades.

**Deviation from the source.** The source states the conclusion at
`I^{n-(1+d)c}/I^{2n-2(1+d)c}`, asserting on the way that the class already dies at
`I^{n-(1+d)c}/I^{2n-(1+d)c}`. Its argument for `d > 0` reaches neither module: the maps `ψᵢ`
Tag 0GAC produces land at level `n - (2+d)c`, so the map `ψ = ∑ ψᵢ ∘ hᵢ` the source sets has
target `I^{n-(2+d)c}/I^{2n-(2+d)c}`, while the `φ'` it equates with `ψ ∘ d` has target
`I^{n-(1+d)c}/I^{2n-(1+d)c}`; the identity holds only after the canonical map between the two,
which is the twist down to level `n - (2+d)c` performed here. For `d ≥ 1` the module
`I^{n-(2+d)c}/I^{2n-(2+d)c}` reached here and the module `I^{n-(1+d)c}/I^{2n-2(1+d)c}` the
source asserts admit no canonical map in either direction, so neither statement implies the
other; for `d = 0` the source's statement implies this one strictly, and the source does reach
it, but by its separate sheaf-theoretic argument — the dotted arrow `p^*K⁰ → 𝒪_{Yₙ}(n-c)`
obtained from `H¹(X, ℱ) = 0` — which is not the argument formalized here. -/
theorem CanDualSituation.ext_one_powQuot_map_eq_zero (S : CanDualSituation A I n c)
    {g f : ℕ} (hgf : g + c = f) (hf : f + (1 + S.d) * c = n) (hq : S.q₀ ≤ f)
    (K : DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n)))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) i).obj K))
    (hfin₁ : Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) (-1)).obj K))
    (hfin₀ : Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj K))
    (hann : ∀ (N : ModuleCat.{u} (A ⧸ I ^ n)), Module.Finite (A ⧸ I ^ n) N →
      ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∀ ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj N) 1, a • ξ = 0)
    (ξ : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj (powQuotObj I n n)) 1) :
    ξ ≫ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n))) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).map
          (powQuotLeHom I n ((Nat.le.intro hgf).trans (Nat.le.intro hf)))) = 0 := by
  classical
  obtain ⟨L, hLge, hLle, hLfin₁, hLfin₀, hLfree, ⟨e₀⟩, hLfac⟩ :=
    ((TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) K hK).2.2
        inferInstance hfin₁ hfin₀).2.mp hann
  have : L.IsStrictlyGE (-1) := hLge
  have : L.IsStrictlyLE 0 := hLle
  have hfree' : Module.Free (A ⧸ I ^ n) (L.X 0) := hLfree
  have : Projective (L.X 0) :=
    (IsProjective.iff_projective (R := A ⧸ I ^ n) (L.X 0)).mp inferInstance
  have hanc : IsANCModule I n c (L.X (-1)) :=
    isANCModule_X_neg_one L hLfin₁ hLfree hLfac
  refine TwoTermComplex.ext_one_map_eq_zero_of_forall_factorization L e₀ _ ?_ ξ
  intro φcat
  obtain ⟨N, a, ha, ψ, hsum⟩ :=
    S.exists_sum_powQuotSmul ⟨L.X (-1), hanc⟩ (toResHom I n n φcat) hgf hf hq
  choose hmap hmapeq using fun i : Fin N =>
    hLfac (Ideal.Quotient.mk (I ^ n) (a i)) (Ideal.mem_map_of_mem _ (ha i))
  refine ⟨ofResHom I g n (∑ i, (ψ i).comp (resMap I n (hmap i))), ?_⟩
  have hmain : (∑ i, (ψ i).comp (resMap I n (hmap i))).comp (resMap I n (L.d (-1) 0)) =
      (powQuotLe I ((Nat.le.intro hgf).trans (Nat.le.intro hf))).comp
        (toResHom I n n φcat) := by
    refine LinearMap.ext fun z => ?_
    have key : ∀ i : Fin N,
        (ψ i) (resMap I n (hmap i) (resMap I n (L.d (-1) 0) z)) = a i • (ψ i) z := by
      intro i
      have hz : resMap I n (hmap i) (resMap I n (L.d (-1) 0) z) = a i • z :=
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hmapeq i)) z
      rw [hz]
      exact (ψ i).map_smul (a i) z
    have h1 := LinearMap.congr_fun hsum z
    rw [LinearMap.comp_apply, LinearMap.sum_apply] at h1
    simp only [LinearMap.comp_apply] at h1
    have h2 : powQuotLe I ((Nat.le.intro hgf).trans (Nat.le.intro hf))
        ((toResHom I n n φcat) z) = ∑ i, a i • (ψ i) z := by
      rw [← powQuotLe_powQuotLe I n (Nat.le.intro hf) (Nat.le.intro hgf), h1, map_sum]
      exact Finset.sum_congr rfl fun i _ => powQuotLe_powQuotSmul I n (ha i) hgf ((ψ i) z)
    rw [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.comp_apply, h2]
    simp only [LinearMap.comp_apply]
    exact Finset.sum_congr rfl fun i _ => key i
  exact ModuleCat.hom_ext (LinearMap.ext fun x => LinearMap.congr_fun hmain x)
end Main

end Stacks.LocalCohomology.UniformityIII

end
