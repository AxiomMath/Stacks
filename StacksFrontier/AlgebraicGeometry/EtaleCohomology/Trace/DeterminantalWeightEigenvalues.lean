module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The centralizing element has eigenvalues of a single weight on an irreducible representation

Let `V` be a finite-dimensional vector space over an algebraically closed field `K`, and
`ι : K →+* ℂ`.  Let `S` be a set of endomorphisms of `V` (the image of the geometric monodromy
group together with a power `U` of Frobenius), `Γ` a group of automorphisms normalizing the
`S`-stable subspaces (the image of the arithmetic fundamental group), and `z` an endomorphism
commuting with `S`, preserving the `S`-stable subspaces, with `det (U |_W) = det (z |_W)` for every
`S`-stable `W` (as produced by `Stacks.LAdic.exists_det_stabRestrict_pow_eq`).  If the absolute
value `‖ι det (U |_W)‖` is invariant under translating `W` by `Γ`, and `V` is `Γ`-irreducible,
then all eigenvalues of `z` have the same absolute value under `ι`.

This is the step of Weil II, 1.3 (Kedlaya, *Fourier transforms and p-adic Weil II*, Proposition
6.1.4) where an irreducible lisse sheaf acquires a determinantal weight: on the subspace `W₀`
where `z` has eigenvalues of maximal absolute value `r₀`, every `γ W₀` is `S`-stable, and the part
of `γ W₀` on which `z` has smaller absolute value `r'` would, translated back by `γ⁻¹` into `W₀`,
have `‖ι det U‖` equal to both `r'^d` and `r₀^d`.  Hence `W₀` is `Γ`-stable, so `W₀ = V`.

## Main results

* `Stacks.EtaleCohomology.absEigenPart`: the sum of the generalized eigenspaces of `z` for
  eigenvalues of a given absolute value.
* `Stacks.EtaleCohomology.norm_det_restrict_of_le_absEigenPart`
* `Stacks.EtaleCohomology.exists_forall_hasEigenvalue_norm_eq`: the main statement.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.3.
* K. S. Kedlaya, *Fourier transforms and p-adic "Weil II"*, Compos. Math. 142 (2006), 6.1.4.
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

open Module Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The sum of the generalized eigenspaces of `z` for the eigenvalues `μ` with `‖ι μ‖ = r`. -/
def absEigenPart (ι : K →+* ℂ) (z : Module.End K V) (r : ℝ) : Submodule K V :=
  ⨆ (μ : K) (_ : ‖ι μ‖ = r), z.maxGenEigenspace μ

/-- `absEigenPart ι z r` is stable under every endomorphism commuting with `z`. -/
theorem absEigenPart_le_comap {ι : K →+* ℂ} {z s : Module.End K V} (h : Commute z s) (r : ℝ) :
    absEigenPart ι z r ≤ (absEigenPart ι z r).comap s := by
  refine iSup₂_le fun μ hμ x hx => ?_
  exact (le_iSup₂ (f := fun (μ : K) (_ : ‖ι μ‖ = r) => z.maxGenEigenspace μ) μ hμ)
    (mapsTo_maxGenEigenspace_of_comm h μ hx)

/-- An eigenvector of `z` in `absEigenPart ι z r` has an eigenvalue of absolute value `r`. -/
theorem norm_eq_of_hasEigenvector_mem_absEigenPart {ι : K →+* ℂ} {z : Module.End K V} {r : ℝ}
    {μ : K} {v : V} (hv : z.HasEigenvector μ v) (hvr : v ∈ absEigenPart ι z r) : ‖ι μ‖ = r := by
  by_contra hne
  have hle : absEigenPart ι z r ≤ ⨆ (μ' : K) (_ : μ' ≠ μ), z.maxGenEigenspace μ' := by
    refine iSup₂_le fun μ' hμ' => le_iSup₂_of_le μ' ?_ le_rfl
    rintro rfl
    exact hne hμ'
  have hdis := (independent_maxGenEigenspace z) μ
  have hv1 : v ∈ z.maxGenEigenspace μ :=
    (z.genEigenspace μ).monotone (show (1 : ℕ∞) ≤ ⊤ from le_top) hv.1
  have hv2 : v ∈ ⨆ (μ' : K) (_ : μ' ≠ μ), z.maxGenEigenspace μ' := hle hvr
  exact hv.2 ((Submodule.disjoint_def.mp hdis) v hv1 hv2)

/-- An eigenvector of the restriction of `z` to a `z`-stable subspace is an eigenvector of `z`. -/
private theorem hasEigenvector_coe_of_restrict {z : Module.End K V} {W : Submodule K V}
    {hW : W ≤ W.comap z} {μ : K} {w : W} (hw : Module.End.HasEigenvector (z.restrict hW) μ w) :
    z.HasEigenvector μ (w : V) :=
  ⟨by rw [mem_eigenspace_iff]; exact congrArg Subtype.val hw.apply_eq_smul,
    fun h0 => hw.2 (Subtype.ext h0)⟩

/-- An eigenvector of `z` with eigenvalue `μ` lies in `absEigenPart ι z ‖ι μ‖`. -/
private theorem mem_absEigenPart_of_hasEigenvector {ι : K →+* ℂ} {z : Module.End K V} {μ : K}
    {v : V} (hv : z.HasEigenvector μ v) : v ∈ absEigenPart ι z ‖ι μ‖ :=
  (le_iSup₂_of_le (f := fun (μ' : K) (_ : ‖ι μ'‖ = ‖ι μ‖) => z.maxGenEigenspace μ') μ rfl le_rfl)
    ((z.genEigenspace μ).monotone (show (1 : ℕ∞) ≤ ⊤ from le_top) hv.1)

variable [FiniteDimensional K V] [IsAlgClosed K]

/-- On a `z`-stable subspace inside `absEigenPart ι z r`, `‖ι det z‖ = r ^ dim`. -/
theorem norm_det_restrict_of_le_absEigenPart {ι : K →+* ℂ} {z : Module.End K V} {r : ℝ}
    {W : Submodule K V} (hW : W ≤ W.comap z) (hWr : W ≤ absEigenPart ι z r) :
    ‖ι (LinearMap.det (z.restrict hW))‖ = r ^ Module.finrank K W := by
  set f := z.restrict hW
  have hsplit : f.charpoly.Splits := IsAlgClosed.splits _
  have hroots : ∀ μ ∈ f.charpoly.roots, ‖ι μ‖ = r := by
    intro μ hμ
    have hev : Module.End.HasEigenvalue f μ := by
      rw [hasEigenvalue_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).mp hμ
    obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
    exact norm_eq_of_hasEigenvector_mem_absEigenPart (hasEigenvector_coe_of_restrict hw)
      (hWr w.2)
  have hcard : Multiset.card f.charpoly.roots = Module.finrank K W := by
    rw [Polynomial.splits_iff_card_roots.mp hsplit, LinearMap.charpoly_natDegree]
  rw [det_eq_prod_roots_charpoly_of_splits hsplit, map_multiset_prod]
  have hn : ‖(Multiset.map ι f.charpoly.roots).prod‖ =
      ((f.charpoly.roots.map ι).map fun x => ‖x‖).prod :=
    map_multiset_prod (normHom : ℂ →*₀ ℝ) _
  have hc : Multiset.map ((fun x : ℂ => ‖x‖) ∘ ι) f.charpoly.roots =
      Multiset.map (fun _ => r) f.charpoly.roots :=
    Multiset.map_congr rfl fun μ hμ => hroots μ hμ
  rw [hn, Multiset.map_map, hc, Multiset.map_const',
    Multiset.prod_replicate, hcard]

/-- A `z`-stable subspace on which all eigenvalues of `z` have absolute value `r` lies in
`absEigenPart ι z r`. -/
theorem le_absEigenPart {ι : K →+* ℂ} {z : Module.End K V} {r : ℝ} {W : Submodule K V}
    (hW : W ≤ W.comap z) (h : ∀ μ, Module.End.HasEigenvalue (z.restrict hW) μ → ‖ι μ‖ = r) :
    W ≤ absEigenPart ι z r := by
  intro w hw
  have htop : (⟨w, hw⟩ : W) ∈ ⨆ μ, Module.End.maxGenEigenspace (z.restrict hW) μ := by
    rw [iSup_maxGenEigenspace_eq_top]; trivial
  have hmap := Submodule.mem_map_of_mem (f := W.subtype) htop
  rw [Submodule.map_iSup] at hmap
  refine (iSup_le (fun μ => ?_) : _ ≤ absEigenPart ι z r) hmap
  by_cases hμ : Module.End.maxGenEigenspace (z.restrict hW) μ = ⊥
  · rw [hμ, Submodule.map_bot]; exact bot_le
  · have hev : Module.End.HasEigenvalue (z.restrict hW) μ := HasUnifEigenvalue.lt zero_lt_one hμ
    refine le_trans ?_ (le_iSup₂_of_le (f := fun (μ : K) (_ : ‖ι μ‖ = r) => z.maxGenEigenspace μ)
      μ (h μ hev) le_rfl)
    rw [maxGenEigenspace, genEigenspace_restrict]
    exact Submodule.map_comap_le _ _

omit [FiniteDimensional K V] [IsAlgClosed K] in
/-- If `W₁ = W₂` are `U`-stable subspaces, the absolute values under `ι` of the determinants of
the restrictions of `U` to `W₁` and to `W₂` agree. -/
theorem norm_det_restrict_congr (ι : K →+* ℂ) (U : Module.End K V) {W₁ W₂ : Submodule K V}
    (h : W₁ = W₂) (h₁ : W₁ ≤ W₁.comap U) (h₂ : W₂ ≤ W₂.comap U) :
    ‖ι (LinearMap.det (U.restrict h₁))‖ = ‖ι (LinearMap.det (U.restrict h₂))‖ := by
  subst h; rfl

/-- **A single weight for the centralizing element on an irreducible representation** (Weil II
1.3; Kedlaya, Proposition 6.1.4).  See the module docstring. -/
theorem exists_forall_hasEigenvalue_norm_eq (ι : K →+* ℂ) (S : Set (Module.End K V))
    (Γ : Subgroup (Module.End K V)ˣ) {U z : Module.End K V} (hUS : U ∈ S)
    (hzS : ∀ s ∈ S, Commute z s)
    (hz : ∀ W : Submodule K V, (∀ s ∈ S, W ≤ W.comap s) → W ≤ W.comap z)
    (hdet : ∀ (W : Submodule K V) (hW : ∀ s ∈ S, W ≤ W.comap s),
      LinearMap.det (U.restrict (hW U hUS)) = LinearMap.det (z.restrict (hz W hW)))
    (hnormal : ∀ γ ∈ Γ, ∀ W : Submodule K V, (∀ s ∈ S, W ≤ W.comap s) →
      ∀ s ∈ S, W.map (γ : Module.End K V) ≤ (W.map (γ : Module.End K V)).comap s)
    (hconj : ∀ γ ∈ Γ, ∀ (W : Submodule K V) (hW : ∀ s ∈ S, W ≤ W.comap s)
      (hW' : ∀ s ∈ S, W.map (γ : Module.End K V) ≤ (W.map (γ : Module.End K V)).comap s),
      ‖ι (LinearMap.det (U.restrict (hW' U hUS)))‖ = ‖ι (LinearMap.det (U.restrict (hW U hUS)))‖)
    (hirr : ∀ W : Submodule K V, W ≠ ⊥ → (∀ γ ∈ Γ, W ≤ W.comap (γ : Module.End K V)) → W = ⊤) :
    ∃ r : ℝ, ∀ μ, z.HasEigenvalue μ → ‖ι μ‖ = r := by
  -- the norm of the determinant of `U` on a stable subspace inside an `absEigenPart`
  have hnorm : ∀ (W : Submodule K V) (hW : ∀ s ∈ S, W ≤ W.comap s) (r : ℝ),
      W ≤ absEigenPart ι z r →
        ‖ι (LinearMap.det (U.restrict (hW U hUS)))‖ = r ^ Module.finrank K W := by
    intro W hW r hWr
    rw [hdet W hW]
    exact norm_det_restrict_of_le_absEigenPart _ hWr
  rcases Set.eq_empty_or_nonempty {μ | z.HasEigenvalue μ} with hempty | hne
  · exact ⟨0, fun μ hμ => absurd (show μ ∈ {μ | z.HasEigenvalue μ} from hμ) (by simp [hempty])⟩
  obtain ⟨μ₀, hμ₀, hmax⟩ := Set.exists_max_image _ (fun μ => ‖ι μ‖)
    (Module.End.finite_hasEigenvalue z) hne
  set r₀ := ‖ι μ₀‖
  set W₀ := absEigenPart ι z r₀
  have hW₀S : ∀ s ∈ S, W₀ ≤ W₀.comap s := fun s hs => absEigenPart_le_comap (hzS s hs) r₀
  have hclaim : ∀ γ ∈ Γ, W₀ ≤ W₀.comap (γ : Module.End K V) := by
    intro γ hγ
    set Y := W₀.map (γ : Module.End K V)
    have hY : ∀ s ∈ S, Y ≤ Y.comap s := hnormal γ hγ W₀ hW₀S
    suffices hYW : Y ≤ W₀ from fun x hx => hYW (Submodule.mem_map_of_mem hx)
    refine le_absEigenPart (hz Y hY) fun μ' hμ' => ?_
    obtain ⟨y, hy⟩ := hμ'.exists_hasEigenvector
    have hyV := hasEigenvector_coe_of_restrict hy
    by_contra hne'
    set r' := ‖ι μ'‖
    set X := Y ⊓ absEigenPart ι z r'
    have hX : ∀ s ∈ S, X ≤ X.comap s := fun s hs x hx =>
      ⟨hY s hs hx.1, absEigenPart_le_comap (hzS s hs) r' hx.2⟩
    have hyX : (y : V) ∈ X := ⟨y.2, mem_absEigenPart_of_hasEigenvector hyV⟩
    have hXne : X ≠ ⊥ := fun h => hyV.2 (by rw [h] at hyX; exact (Submodule.mem_bot K).mp hyX)
    set X' := X.map ((γ⁻¹ : (Module.End K V)ˣ) : Module.End K V)
    have hX' : ∀ s ∈ S, X' ≤ X'.comap s := hnormal γ⁻¹ (inv_mem hγ) X hX
    have hX'W : X' ≤ W₀ := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hx.1
      change ((γ⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((γ : Module.End K V) w) ∈ W₀
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
      exact hw
    have hcomp : (γ : Module.End K V) ∘ₗ ((γ⁻¹ : (Module.End K V)ˣ) : Module.End K V) =
        LinearMap.id := by
      rw [← Module.End.mul_eq_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      rfl
    have hXX : X'.map (γ : Module.End K V) = X := by
      rw [← Submodule.map_comp, hcomp, Submodule.map_id]
    have hfin : Module.finrank K X' = Module.finrank K X := by
      rw [← hXX]
      have hinj : Function.Injective (γ : Module.End K V) := fun a b hab => by
        have := congrArg ((γ⁻¹ : (Module.End K V)ˣ) : Module.End K V) hab
        simpa [← Module.End.mul_apply, ← Units.val_mul] using this
      exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj X')
    have e1 := hconj γ hγ X' hX' (hnormal γ hγ X' hX')
    rw [norm_det_restrict_congr ι U hXX _ (hX U hUS), hnorm X hX r' inf_le_right,
      hnorm X' hX' r₀ hX'W, hfin] at e1
    have hd : Module.finrank K X ≠ 0 := fun h => hXne (Submodule.finrank_eq_zero.mp h)
    exact hne' ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd).mp e1)
  have hW₀ : W₀ = ⊤ := by
    refine hirr W₀ ?_ hclaim
    obtain ⟨v, hv⟩ := hμ₀.exists_hasEigenvector
    intro h
    have : v ∈ W₀ := mem_absEigenPart_of_hasEigenvector hv
    rw [h] at this
    exact hv.2 ((Submodule.mem_bot K).mp this)
  refine ⟨r₀, fun μ hμ => ?_⟩
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hvW : v ∈ W₀ := by rw [hW₀]; exact Submodule.mem_top
  exact norm_eq_of_hasEigenvector_mem_absEigenPart hv hvW

end Stacks.EtaleCohomology
