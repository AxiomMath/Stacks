module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Classes killed in a filtered colimit of derived functors

Let `(Φ_k)_{k ∈ ι}` be a directed system of additive functors `𝒜 ⥤ Ab` with a cocone
`θ_k : Φ_k ⟶ Ψ` which is a colimit *pointwise*: every element of `Ψ(G)` comes from some
`Φ_k(G)`, and an element of `Φ_k(G)` killed by `θ_k` already dies in some `Φ_l(G)`, `l ≥ k`.
Filtered colimits of abelian groups are exact, so homology commutes with them, and the right
derived functors of `Ψ` are the colimits of those of the `Φ_k`. This file proves the half of that
statement which the dévissage of Travaux de Gabber, Exposé XVIII-A, Lemma 2.2 uses:
**if `R^iΨ(F) = 0`, then every class of `R^iΦ_k(F)` dies in some `R^iΦ_l(F)`**, and more generally
every class of `R^iΦ₀(F)` dies in some `R^iΦ_l(F)` for a functor `Φ₀` mapping compatibly to the
system.

The argument is elementwise, on one injective resolution `I^•` of `F`: a cycle `z` of `Φ₀(I^•)`
whose image in `Ψ(I^•)` is a boundary `d w`; `w` comes from some `Φ_k(I^{i-1})`, and the difference
of the two cycles dies at some later level, where `z` becomes a boundary.

## Main results

* `HomologicalComplex.exists_homologyMap_eq_zero_of_isZero_homology`: the statement for complexes
  of abelian groups.
* `CategoryTheory.exists_rightDerived_app_eq_zero_of_isZero`: the statement for right derived
  functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomologicalComplex

variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]

/-- A chain map of cochain complexes of abelian groups commutes with the differentials. -/
private theorem map_d_apply {K L : CochainComplex AddCommGrpCat.{w} ℕ} (f : K ⟶ L) (i j : ℕ)
    (x : K.X i) : f.f j (K.d i j x) = L.d i j (f.f i x) := by
  have := ConcreteCategory.congr_hom (f.comm i j) x
  simpa only [ConcreteCategory.comp_apply] using this.symm

/-- **Killing a homology class in a pointwise filtered colimit of complexes of abelian groups.**
Let `σ_k : K₀ ⟶ K_k`, `ρ : K_k ⟶ K_l` (`k ≤ l`) and `τ_k : K_k ⟶ L` be compatible maps of cochain
complexes of abelian groups such that, in every degree, `L` is the colimit of the `K_k` (every
element of `L^n` comes from some `K_k^n`, and an element of `K_k^n` killed by `τ_k` dies in some
`K_l^n`). If `H^j(L) = 0` then every class of `H^j(K₀)` dies in some `H^j(K_l)`. -/
theorem exists_homologyMap_eq_zero_of_isZero_homology
    (K₀ : CochainComplex AddCommGrpCat.{w} ℕ) (K : ι → CochainComplex AddCommGrpCat.{w} ℕ)
    (L : CochainComplex AddCommGrpCat.{w} ℕ) (σ : ∀ k, K₀ ⟶ K k)
    (ρ : ∀ {k l : ι}, k ≤ l → (K k ⟶ K l)) (τ : ∀ k, K k ⟶ L)
    (hσρ : ∀ {k l : ι} (h : k ≤ l), σ k ≫ ρ h = σ l)
    (hρτ : ∀ {k l : ι} (h : k ≤ l), ρ h ≫ τ l = τ k)
    (hsurj : ∀ (n : ℕ) (y : L.X n), ∃ (k : ι) (x : (K k).X n), (τ k).f n x = y)
    (hker : ∀ (n : ℕ) (k : ι) (x : (K k).X n), (τ k).f n x = 0 →
      ∃ (l : ι) (h : k ≤ l), (ρ h).f n x = 0)
    (j : ℕ) (hL : IsZero (L.homology j)) (ξ : K₀.homology j) :
    ∃ l : ι, homologyMap (σ l) j ξ = 0 := by
  let p := (ComplexShape.up ℕ).prev j
  -- exactness of `X^{j-1} → Z^j → H^j`
  have hex : ∀ M : CochainComplex AddCommGrpCat.{w} ℕ,
      (ShortComplex.mk (M.toCycles p j) (M.homologyπ j) (M.toCycles_comp_homologyπ p j)).Exact :=
    fun M => ShortComplex.exact_of_g_is_cokernel _ (M.homologyIsCokernel p j rfl)
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K₀.homologyπ j)).1 inferInstance ξ
  let k₀ : ι := Classical.arbitrary ι
  let yL := cyclesMap (σ k₀ ≫ τ k₀) j z
  have hyL : L.homologyπ j yL = 0 := (AddCommGrpCat.subsingleton_of_isZero hL).elim _ _
  obtain ⟨w', hw'⟩ := (ShortComplex.ab_exact_iff _).1 (hex L) yL hyL
  obtain ⟨k₁, w₁, hw₁⟩ := hsurj p w'
  obtain ⟨m, hk₀m, hk₁m⟩ := directed_of (· ≤ ·) k₀ k₁
  let z₂ := K₀.iCycles j z
  -- the difference of the two cycles at the level `m`
  let e := (σ m).f j z₂ - (K m).d p j ((ρ hk₁m).f p w₁)
  have hστ : σ m ≫ τ m = σ k₀ ≫ τ k₀ := by
    rw [← hσρ hk₀m, Category.assoc, hρτ]
  have he : (τ m).f j e = 0 := by
    have h1 : (τ m).f j ((σ m).f j z₂) = L.iCycles j yL := by
      have := ConcreteCategory.congr_hom (cyclesMap_i (σ k₀ ≫ τ k₀) j) z
      simp only [ConcreteCategory.comp_apply] at this
      rw [this, ← hστ]
      rfl
    have h2 : (τ m).f j ((K m).d p j ((ρ hk₁m).f p w₁)) = L.iCycles j yL := by
      rw [map_d_apply]
      have hτ : (τ m).f p ((ρ hk₁m).f p w₁) = w' := by
        rw [← hw₁, ← hρτ hk₁m]
        rfl
      rw [hτ, ← hw']
      have := ConcreteCategory.congr_hom (L.toCycles_i p j) w'
      simp only [ConcreteCategory.comp_apply] at this
      exact this.symm
    rw [map_sub, h1, h2, sub_self]
  obtain ⟨l, hml, hl⟩ := hker j m e he
  refine ⟨l, ?_⟩
  -- at the level `l` the cycle `z` is a boundary
  have hbd : cyclesMap (σ l) j z = (K l).toCycles p j ((ρ hml).f p ((ρ hk₁m).f p w₁)) := by
    apply (AddCommGrpCat.mono_iff_injective ((K l).iCycles j)).1 inferInstance
    have h1 := ConcreteCategory.congr_hom (cyclesMap_i (σ l) j) z
    have h2 := ConcreteCategory.congr_hom ((K l).toCycles_i p j) ((ρ hml).f p ((ρ hk₁m).f p w₁))
    simp only [ConcreteCategory.comp_apply] at h1 h2
    rw [h1, h2]
    have h3 : (ρ hml).f j e = (σ l).f j z₂ -
        (K l).d p j ((ρ hml).f p ((ρ hk₁m).f p w₁)) := by
      rw [map_sub, map_d_apply, ← hσρ hml]
      rfl
    rw [hl] at h3
    exact (sub_eq_zero.1 h3.symm)
  have := ConcreteCategory.congr_hom (homologyπ_naturality (σ l) j) z
  simp only [ConcreteCategory.comp_apply] at this
  rw [this, hbd]
  have h0 := ConcreteCategory.congr_hom ((K l).toCycles_comp_homologyπ p j)
    ((ρ hml).f p ((ρ hk₁m).f p w₁))
  simp only [ConcreteCategory.comp_apply] at h0
  exact h0

end HomologicalComplex

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasInjectiveResolutions 𝒜]
  {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]

/-- **Classes killed in a pointwise filtered colimit of derived functors.** Let `Φ_k`
(`k ∈ ι`, directed) be additive functors `𝒜 ⥤ Ab` with transitions `ρ` and a cocone `θ_k : Φ_k ⟶ Ψ`
which is a colimit pointwise, and let `s_k : Φ₀ ⟶ Φ_k` be compatible maps from a further additive
functor. If `R^iΨ(F) = 0`, every class of `R^iΦ₀(F)` dies in some `R^iΦ_k(F)`. -/
theorem exists_rightDerived_app_eq_zero_of_isZero
    (Φ₀ : 𝒜 ⥤ AddCommGrpCat.{w}) [Φ₀.Additive] (Φ : ι → 𝒜 ⥤ AddCommGrpCat.{w})
    [∀ k, (Φ k).Additive] (Ψ : 𝒜 ⥤ AddCommGrpCat.{w}) [Ψ.Additive]
    (s : ∀ k, Φ₀ ⟶ Φ k) (ρ : ∀ {k l : ι}, k ≤ l → (Φ k ⟶ Φ l)) (θ : ∀ k, Φ k ⟶ Ψ)
    (hsρ : ∀ {k l : ι} (h : k ≤ l), s k ≫ ρ h = s l)
    (hρθ : ∀ {k l : ι} (h : k ≤ l), ρ h ≫ θ l = θ k)
    (hsurj : ∀ (G : 𝒜) (y : Ψ.obj G), ∃ (k : ι) (x : (Φ k).obj G), (θ k).app G x = y)
    (hker : ∀ (G : 𝒜) (k : ι) (x : (Φ k).obj G), (θ k).app G x = 0 →
      ∃ (l : ι) (h : k ≤ l), (ρ h).app G x = 0)
    (F : 𝒜) (i : ℕ) (hF : IsZero ((Ψ.rightDerived i).obj F))
    (ξ : (Φ₀.rightDerived i).obj F) :
    ∃ k : ι, (NatTrans.rightDerived (s k) i).app F ξ = 0 := by
  let P := injectiveResolution F
  let c := ComplexShape.up ℕ
  let K₀ := (Φ₀.mapHomologicalComplex c).obj P.cocomplex
  let K : ι → CochainComplex AddCommGrpCat.{w} ℕ := fun k =>
    ((Φ k).mapHomologicalComplex c).obj P.cocomplex
  let L := (Ψ.mapHomologicalComplex c).obj P.cocomplex
  obtain ⟨l, hl⟩ := HomologicalComplex.exists_homologyMap_eq_zero_of_isZero_homology K₀ K L
    (fun k => (NatTrans.mapHomologicalComplex (s k) c).app P.cocomplex)
    (fun h => (NatTrans.mapHomologicalComplex (ρ h) c).app P.cocomplex)
    (fun k => (NatTrans.mapHomologicalComplex (θ k) c).app P.cocomplex)
    (fun h => by rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, hsρ])
    (fun h => by rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, hρθ])
    (fun n y => hsurj (P.cocomplex.X n) y)
    (fun n k x hx => hker (P.cocomplex.X n) k x hx)
    i (hF.of_iso (P.isoRightDerivedObj' Ψ i).symm) ((P.isoRightDerivedObj' Φ₀ i).hom ξ)
  refine ⟨l, ?_⟩
  have h := homologyMap_comp_isoRightDerivedObj'_inv (s l) P i
  have h' := congrArg (fun φ => (ConcreteCategory.hom φ) ((P.isoRightDerivedObj' Φ₀ i).hom ξ)) h
  dsimp only at h'
  rw [ConcreteCategory.comp_apply, hl, map_zero, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_apply] at h'
  exact h'.symm

end CategoryTheory

end
