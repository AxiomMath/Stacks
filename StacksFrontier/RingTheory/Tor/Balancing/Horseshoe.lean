module

public import StacksFrontier.RingTheory.Tor.Balancing.TorShift

/-!
# The horseshoe resolution and the dimension shift on the `Tor'` side

The twisted biproduct resolution of `P₀ = Projective.over M` lifting the syzygy sequence
(the horseshoe lemma), the long exact sequence of `Tor'` for a short exact sequence of
objects, the description of `Tor'_1` as the common kernel functor, the dimension shift
`Tor_iso_Tor'.tor'Shift`, and the objectwise isomorphism `Tor_iso_Tor'.app`.

This is part of the split of `StacksFrontier.RingTheory.Tor.Balancing`.
-/

@[expose] public section

open LinearMap Submodule

universe u

-- `Tor_iso_Tor'.fromLeftDerivedZero_natTrans`, `Tor_iso_Tor'.zeroIso`,
-- `lesShift.phi_preservesZeroMorphisms` and `lesShift.comp_naturality` rewrite through
-- `ModuleCat`/`Functor.leftDerived` bundling, which only unfolds with relaxed defeq transparency.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

variable (R : Type u) [CommRing R]

/-! ### The twisted biproduct resolution of `P₀ = Projective.over M`

The two outer resolutions `hsResK` of `K` and `hsResM` of `M` are chosen arbitrarily, and the
middle resolution of `P₀` is built from them as the degreewise binary biproduct
`Q_n(P₀) := Q_n(K) ⊕ Q_n(M)` with the lower-triangular twisted differential
`d^P_n = [[d^K_n, τ_n],[0, d^M_n]]`. The connecting maps `τ_n` are produced by induction using
projectivity of `Q_n(M)`, and the augmentation is `ε^P = biprod.desc (ε^K ≫ ι) s₀`.
-/

/-- Chosen projective resolution of the syzygy `K = syzygy M`. -/
noncomputable def Tor_iso_Tor'.hsResK (M : ModuleCat.{u} R) :
    ProjectiveResolution (Tor_iso_Tor'.syzygy R M) :=
  CategoryTheory.projectiveResolution (Tor_iso_Tor'.syzygy R M)

/-- Chosen projective resolution of `M`. -/
noncomputable def Tor_iso_Tor'.hsResM (M : ModuleCat.{u} R) :
    ProjectiveResolution M :=
  CategoryTheory.projectiveResolution M

/-- The lift `s₀ : Q₀(M) → P₀` of the augmentation `ε^M = resM.π.f 0` through the epimorphism
`π = Projective.π M`. -/
noncomputable def Tor_iso_Tor'.hsS0 (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsResM R M).complex.X 0 ⟶ (Tor_iso_Tor'.syzygySC R M).X₂ :=
  haveI : Epi (Projective.π M) := Projective.π_epi M
  Projective.factorThru ((Tor_iso_Tor'.hsResM R M).π.f 0) (Projective.π M)

/-- `s₀ ≫ π = ε^M`. -/
theorem Tor_iso_Tor'.hsS0_spec (M : ModuleCat.{u} R) :
    Tor_iso_Tor'.hsS0 R M ≫ Projective.π M = (Tor_iso_Tor'.hsResM R M).π.f 0 := by
  have : Epi (Projective.π M) := Projective.π_epi M
  exact Projective.factorThru_comp _ _

/-- The base connecting map `τ₁ : Q₁(M) → Q₀(K)` (indexed as `hsTau M 0`), a lift through the
augmentation `ε^K` of the kernel factorization of `-(d^M₁ ≫ s₀)`. -/
noncomputable def Tor_iso_Tor'.hsTau0 (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsResM R M).complex.X 1 ⟶ (Tor_iso_Tor'.hsResK R M).complex.X 0 :=
  haveI : Epi (Projective.π M) := Projective.π_epi M
  Projective.factorThru
    (Limits.kernel.lift (Projective.π M)
      (-((Tor_iso_Tor'.hsResM R M).complex.d 1 0 ≫ Tor_iso_Tor'.hsS0 R M)) (by
        rw [Preadditive.neg_comp, Category.assoc, Tor_iso_Tor'.hsS0_spec, neg_eq_zero]
        exact ProjectiveResolution.complex_d_comp_π_f_zero _))
    ((Tor_iso_Tor'.hsResK R M).π.f 0)

/-- `τ₁ ≫ ε^K ≫ ι = -(d^M₁ ≫ s₀)` in `P₀`. -/
theorem Tor_iso_Tor'.hsTau0_spec (M : ModuleCat.{u} R) :
    Tor_iso_Tor'.hsTau0 R M ≫ (Tor_iso_Tor'.hsResK R M).π.f 0
        ≫ Limits.kernel.ι (Projective.π M)
      = -((Tor_iso_Tor'.hsResM R M).complex.d 1 0 ≫ Tor_iso_Tor'.hsS0 R M) := by
  have : Epi (Projective.π M) := Projective.π_epi M
  rw [Tor_iso_Tor'.hsTau0, ← Category.assoc, Projective.factorThru_comp, Limits.kernel.lift_ι]

/-- `-(d^M₂₁ ≫ τ₁) ≫ ε^K = 0`. -/
theorem Tor_iso_Tor'.hsVanish_zero (M : ModuleCat.{u} R) :
    (-((Tor_iso_Tor'.hsResM R M).complex.d 2 1 ≫ Tor_iso_Tor'.hsTau0 R M))
        ≫ (Tor_iso_Tor'.hsResK R M).π.f 0 = 0 := by
  rw [← cancel_mono (Limits.kernel.ι (Projective.π M))]
  have h := Tor_iso_Tor'.hsTau0_spec R M
  simp only [Preadditive.neg_comp, Limits.zero_comp, Category.assoc] at h ⊢
  rw [h, Preadditive.comp_neg, ← Category.assoc, HomologicalComplex.d_comp_d, Limits.zero_comp]
  simp

/-- The exact short complex of `Q_•(K)` at degree `m+1`: `Q_{m+2}(K) → Q_{m+1}(K) → Q_m(K)`,
exact at the middle. -/
noncomputable def Tor_iso_Tor'.hsSCsucc (M : ModuleCat.{u} R) (m : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk ((Tor_iso_Tor'.hsResK R M).complex.d (m + 2) (m + 1))
    ((Tor_iso_Tor'.hsResK R M).complex.d (m + 1) m) (HomologicalComplex.d_comp_d _ _ _ _)

/-- `Q_•(K)` is exact at `Q_{m+1}(K)`, since it is a resolution. -/
theorem Tor_iso_Tor'.hsSCsucc_exact (M : ModuleCat.{u} R) (m : ℕ) :
    (Tor_iso_Tor'.hsSCsucc R M m).Exact :=
  (Tor_iso_Tor'.hsResK R M).exact_succ m

/-- The exact short complex of `Q_•(K)` at degree `0` (augmented): `Q₁(K) → Q₀(K) → K`. -/
noncomputable def Tor_iso_Tor'.hsSC0 (M : ModuleCat.{u} R) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk ((Tor_iso_Tor'.hsResK R M).complex.d 1 0) ((Tor_iso_Tor'.hsResK R M).π.f 0)
    (ProjectiveResolution.complex_d_comp_π_f_zero _)

/-- The augmented complex `Q₁(K) → Q₀(K) → K` is exact at `Q₀(K)`. -/
theorem Tor_iso_Tor'.hsSC0_exact (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsSC0 R M).Exact :=
  (Tor_iso_Tor'.hsResK R M).exact₀

/-- At level `m`: a map `τ_{m+1} : Q_{m+2}(M) → Q_{m+1}(K)` together with the vanishing
`-(d^M ≫ τ_{m+1}) ≫ d^K = 0`. -/
def Tor_iso_Tor'.hsTauStep (M : ModuleCat.{u} R) (m : ℕ) : Type _ :=
  Σ' (t : (Tor_iso_Tor'.hsResM R M).complex.X (m + 2) ⟶ (Tor_iso_Tor'.hsResK R M).complex.X (m +
      1)),
    (-((Tor_iso_Tor'.hsResM R M).complex.d (m + 3) (m + 2) ≫ t))
        ≫ (Tor_iso_Tor'.hsResK R M).complex.d (m + 1) m = 0

/-- The connecting maps `τ_{m+1}`, constructed inductively together with the invariant they
carry. -/
noncomputable def Tor_iso_Tor'.hsTauAux (M : ModuleCat.{u} R) :
    (m : ℕ) → Tor_iso_Tor'.hsTauStep R M m
  | 0 =>
    let t1 := (Tor_iso_Tor'.hsSC0_exact R M).liftFromProjective
      (-((Tor_iso_Tor'.hsResM R M).complex.d 2 1 ≫ Tor_iso_Tor'.hsTau0 R M))
      (Tor_iso_Tor'.hsVanish_zero R M)
    have hcomp : t1 ≫ (Tor_iso_Tor'.hsResK R M).complex.d 1 0
        = -((Tor_iso_Tor'.hsResM R M).complex.d 2 1 ≫ Tor_iso_Tor'.hsTau0 R M) :=
      (Tor_iso_Tor'.hsSC0_exact R M).liftFromProjective_comp _ _
    ⟨t1, by
      simp only [Preadditive.neg_comp, Category.assoc]
      rw [hcomp, Preadditive.comp_neg, ← Category.assoc, HomologicalComplex.d_comp_d]; simp⟩
  | (m + 1) =>
    let prev := Tor_iso_Tor'.hsTauAux M m
    let t := prev.fst
    let t' := (Tor_iso_Tor'.hsSCsucc_exact R M m).liftFromProjective
      (-((Tor_iso_Tor'.hsResM R M).complex.d (m + 3) (m + 2) ≫ t)) prev.snd
    have hcomp : t' ≫ (Tor_iso_Tor'.hsResK R M).complex.d (m + 2) (m + 1)
        = -((Tor_iso_Tor'.hsResM R M).complex.d (m + 3) (m + 2) ≫ t) :=
      (Tor_iso_Tor'.hsSCsucc_exact R M m).liftFromProjective_comp _ _
    ⟨t', by
      simp only [Preadditive.neg_comp, Category.assoc]
      rw [hcomp, Preadditive.comp_neg, ← Category.assoc, HomologicalComplex.d_comp_d]; simp⟩

/-- The connecting maps `τ_n : Q_{n+1}(M) ⟶ Q_n(K)` of the twisted differential, assembled from
the base map `hsTau0` and the inductive construction `hsTauAux`. -/
noncomputable def Tor_iso_Tor'.hsTau (M : ModuleCat.{u} R) : (n : ℕ) →
    ((Tor_iso_Tor'.hsResM R M).complex.X (n + 1) ⟶ (Tor_iso_Tor'.hsResK R M).complex.X n)
  | 0 => Tor_iso_Tor'.hsTau0 R M
  | (n + 1) => (Tor_iso_Tor'.hsTauAux R M n).fst

/-! ### The twisted biproduct complex `Q_•(P₀)` and its augmentation

The middle resolution `Q_n(P₀) := Q_n(K) ⊕ Q_n(M)` is assembled from `hsResK`, `hsResM` and the
connecting maps `hsTau`, with lower-triangular differential
`d^P_n = [[d^K_n, τ_n],[0, d^M_n]]` (`hsDP`) and augmentation
`ε^P = biprod.desc (resK.π.f 0 ≫ ι) s₀` (`hsEpsP`). That `d^P` squares to zero is `hsDP_comp`,
that the augmentation kills the image of `d^P_1` is `hsEpsP_zero`, and that the result really
resolves `P₀` is `hsPiP_quasiIso`. -/

/-- The middle term `Q_n(P₀) := Q_n(K) ⊕ Q_n(M)`. -/
noncomputable def Tor_iso_Tor'.hsXP (M : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  Limits.biprod ((Tor_iso_Tor'.hsResK R M).complex.X n) ((Tor_iso_Tor'.hsResM R M).complex.X n)

/-- The twisted differential `d^P_n = [[d^K_n, τ_n],[0, d^M_n]] : Q_{n+1}(P₀) → Q_n(P₀)`,
acting as `(k, m) ↦ (d^K k + τ_n m, d^M m)`. As a `biprod.desc`/`biprod.lift` matrix:
from the `K`-summand `(k) ↦ (d^K k, 0)`, from the `M`-summand `(m) ↦ (τ_n m, d^M m)`. -/
noncomputable def Tor_iso_Tor'.hsDP (M : ModuleCat.{u} R) (n : ℕ) :
    Tor_iso_Tor'.hsXP R M (n + 1) ⟶ Tor_iso_Tor'.hsXP R M n :=
  Limits.biprod.desc
    (Limits.biprod.lift ((Tor_iso_Tor'.hsResK R M).complex.d (n + 1) n) 0)
    (Limits.biprod.lift (Tor_iso_Tor'.hsTau R M n) ((Tor_iso_Tor'.hsResM R M).complex.d (n + 1) n))

/-- `d^P_{n+1} ≫ d^P_n = 0`: the twisted differential squares to zero. -/
theorem Tor_iso_Tor'.hsDP_comp (M : ModuleCat.{u} R) (n : ℕ) :
    Tor_iso_Tor'.hsDP R M (n + 1) ≫ Tor_iso_Tor'.hsDP R M n = 0 := by
  have hE : Tor_iso_Tor'.hsTau R M (n + 1)
        ≫ (Tor_iso_Tor'.hsResK R M).complex.d (n + 1) n
      = -((Tor_iso_Tor'.hsResM R M).complex.d (n + 2) (n + 1)
          ≫ Tor_iso_Tor'.hsTau R M n) := by
    cases n with
    | zero =>
      show (Tor_iso_Tor'.hsTauAux R M 0).fst ≫ _ = _
      exact (Tor_iso_Tor'.hsSC0_exact R M).liftFromProjective_comp _ _
    | succ m =>
      show (Tor_iso_Tor'.hsTauAux R M (m + 1)).fst ≫ _ = _
      exact (Tor_iso_Tor'.hsSCsucc_exact R M m).liftFromProjective_comp _ _
  apply Limits.biprod.hom_ext' <;>
    apply Limits.biprod.hom_ext <;>
    simp only [Tor_iso_Tor'.hsDP, Limits.biprod.inl_desc_assoc,
      Limits.biprod.inr_desc_assoc, Limits.biprod.lift_desc_assoc,
      Preadditive.add_comp, Category.assoc, Limits.biprod.lift_fst,
      Limits.biprod.lift_snd, Limits.zero_comp, Limits.comp_zero, add_zero, zero_add]
  · rw [HomologicalComplex.d_comp_d]
  · rw [hE]; abel
  · rw [HomologicalComplex.d_comp_d]

/-- The twisted biproduct complex `Q_•(P₀) = (Q_•(K) ⊕ Q_•(M), d^P)`. -/
noncomputable def Tor_iso_Tor'.hsQP (M : ModuleCat.{u} R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (Tor_iso_Tor'.hsXP R M) (Tor_iso_Tor'.hsDP R M) (Tor_iso_Tor'.hsDP_comp R M)

/-- The augmentation `ε^P = biprod.desc (ε^K ≫ ι) s₀ : Q_0(P₀) → P₀`. -/
noncomputable def Tor_iso_Tor'.hsEpsP (M : ModuleCat.{u} R) :
    Tor_iso_Tor'.hsXP R M 0 ⟶ (Tor_iso_Tor'.syzygySC R M).X₂ :=
  Limits.biprod.desc
    ((Tor_iso_Tor'.hsResK R M).π.f 0 ≫ (Tor_iso_Tor'.syzygySC R M).f)
    (Tor_iso_Tor'.hsS0 R M)

/-- `d^P_1 ≫ ε^P = 0`: the augmentation kills the image of `d^P_1`. -/
theorem Tor_iso_Tor'.hsEpsP_zero (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsQP R M).d 1 0 ≫ Tor_iso_Tor'.hsEpsP R M = 0 := by
  have hd : (Tor_iso_Tor'.hsQP R M).d 1 0 = Tor_iso_Tor'.hsDP R M 0 :=
    ChainComplex.of_d (Tor_iso_Tor'.hsXP R M) (Tor_iso_Tor'.hsDP R M) 0
  rw [hd]
  apply Limits.biprod.hom_ext' <;>
    simp only [Tor_iso_Tor'.hsDP, Tor_iso_Tor'.hsEpsP,
      Limits.biprod.inl_desc_assoc, Limits.biprod.inr_desc_assoc,
      Limits.biprod.lift_desc,
       Limits.zero_comp, Limits.comp_zero,
      add_zero]
  · rw [← Category.assoc, ProjectiveResolution.complex_d_comp_π_f_zero, Limits.zero_comp]
  · show Tor_iso_Tor'.hsTau0 R M ≫ (Tor_iso_Tor'.hsResK R M).π.f 0
        ≫ (Tor_iso_Tor'.syzygySC R M).f
      + (Tor_iso_Tor'.hsResM R M).complex.d 1 0 ≫ Tor_iso_Tor'.hsS0 R M = 0
    rw [show (Tor_iso_Tor'.syzygySC R M).f = Limits.kernel.ι (Projective.π M) from rfl,
      Tor_iso_Tor'.hsTau0_spec, neg_add_cancel]

/-- The augmentation as a chain map `Q_•(P₀) ⟶ (single₀).obj P₀` (via `toSingle₀Equiv`). -/
noncomputable def Tor_iso_Tor'.hsPiP (M : ModuleCat.{u} R) :
    Tor_iso_Tor'.hsQP R M ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj ((Tor_iso_Tor'.syzygySC R
        M).X₂) :=
  ((Tor_iso_Tor'.hsQP R M).toSingle₀Equiv ((Tor_iso_Tor'.syzygySC R M).X₂)).symm
    ⟨Tor_iso_Tor'.hsEpsP R M, Tor_iso_Tor'.hsEpsP_zero R M⟩

open HomologicalComplex HomologicalComplex.HomologySequence Limits CategoryTheory.ComposableArrows
    in
/-- Two-out-of-three for quasi-isomorphisms in a short exact sequence of complexes: if a
morphism of short exact sequences is a quasi-isomorphism on the outer terms, it is one on the
middle. -/
lemma Tor_iso_Tor'.quasiIso_τ₂_of_shortExact {ι : Type} {c : ComplexShape ι}
    {S₁ S₂ : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  have e₁ : ∀ n, IsIso (homologyMap φ.τ₁ n) := by
    intro n; rw [← quasiIsoAt_iff_isIso_homologyMap]; exact (quasiIso_iff _).mp h₁ n
  have e₃ : ∀ n, IsIso (homologyMap φ.τ₃ n) := by
    intro n; rw [← quasiIsoAt_iff_isIso_homologyMap]; exact (quasiIso_iff _).mp h₃ n
  let ψ : (n : ι) → (S₁.map (homologyFunctor _ c n)) ⟶ (S₂.map (homologyFunctor _ c n)) :=
    fun n => (homologyFunctor _ c n).mapShortComplex.map φ
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (homologyMap φ.τ₂ i) := by
    by_cases hk : ∃ k, c.Rel k i
    · obtain ⟨k, hki⟩ := hk
      have i3k := e₃ k
      have i1i := e₁ i
      have i3i := e₃ i
      apply Abelian.mono_of_epi_of_mono_of_mono
        ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ k i hki))
      · exact (composableArrows₅_exact hS₁ k i hki).δ₀.δ₀
      · exact (composableArrows₅_exact hS₂ k i hki).δ₀.δ₀
      · exact (inferInstanceAs (Epi (homologyMap φ.τ₃ k)))
      · exact (inferInstanceAs (Mono (homologyMap φ.τ₁ i)))
      · exact (inferInstanceAs (Mono (homologyMap φ.τ₃ i)))
    · have hf' : Mono (S₂.map (homologyFunctor _ c i)).f := by
        have := hS₂.mono_f
        exact mono_homologyMap_of_mono_of_not_rel S₂.f i (by simpa using hk)
      have i1i := e₁ i
      have i3i := e₃ i
      exact ShortComplex.mono_of_mono_of_mono_of_mono (ψ i)
        (hS₁.homology_exact₂ i) hf' (inferInstanceAs (Mono (homologyMap φ.τ₁ i)))
        (inferInstanceAs (Mono (homologyMap φ.τ₃ i)))
  have hepi : Epi (homologyMap φ.τ₂ i) := by
    by_cases hj : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hj
      have i1i := e₁ i
      have i3i := e₃ i
      have i1j := e₁ j
      apply Abelian.epi_of_epi_of_epi_of_mono
        ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
      · exact (composableArrows₅_exact hS₁ i j hij).δlast.δlast
      · exact (composableArrows₅_exact hS₂ i j hij).δlast.δlast
      · exact (inferInstanceAs (Epi (homologyMap φ.τ₁ i)))
      · exact (inferInstanceAs (Epi (homologyMap φ.τ₃ i)))
      · exact (inferInstanceAs (Mono (homologyMap φ.τ₁ j)))
    · have hg' : Epi (S₁.map (homologyFunctor _ c i)).g := by
        have := hS₁.epi_g
        exact epi_homologyMap_of_epi_of_not_rel S₁.g i (by simpa using hj)
      have i1i := e₁ i
      have i3i := e₃ i
      exact ShortComplex.epi_of_epi_of_epi_of_epi (ψ i)
        (hS₂.homology_exact₂ i) hg' (inferInstanceAs (Epi (homologyMap φ.τ₁ i)))
        (inferInstanceAs (Epi (homologyMap φ.τ₃ i)))
  exact isIso_of_mono_of_epi _

/-- The chain map `α = inl : Q_•(K) ⟶ Q_•(P₀)` (degreewise `biprod.inl`). -/
noncomputable def Tor_iso_Tor'.qiAlpha (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsResK R M).complex ⟶ Tor_iso_Tor'.hsQP R M where
  f n := Limits.biprod.inl
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    simp only [ChainComplex.of_d, Tor_iso_Tor'.hsQP, Tor_iso_Tor'.hsDP]
    apply Limits.biprod.hom_ext <;> simp

/-- The chain map `β = snd : Q_•(P₀) ⟶ Q_•(M)` (degreewise `biprod.snd`). -/
noncomputable def Tor_iso_Tor'.qiBeta (M : ModuleCat.{u} R) :
    Tor_iso_Tor'.hsQP R M ⟶ (Tor_iso_Tor'.hsResM R M).complex where
  f n := Limits.biprod.snd
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    simp only [ChainComplex.of_d, Tor_iso_Tor'.hsQP, Tor_iso_Tor'.hsDP]
    apply Limits.biprod.hom_ext' <;> simp

/-- `α ≫ β = 0` for the biproduct chain maps (degreewise `biprod.inl_snd`). -/
theorem Tor_iso_Tor'.qiComp_zero (M : ModuleCat.{u} R) :
    Tor_iso_Tor'.qiAlpha R M ≫ Tor_iso_Tor'.qiBeta R M = 0 := by
  ext n
  simp [Tor_iso_Tor'.qiAlpha, Tor_iso_Tor'.qiBeta]

/-- The short complex of complexes `Q_•(K) → Q_•(P₀) → Q_•(M)`. -/
noncomputable def Tor_iso_Tor'.qiSC (M : ModuleCat.{u} R) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
  ShortComplex.mk _ _ (Tor_iso_Tor'.qiComp_zero R M)

/-- The short complex `Q_•(K) → Q_•(P₀) → Q_•(M)` is short exact (degreewise split). -/
theorem Tor_iso_Tor'.qiSC_shortExact (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.qiSC R M).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine ShortComplex.shortExact_of_iso ?_
    (ShortComplex.Splitting.ofHasBinaryBiproduct
      ((Tor_iso_Tor'.hsResK R M).complex.X i) ((Tor_iso_Tor'.hsResM R M).complex.X i)).shortExact
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · dsimp [Tor_iso_Tor'.qiSC, Tor_iso_Tor'.qiAlpha, Tor_iso_Tor'.hsXP]; simp
  · dsimp [Tor_iso_Tor'.qiSC, Tor_iso_Tor'.qiBeta, Tor_iso_Tor'.hsXP]; simp

/-- The augmentation `hsPiP` is a quasi-isomorphism, i.e. `Q_•(P₀) → P₀` is a resolution. -/
instance Tor_iso_Tor'.hsPiP_quasiIso (M : ModuleCat.{u} R) :
    QuasiIso (Tor_iso_Tor'.hsPiP R M) := by
  let T : ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
    (Tor_iso_Tor'.syzygySC R M).map (ChainComplex.single₀ (ModuleCat.{u} R))
  have hT : T.ShortExact := (Tor_iso_Tor'.syzygySC_shortExact R M).map_of_exact _
  let φ : Tor_iso_Tor'.qiSC R M ⟶ T :=
    { τ₁ := (Tor_iso_Tor'.hsResK R M).π
      τ₂ := Tor_iso_Tor'.hsPiP R M
      τ₃ := (Tor_iso_Tor'.hsResM R M).π
      comm₁₂ := by
        apply HomologicalComplex.to_single_hom_ext (j := 0)
        simp only [HomologicalComplex.comp_f, Tor_iso_Tor'.hsPiP,
          ChainComplex.toSingle₀Equiv_symm_apply_f_zero, Tor_iso_Tor'.qiSC, Tor_iso_Tor'.qiAlpha,
          Tor_iso_Tor'.hsEpsP, ChainComplex.single₀_map_f_zero, ShortComplex.map_f, T]
        simp
      comm₂₃ := by
        apply HomologicalComplex.to_single_hom_ext (j := 0)
        simp only [HomologicalComplex.comp_f, Tor_iso_Tor'.hsPiP,
          ChainComplex.toSingle₀Equiv_symm_apply_f_zero, Tor_iso_Tor'.qiSC, Tor_iso_Tor'.qiBeta,
          Tor_iso_Tor'.hsEpsP, ChainComplex.single₀_map_f_zero, ShortComplex.map_g, T]
        apply Limits.biprod.hom_ext'
        · simp [Tor_iso_Tor'.syzygySC]
        · simp only [Tor_iso_Tor'.syzygySC, Limits.biprod.inr_desc_assoc,
            Limits.biprod.inr_snd_assoc]
          exact Tor_iso_Tor'.hsS0_spec R M }
  have h₁ : QuasiIso φ.τ₁ := (Tor_iso_Tor'.hsResK R M).quasiIso
  have h₃ : QuasiIso φ.τ₃ := (Tor_iso_Tor'.hsResM R M).quasiIso
  have := Tor_iso_Tor'.quasiIso_τ₂_of_shortExact (R := R) (φ := φ)
    (Tor_iso_Tor'.qiSC_shortExact R M) hT h₁ h₃
  exact this

/-- The twisted biproduct resolution `Q_•(P₀) → P₀` as a `ProjectiveResolution`. -/
noncomputable def Tor_iso_Tor'.hsResP (M : ModuleCat.{u} R) :
    ProjectiveResolution ((Tor_iso_Tor'.syzygySC R M).X₂) where
  complex := Tor_iso_Tor'.hsQP R M
  projective n := by
    dsimp [Tor_iso_Tor'.hsQP, ChainComplex.of, Tor_iso_Tor'.hsXP]
    infer_instance
  π := Tor_iso_Tor'.hsPiP R M

/-- The split chain map `α = inl : Q_•(K) → Q_•(P₀)`. -/
noncomputable def Tor_iso_Tor'.hsAlpha (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsResK R M).complex ⟶ (Tor_iso_Tor'.hsResP R M).complex :=
  Tor_iso_Tor'.qiAlpha R M

/-- The split chain map `β = snd : Q_•(P₀) → Q_•(M)`. -/
noncomputable def Tor_iso_Tor'.hsBeta (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsResP R M).complex ⟶ (Tor_iso_Tor'.hsResM R M).complex :=
  Tor_iso_Tor'.qiBeta R M

/-- `α ≫ β = 0` for the split chain maps. -/
theorem Tor_iso_Tor'.hsComp_zero (M : ModuleCat.{u} R) :
    Tor_iso_Tor'.hsAlpha R M ≫ Tor_iso_Tor'.hsBeta R M = 0 := by
  ext n
  simp [Tor_iso_Tor'.hsAlpha, Tor_iso_Tor'.hsBeta, Tor_iso_Tor'.qiAlpha, Tor_iso_Tor'.qiBeta]

/-- The degreewise splitting of `Q_n(K) → Q_n(P₀) → Q_n(M)`. -/
noncomputable def Tor_iso_Tor'.hsSplit (M : ModuleCat.{u} R) (i : ℕ) :
    ((ShortComplex.mk _ _ (Tor_iso_Tor'.hsComp_zero R M)).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) i)).Splitting :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct
    ((Tor_iso_Tor'.hsResK R M).complex.X i) ((Tor_iso_Tor'.hsResM R M).complex.X i)).ofIso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by dsimp [Tor_iso_Tor'.hsAlpha, Tor_iso_Tor'.qiAlpha]; simp)
      (by dsimp [Tor_iso_Tor'.hsBeta, Tor_iso_Tor'.qiBeta]; simp)).symm

/-- Compatibility of the augmentations with the syzygy inclusion `K ↪ P₀`. -/
theorem Tor_iso_Tor'.hsComm_alpha (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsAlpha R M).f 0 ≫ (Tor_iso_Tor'.hsResP R M).π.f 0
      = (Tor_iso_Tor'.hsResK R M).π.f 0 ≫ (Tor_iso_Tor'.syzygySC R M).f := by
  simp only [Tor_iso_Tor'.hsAlpha, Tor_iso_Tor'.qiAlpha, Tor_iso_Tor'.hsResP,
    Tor_iso_Tor'.hsPiP, ChainComplex.toSingle₀Equiv_symm_apply_f_zero, Tor_iso_Tor'.hsEpsP,
    Limits.biprod.inl_desc]

/-- Compatibility of the augmentations with the syzygy projection `P₀ ↠ M`. -/
theorem Tor_iso_Tor'.hsComm_beta (M : ModuleCat.{u} R) :
    (Tor_iso_Tor'.hsBeta R M).f 0 ≫ (Tor_iso_Tor'.hsResM R M).π.f 0
      = (Tor_iso_Tor'.hsResP R M).π.f 0 ≫ (Tor_iso_Tor'.syzygySC R M).g := by
  simp only [Tor_iso_Tor'.hsBeta, Tor_iso_Tor'.qiBeta, Tor_iso_Tor'.hsResP,
    Tor_iso_Tor'.hsPiP, ChainComplex.toSingle₀Equiv_symm_apply_f_zero, Tor_iso_Tor'.hsEpsP]
  apply Limits.biprod.hom_ext'
  · simp [Tor_iso_Tor'.syzygySC]
  · simp only [Tor_iso_Tor'.syzygySC, Limits.biprod.inr_desc_assoc,
      Limits.biprod.inr_snd_assoc]
    exact (Tor_iso_Tor'.hsS0_spec R M).symm

/-- The output of the horseshoe lemma (Weibel 2.2.8) for the syzygy short exact sequence
`0 → K → P₀ → M → 0`: projective resolutions of `K`, of `P₀` and of `M`, together with a
degreewise *split* short exact sequence of their underlying complexes whose augmentations are
compatible with the maps of the syzygy sequence. -/
structure Tor_iso_Tor'.Horseshoe (M : ModuleCat.{u} R) where
  /-- Projective resolution of the syzygy `K = kernel (Projective.π M)`. -/
  resK : ProjectiveResolution (Tor_iso_Tor'.syzygy R M)
  /-- Projective resolution of `P₀ = Projective.over M` (can be `P₀[0]`). -/
  resP : ProjectiveResolution ((Tor_iso_Tor'.syzygySC R M).X₂)
  /-- Projective resolution of `M`. -/
  resM : ProjectiveResolution M
  /-- The chain map `Q_•(K) → Q_•(P₀)` of complexes (lifting the inclusion `K ↪ P₀`). -/
  α : resK.complex ⟶ resP.complex
  /-- The chain map `Q_•(P₀) → Q_•(M)` of complexes (lifting `P₀ ↠ M`). -/
  β : resP.complex ⟶ resM.complex
  /-- The composite `α ≫ β` vanishes, so `Q_•(K) → Q_•(P₀) → Q_•(M)` is a short complex. -/
  comp_zero : α ≫ β = 0
  /-- In each degree the short complex is split. -/
  splitSES : ∀ i, ((ShortComplex.mk α β comp_zero).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) i)).Splitting
  /-- The augmentations are compatible with the syzygy inclusion `K ↪ P₀`. -/
  comm_α : α.f 0 ≫ resP.π.f 0 = resK.π.f 0 ≫ (Tor_iso_Tor'.syzygySC R M).f
  /-- The augmentations are compatible with the syzygy projection `P₀ ↠ M`. -/
  comm_β : β.f 0 ≫ resM.π.f 0 = resP.π.f 0 ≫ (Tor_iso_Tor'.syzygySC R M).g

/-- The horseshoe lemma (Weibel 2.2.8) for the syzygy short exact sequence
`0 → K → P₀ → M → 0`: a degreewise split short exact sequence of projective resolutions
lifting it, with `Q_n(P₀) := Q_n(K) ⊕ Q_n(M)` and lower-triangular differential
`d^P_n = [[d^K_n, τ_n],[0, d^M_n]]`. -/
noncomputable def Tor_iso_Tor'.horseshoe (M : ModuleCat.{u} R) :
    Tor_iso_Tor'.Horseshoe R M where
  resK := Tor_iso_Tor'.hsResK R M
  resP := Tor_iso_Tor'.hsResP R M
  resM := Tor_iso_Tor'.hsResM R M
  α := Tor_iso_Tor'.hsAlpha R M
  β := Tor_iso_Tor'.hsBeta R M
  comp_zero := Tor_iso_Tor'.hsComp_zero R M
  splitSES := Tor_iso_Tor'.hsSplit R M
  comm_α := Tor_iso_Tor'.hsComm_alpha R M
  comm_β := Tor_iso_Tor'.hsComm_beta R M

section tor'LESAux
open CategoryTheory.Limits MonoidalCategory CategoryTheory.ShortComplex

/-- The horseshoe short complex of projective resolutions `Q_•(K) → Q_•(P₀) → Q_•(M)`, split in
each degree and hence short exact and preserved by any additive functor. -/
noncomputable def Tor_iso_Tor'.hsSCcplx (M : ModuleCat.{u} R) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
  ShortComplex.mk (Tor_iso_Tor'.horseshoe R M).α (Tor_iso_Tor'.horseshoe R M).β
    (Tor_iso_Tor'.horseshoe R M).comp_zero

/-- Applying `tensorRight N` degreewise to the horseshoe sequence of complexes again gives a
short exact sequence of complexes, since each degree is split. -/
theorem Tor_iso_Tor'.tor'LES_ses (M N : ModuleCat.{u} R) :
    ((Tor_iso_Tor'.hsSCcplx R M).map
      ((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
    (((Tor_iso_Tor'.horseshoe R M).splitSES i).map (tensorRight N)).shortExact

end tor'LESAux

/-! ### The `Tor'` long exact sequence for a short exact sequence of objects

`Tor'` derives the *first* variable, so its long exact sequence for a short exact sequence of
objects comes from the horseshoe:

* the horseshoe gives a degreewise split short exact sequence of projective resolutions
  `0 → Q_•(K) → Q_•(P₀) → Q_•(M) → 0` lifting the syzygy sequence, with
  `Q_n(P₀) = Q_n(K) ⊕ Q_n(M)`; being split, each degree stays short exact under any functor;
* applying `tensorRight N` degreewise therefore gives a short exact sequence of complexes;
* its homology long exact sequence transports to `Tor'` along
  `ProjectiveResolution.isoLeftDerivedObj`, naturally in `N` by `SnakeInput.naturality_δ`, with
  the degree-zero identification `Tor'_0(X, -) = X ⊗ -` supplied by
  `Functor.leftDerivedZeroIsoSelf (tensorRight N)`.
-/

/-! ### Degree one on the `Tor'` side

`(Tor' C 1).obj M ≅ oneKer M`, natural in `N`, is read off the bottom of the homology long exact
sequence of the tensored horseshoe sequence `tor'LES_ses R M N`, whose terms are
`X₁ = Q_•(K)⊗N`, `X₂ = Q_•(P₀)⊗N` and `X₃ = Q_•(M)⊗N`:

* `((Tor' C 1).obj M).obj N = H_1(Q_•(M)⊗N) = H_1(X₃)` by `isoLeftDerivedObj (tensorRight N)`
  applied to `resM`;
* `H_1(X₂) = Tor'_1(P₀, N) = 0` by `isZero_Tor'_succ_of_projective`, so the connecting map
  `δ : H_1(X₃) → H_0(X₁)` is a monomorphism and `homology_exact₁` exhibits
  `H_1(X₃) ≅ ker (homologyMap X.f 0)`;
* `homologyMap (hsSCcplx).f 0 : H_0(X₁) → H_0(X₂)` is the map `K ⊗ N ⟶ P₀ ⊗ N` defining
  `oneKer M`, by `leftDerivedZeroIsoSelf (tensorRight N)` on `resK` and `resP` together with the
  augmentation compatibility `comm_α`; `kernel.mapIso` then transports the kernel onto
  `(oneKer M).obj N`.

Because the degree-zero identifications `Tor'₀(K, -) = K ⊗ -` and `Tor'₀(P₀, -) = P₀ ⊗ -` agree
with the `Tor`-side ones, both sides land on the same functor `oneKer M`.
-/
section oneIsoTor'KerAux
open CategoryTheory.Limits MonoidalCategory CategoryTheory.ShortComplex

/-- The tensored horseshoe short complex of complexes, as a function of `N`. -/
noncomputable def Tor_iso_Tor'.oneIso_S (M N : ModuleCat.{u} R) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :=
  (Tor_iso_Tor'.hsSCcplx R M).map
    ((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ))

/-- `e1`: `Tor'_1(M,N) ≅ H_1(X₃)`. -/
noncomputable def Tor_iso_Tor'.oneIso_e1 (M N : ModuleCat.{u} R) :
    ((Tor' (ModuleCat.{u} R) 1).obj M).obj N ≅ (Tor_iso_Tor'.oneIso_S R M N).X₃.homology 1 :=
  (Tor_iso_Tor'.horseshoe R M).resM.isoLeftDerivedObj (tensorRight N) 1

/-- The middle complex of the tensored horseshoe has vanishing homology in positive degrees. -/
private theorem Tor_iso_Tor'.oneIso_S_X₂_isZero (M N : ModuleCat.{u} R) (m : ℕ) :
    Limits.IsZero ((Tor_iso_Tor'.oneIso_S R M N).X₂.homology (m + 1)) := by
  have : Projective ((Tor_iso_Tor'.syzygySC R M).X₂) := by
    dsimp [Tor_iso_Tor'.syzygySC]; exact Projective.projective_over M
  have hz := isZero_Tor'_succ_of_projective (ModuleCat.{u} R)
    ((Tor_iso_Tor'.syzygySC R M).X₂) N m
  exact Limits.IsZero.of_iso hz
    ((Tor_iso_Tor'.horseshoe R M).resP.isoLeftDerivedObj (tensorRight N) (m + 1)).symm

/-- The middle complex of the tensored horseshoe has vanishing degree-1 homology. -/
theorem Tor_iso_Tor'.oneIso_hP (M N : ModuleCat.{u} R) :
    Limits.IsZero ((Tor_iso_Tor'.oneIso_S R M N).X₂.homology 1) :=
  Tor_iso_Tor'.oneIso_S_X₂_isZero R M N 0

/-- `e3`: `H_1(X₃) ≅ kernel (homologyMap S.f 0)`. -/
noncomputable def Tor_iso_Tor'.oneIso_e3 (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIso_S R M N).X₃.homology 1 ≅
      Limits.kernel (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0) :=
  haveI hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  haveI hmono : Mono ((Tor_iso_Tor'.tor'LES_ses R M N).δ 1 0 hrel) :=
    (Tor_iso_Tor'.tor'LES_ses R M N).mono_δ 1 0 hrel (Tor_iso_Tor'.oneIso_hP R M N)
  IsLimit.conePointUniqueUpToIso
    ((Tor_iso_Tor'.tor'LES_ses R M N).homology_exact₁ 1 0 hrel).fIsKernel
    (Limits.limit.isLimit _)

/-- The degree-0 comparison `p : H_0(X₁) ≅ K ⊗ N`. -/
noncomputable def Tor_iso_Tor'.oneIso_p (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIso_S R M N).X₁.homology 0 ≅ (tensorRight N).obj (Tor_iso_Tor'.syzygy R M) :=
  ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) 0).symm ≪≫
    (Functor.leftDerivedZeroIsoSelf (tensorRight N)).app (Tor_iso_Tor'.syzygy R M)

/-- The degree-0 comparison `q : H_0(X₂) ≅ P₀ ⊗ N`. -/
noncomputable def Tor_iso_Tor'.oneIso_q (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIso_S R M N).X₂.homology 0 ≅
      (tensorRight N).obj ((Tor_iso_Tor'.syzygySC R M).X₂) :=
  ((Tor_iso_Tor'.horseshoe R M).resP.isoLeftDerivedObj (tensorRight N) 0).symm ≪≫
    (Functor.leftDerivedZeroIsoSelf (tensorRight N)).app ((Tor_iso_Tor'.syzygySC R M).X₂)

/-- The `oneKer` defining map at `N`. -/
noncomputable def Tor_iso_Tor'.oneIso_κ (M N : ModuleCat.{u} R) :
    (tensorRight N).obj (Tor_iso_Tor'.syzygy R M) ⟶
      (tensorRight N).obj ((Tor_iso_Tor'.syzygySC R M).X₂) :=
  ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M))).app N

/-- The comm square identifying `homologyMap S.f 0` with `κ`. -/
theorem Tor_iso_Tor'.oneIso_hsq (M N : ModuleCat.{u} R) :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0 ≫ (Tor_iso_Tor'.oneIso_q R M
        N).hom
      = (Tor_iso_Tor'.oneIso_p R M N).hom ≫ Tor_iso_Tor'.oneIso_κ R M N := by
  show HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0 ≫
      ((Tor_iso_Tor'.horseshoe R M).resP.isoLeftDerivedObj (tensorRight N) 0).inv ≫
        (Functor.leftDerivedZeroIsoSelf (tensorRight N)).hom.app ((Tor_iso_Tor'.syzygySC R M).X₂)
    = (((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) 0).inv ≫
        (Functor.leftDerivedZeroIsoSelf (tensorRight N)).hom.app (Tor_iso_Tor'.syzygy R M)) ≫
        Tor_iso_Tor'.oneIso_κ R M N
  have hnat := ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    (Limits.kernel.ι (Projective.π M))
    (Tor_iso_Tor'.horseshoe R M).resK (Tor_iso_Tor'.horseshoe R M).resP
    (Tor_iso_Tor'.horseshoe R M).α (Tor_iso_Tor'.horseshoe R M).comm_α (tensorRight N) 0
  have hldz := (Functor.leftDerivedZeroIsoSelf (tensorRight N)).hom.naturality
    (Limits.kernel.ι (Projective.π M))
  have hSf : HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0
      = ((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map
          (Tor_iso_Tor'.horseshoe R M).α := rfl
  have hnat' : ((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).map
          (Tor_iso_Tor'.horseshoe R M).α
        ≫ ((Tor_iso_Tor'.horseshoe R M).resP.isoLeftDerivedObj (tensorRight N) 0).inv
      = ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) 0).inv
        ≫ ((tensorRight N).leftDerived 0).map (Limits.kernel.ι (Projective.π M)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hnat, Iso.inv_hom_id_assoc]
  rw [hSf, ← Category.assoc, hnat', Category.assoc]
  exact congrArg (((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) 0).inv ≫ ·)
      hldz

/-- `e4`: `kernel (homologyMap S.f 0) ≅ kernel κ`. -/
noncomputable def Tor_iso_Tor'.oneIso_e4 (M N : ModuleCat.{u} R) :
    Limits.kernel (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0) ≅
      Limits.kernel (Tor_iso_Tor'.oneIso_κ R M N) :=
  Limits.kernel.mapIso (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0)
    (Tor_iso_Tor'.oneIso_κ R M N) (Tor_iso_Tor'.oneIso_p R M N) (Tor_iso_Tor'.oneIso_q R M N)
    (Tor_iso_Tor'.oneIso_hsq R M N)

/-- `e5`: `kernel κ ≅ (oneKer M).obj N`. -/
noncomputable def Tor_iso_Tor'.oneIso_e5 (M N : ModuleCat.{u} R) :
    Limits.kernel (Tor_iso_Tor'.oneIso_κ R M N) ≅ (Tor_iso_Tor'.oneKer R M).obj N :=
  (PreservesKernel.iso ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj N)
    ((tensoringLeft (ModuleCat.{u} R)).map (Limits.kernel.ι (Projective.π M)))).symm

/-- The per-`N` component of `oneIso_tor'Ker`, assembled from the four steps. -/
@[ega "IV 11.2.3" "Tor₁(M, special case"]
noncomputable def Tor_iso_Tor'.oneIso_tor'Ker_comp (M N : ModuleCat.{u} R) :
    ((Tor' (ModuleCat.{u} R) 1).obj M).obj N ≅ (Tor_iso_Tor'.oneKer R M).obj N :=
  Tor_iso_Tor'.oneIso_e1 R M N ≪≫ Tor_iso_Tor'.oneIso_e3 R M N ≪≫
    Tor_iso_Tor'.oneIso_e4 R M N ≪≫ Tor_iso_Tor'.oneIso_e5 R M N

/-- The morphism of short complexes of complexes `S(N) ⟶ S(N')` induced by `g`. -/
noncomputable def Tor_iso_Tor'.oneIso_φ (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (g : N ⟶ N')
    :
    Tor_iso_Tor'.oneIso_S R M N ⟶ Tor_iso_Tor'.oneIso_S R M N' :=
  (Tor_iso_Tor'.hsSCcplx R M).mapNatTrans
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map g)
      (ComplexShape.down ℕ))

/-- Naturality in `N` of the transport `isoLeftDerivedObj` of `Tor'_n(X, -)` along a projective
resolution of `X`. -/
private theorem Tor_iso_Tor'.tor'_map_comp_isoLeftDerivedObj_hom {X : ModuleCat.{u} R}
    (P : ProjectiveResolution X) (n : ℕ) {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor' (ModuleCat.{u} R) n).obj X).map g ≫ (P.isoLeftDerivedObj (tensorRight N') n).hom
      = (P.isoLeftDerivedObj (tensorRight N) n).hom ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map g)
          (ComplexShape.down ℕ)).app P.complex) n := by
  rw [show ((Tor' (ModuleCat.{u} R) n).obj X).map g
        = (NatTrans.leftDerived ((tensoringRight (ModuleCat.{u} R)).map g) n).app X from rfl,
    ProjectiveResolution.leftDerived_app_eq ((tensoringRight (ModuleCat.{u} R)).map g) P n,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Naturality in `N` of the comparison `e1 : Tor'_1(M, N) ≅ H_1(Q_•(M) ⊗ N)`. -/
theorem Tor_iso_Tor'.oneIso_e1_naturality (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor' (ModuleCat.{u} R) 1).obj M).map g ≫ (Tor_iso_Tor'.oneIso_e1 R M N').hom
      = (Tor_iso_Tor'.oneIso_e1 R M N).hom ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₃ 1 :=
  Tor_iso_Tor'.tor'_map_comp_isoLeftDerivedObj_hom R (Tor_iso_Tor'.horseshoe R M).resM 1 g

/-- `S(N)` is short exact. -/
theorem Tor_iso_Tor'.oneIso_S_shortExact (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIso_S R M N).ShortExact :=
  Tor_iso_Tor'.tor'LES_ses R M N

/-- `e3` characterization: `e3.hom ≫ kernel.ι = δ`. -/
theorem Tor_iso_Tor'.oneIso_e3_hom_ι (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIso_e3 R M N).hom ≫
        Limits.kernel.ι (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0)
      = (Tor_iso_Tor'.oneIso_S_shortExact R M N).δ 1 0 (by simp [ComplexShape.down_Rel]) := by
  dsimp only [Tor_iso_Tor'.oneIso_e3, Tor_iso_Tor'.oneIso_S_shortExact]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ (Limits.limit.isLimit _) WalkingParallelPair.zero

/-- Commutativity of the degree-0 homology square induced by `g`. -/
theorem Tor_iso_Tor'.oneIso_kerComm (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0 ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₂ 0
      = HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₁ 0 ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N').f 0 := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  exact (Tor_iso_Tor'.oneIso_φ R M g).comm₁₂.symm

/-- `e3` naturality square. -/
@[reassoc]
theorem Tor_iso_Tor'.oneIso_e3_naturality (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₃ 1 ≫
        (Tor_iso_Tor'.oneIso_e3 R M N').hom
      = (Tor_iso_Tor'.oneIso_e3 R M N).hom ≫
        Limits.kernel.map _ _ (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₁ 0)
          (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₂ 0)
          (Tor_iso_Tor'.oneIso_kerComm R M g) := by
  apply (cancel_mono (Limits.kernel.ι
    (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N').f 0))).mp
  rw [Category.assoc, Category.assoc, Tor_iso_Tor'.oneIso_e3_hom_ι,
    Limits.kernel.lift_ι, ← Category.assoc, Tor_iso_Tor'.oneIso_e3_hom_ι]
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down_Rel]
  exact (HomologicalComplex.HomologySequence.δ_naturality (Tor_iso_Tor'.oneIso_φ R M g)
    (Tor_iso_Tor'.oneIso_S_shortExact R M N) (Tor_iso_Tor'.oneIso_S_shortExact R M N') 1 0
        hrel).symm

/-- `e5` compatibility with `kernel.ι`. -/
@[reassoc]
theorem Tor_iso_Tor'.oneIso_e5_hom_ι (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIso_e5 R M N).hom ≫ (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).app N
      = Limits.kernel.ι (Tor_iso_Tor'.oneIso_κ R M N) := by
  dsimp only [Tor_iso_Tor'.oneIso_e5]
  exact PreservesKernel.iso_inv_ι ((evaluation (ModuleCat.{u} R) (ModuleCat.{u} R)).obj N)
    (Tor_iso_Tor'.oneIsoTK_η R M)

/-- Naturality of the degree-0 comparison `p`. -/
theorem Tor_iso_Tor'.oneIso_p_naturality (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (g : N ⟶
    N') :
    HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₁ 0 ≫
        (Tor_iso_Tor'.oneIso_p R M N').hom
      = (Tor_iso_Tor'.oneIso_p R M N).hom ≫
        ((tensoringLeft (ModuleCat.{u} R)).obj (Tor_iso_Tor'.syzygy R M)).map g := by
  have hτ₁ : HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₁ 0
      = ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) 0).inv ≫
          (NatTrans.leftDerived ((tensoringRight (ModuleCat.{u} R)).map g) 0).app
            (Tor_iso_Tor'.syzygy R M) ≫
          ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N') 0).hom := by
    have h := ProjectiveResolution.leftDerived_app_eq ((tensoringRight (ModuleCat.{u} R)).map g)
      (Tor_iso_Tor'.horseshoe R M).resK 0 (X := Tor_iso_Tor'.syzygy R M)
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  dsimp only [Tor_iso_Tor'.oneIso_p]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.leftDerivedZeroIsoSelf_hom,
    Category.assoc]
  rw [hτ₁]
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
  have hfd := Tor_iso_Tor'.fromLeftDerivedZero_natTrans ((tensoringRight (ModuleCat.{u} R)).map g)
  have hfd' := congrArg (fun t => NatTrans.app t (Tor_iso_Tor'.syzygy R M)) hfd
  simp only [NatTrans.comp_app] at hfd'
  rw [hfd']
  rfl

/-- `e4` compatibility with `kernel.ι`. -/
@[reassoc]
theorem Tor_iso_Tor'.oneIso_e4_hom_ι (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIso_e4 R M N).hom ≫ Limits.kernel.ι (Tor_iso_Tor'.oneIso_κ R M N)
      = Limits.kernel.ι (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_S R M N).f 0) ≫
        (Tor_iso_Tor'.oneIso_p R M N).hom := by
  dsimp only [Tor_iso_Tor'.oneIso_e4, Limits.kernel.mapIso]
  exact Limits.kernel.lift_ι _ _ _

/-- The combined `e4 ≫ e5` naturality square. -/
theorem Tor_iso_Tor'.oneIso_e45_naturality (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') :
    Limits.kernel.map _ _ (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₁ 0)
          (HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₂ 0)
          (Tor_iso_Tor'.oneIso_kerComm R M g) ≫
        ((Tor_iso_Tor'.oneIso_e4 R M N').hom ≫ (Tor_iso_Tor'.oneIso_e5 R M N').hom)
      = ((Tor_iso_Tor'.oneIso_e4 R M N).hom ≫ (Tor_iso_Tor'.oneIso_e5 R M N).hom) ≫
        (Tor_iso_Tor'.oneKer R M).map g := by
  apply (cancel_mono ((Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).app N')).mp
  have hιnat : (Tor_iso_Tor'.oneKer R M).map g ≫ (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).app
      N'
      = (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).app N ≫
        ((tensoringLeft (ModuleCat.{u} R)).obj (Tor_iso_Tor'.syzygy R M)).map g :=
    (Limits.kernel.ι (Tor_iso_Tor'.oneIsoTK_η R M)).naturality g
  simp only [Category.assoc]
  rw [hιnat]
  simp only [Tor_iso_Tor'.oneIso_e5_hom_ι_assoc, Tor_iso_Tor'.oneIso_e5_hom_ι,
    Tor_iso_Tor'.oneIso_e4_hom_ι_assoc, Tor_iso_Tor'.oneIso_e4_hom_ι]
  rw [← Category.assoc, Limits.kernel.lift_ι]
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneIso_p_naturality R M g]

/-- Naturality in `N` of the composite comparison `Tor'_1(M, N) ≅ (oneKer M).obj N`. -/
theorem Tor_iso_Tor'.oneIso_tor'Ker_comp_naturality (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor' (ModuleCat.{u} R) 1).obj M).map g ≫ (Tor_iso_Tor'.oneIso_tor'Ker_comp R M N').hom
      = (Tor_iso_Tor'.oneIso_tor'Ker_comp R M N).hom ≫ (Tor_iso_Tor'.oneKer R M).map g := by
  simp only [Tor_iso_Tor'.oneIso_tor'Ker_comp, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc (((Tor' (ModuleCat.{u} R) 1).obj M).map g),
    Tor_iso_Tor'.oneIso_e1_naturality]
  simp only [Category.assoc]
  rw [Tor_iso_Tor'.oneIso_e3_naturality_assoc, Tor_iso_Tor'.oneIso_e45_naturality]
  simp only [Category.assoc]

end oneIsoTor'KerAux

/-- `Tor'`-side kernel description: `(Tor' C 1).obj M ≅ oneKer M`, natural in `N`. -/
@[ega "IV 11.2.3" "Tor₁(M, special case"]
noncomputable def Tor_iso_Tor'.oneIso_tor'Ker (M : ModuleCat.{u} R) :
    (Tor' (ModuleCat.{u} R) 1).obj M ≅ Tor_iso_Tor'.oneKer R M :=
  NatIso.ofComponents (fun N => Tor_iso_Tor'.oneIso_tor'Ker_comp R M N)
    (fun g => Tor_iso_Tor'.oneIso_tor'Ker_comp_naturality R M g)

/-- The degree-one balancing isomorphism `(Tor C 1).obj M ≅ (Tor' C 1).obj M`, natural in `N`,
through the common kernel functor `oneKer M`. -/
noncomputable def Tor_iso_Tor'.oneIso (M : ModuleCat.{u} R) :
    (Tor (ModuleCat.{u} R) 1).obj M ≅ (Tor' (ModuleCat.{u} R) 1).obj M :=
  Tor_iso_Tor'.oneIso_torKer R M ≪≫ (Tor_iso_Tor'.oneIso_tor'Ker R M).symm

section tor'ShiftAux
open CategoryTheory.Limits MonoidalCategory

/-- The middle complex `X₂ = Q_•(P₀)⊗N` of the tensored horseshoe sequence has vanishing homology
in every positive degree. -/
theorem Tor_iso_Tor'.tor'Shift_hX₂ (M N : ModuleCat.{u} R) (m : ℕ) :
    Limits.IsZero ((Tor_iso_Tor'.oneIso_S R M N).X₂.homology (m + 1)) :=
  Tor_iso_Tor'.oneIso_S_X₂_isZero R M N m

/-- The connecting δ-iso for `tor'Shift` at degrees `(j+2, j+1)`: both flanking middle
homologies vanish. -/
noncomputable def Tor_iso_Tor'.tor'Shift_δIso (j : ℕ) (M N : ModuleCat.{u} R) :
    (Tor_iso_Tor'.oneIso_S R M N).X₃.homology (j + 2) ≅
      (Tor_iso_Tor'.oneIso_S R M N).X₁.homology (j + 1) :=
  (Tor_iso_Tor'.oneIso_S_shortExact R M N).δIso (j + 2) (j + 1)
    (by simp [ComplexShape.down_Rel])
    (Tor_iso_Tor'.tor'Shift_hX₂ R M N (j + 1))
    (Tor_iso_Tor'.tor'Shift_hX₂ R M N j)

/-- The per-`N` component of `tor'Shift`: `Tor'_{j+2}(M,N) ≅ Tor'_{j+1}(K,N)`. -/
noncomputable def Tor_iso_Tor'.tor'Shift_comp (j : ℕ) (M N : ModuleCat.{u} R) :
    ((Tor' (ModuleCat.{u} R) (j + 2)).obj M).obj N
      ≅ ((Tor' (ModuleCat.{u} R) (j + 1)).obj (Tor_iso_Tor'.syzygy R M)).obj N :=
  ((Tor_iso_Tor'.horseshoe R M).resM.isoLeftDerivedObj (tensorRight N) (j + 2)) ≪≫
    Tor_iso_Tor'.tor'Shift_δIso R j M N ≪≫
    ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) (j + 1)).symm

/-- Naturality at degree `n` of the `resM` transport. -/
theorem Tor_iso_Tor'.tor'Shift_e1_naturality (M : ModuleCat.{u} R) (n : ℕ)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor' (ModuleCat.{u} R) n).obj M).map g ≫
        ((Tor_iso_Tor'.horseshoe R M).resM.isoLeftDerivedObj (tensorRight N') n).hom
      = ((Tor_iso_Tor'.horseshoe R M).resM.isoLeftDerivedObj (tensorRight N) n).hom ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₃ n :=
  Tor_iso_Tor'.tor'_map_comp_isoLeftDerivedObj_hom R (Tor_iso_Tor'.horseshoe R M).resM n g

/-- Naturality at degree `n` of the `resK` transport (the `X₁` = `Q(K)⊗N` side). -/
theorem Tor_iso_Tor'.tor'Shift_eK_naturality (M : ModuleCat.{u} R) (n : ℕ)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor' (ModuleCat.{u} R) n).obj (Tor_iso_Tor'.syzygy R M)).map g ≫
        ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N') n).hom
      = ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) n).hom ≫
        HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₁ n :=
  Tor_iso_Tor'.tor'_map_comp_isoLeftDerivedObj_hom R (Tor_iso_Tor'.horseshoe R M).resK n g

/-- Naturality in `N` of `tor'Shift_comp`. -/
theorem Tor_iso_Tor'.tor'Shift_comp_naturality (j : ℕ) (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((Tor' (ModuleCat.{u} R) (j + 2)).obj M).map g ≫ (Tor_iso_Tor'.tor'Shift_comp R j M N').hom
      = (Tor_iso_Tor'.tor'Shift_comp R j M N).hom ≫
        ((Tor' (ModuleCat.{u} R) (j + 1)).obj (Tor_iso_Tor'.syzygy R M)).map g := by
  simp only [Tor_iso_Tor'.tor'Shift_comp, Tor_iso_Tor'.tor'Shift_δIso, Iso.trans_hom, Iso.symm_hom,
    ShortComplex.ShortExact.δIso, asIso_hom, Category.assoc]
  have hrel : (ComplexShape.down ℕ).Rel (j + 2) (j + 1) := by simp [ComplexShape.down_Rel]
  have hδ := HomologicalComplex.HomologySequence.δ_naturality (Tor_iso_Tor'.oneIso_φ R M g)
    (Tor_iso_Tor'.oneIso_S_shortExact R M N) (Tor_iso_Tor'.oneIso_S_shortExact R M N')
    (j + 2) (j + 1) hrel
  have hK := Tor_iso_Tor'.tor'Shift_eK_naturality R M (j + 1) g
  have hKinv : HomologicalComplex.homologyMap (Tor_iso_Tor'.oneIso_φ R M g).τ₁ (j + 1) ≫
        ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N') (j + 1)).inv
      = ((Tor_iso_Tor'.horseshoe R M).resK.isoLeftDerivedObj (tensorRight N) (j + 1)).inv ≫
        ((Tor' (ModuleCat.{u} R) (j + 1)).obj (Tor_iso_Tor'.syzygy R M)).map g := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, hK]
  have hM := Tor_iso_Tor'.tor'Shift_e1_naturality R M (j + 2) g
  rw [← Category.assoc (((Tor' (ModuleCat.{u} R) (j + 2)).obj M).map g), hM]
  rw [Category.assoc]
  congr 1
  rw [← Category.assoc, ← hδ, Category.assoc, hKinv]

end tor'ShiftAux

/-- The dimension shift `(Tor' C (j+2)).obj M ≅ (Tor' C (j+1)).obj K` for `Tor'`, natural in
`N`, where `K = Tor_iso_Tor'.syzygy M`. -/
noncomputable def Tor_iso_Tor'.tor'Shift (j : ℕ) (M : ModuleCat.{u} R) :
    (Tor' (ModuleCat.{u} R) (j + 2)).obj M
      ≅ (Tor' (ModuleCat.{u} R) (j + 1)).obj (Tor_iso_Tor'.syzygy R M) :=
  NatIso.ofComponents (fun N => Tor_iso_Tor'.tor'Shift_comp R j M N)
    (fun g => Tor_iso_Tor'.tor'Shift_comp_naturality R j M g)

/-- For fixed `M`, the functors `(Tor C i).obj M` and `(Tor' C i).obj M` (both `C ⥤ C`, in the
second variable `N`) are naturally isomorphic. -/
noncomputable def Tor_iso_Tor'.app (i : ℕ) (M : ModuleCat.{u} R) :
    (Tor (ModuleCat.{u} R) i).obj M ≅ (Tor' (ModuleCat.{u} R) i).obj M :=
  match i with
  | 0 => Tor_iso_Tor'.zeroIso R M
  | 1 => Tor_iso_Tor'.oneIso R M
  | (j + 2) =>
      Tor_iso_Tor'.torShift R j M
        ≪≫ Tor_iso_Tor'.app (j + 1) (Tor_iso_Tor'.syzygy R M)
        ≪≫ (Tor_iso_Tor'.tor'Shift R j M).symm
