module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.BaseIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionExact
public import Mathlib.RingTheory.Filtration

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (𝓘 : (SheafOfModules.unit
    (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).Submodule)

/-- The kernel of `Γ(X, M) ⟶ Γ(X, M / 𝓘ⁿ M)`, as an `A`-submodule of `Γ(X, M)`. -/
def sectionsKer (n : ℕ) (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    Submodule A ((sectionsOverBase A B hA X.1 X.2).obj M) :=
  LinearMap.ker ((sectionsOverBase A B hA X.1 X.2).map
    (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 n M).ι)).hom

/-- A global section lies in `sectionsKer A X 𝓘 n M` if and only if its value on every object lies
in `𝓘ⁿ M`. -/
theorem mem_sectionsKer_iff {n : ℕ} {M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (s : (sectionsOverBase A B hA X.1 X.2).obj M) :
    s ∈ sectionsKer A X 𝓘 n M ↔
      ∀ U, s.1 U ∈ (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 n M).obj U := by
  refine ⟨fun h U => ?_, fun h => ?_⟩
  · have h' := congrArg (fun t : (sectionsOverBase A B hA X.1 X.2).obj
      (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 n M) => t.1 U) h
    exact (cokernel_π_app_eq_zero_iff B (Spec (.of A)) hA X.1 X.2 _ U (s.1 U)).1 h'
  · refine Subtype.ext (funext fun U => ?_)
    exact (cokernel_π_app_eq_zero_iff B (Spec (.of A)) hA X.1 X.2 _ U (s.1 U)).2 (h U)

/-- The kernels `sectionsKer A X 𝓘 n M` decrease as `n` increases. -/
theorem sectionsKer_antitone {k n : ℕ} (h : k ≤ n)
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    sectionsKer A X 𝓘 n M ≤ sectionsKer A X 𝓘 k M := fun s hs =>
  (mem_sectionsKer_iff A X 𝓘 s).2 fun U =>
    idealPowerMultiple_antitone B (Spec (.of A)) hA X.1 X.2 𝓘 h M U
      ((mem_sectionsKer_iff A X 𝓘 s).1 hs U)

/-- A morphism `g : M ⟶ N` sends `sectionsKer A X 𝓘 n M` into `sectionsKer A X 𝓘 n N`. -/
theorem map_mem_sectionsKer {n : ℕ} {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (g : M ⟶ N) {s : (sectionsOverBase A B hA X.1 X.2).obj M} (hs : s ∈ sectionsKer A X 𝓘 n M) :
    (sectionsOverBase A B hA X.1 X.2).map g s ∈ sectionsKer A X 𝓘 n N := by
  show ((sectionsOverBase A B hA X.1 X.2).map g ≫ (sectionsOverBase A B hA X.1 X.2).map
    (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 n N).ι)).hom s = 0
  rw [← Functor.map_comp, ← π_comp_idealPowerQuotientMapOfHom, Functor.map_comp]
  show ((sectionsOverBase A B hA X.1 X.2).map _).hom
    (((sectionsOverBase A B hA X.1 X.2).map _).hom s) = 0
  rw [show ((sectionsOverBase A B hA X.1 X.2).map
    (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 n M).ι)).hom s = 0 from hs,
    map_zero]

/-- The structure ring map of a chart, in the spelling `AlgebraicGeometry.Space.chartRing`. -/
def chartRingBaseRingHom (U : SmallEtale B (Spec (.of A)) hA X.1) :
    A →+* chartRing B (Spec (.of A)) hA X.1 X.2 U :=
  chartBaseRingHom A X U

/-- The image of `sectionsKer A X 𝓘 n M` under `Γ(X, g)` is contained in
`sectionsKer A X 𝓘 n N`. -/
theorem map_sectionsKer_le {n : ℕ} {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (g : M ⟶ N) :
    (sectionsKer A X 𝓘 n M).map ((sectionsOverBase A B hA X.1 X.2).map g).hom ≤
      sectionsKer A X 𝓘 n N := by
  rintro _ ⟨s, hs, rfl⟩
  exact map_mem_sectionsKer A X 𝓘 g hs

/-- If `𝓘` contains the extension of `I`, then `Iⁿ Γ(X, M)` dies in `Γ(X, M / 𝓘ⁿ M)`. -/
theorem pow_smul_top_le_sectionsKer {I : Ideal A}
    (h𝓘 : ∀ (U : SmallEtale B (Spec (.of A)) hA X.1) a, a ∈ I →
      chartRingBaseRingHom A X U a ∈ chartIdeal B (Spec (.of A)) hA X 𝓘 U) (n : ℕ)
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    I ^ n • (⊤ : Submodule A ((sectionsOverBase A B hA X.1 X.2).obj M)) ≤
      sectionsKer A X 𝓘 n M := by
  refine Submodule.smul_le.2 fun a ha s _ => (mem_sectionsKer_iff A X 𝓘 _).2 fun U => ?_
  let V : SmallEtale B (Spec (.of A)) hA X.1 := U.unop
  have hmap : Ideal.map (chartRingBaseRingHom A X V) (I ^ n) ≤
      chartIdeal B (Spec (.of A)) hA X 𝓘 V ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun a ha => h𝓘 V a ha) n
  exact le_idealPowerMultiple_obj B (Spec (.of A)) hA X.1 X.2 𝓘 n M V
    (Submodule.smul_mem_smul (hmap (Ideal.mem_map_of_mem _ ha)) Submodule.mem_top)

/-- Artin-Rees for a linear map `g` into a finite module over a Noetherian ring: an element of
`range g` lying in `I ^ (m + c) M₃` is the image of an element of `I ^ m M₂`. -/
private theorem exists_pow_smul_map_eq {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M₂ M₃ : Type*} [AddCommGroup M₂] [AddCommGroup M₃] [Module A M₂] [Module A M₃]
    [Module.Finite A M₃] (g : M₂ →ₗ[A] M₃) :
    ∃ c : ℕ, ∀ (m : ℕ) (y : M₃), y ∈ I ^ (m + c) • (⊤ : Submodule A M₃) → y ∈ LinearMap.range g →
      ∃ q ∈ I ^ m • (⊤ : Submodule A M₂), g q = y := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range g)
  refine ⟨c, fun m y hy hyg => ?_⟩
  have h : y ∈ I ^ (m + c) • (⊤ : Submodule A M₃) ⊓ LinearMap.range g := ⟨hy, hyg⟩
  rw [hc _ (by omega), Nat.add_sub_cancel] at h
  have : y ∈ (I ^ m • (⊤ : Submodule A M₂)).map g := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right h
  exact this

omit [CommRing A] in
/-- **Extensions and Artin-Rees filtrations, in commutative algebra.**  Let
`M₁ →f M₂ →g M₃` be exact at `M₂`, with `M₃` finite over a Noetherian ring `A`, and let
`K₁, K₂, K₃` be decreasing filtrations such that `g` maps `K₂` into `K₃`, `Iⁿ M₂ ⊆ K₂ n`, and
`f t ∈ K₂ (k + c + 1)` forces `t ∈ K₁ (k + 1)`.  If `K₁` and `K₃` are no finer than the `I`-adic
filtrations, neither is `K₂`. -/
theorem exists_le_pow_smul_of_exact {A : Type*} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module A M₁]
    [Module A M₂] [Module A M₃] [Module.Finite A M₃] (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hfg : LinearMap.ker g ≤ LinearMap.range f) (K₁ : ℕ → Submodule A M₁)
    (K₂ : ℕ → Submodule A M₂) (K₃ : ℕ → Submodule A M₃) (hK₂ : Antitone K₂)
    (hg : ∀ n, (K₂ n).map g ≤ K₃ n) (hI : ∀ n, I ^ n • (⊤ : Submodule A M₂) ≤ K₂ n)
    (hK₃ : Antitone K₃) (hK₁ : Antitone K₁)
    {c₂ : ℕ} (hf : ∀ k t, f t ∈ K₂ (k + c₂ + 1) → t ∈ K₁ (k + 1))
    (R₁ : ∀ m, ∃ n, K₁ n ≤ I ^ m • ⊤) (R₃ : ∀ m, ∃ n, K₃ n ≤ I ^ m • ⊤) :
    ∀ m, ∃ n, K₂ n ≤ I ^ m • ⊤ := by
  obtain ⟨c₁, hc₁⟩ := exists_pow_smul_map_eq I g
  intro m
  obtain ⟨nT, hnT⟩ := R₁ m
  obtain ⟨n', hn'⟩ := R₃ (m + nT + c₂ + 1 + c₁)
  refine ⟨max n' (m + nT + c₂ + 1), fun s hs => ?_⟩
  obtain ⟨q, hq, hqs⟩ := hc₁ (m + nT + c₂ + 1) (g s)
    (hn' (hK₃ (le_max_left _ _) (hg _ ⟨s, hs, rfl⟩))) ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := hfg (show s - q ∈ LinearMap.ker g by
    rw [LinearMap.mem_ker, map_sub, hqs, sub_self])
  have htK : f t ∈ K₂ (nT + c₂ + 1) := by
    rw [ht]
    exact hK₂ (by omega) (Submodule.sub_mem _ (hK₂ (le_max_right _ _) hs) (hI _ hq))
  have h1 : f t ∈ I ^ m • (⊤ : Submodule A M₂) := by
    have := Submodule.mem_map_of_mem (f := f) (hnT (hK₁ (Nat.le_succ nT) (hf nT t htK)))
    rw [Submodule.map_smul'', Submodule.map_top] at this
    exact Submodule.smul_mono le_rfl le_top this
  rw [show s = f t + q by rw [ht, sub_add_cancel]]
  exact Submodule.add_mem _ h1 (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl hq)

/-- **The Artin-Rees property of the global sections of a module**: the topology on `Γ(X, M)`
defined by the kernels of `Γ(X, M) ⟶ Γ(X, M / 𝓘ⁿ M)` is no finer than the `I`-adic topology. -/
def HasSectionsArtinRees (I : Ideal A) (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) : Prop :=
  ∀ m : ℕ, ∃ n : ℕ, sectionsKer A X 𝓘 n M ≤
    I ^ m • (⊤ : Submodule A ((sectionsOverBase A B hA X.1 X.2).obj M))

/-- The Artin-Rees property passes to a submodule, when the sections of the ambient module are
finite over a Noetherian `A`. -/
theorem HasSectionsArtinRees.of_mono [IsNoetherianRing A] {I : Ideal A}
    {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (f : M ⟶ N) [Mono f]
    (hN : Module.Finite A ((sectionsOverBase A B hA X.1 X.2).obj N))
    (h : HasSectionsArtinRees A X 𝓘 I N) : HasSectionsArtinRees A X 𝓘 I M := by
  let Γf := ((sectionsOverBase A B hA X.1 X.2).map f).hom
  obtain ⟨k, hk⟩ := exists_pow_smul_map_eq I Γf
  intro m
  obtain ⟨n, hn⟩ := h (m + k)
  refine ⟨n, fun s hs => ?_⟩
  obtain ⟨t, ht, hts⟩ := hk m (Γf s) (hn (map_mem_sectionsKer A X 𝓘 f hs)) ⟨s, rfl⟩
  exact sectionsOverBase_map_injective_of_mono A f hts ▸ ht

/-- **Artin-Rees along a monomorphism of coherent modules, on global sections**
(Stacks 07UL): a global section of `T` whose image in `Q` dies modulo `𝓘ⁿ⁺ᶜ⁺¹` already dies
modulo `𝓘ⁿ⁺¹`. -/
theorem exists_sectionsKer_of_mono (hN : IsNoetherian B (Spec (.of A)) hA B.contains_terminal X.1)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    {T Q : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hT : IsCoherent B (Spec (.of A)) hA X.1 X.2 T)
    (hQ : IsCoherent B (Spec (.of A)) hA X.1 X.2 Q) (f : T ⟶ Q) [Mono f] :
    ∃ c : ℕ, ∀ (n : ℕ) (t : (sectionsOverBase A B hA X.1 X.2).obj T),
      (sectionsOverBase A B hA X.1 X.2).map f t ∈ sectionsKer A X 𝓘 (n + c + 1) Q →
        t ∈ sectionsKer A X 𝓘 (n + 1) T := by
  have : Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  let T' : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 := ⟨T, hT⟩
  let Q' : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 := ⟨Q, hQ⟩
  let f' : T' ⟶ Q' := ObjectProperty.homMk f
  have : Mono f' := (ObjectProperty.ι _).mono_of_mono_map (by exact (inferInstance : Mono f))
  obtain ⟨c, hc⟩ := exists_comp_completionTermProjection_eq_zero_of_mono B (Spec (.of A)) hA X.1
    X.2 𝓘 hI B.contains_terminal hN f'
  refine ⟨c, fun n t ht => ?_⟩
  have h0 : ∀ {M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2},
      M.unitHomEquiv (0 : SheafOfModules.unit _ ⟶ M) = 0 := fun {_} => rfl
  let t' : T.sections := t
  have h := hc n (T.unitHomEquiv.symm t') (by
    show T.unitHomEquiv.symm t' ≫ (f ≫ cokernel.π
      (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 (n + c + 1) Q).ι) = 0
    rw [SheafOfModules.unitHomEquiv_symm_comp]
    refine (Equiv.symm_apply_eq _).2 (Eq.trans ?_ h0.symm)
    exact ht)
  rw [SheafOfModules.unitHomEquiv_symm_comp] at h
  have h' := congrArg (SheafOfModules.unitHomEquiv _) h
  rwa [Equiv.apply_symm_apply, h0] at h'

/-- **The Artin-Rees property is closed under extensions of coherent modules.** -/
theorem HasSectionsArtinRees.of_shortExact [IsNoetherianRing A]
    (hN : IsNoetherian B (Spec (.of A)) hA B.contains_terminal X.1)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) {I : Ideal A}
    (h𝓘 : ∀ (U : SmallEtale B (Spec (.of A)) hA X.1) a, a ∈ I →
      chartRingBaseRingHom A X U a ∈ chartIdeal B (Spec (.of A)) hA X 𝓘 U)
    (E : ShortComplex (Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)) (hE : E.ShortExact)
    (h₁ : IsCoherent B (Spec (.of A)) hA X.1 X.2 E.X₁)
    (h₂ : IsCoherent B (Spec (.of A)) hA X.1 X.2 E.X₂)
    (hfin : Module.Finite A ((sectionsOverBase A B hA X.1 X.2).obj E.X₃))
    (R₁ : HasSectionsArtinRees A X 𝓘 I E.X₁) (R₃ : HasSectionsArtinRees A X 𝓘 I E.X₃) :
    HasSectionsArtinRees A X 𝓘 I E.X₂ := by
  have := hE.mono_f
  have hex := hE.exact.map_of_mono_of_preservesKernel (sectionsOverBase A B hA X.1 X.2)
    hE.mono_f inferInstance
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at hex
  have hfg : LinearMap.ker ((sectionsOverBase A B hA X.1 X.2).map E.g).hom ≤
      LinearMap.range ((sectionsOverBase A B hA X.1 X.2).map E.f).hom := hex
  obtain ⟨c₂, hc₂⟩ := exists_sectionsKer_of_mono A X 𝓘 hN hI h₁ h₂ E.f
  exact exists_le_pow_smul_of_exact (I := I) (c₂ := c₂)
    ((sectionsOverBase A B hA X.1 X.2).map E.f).hom
    ((sectionsOverBase A B hA X.1 X.2).map E.g).hom hfg (fun n => sectionsKer A X 𝓘 n E.X₁)
    (fun n => sectionsKer A X 𝓘 n E.X₂) (fun n => sectionsKer A X 𝓘 n E.X₃)
    (fun _ _ h => sectionsKer_antitone A X 𝓘 h _)
    (fun _ => map_sectionsKer_le A X 𝓘 E.g)
    (fun n => pow_smul_top_le_sectionsKer A X 𝓘 h𝓘 n E.X₂)
    (fun _ _ h => sectionsKer_antitone A X 𝓘 h _) (fun _ _ h => sectionsKer_antitone A X 𝓘 h _)
    hc₂ R₁ R₃

end AlgebraicGeometry.Space
