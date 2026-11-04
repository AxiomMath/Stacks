module

public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwistFromFormalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.FirstCohomologyVanishingCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ReesImageCohomologyEquivariance
public import StacksFrontier.AlgebraicGeometry.Spaces.ReesModuleCohomologyFinite

/-!
# Clauses (1) and (3) of the theorem on formal functions, from the Rees stability

Let `T` be an affine object of the site with Noetherian `A = Γ(T₀, ⊤)`, `f : X ⟶ h_T` proper,
`J ⊆ A` an ideal and `I` a sheaf of ideals of `X` generated on affine charts by the images of
generators of `J`.  For a coherent `F` and a coherent submodule `N₀ ⊆ F`, the images of
`Hᵖ(X, IᵐN₀) ⟶ Hᵖ(X, N₀)` form a stable `J`-filtration of `Hᵖ(X, N₀)` ([Stacks, Tag 08AW],
[Stacks, Tag 08AX]); this is `AlgebraicGeometry.Space.cohomologyIdealPowFiltration_stable`.

The stability is the source's Rees argument: the Rees module `⨁ IᵐN₀ tᵐ` is `π_*G` for the image
`G` of `π^*N₀ ⟶ ψ_*ψ^*π^*N₀` on the base change `X_R` to `R = A[Jt]`, whose cohomology is finite
over `R` (Stacks 08AS on `X_R`); the Rees module of the filtration embeds into its image in
`Hᵖ(X, π_*ψ_*ψ^*π^*N₀) = Hᵖ(X, N₀) ⊗_A A[t]` (Stacks 073K).

A bound `Im(Hᵖ(X, IᵐN₀) ⟶ Hᵖ(X, N₀)) ⊆ J^{m-c} Hᵖ(X, N₀)` gives the two clauses of
[Stacks, Tag 08AY] that the proof of [Stacks, Tag 0D39] uses, for `I` the ideal of a closed fibre:

1. `N₀ = F`: the kernel of `Hⁱ(X, F) ⟶ Hⁱ(X, F/IⁿF)` is the image of `Hⁱ(X, IⁿF)` (long exact
   sequence), so it lies in `J^{n-c} Hⁱ(X, F)`
   (`AlgebraicGeometry.Space.ker_rightDerived_idealPowTowerπ_le_of_range_le`);
2. `N₀ = IF`, degree zero: if the transitions `H⁰(X, F/Iᵐ⁺¹F) ⟶ H⁰(X, F/IF)` are surjective, the
   connecting map `H⁰(X, F/IF) ⟶ H¹(X, IF)` takes values in the images of every
   `H¹(X, Iᵐ⁺¹F) ⟶ H¹(X, IF)` (naturality of `δ`), which factor through `H¹(X, Iᵐ(IF))`; so it
   takes values in `⋂ₖ Jᵏ H¹(X, IF) = 0` (Krull, `H¹(X, IF)` finite by [Stacks, Tag 08AS]), and
   `H⁰(X, F) ⟶ H⁰(X, F/IF)` is surjective
   (`AlgebraicGeometry.Space.epi_rightDerived_zero_idealPowTowerπ_one_of_range_le`).

## Main results

* `AlgebraicGeometry.Space.cohomologyIdealPowFiltration_stable`: the filtration is stable.
* `AlgebraicGeometry.Space.ker_rightDerived_idealPowTowerπ_le_of_range_le`,
  `AlgebraicGeometry.Space.epi_rightDerived_zero_idealPowTowerπ_one_of_range_le`: the two clauses
  from a bound on images.
* `AlgebraicGeometry.Space.exists_range_idealPowSmulIncl_le_fibreIdeal`: the bound on images for
  the ideal of a closed fibre, over the ring `Γ(h_T)` and its ideal `ker(Γ(h_T) ⟶ Γ(h_P))`.
* `AlgebraicGeometry.Space.formalFunctionsKernelClause`,
  `AlgebraicGeometry.Space.formalFunctionsImageClause`: the clauses
  `AlgebraicGeometry.Space.FormalFunctionsKernelClause` and
  `AlgebraicGeometry.Space.FormalFunctionsImageClause` over `Spec 𝒪_{Y,y}` that the proof of
  [Stacks, Tag 0D39] consumes.

## Implementation notes

The degree-`m` factorization is re-proved here with its composite written out
(`AlgebraicGeometry.Space.exists_comp_algebraImageModuleι_eq_degree`): converting
`AlgebraicGeometry.Space.algebraImageDegreeComposite` to the composite does not finish in the
kernel.  The abstract lemmas are instantiated with their implicit arguments given by name, and
the action of `A[Jt]` is passed to `Ideal.Filtration.stable_of_reesAction_of_moduleCat` in the
spelling of its equivariance lemma.

The stability is over `A = Γ(T₀, ⊤)`, the clauses over `Γ(h_T)`.  The two rings are identified by
evaluation at the identity chart, passed to `ModuleCat.mem_pow_smul_top_restrictScalars_of_equiv`
as a bare equivalence with its additivity and multiplicativity as separate arguments, so that the
ring structures of the two spellings of `Γ(h_T)` are compared only inside those small arguments.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

universe v u

/-- **`Ideal.Filtration.stable_of_reesAction` for modules over rings of global functions**: the
filtration lives on `M₀` read over `A` along `g`, the Rees module embeds in `Q` through `u` and
`χ`, and the finite `A[Jt]`-module is `P₀` read along `gR`, mapped to `Q` through `c` and `ι`.
The action `act` of `A[Jt]` on `P₀` and the inclusion `ev` of `A[Jt]` in `A[t]` are taken as
functions equal to the given ones, so that the equivariance `hΦ` can be supplied in the spelling
of its proof. -/
theorem Ideal.Filtration.stable_of_reesAction_of_moduleCat {A Γ Γ' : Type*} [CommRing A]
    [IsNoetherianRing A] [Ring Γ] [Ring Γ'] {J : Ideal A} (g : A →+* Γ)
    (M₀ : ModuleCat.{v} Γ) (hM : Module.Finite A ((ModuleCat.restrictScalars g).obj M₀))
    (F : J.Filtration ((ModuleCat.restrictScalars g).obj M₀)) (Q : ModuleCat.{v} Γ)
    (χ : Polynomial A →+* AddMonoid.End Q) (u : M₀ ⟶ Q)
    (hu : ∀ (a : A) (m : M₀), u.hom (g a • m) = χ (Polynomial.C a) (u.hom m))
    (hinj : ∀ v : ℕ →₀ M₀, (v.sum fun k y => χ (Polynomial.X ^ k) (u.hom y)) = 0 → v = 0)
    (gR : reesAlgebra J →+* Γ') (P₀ : ModuleCat.{v} Γ')
    (hP : Module.Finite (reesAlgebra J) ((ModuleCat.restrictScalars gR).obj P₀))
    (gπ : Γ →+* Γ') (W : ModuleCat.{v} Γ) (c : (ModuleCat.restrictScalars gπ).obj P₀ ≅ W)
    (ι : W ⟶ Q)
    (act : reesAlgebra J → P₀ → P₀) (hact : ∀ r z, act r z = gR r • z)
    (ev : reesAlgebra J → Polynomial A) (hev : ∀ r, ev r = r)
    (hΦ : ∀ (r : reesAlgebra J) (z : P₀),
      ι.hom (c.hom.hom (act r z)) = χ (ev r) (ι.hom (c.hom.hom z)))
    (N₁ : ℕ → ModuleCat.{v} Γ) (incl : ∀ k, N₁ k ⟶ M₀)
    (hN : ∀ k, F.N k = LinearMap.range ((ModuleCat.restrictScalars g).map (incl k)).hom)
    (hsub : ∀ k (z : N₁ k), ∃ q : P₀,
      ι.hom (c.hom.hom q) = χ (Polynomial.X ^ k) (u.hom ((incl k).hom z))) :
    F.Stable := by
  have := hM
  have := hP
  refine Ideal.Filtration.stable_of_reesAction F χ u.hom.toAddMonoidHom
    (fun a m => hu a m) hinj (P := (ModuleCat.restrictScalars gR).obj P₀)
    ((ι.hom.toAddMonoidHom).comp (c.hom.hom.toAddMonoidHom))
    (fun r z => (congrArg (fun y => ι.hom (c.hom.hom y)) (hact r z)).symm.trans
      ((hΦ r z).trans (congrArg (fun p => χ p (ι.hom (c.hom.hom z))) (hev r)))) ?_
  intro k y hy
  rw [hN k] at hy
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨q, hq⟩ := hsub k z
  exact ⟨q, hq⟩



/-- **`Iᵏ • ⊤` along an equivalence of scalar rings**: if `e : A' ≃ A₀` is additive and
multiplicative, `g' = g₀ ∘ e` and `e a ∈ J₀` forces `a ∈ J'`, then `J₀ᵏ • ⊤ ⊆ J'ᵏ • ⊤` on a
`Γ`-module read over `A₀` along `g₀` and over `A'` along `g'`. -/
theorem ModuleCat.mem_pow_smul_top_restrictScalars_of_equiv {A₀ A' Γ : Type*}
    [CommRing A₀] [CommRing A'] [Ring Γ] (g₀ : A₀ →+* Γ) (g' : A' →+* Γ) (e : A' ≃ A₀)
    (hmul : ∀ a b, e (a * b) = e a * e b) (hadd : ∀ a b, e (a + b) = e a + e b)
    (he : ∀ a, g' a = g₀ (e a)) (J₀ : Ideal A₀) (J' : Ideal A') (hJ : ∀ a, e a ∈ J₀ → a ∈ J')
    (M : ModuleCat.{v} Γ) (k : ℕ) (y : M)
    (hy : (show (ModuleCat.restrictScalars g₀).obj M from y) ∈
      J₀ ^ k • (⊤ : Submodule A₀ ((ModuleCat.restrictScalars g₀).obj M))) :
    (show (ModuleCat.restrictScalars g').obj M from y) ∈
      J' ^ k • (⊤ : Submodule A' ((ModuleCat.restrictScalars g').obj M)) := by
  let E : A' ≃+* A₀ := { e with map_mul' := hmul, map_add' := hadd }
  have hle : J₀ ^ k ≤ (J' ^ k).comap E.symm.toRingHom :=
    (Ideal.pow_right_mono (show J₀ ≤ J'.comap E.symm.toRingHom from fun a ha =>
      hJ (E.symm a) ((congrArg (· ∈ J₀) (E.apply_symm_apply a)).mpr ha)) k).trans
      (Ideal.le_comap_pow _ k)
  refine Submodule.smul_induction_on hy (fun a ha m _ => ?_)
    (fun y z hy hz => Submodule.add_mem _ hy hz)
  have h1 : g' (E.symm a) = g₀ a := (he _).trans (congrArg g₀ (E.apply_symm_apply a))
  have h2 := Submodule.smul_mem_smul (M := (ModuleCat.restrictScalars g').obj M)
    (r := E.symm a) (n := m) (hle ha) Submodule.mem_top
  have h2' : ((g' (E.symm a) • (m : M) : M) : (ModuleCat.restrictScalars g').obj M) ∈
      J' ^ k • (⊤ : Submodule A' ((ModuleCat.restrictScalars g').obj M)) := h2
  rwa [h1] at h2'



/-- **The degree-`k` class in the image of the comparison** (abstract): a factorization
`w ≫ ι = incl ≫ u ≫ ρ` and an isomorphism `c` onto the cohomology of the source of `ι` give a
class `q` with `H(ι)(c q) = H(ρ')(H(u)(H(incl) z))`, for any `ρ' = ρ`. -/
theorem ModuleCat.exists_map_comp_eq_of_fac {C : Type*} [Category C] {Γ Γ' : Type*} [Ring Γ]
    [Ring Γ'] (H : C ⥤ ModuleCat.{v} Γ) {N₁ N V W : C} (incl : N₁ ⟶ N) (u : N ⟶ V)
    (ρ ρ' : V ⟶ V) (hρ : ρ' = ρ) (w : N₁ ⟶ W) (ι : W ⟶ V) (hw : w ≫ ι = incl ≫ u ≫ ρ)
    (gπ : Γ →+* Γ') {P₀ : ModuleCat.{v} Γ'} (c : (ModuleCat.restrictScalars gπ).obj P₀ ≅ H.obj W)
    (z : H.obj N₁) :
    ∃ q : P₀, (H.map ι).hom (c.hom.hom q) = (H.map ρ').hom ((H.map u).hom ((H.map incl).hom z)) :=
  ⟨c.inv.hom ((H.map w).hom z), hρ ▸ ModuleCat.map_comp_inv_eq_of_fac H incl u ρ w ι hw c z⟩


/-! ### Abstract: the long exact sequence read through a bound on images -/

namespace CategoryTheory.DeltaFunctor

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {Γ : Type*} [Ring Γ]
  (D : DeltaFunctor 𝒜 (ModuleCat.{v} Γ))

/-- **Kernels from a bound on images**: for a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with
`X₁ ⟶ X₂` factoring through `incl : K ⟶ K₀`, a bound `Im Dⁱ(incl) ⊆ Jᵏ Dⁱ(K₀)` gives
`ker(Dⁱ(X₂) ⟶ Dⁱ(X₃)) ⊆ Jᵏ Dⁱ(X₂)`. -/
theorem ker_map_g_le_pow_smul_top {S : ShortComplex 𝒜} (hS : S.ShortExact) (i : ℕ)
    {A : Type*} [CommRing A] (g : A →+* Γ) (J : Ideal A) (k : ℕ) {K K₀ : 𝒜} (a : S.X₁ ⟶ K)
    (incl : K ⟶ K₀) (j : K₀ ⟶ S.X₂) (hfac : a ≫ incl ≫ j = S.f)
    (h : LinearMap.range ((ModuleCat.restrictScalars g).map ((D.functor i).map incl)).hom ≤
      J ^ k • ⊤) :
    LinearMap.ker ((ModuleCat.restrictScalars g).map ((D.functor i).map S.g)).hom ≤
      J ^ k • ⊤ := by
  intro y hy
  have hex := (D.exact_map hS i).moduleCat_range_eq_ker
  obtain ⟨w, hw⟩ := hex.symm.le (show y ∈ LinearMap.ker ((D.functor i).map S.g).hom from hy)
  have hw' : ((D.functor i).map j).hom (((D.functor i).map incl).hom
      (((D.functor i).map a).hom w)) = y := by
    refine Eq.trans ?_ hw
    change _ = ((D.functor i).map S.f).hom w
    rw [← hfac, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp]
    rfl
  have hm := h ⟨((D.functor i).map a).hom w, rfl⟩
  have hmap := Submodule.mem_map_of_mem
    (f := ((ModuleCat.restrictScalars g).map ((D.functor i).map j)).hom) hm
  rw [Submodule.map_smul''] at hmap
  exact hw' ▸ Submodule.smul_mono le_rfl le_top hmap

/-- **Surjectivity in degree zero from a bound on images** (the degree-zero step of the proof of
Stacks 08AY (3)): let `σₘ : Eₘ ⟶ E` be morphisms of short exact sequences, surjective on `D⁰` of
the right terms, whose left components factor through `inclₘ : Kₘ ⟶ X₁` with
`Im D¹(inclₘ) ⊆ J^{m-c} D¹(X₁)`.  If `D¹(X₁)` is finite over a Noetherian `A` and `J` lies in the
Jacobson radical, then `D⁰(X₂) ⟶ D⁰(X₃)` is surjective: the connecting map kills everything,
its values lying in `⋂ₖ Jᵏ D¹(X₁) = 0` (Krull). -/
theorem epi_map_g_zero_of_range_le (H : ℕ → 𝒜 ⥤ ModuleCat.{v} Γ) (hD : ∀ n, D.functor n = H n)
    {E : ShortComplex 𝒜} (hE : E.ShortExact)
    (E' : ℕ → ShortComplex 𝒜) (hE' : ∀ m, (E' m).ShortExact) (σ : ∀ m, E' m ⟶ E)
    (hepi : ∀ m, Epi ((H 0).map (σ m).τ₃))
    {A : Type*} [CommRing A] [IsNoetherianRing A] (g : A →+* Γ) (J : Ideal A)
    (hJ : J ≤ Ideal.jacobson ⊥)
    (hfin : Module.Finite A ((ModuleCat.restrictScalars g).obj ((H 1).obj E.X₁)))
    (K : ℕ → 𝒜) (a : ∀ m, (E' m).X₁ ⟶ K m) (incl : ∀ m, K m ⟶ E.X₁)
    (hfac : ∀ m, a m ≫ incl m = (σ m).τ₁) (c : ℕ)
    (hc : ∀ m, c ≤ m → LinearMap.range ((ModuleCat.restrictScalars g).map
      ((H 1).map (incl m))).hom ≤ J ^ (m - c) • ⊤) :
    Epi ((H 0).map E.g) := by
  obtain rfl : D.functor = H := funext hD
  rw [ModuleCat.epi_iff_surjective]
  intro x
  have hmem : ∀ k, (show (ModuleCat.restrictScalars g).obj ((D.functor 1).obj E.X₁) from
      (D.δ hE 0).hom x) ∈ J ^ k • (⊤ : Submodule A _) := by
    intro k
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 (hepi (k + c)) x
    have hnat := congrArg (fun φ => φ.hom y) (D.δ_naturality (hE' (k + c)) hE (σ (k + c)) 0)
    have hτ := congrArg (fun φ => ((D.functor 1).map φ).hom ((D.δ (hE' (k + c)) 0).hom y))
      (hfac (k + c))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.map_comp] at hnat hτ
    rw [hy] at hnat
    have hr : (show (ModuleCat.restrictScalars g).obj ((D.functor 1).obj E.X₁) from
        (D.δ hE 0).hom x) ∈ LinearMap.range ((ModuleCat.restrictScalars g).map
          ((D.functor 1).map (incl (k + c)))).hom :=
      ⟨((D.functor 1).map (a (k + c))).hom ((D.δ (hE' (k + c)) 0).hom y), hτ.trans hnat.symm⟩
    simpa using hc (k + c) (Nat.le_add_left c k) hr
  have := hfin
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
    (M := (ModuleCat.restrictScalars g).obj ((D.functor 1).obj E.X₁)) J hJ
  have hzero : (D.δ hE 0).hom x = 0 := by
    have h := (Submodule.mem_iInf _).2 hmem
    rw [hbot, Submodule.mem_bot] at h
    exact h
  obtain ⟨z, hz⟩ := (D.exact_δ₁ hE 0).moduleCat_range_eq_ker.symm.le
    (show x ∈ LinearMap.ker (D.δ hE 0).hom from hzero)
  exact ⟨z, hz⟩

end CategoryTheory.DeltaFunctor



namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Degree

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  (R' : Type u) [CommRing R'] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
  (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R')
  (F : Modules.{u, u} B S hS X.1 X.2) (N₀ : F.Submodule)
  (I : IdealSheaves B S hS X.1 X.2) {r : ℕ}
  (a : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
  (ha : ∀ i (W : SmallEtale B S hS X.1), (a i).1 (op W) ∈ I.obj (op W))
  (hgen : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      ∀ b ∈ I.obj (op A), ∃ c : Fin r → (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        (op A), b = ∑ i, c i * (a i).1 (op A))
  (t : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R').1 (algebraBaseChange B S hS T f R').2).O).obj)
  (s : Fin r → RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R).1 (algebraBaseChange B S hS T f R).2).O).obj)
  (hs : ∀ i, globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ) (s i) =
    globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ)
      (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f R) (a i)) * t)


include ha hgen hs in
/-- **The degree-`m` map `IᵐN₀ ⟶ π_*G`** (`AlgebraicGeometry.Space.exists_algebraImageDegreeMap`
with the composite written out): `IᵐN₀ ⟶ N₀ ⟶ V` followed by `ρ(tᵐ)` factors through
`π_*G ⊆ V`. -/
theorem exists_comp_algebraImageModuleι_eq_degree (hN : N₀.toSheafOfModules.IsQuasicoherentOnSite)
    (m : ℕ) :
    ∃ w, w ≫ algebraImageModuleι B S hS T f R R' φ N₀.toSheafOfModules =
      idealPowSmulIncl B S hS F N₀ I m ≫
        algebraImageTotalUnit B S hS T f R R' φ N₀.toSheafOfModules ≫
          algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules (t ^ m) := by
  refine exists_comp_eq_idealPowSmul_homOfLE_comp
    (hι := (epi_mono_modulePushforward_algebraImageModule B S hS T f R R' φ
      N₀.toSheafOfModules hN).2) N₀ I a ha hgen
    (algebraImageTotalUnit B S hS T f R R' φ N₀.toSheafOfModules)
    (fun m => algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules (t ^ m))
    (algebraImageModuleι B S hS T f R R' φ N₀.toSheafOfModules)
    (fun i => algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules
      (globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ) (s i)))
    (fun i => (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
      (globalSmul _ (s i) (algebraImageModule B S hS T f R R' φ N₀.toSheafOfModules)))
    ⟨Stacks.SheafOfModules.Submodule.homOfLE (Stacks.Sites.idealPowSmul_le_self I 0 N₀) ≫
      (exists_comp_algebraImageModuleι_eq_totalUnit B S hS T f R R' φ N₀.toSheafOfModules).choose,
      ?_⟩
    (fun i m => ?_)
    (fun i => algebraImageModuleι_comp_scalarEnd B S hS T f R R' φ N₀.toSheafOfModules (s i)) m
  · rw [pow_zero, algebraImageScalarEnd_one, Category.comp_id, Category.assoc,
      (exists_comp_algebraImageModuleι_eq_totalUnit B S hS T f R R' φ
        N₀.toSheafOfModules).choose_spec]
  · have e4 := mul_pow_succ_eq_pow_mul_of_eq _ _ _ (hs i) m
    exact (congrArg (· ≫ algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules (t ^ (m + 1)))
      (algebraImageScalarEnd_globalSectionsRingHomSite_comp B S hS T f R R' φ
        N₀.toSheafOfModules (a i)).symm).trans
      ((algebraImageScalarEnd_mul B S hS T f R R' φ N₀.toSheafOfModules _ _).symm.trans
        ((congrArg (algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules) e4).trans
          (algebraImageScalarEnd_mul B S hS T f R R' φ N₀.toSheafOfModules _ _)))

include ha hgen hs in
/-- **The degree-`m` classes lie in the image of `H^p(X_R, G)`**: `tᵐ · u(z)` for
`z ∈ H^p(X, IᵐN₀)` is the image of a class of `H^p(X_R, G)`. -/
theorem exists_reesImageCohomology_eq_degree (hN : N₀.toSheafOfModules.IsQuasicoherentOnSite)
    (hG : (algebraImageModule B S hS T f R R' φ N₀.toSheafOfModules).IsQuasicoherentOnSite)
    (p m : ℕ) (tk : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f R').1 (algebraBaseChange B S hS T f R').2).O).obj)
    (htk : tk = t ^ m)
    (z : (modulesCohomologyFunctor B S hS X p).obj
      (Stacks.Sites.idealPowSmul (M := F) I m N₀).toSheafOfModules) :
    ∃ q : (modulesCohomologyFunctor B S hS (algebraBaseChange B S hS T f R) p).obj
        (algebraImageModule B S hS T f R R' φ N₀.toSheafOfModules),
      ((modulesCohomologyFunctor B S hS X p).map
          (algebraImageModuleι B S hS T f R R' φ N₀.toSheafOfModules)).hom
        ((cohomologyPushforwardLinearIsoOfIsAffineHom B S hS
          (algebraBaseChangeProjection B S hS T f R)
          (isAffineHom_algebraBaseChangeProjection B S hS T f R)
          (algebraImageModule B S hS T f R R' φ N₀.toSheafOfModules) hG p).hom.hom q) =
      ((modulesCohomologyFunctor B S hS X p).map
          (algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules tk)).hom
        (((modulesCohomologyFunctor B S hS X p).map
          (algebraImageTotalUnit B S hS T f R R' φ N₀.toSheafOfModules)).hom
          (((modulesCohomologyFunctor B S hS X p).map
            (idealPowSmulIncl B S hS F N₀ I m)).hom z)) :=
  Exists.elim (exists_comp_algebraImageModuleι_eq_degree B S hS T f R R' φ F N₀ I a ha hgen t s hs
    hN m)
    fun w hw => ModuleCat.exists_map_comp_eq_of_fac (modulesCohomologyFunctor B S hS X p)
      (idealPowSmulIncl B S hS F N₀ I m)
      (algebraImageTotalUnit B S hS T f R R' φ N₀.toSheafOfModules)
      (algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules (t ^ m))
      (algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules tk)
      (congrArg (algebraImageScalarEnd B S hS T f R R' φ N₀.toSheafOfModules) htk) w
      (algebraImageModuleι B S hS T f R R' φ N₀.toSheafOfModules) hw
      (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f R))
      (cohomologyPushforwardLinearIsoOfIsAffineHom B S hS
        (algebraBaseChangeProjection B S hS T f R)
        (isAffineHom_algebraBaseChangeProjection B S hS T f R)
        (algebraImageModule B S hS T f R R' φ N₀.toSheafOfModules) hG p) z

end Degree

section Stable

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] in
/-- The `k`-th step of `cohomologyIdealPowFiltration` is the image of `H^p(X, IᵏN₀) → H^p(X, N₀)`,
viewed as an `A`-submodule. -/
theorem cohomologyIdealPowFiltration_N (F : Modules.{u, u} B S hS X.1 X.2) (N₀ : F.Submodule)
    (I : IdealSheaves B S hS X.1 X.2)
    (hJ : ∀ a ∈ J, ∀ W : SmallEtale B S hS X.1, (baseScalar f a).1 (op W) ∈ I.obj (op W))
    (p k : ℕ) :
    (cohomologyIdealPowFiltration B S hS T f J F N₀ I hJ p).N k =
      LinearMap.range ((ModuleCat.restrictScalars (baseScalarRingHom B S hS T f)).map
        ((modulesCohomologyFunctor B S hS X p).map (idealPowSmulIncl B S hS F N₀ I k))).hom := by
  unfold cohomologyIdealPowFiltration
  rfl

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] in
/-- For `f : X → Spec A` proper with `Spec A` locally Noetherian and `N` coherent, `H^p(X, N)` is a
finite `A`-module. -/
theorem finite_baseScalar_cohomology [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hf : IsProper B S hS f.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) (hN : IsCoherent B S hS X.1 X.2 N) (p : ℕ) :
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
      ((ModuleCat.restrictScalars (baseScalarRingHom B S hS T f)).obj
        ((modulesCohomologyFunctor B S hS X p).obj N)) :=
  Module.Finite.of_restrictScalars_ringEquiv (globalSectionsRingHomSite B S hS f)
    (schemeSpaceGlobalSectionsEquiv B S hS T).symm
    ((modulesCohomologyFunctor B S hS X p).obj N)
    (hM := hasFiniteGlobalCohomologyOver_of_isProper B S hS hZ f hf N hN p)

/-- For `f : X → Spec A` proper and `N` coherent, with `A` Noetherian, the cohomology
`H^p(X_R, im(π^*N → ψ_*ψ^*π^*N))` on the base change `X_R` to the Rees algebra `R = A[Jt]` is a
finite `R`-module. -/
theorem finite_reesImage_cohomology (hZ : B.Contains (⊤_ Scheme.{u})) (hf : IsProper B S hS f.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) (hN : IsCoherent B S hS X.1 X.2 N) (p : ℕ) :
    Module.Finite (reesAlgebra J)
      ((ModuleCat.restrictScalars (algebraBaseChangeScalar B S hS T f (reesAlgebra J))).obj
        ((modulesCohomologyFunctor B S hS (algebraBaseChange B S hS T f (reesAlgebra J)) p).obj
          (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
            (reesAlgebra J).val N))) :=
  Module.Finite.of_restrictScalars_ringEquiv
    (globalSectionsRingHomSite B S hS (algebraBaseChangeStructure B S hS T f (reesAlgebra J)))
    (algebraSpectrumGlobalSectionsEquiv B S hS T (reesAlgebra J)).symm
    ((modulesCohomologyFunctor B S hS (algebraBaseChange B S hS T f (reesAlgebra J)) p).obj
      (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N))
    (hM := @hasFiniteGlobalCohomologyOver_algebraImageModule B S hS T _ X f (reesAlgebra J)
      _ _ _ (basePolynomialRing B S hS T) _ _ _ (reesAlgebra J).val hZ
      (isNoetherianRing_of_fg (reesAlgebra.fg (IsNoetherian.noetherian J))) hf N hN p)

/-- The map `H^p(X, N) → H^p(X, π_*ψ_*ψ^*π^*N)` induced by the unit intertwines the action of
`a ∈ A` with the action of the constant `Polynomial.C a` through `reesTotalCohomologyAction`. -/
theorem reesTotalCohomologyAction_unit_smul (N : Modules.{u, u} B S hS X.1 X.2) (p : ℕ)
    (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (m : (modulesCohomologyFunctor B S hS X p).obj N) :
    ((modulesCohomologyFunctor B S hS X p).map (algebraImageTotalUnit B S hS T f (reesAlgebra J)
      (basePolynomialRing B S hS T) (reesAlgebra J).val N)).hom
        (baseScalarRingHom B S hS T f a • m) =
      reesTotalCohomologyAction B S hS T f J N p (Polynomial.C a)
        (((modulesCohomologyFunctor B S hS X p).map (algebraImageTotalUnit B S hS T f
          (reesAlgebra J) (basePolynomialRing B S hS T) (reesAlgebra J).val N)).hom m) :=
  ((((modulesCohomologyFunctor B S hS X p).map (algebraImageTotalUnit B S hS T f
      (reesAlgebra J) (basePolynomialRing B S hS T) (reesAlgebra J).val N)).hom.map_smul
      (baseScalarRingHom B S hS T f a) m).trans
    (reesTotalCohomologyAction_C B S hS T f J N p a
      (((modulesCohomologyFunctor B S hS X p).map (algebraImageTotalUnit B S hS T f
        (reesAlgebra J) (basePolynomialRing B S hS T) (reesAlgebra J).val N)).hom m)).symm)


/-- **The filtration of `H^p(X, N₀)` by the images of `H^p(X, IᵐN₀)` is stable** (the content of
Stacks 08AW, 08AX used by Stacks 08AY), for `I` generated on affine charts by the images of
`x₁, …, x_r ∈ J`. -/
theorem cohomologyIdealPowFiltration_stable
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)] (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (N₀ : F.Submodule)
    (hN₀ : IsCoherent B S hS X.1 X.2 N₀.toSheafOfModules) (I : IdealSheaves B S hS X.1 X.2)
    (hJ : ∀ a ∈ J, ∀ W : SmallEtale B S hS X.1, (baseScalar f a).1 (op W) ∈ I.obj (op W))
    {r : ℕ} (x : Fin r → Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hxJ : ∀ i, x i ∈ J)
    (hgen : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      ∀ b ∈ I.obj (op A), ∃ c : Fin r → (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        (op A), b = ∑ i, c i * (baseScalar f (x i)).1 (op A))
    (p : ℕ) :
    (cohomologyIdealPowFiltration B S hS T f J F N₀ I hJ p).Stable := by
  have hG := isQuasicoherentOnSite_algebraImageModule B S hS T f (reesAlgebra J)
    (basePolynomialRing B S hS T) (reesAlgebra J).val N₀.toSheafOfModules
    hN₀.toIsQuasicoherentOnSite
  have hmem : ∀ i, Polynomial.monomial 1 (x i) ∈ reesAlgebra J := fun i =>
    reesAlgebra.monomial_mem.2 (by rw [pow_one]; exact hxJ i)
  exact Ideal.Filtration.stable_of_reesAction_of_moduleCat
    (A := Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (Γ := RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (Γ' := RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (algebraBaseChange B S hS T f (reesAlgebra J)).1
      (algebraBaseChange B S hS T f (reesAlgebra J)).2).O).obj) (J := J)
    (baseScalarRingHom B S hS T f)
    ((modulesCohomologyFunctor B S hS X p).obj N₀.toSheafOfModules)
    (finite_baseScalar_cohomology B S hS T f B.contains_terminal hf N₀.toSheafOfModules hN₀ p)
    (cohomologyIdealPowFiltration B S hS T f J F N₀ I hJ p)
    ((modulesCohomologyFunctor B S hS X p).obj (algebraImageTotal B S hS T f (reesAlgebra J)
      (basePolynomialRing B S hS T) (reesAlgebra J).val N₀.toSheafOfModules))
    (reesTotalCohomologyAction B S hS T f J N₀.toSheafOfModules p)
    ((modulesCohomologyFunctor B S hS X p).map (algebraImageTotalUnit B S hS T f (reesAlgebra J)
      (basePolynomialRing B S hS T) (reesAlgebra J).val N₀.toSheafOfModules))
    (fun a m => reesTotalCohomologyAction_unit_smul B S hS T f J N₀.toSheafOfModules p a m)
    (fun v hv => eq_zero_of_sum_reesTotalCohomologyAction B S hS T f J B.contains_terminal
      hf.2.1.2 (isQuasiSeparated_of_isSeparated B S hS hf.1) N₀.toSheafOfModules
      hN₀.toIsQuasicoherentOnSite p v hv)
    (algebraBaseChangeScalar B S hS T f (reesAlgebra J))
    ((modulesCohomologyFunctor B S hS (algebraBaseChange B S hS T f (reesAlgebra J)) p).obj
      (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N₀.toSheafOfModules))
    (finite_reesImage_cohomology B S hS T f J B.contains_terminal hf N₀.toSheafOfModules hN₀ p)
    (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f (reesAlgebra J)))
    ((modulesCohomologyFunctor B S hS X p).obj ((modulePushforward B S hS
      (algebraBaseChangeProjection B S hS T f (reesAlgebra J))).obj
      (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N₀.toSheafOfModules)))
    (cohomologyPushforwardLinearIsoOfIsAffineHom B S hS
      (algebraBaseChangeProjection B S hS T f (reesAlgebra J))
      (isAffineHom_algebraBaseChangeProjection B S hS T f (reesAlgebra J))
      (algebraImageModule B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N₀.toSheafOfModules) hG p)
    ((modulesCohomologyFunctor B S hS X p).map (algebraImageModuleι B S hS T f (reesAlgebra J)
      (basePolynomialRing B S hS T) (reesAlgebra J).val N₀.toSheafOfModules))
    (fun r z => algebraBaseChangeScalar B S hS T f (reesAlgebra J) r • z) (fun _ _ => rfl)
    (fun r => (reesAlgebra J).val r) (fun _ => rfl)
    (reesImageCohomology_smul B S hS T f J N₀.toSheafOfModules hG p)
    (fun k => (modulesCohomologyFunctor B S hS X p).obj
      (Stacks.Sites.idealPowSmul (M := F) I k N₀).toSheafOfModules)
    (fun k => (modulesCohomologyFunctor B S hS X p).map (idealPowSmulIncl B S hS F N₀ I k))
    (fun k => cohomologyIdealPowFiltration_N B S hS T f J F N₀ I hJ p k)
    (fun k z => Exists.elim (exists_reesImageCohomology_eq_degree B S hS T f (reesAlgebra J)
      (basePolynomialRing B S hS T) (reesAlgebra J).val F N₀ I (fun i => baseScalar f (x i))
      (fun i W => hJ (x i) (hxJ i) W) hgen
      (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) Polynomial.X)
      (fun i => algebraBaseChangeScalar B S hS T f (reesAlgebra J) ⟨_, hmem i⟩)
      (fun i => globalSectionsRingHomSite_algebraBaseChangeMap_reesGenerator B S hS T f J (x i)
        (hmem i)) hN₀.toIsQuasicoherentOnSite hG p k
      (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) (Polynomial.X ^ k))
      (map_pow _ _ _) z) fun q hq =>
        ⟨q, hq.trans (reesTotalCohomologyAction_apply B S hS T f J N₀.toSheafOfModules p _ _).symm⟩)

end Stable

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian




open Stacks.Cohomology.SiteModules (globalSectionsFunctor)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


/-! ### The short exact sequences `0 → IⁿM → M → M/IⁿM → 0` -/

section Tower

variable {X : AlgebraicSpaces B S hS} (I : IdealSheaves B S hS X.1 X.2)
  (M : Modules.{u, u} B S hS X.1 X.2)

/-- **The short exact sequence `0 → IⁿM → M → M/IⁿM → 0`.** -/
abbrev idealPowCokernelShortComplex (n : ℕ) : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
  ShortComplex.mk (idealPowSubmodule I n M).ι (idealPowTowerπ I M n) (cokernel.condition _)

/-- The sequence `0 → IⁿM → M → M/IⁿM → 0` is short exact. -/
theorem idealPowCokernelShortComplex_shortExact (n : ℕ) :
    (idealPowCokernelShortComplex I M n).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := inferInstanceAs (Mono (idealPowSubmodule I n M).ι)
  epi_g := inferInstanceAs (Epi (cokernel.π _))

/-- `Iᵐ⁺¹M ⊆ Iᵐ(IM)`, as submodules of `M`. -/
theorem idealPowSubmodule_succ_le_idealPowSmul_one (m : ℕ) :
    idealPowSubmodule I (m + 1) M ≤
      Stacks.Sites.idealPowSmul (M := M) I m (idealPowSubmodule I 1 M) := by
  induction m with
  | zero => exact (Stacks.Sites.idealPowSmul_zero (M := M) I _).symm.le
  | succ m ih =>
    refine (idealPowSmul_succ_eq_idealSmul I (m + 1) ⊤).le.trans ?_
    refine (Stacks.Sites.idealSmul_mono_right I ih).trans ?_
    exact (idealPowSmul_succ_eq_idealSmul I m _).symm.le

/-- The square `Iᵐ⁺¹M ⟶ IM`, `M = M` of the morphism of short exact sequences. -/
theorem idealPowCokernelShortComplex_comm₁₂ (m : ℕ) :
    (Stacks.SheafOfModules.Submodule.homOfLE (idealPowSubmodule_succ_le_idealPowSmul_one I M m) ≫
        idealPowSmulIncl B S hS M (idealPowSubmodule I 1 M) I m) ≫
        (idealPowSubmodule I 1 M).ι = (idealPowSubmodule I (m + 1) M).ι ≫ 𝟙 M :=
  ((Category.assoc _ _ _).trans ((congrArg (Stacks.SheafOfModules.Submodule.homOfLE
    (idealPowSubmodule_succ_le_idealPowSmul_one I M m) ≫ ·)
      (Stacks.SheafOfModules.Submodule.homOfLE_comp_ι _)).trans
        (Stacks.SheafOfModules.Submodule.homOfLE_comp_ι _))).trans (Category.comp_id _).symm

/-- The square `M = M`, `M/Iᵐ⁺¹M ⟶ M/IM` of the morphism of short exact sequences. -/
theorem idealPowCokernelShortComplex_comm₂₃ (m : ℕ) :
    𝟙 M ≫ idealPowTowerπ I M 1 = idealPowTowerπ I M (m + 1) ≫ idealPowTransitionToOne I M m :=
  (Category.id_comp _).trans (π_idealPowTransitionToOne I M m).symm

end Tower

/-- A proper `f'` over the spectrum of a stalk makes the source locally Noetherian étale-locally. -/
private theorem fact_hasEtaleLocalProperty_of_isProper_stalkPoint (Y : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    (y : (BigFppfOver.toScheme B S hS).obj Y) {X' : AlgebraicSpaces B S hS}
    {f' : X' ⟶ representedAlgebraicSpace B S hS (stalkPointObject Y y)}
    (hf' : IsProper B S hS f'.hom) :
    Fact (HasEtaleLocalProperty B S hS X'.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  ⟨(isNoetherian_of_isProper_schemeSpace B S hS B.contains_terminal inferInstance inferInstance
    f' hf').2.2⟩

/-- The `n`-th power of the fibre ideal times a coherent module is coherent. -/
private theorem isCoherent_idealPowSubmodule_fibreIdeal {X : AlgebraicSpaces B S hS}
    {P T : BigFppfOver B S hS} (ι : P ⟶ T)
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (f : X ⟶ representedAlgebraicSpace B S hS T)
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (n : ℕ) (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G) :
    IsCoherent B S hS X.1 X.2 (idealPowSubmodule (fibreIdeal ι hι f) n G).toSheafOfModules :=
  isCoherent_idealPowModule_of_isQuasicoherentOnSite B S hS X.1 X.2 _ n G hG
    (isQuasicoherentOnSite_definingIdealSheaf B S hS X _)

/-! ### The two clauses from a bound on the images of `Hᵖ(X, IᵐN₀) ⟶ Hᵖ(X, N₀)` -/

section Bound

variable {X : AlgebraicSpaces B S hS} {P T : BigFppfOver B S hS} (ι : P ⟶ T)
  (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
  (f : X ⟶ representedAlgebraicSpace B S hS T)
  (J : Ideal (RingCat.sectionsSubring
    (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).O).obj))

/-- **Clause (1) from a bound on images**, for `N₀ = ⊤`: if the image of
`Hⁱ(X, IⁿG) ⟶ Hⁱ(X, G)` lies in `Jᵏ Hⁱ(X, G)`, so does the kernel of `Hⁱ(X, G) ⟶ Hⁱ(X, G/IⁿG)`. -/
theorem ker_rightDerived_idealPowTowerπ_le_of_range_le (G : Modules.{u, u} B S hS X.1 X.2)
    (i n k : ℕ)
    (h : LinearMap.range ((globalSectionsRestrictScalars B S hS f).map
      ((modulesCohomologyFunctor B S hS X i).map
        (idealPowSmulIncl B S hS G ⊤ (fibreIdeal ι hι f) n))).hom ≤ J ^ k • ⊤) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    LinearMap.ker ((globalSectionsRestrictScalars B S hS f).map
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).map
          (idealPowTowerπ (fibreIdeal ι hι f) G n))).hom ≤ J ^ k • ⊤ :=
  (firstCohomologyDeltaFunctor B S hS X).ker_map_g_le_pow_smul_top
    (idealPowCokernelShortComplex_shortExact (fibreIdeal ι hι f) G n) i
    (globalSectionsRingHomSite B S hS f) J k
    (𝟙 (idealPowSubmodule (fibreIdeal ι hι f) n G).toSheafOfModules)
    (idealPowSmulIncl B S hS G ⊤ (fibreIdeal ι hι f) n) (⊤ : G.Submodule).ι
    ((Category.id_comp _).trans (Stacks.SheafOfModules.Submodule.homOfLE_comp_ι _)) h

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
  [IsNoetherianRing (RingCat.sectionsSubring
    (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).O).obj)]

/-- **Clause (3) in degree zero from a bound on images**, for `N₀ = IG`: if the images of
`H¹(X, Iᵐ(IG)) ⟶ H¹(X, IG)` lie in `J^{m-c} H¹(X, IG)` and the transitions
`H⁰(X, G/Iᵐ⁺¹G) ⟶ H⁰(X, G/IG)` are surjective, so is `H⁰(X, G) ⟶ H⁰(X, G/IG)`. -/
theorem epi_rightDerived_zero_idealPowTowerπ_one_of_range_le
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hf : IsProper B S hS f.hom) (hJ : J ≤ Ideal.jacobson ⊥)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G) (c : ℕ)
    (hc : ∀ m, c ≤ m → LinearMap.range ((globalSectionsRestrictScalars B S hS f).map
      ((modulesCohomologyFunctor B S hS X 1).map (idealPowSmulIncl B S hS G
        (idealPowSubmodule (fibreIdeal ι hι f) 1 G) (fibreIdeal ι hι f) m))).hom ≤
          J ^ (m - c) • ⊤) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (∀ m, Epi (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map
          (idealPowTransitionToOne (fibreIdeal ι hι f) G m))) →
      Epi (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map
          (idealPowTowerπ (fibreIdeal ι hι f) G 1)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  change (∀ m, _) → _
  intro hepi
  have hfin : Module.Finite (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O).obj)
      ((ModuleCat.restrictScalars (globalSectionsRingHomSite B S hS f)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj
            (idealPowSubmodule (fibreIdeal ι hι f) 1 G).toSheafOfModules)) :=
    hasFiniteGlobalCohomologyOver_of_isProper B S hS B.contains_terminal f hf
      (idealPowModule (fibreIdeal ι hι f) 1 G)
      (isCoherent_idealPowSubmodule_fibreIdeal ι hι f 1 G hG) 1
  exact (firstCohomologyDeltaFunctor B S hS X).epi_map_g_zero_of_range_le
    (E := (idealPowCokernelShortComplex (fibreIdeal ι hι f) G 1))
    (A := (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).O).obj))
    (firstCohomologyDeltaFunctor B S hS X).functor (fun _ => rfl)
    (idealPowCokernelShortComplex_shortExact (fibreIdeal ι hι f) G 1)
    (fun m => idealPowCokernelShortComplex (fibreIdeal ι hι f) G (m + 1))
    (fun m => idealPowCokernelShortComplex_shortExact (fibreIdeal ι hι f) G (m + 1))
    (fun m => ShortComplex.Hom.mk
      (Stacks.SheafOfModules.Submodule.homOfLE
        (idealPowSubmodule_succ_le_idealPowSmul_one (fibreIdeal ι hι f) G m) ≫
          idealPowSmulIncl B S hS G (idealPowSubmodule (fibreIdeal ι hι f) 1 G)
            (fibreIdeal ι hι f) m)
      (𝟙 G) (idealPowTransitionToOne (fibreIdeal ι hι f) G m)
      (idealPowCokernelShortComplex_comm₁₂ (fibreIdeal ι hι f) G m)
      (idealPowCokernelShortComplex_comm₂₃ (fibreIdeal ι hι f) G m)) hepi
    (globalSectionsRingHomSite B S hS f) J hJ hfin
    (fun m => (Stacks.Sites.idealPowSmul (M := G) (fibreIdeal ι hι f) m
      (idealPowSubmodule (fibreIdeal ι hι f) 1 G)).toSheafOfModules)
    (fun m => Stacks.SheafOfModules.Submodule.homOfLE
      (idealPowSubmodule_succ_le_idealPowSmul_one (fibreIdeal ι hι f) G m))
    (fun m => idealPowSmulIncl B S hS G (idealPowSubmodule (fibreIdeal ι hι f) 1 G)
      (fibreIdeal ι hι f) m)
    (fun _ => rfl) c hc

end Bound

/-! ### The bound on images over the ring of `h_T`, for the ideal of a closed fibre -/

section FibreBound

variable {X : AlgebraicSpaces B S hS} {P T : BigFppfOver B S hS} (ι : P ⟶ T)
  (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
  (f : X ⟶ representedAlgebraicSpace B S hS T)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)] in
/-- A function of `Γ(h_T)` whose value at the identity chart lies in `J = ker Γ(ι)` lies in
`J' = ker(Γ(h_T) ⟶ Γ(h_P))`. -/
theorem mem_ker_globalSectionsRingHomSite_representedSpaceMap_of_chartEval
    (a : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O).obj)
    (ha : (globalSectionsChartRingEquiv B S hS (representedAlgebraicSpace B S hS T)
      (isTerminalIdEtaleChart B S hS T)).toEquiv a ∈
        RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom) :
    a ∈ RingHom.ker (globalSectionsRingHomSite B S hS (representedSpaceMap B S hS ι)) :=
  RingHom.mem_ker.2 ((bijective_globalSectionsChartEval_of_isTerminal B S hS
    (representedAlgebraicSpace B S hS P) (isTerminalIdEtaleChart B S hS P)).1
      (((globalSectionsChartEval_globalSectionsRingHomSite B S hS (representedSpaceMap B S hS ι)
        ⟨idEtaleChart B S hS P, idEtaleChart B S hS T, ι,
          (Category.id_comp _).trans (Category.comp_id _).symm⟩ a).trans
            (RingHom.mem_ker.1 ha)).trans (map_zero _).symm))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)] in
/-- The functions of `Γ(h_T)` on `X` are the functions of the base read through the identity
chart of `T`. -/
theorem globalSectionsRingHomSite_eq_baseScalarRingHom_chartEval
    (a : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O).obj) :
    globalSectionsRingHomSite B S hS f a =
      baseScalarRingHom B S hS T f ((globalSectionsChartRingEquiv B S hS
        (representedAlgebraicSpace B S hS T) (isTerminalIdEtaleChart B S hS T)).toEquiv a) :=
  congrArg (globalSectionsRingHomSite B S hS f)
    ((schemeSpaceGlobalSectionsEquiv B S hS T).symm_apply_apply a).symm

/-- **The images of `Hᵖ(X, IᵐN₀) ⟶ Hᵖ(X, N₀)` lie in `J^{m-c} Hᵖ(X, N₀)`**, for `I` the ideal of
the fibre over a closed `ι : P ⟶ T` and `J = ker(Γ(h_T) ⟶ Γ(h_P))`: the stability of the
filtration (`AlgebraicGeometry.Space.cohomologyIdealPowFiltration_stable`), read over `Γ(h_T)`. -/
theorem exists_range_idealPowSmulIncl_le_fibreIdeal (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (N₀ : F.Submodule)
    (hN₀ : IsCoherent B S hS X.1 X.2 N₀.toSheafOfModules) (p : ℕ) :
    ∃ c : ℕ, ∀ m, c ≤ m → LinearMap.range ((globalSectionsRestrictScalars B S hS f).map
      ((modulesCohomologyFunctor B S hS X p).map
        (idealPowSmulIncl B S hS F N₀ (fibreIdeal ι hι f) m))).hom ≤
      RingHom.ker (globalSectionsRingHomSite B S hS (representedSpaceMap B S hS ι)) ^ (m - c) •
        ⊤ := by
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  refine Exists.elim (exists_fin_span_eq_ker ι) fun r hr => Exists.elim hr fun x hx => ?_
  have hJ : ∀ a ∈ RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom,
      ∀ W : SmallEtale B S hS X.1, (baseScalar f a).1 (op W) ∈ (fibreIdeal ι hι f).obj (op W) :=
    fun a ha W => baseScalar_val_mem_fibreIdeal f ι hι a ha W
  have hxJ : ∀ i, x i ∈ RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom :=
    fun i => hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have hst := cohomologyIdealPowFiltration_stable B S hS T (X := X) f
    (RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom) hf F N₀ hN₀
    (fibreIdeal ι hι f) hJ x hxJ
    (fun A hA b hb => exists_eq_sum_baseScalar ι hι f x hx A hA b hb) p
  refine Exists.elim hst.exists_pow_smul_eq_of_ge fun c hc => ⟨c, fun m hm y hy => ?_⟩
  refine Exists.elim hy fun z hz => ?_
  have hy₀ := (cohomologyIdealPowFiltration_N B S hS T (X := X) f
    (RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom) F N₀ (fibreIdeal ι hι f)
    hJ p m).ge ⟨z, hz⟩
  have hy₁ := Submodule.smul_mono le_rfl le_top ((hc m hm).le hy₀)
  exact ModuleCat.mem_pow_smul_top_restrictScalars_of_equiv
    (A₀ := Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (A' := RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O).obj)
    (Γ := RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (baseScalarRingHom B S hS T f) (globalSectionsRingHomSite B S hS f)
    (globalSectionsChartRingEquiv B S hS (representedAlgebraicSpace B S hS T)
      (isTerminalIdEtaleChart B S hS T)).toEquiv
    (fun a b => map_mul (globalSectionsChartRingEquiv B S hS (representedAlgebraicSpace B S hS T)
      (isTerminalIdEtaleChart B S hS T)) a b)
    (fun a b => map_add (globalSectionsChartRingEquiv B S hS (representedAlgebraicSpace B S hS T)
      (isTerminalIdEtaleChart B S hS T)) a b)
    (globalSectionsRingHomSite_eq_baseScalarRingHom_chartEval f)
    (RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)
    (RingHom.ker (globalSectionsRingHomSite B S hS (representedSpaceMap B S hS ι)))
    (mem_ker_globalSectionsRingHomSite_representedSpaceMap_of_chartEval ι) _ (m - c) y hy₁

end FibreBound

/-! ### Clauses (1) and (3) of the theorem on formal functions over `Spec 𝒪_{Y,y}` -/

/-- **Clause (1) of the theorem on formal functions over `Spec 𝒪_{Y,y}`** (Stacks 08AY (1)). -/
theorem formalFunctionsKernelClause : FormalFunctionsKernelClause B S hS := by
  intro Y _ y X' f' hf' G hG i
  have := fact_hasEtaleLocalProperty_of_isProper_stalkPoint Y y hf'
  have hN₀ := isCoherent_idealPowSubmodule_fibreIdeal (residueToStalkPointHom Y y)
    (isClosedImmersion_residueToStalkPointHom Y y) f' 0 G hG
  rw [idealPowSubmodule_zero] at hN₀
  exact Exists.elim (exists_range_idealPowSmulIncl_le_fibreIdeal (residueToStalkPointHom Y y)
    (isClosedImmersion_residueToStalkPointHom Y y) f' hf' G ⊤ hN₀ i) fun c hc =>
    ⟨c, fun n hn => ker_rightDerived_idealPowTowerπ_le_of_range_le
      (residueToStalkPointHom Y y) (isClosedImmersion_residueToStalkPointHom Y y) f'
      (RingHom.ker (globalSectionsRingHomSite B S hS
        (representedSpaceMap B S hS (residueToStalkPointHom Y y)))) G i n (n - c) (hc n hn)⟩

/-- **Clause (3) of the theorem on formal functions over `Spec 𝒪_{Y,y}`, in degree zero**
(the consequence of Stacks 08AY (3) used by Stacks 0D39). -/
theorem formalFunctionsImageClause : FormalFunctionsImageClause B S hS := by
  intro Y _ y X' f' hf' G hG
  have := fact_hasEtaleLocalProperty_of_isProper_stalkPoint Y y hf'
  have : IsNoetherianRing (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj (stalkPointObject Y y)) (isAlgebraicSpace_yoneda B S hS _)).O).obj) :=
    isNoetherianRing_globalSections_schemeSpace B S hS (stalkPointObject Y y)
  have hN₀ := isCoherent_idealPowSubmodule_fibreIdeal (residueToStalkPointHom Y y)
    (isClosedImmersion_residueToStalkPointHom Y y) f' 1 G hG
  exact Exists.elim (exists_range_idealPowSmulIncl_le_fibreIdeal (residueToStalkPointHom Y y)
    (isClosedImmersion_residueToStalkPointHom Y y) f' hf' G
    (idealPowSubmodule (fibreIdeal (residueToStalkPointHom Y y)
      (isClosedImmersion_residueToStalkPointHom Y y) f') 1 G) hN₀ 1) fun c hc =>
    epi_rightDerived_zero_idealPowTowerπ_one_of_range_le (residueToStalkPointHom Y y)
      (isClosedImmersion_residueToStalkPointHom Y y) f'
      (RingHom.ker (globalSectionsRingHomSite B S hS
        (representedSpaceMap B S hS (residueToStalkPointHom Y y)))) hf'
      (ker_globalSectionsRingHomSite_residueToStalkPointHom_le_jacobson Y y) G hG c hc

end AlgebraicGeometry.Space

end
