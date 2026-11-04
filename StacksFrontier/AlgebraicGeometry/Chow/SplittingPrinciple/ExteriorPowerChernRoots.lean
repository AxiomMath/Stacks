module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerLineSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernPowerSumElem
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.FiltrationChowCohomology

/-!
# The Chern roots of the exterior powers of a filtered module

Let `X` be locally of finite type over the base of chapter 42 and let `ℰ` be finite locally free
of rank `r` with a filtration whose successive quotients are invertible modules `ℒ₁, …, ℒᵣ`, with
first Chern classes `x₁, …, xᵣ`. Then

  `c(⋀ⁿ ℰ) = ∏_{#I = n} (1 + ∑_{i ∈ I} xᵢ)`

in the ring of graded cap families: the Chern roots of `⋀ⁿ ℰ` are the sums of `n` distinct Chern
roots of `ℰ`. This is the display in the proof of [Stacks, Tag 0FEE].

The bottom step `ℒᵣ ⊆ ℰ` of the filtration is an invertible subsheaf with quotient `𝒬` filtered
by `ℒ₁, …, ℒ_{r-1}`, and

  `0 → ⋀¹ ℒᵣ ⊗ ⋀ⁿ⁻¹ 𝒬 → ⋀ⁿ ℰ → ⋀ⁿ 𝒬 → 0`

is short exact (`Stacks.SheafOfModules.TopWedge.shortExact_lineComparison`).

## Main results

* `AlgebraicGeometry.Scheme.Modules.shortExact_exteriorPower_of_rankOne`: the exact sequence on
  a scheme.
* `Stacks.Chow.shortExact_thirdIso`: the third isomorphism theorem for sheaves of modules.
* `Stacks.Chow.exists_bottom_of_hasQuotients`: the bottom step of a filtration with prescribed
  quotients, with its quotient filtered by the remaining quotients.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {N V Q : X.Modules}

/-- **The exterior powers of a module with an invertible submodule, on a scheme.** For
`0 → N → V → Q → 0` short exact with `N` of rank one and `Q` finite locally free of rank `m`,
the sequence `0 → ⋀¹ N ⊗ ⋀ᵏ⁺¹ Q → ⋀ᵏ⁺² V → ⋀ᵏ⁺² Q → 0` is short exact. -/
theorem shortExact_exteriorPower_of_rankOne (f : N ⟶ V) (g : V ⟶ Q) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q m] (k : ℕ) :
    ∃ (φ : tensorObj (exteriorPower N 1) (exteriorPower Q ((k + 1 : ℕ) : ℤ)) ⟶
        exteriorPower V ((1 + (k + 1) : ℕ) : ℤ))
      (w : φ ≫ exteriorPowerMap g ((1 + (k + 1) : ℕ) : ℤ) = 0),
      (ShortComplex.mk φ (exteriorPowerMap g ((1 + (k + 1) : ℕ) : ℤ)) w).ShortExact := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf) N 1 := ‹_›
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf) Q m := ‹_›
  have : Mono (C := _root_.SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf)) f := hS.mono_f
  have : Epi (C := _root_.SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf)) g := hS.epi_g
  have hz := Stacks.SheafOfModules.TopWedge.lineComparison_comp_extHom (X := X.toTopCat)
      (Osharp := X.sheaf) (_root_.SheafOfModules.algebras _ N)
      (_root_.SheafOfModules.algebras _ V) (_root_.SheafOfModules.algebras _ Q) f g hfg
      hS.exact m k
  have hw : (Stacks.SheafOfModules.TopWedge.lineComparison (X := X.toTopCat) (Osharp := X.sheaf)
      (_root_.SheafOfModules.algebras _ N) (_root_.SheafOfModules.algebras _ V)
      (_root_.SheafOfModules.algebras _ Q) f g hfg hS.exact k : tensorObj (exteriorPower N 1)
        (exteriorPower Q ((k + 1 : ℕ) : ℤ)) ⟶ exteriorPower V ((1 + (k + 1) : ℕ) : ℤ)) ≫
      exteriorPowerMap g ((1 + (k + 1) : ℕ) : ℤ) = 0 :=
    _root_.SheafOfModules.hom_ext (congrArg (fun φ => φ.val) hz)
  have hse := Stacks.SheafOfModules.TopWedge.shortExact_lineComparison (X := X.toTopCat)
      (Osharp := X.sheaf) (_root_.SheafOfModules.algebras _ N)
      (_root_.SheafOfModules.algebras _ V) (_root_.SheafOfModules.algebras _ Q) f g hfg
      hS.exact m k
  exact ⟨_, hw, hse⟩

end AlgebraicGeometry.Scheme.Modules

/-! ### The bottom step of a filtration -/

namespace LinearMap

variable {R : Type*} [Ring R] {N F V L QF Q : Type*} [AddCommGroup N] [Module R N]
  [AddCommGroup F] [Module R F] [AddCommGroup V] [Module R V] [AddCommGroup L] [Module R L]
  [AddCommGroup QF] [Module R QF] [AddCommGroup Q] [Module R Q]

/-- **The third isomorphism theorem, read on exact sequences.** For `N ⊆ F ⊆ V`, with
`QF = F/N`, `Q = V/N` and `L = V/F`, the induced sequence `0 → QF → Q → L → 0` is exact. -/
theorem third_iso_exact (f₁ : N →ₗ[R] F) (g₁ : F →ₗ[R] QF) (f₀ : F →ₗ[R] V) (g₀ : V →ₗ[R] L)
    (π : V →ₗ[R] Q) (a : QF →ₗ[R] Q) (b : Q →ₗ[R] L) (hf₀ : Function.Injective f₀)
    (hg₁ : Function.Surjective g₁) (hg₀ : Function.Surjective g₀)
    (hex₀ : ∀ v, g₀ v = 0 → ∃ y, f₀ y = v) (hg₀f₀ : ∀ y, g₀ (f₀ y) = 0)
    (hg₁f₁ : ∀ n, g₁ (f₁ n) = 0) (hπ : Function.Surjective π)
    (hkerπ : ∀ v, π v = 0 → ∃ n, f₀ (f₁ n) = v)
    (ha : ∀ y, a (g₁ y) = π (f₀ y)) (hb : ∀ v, b (π v) = g₀ v) :
    Function.Injective a ∧ Function.Surjective b ∧ (∀ q, b (a q) = 0) ∧
      ∀ z, b z = 0 → ∃ q, a q = z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero a).2 fun q hq => ?_
    obtain ⟨y, rfl⟩ := hg₁ q
    obtain ⟨n, hn⟩ := hkerπ (f₀ y) ((ha y).symm.trans hq)
    rw [← hf₀ hn, hg₁f₁]
  · intro l
    obtain ⟨v, rfl⟩ := hg₀ l
    exact ⟨π v, hb v⟩
  · intro q
    obtain ⟨y, rfl⟩ := hg₁ q
    rw [ha, hb, hg₀f₀]
  · intro z hz
    obtain ⟨v, rfl⟩ := hπ z
    obtain ⟨y, rfl⟩ := hex₀ v ((hb v).symm.trans hz)
    exact ⟨g₁ y, ha y⟩

end LinearMap

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- The cokernel sequence of a composite of two monomorphisms is short exact. -/
private theorem shortExact_cokernelSequence_comp {N F V : X.Modules} (f₁ : N ⟶ F) (f₀ : F ⟶ V)
    [Mono f₁] [Mono f₀] : (ShortComplex.cokernelSequence (f₁ ≫ f₀)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (show Mono (f₁ ≫ f₀) from mono_comp _ _) inferInstance

section ThirdIso

variable {N F V L QF : X.Modules} (f₁ : N ⟶ F) (g₁ : F ⟶ QF) (w₁ : f₁ ≫ g₁ = 0)
  (h₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact) (f₀ : F ⟶ V) (g₀ : V ⟶ L) (w₀ : f₀ ≫ g₀ = 0)
  (h₀ : (ShortComplex.mk f₀ g₀ w₀).ShortExact)

/-- The map `F/N ⟶ V/N` of the third isomorphism theorem. -/
noncomputable def thirdIsoLeft : QF ⟶ cokernel (f₁ ≫ f₀) :=
  haveI := h₁.epi_g
  h₁.exact.desc (f₀ ≫ cokernel.π (f₁ ≫ f₀)) (by
    change f₁ ≫ f₀ ≫ cokernel.π (f₁ ≫ f₀) = 0
    rw [← Category.assoc, cokernel.condition])

/-- The map `V/N ⟶ V/F` of the third isomorphism theorem. -/
noncomputable def thirdIsoRight : cokernel (f₁ ≫ f₀) ⟶ L :=
  cokernel.desc (f₁ ≫ f₀) g₀ (by rw [Category.assoc, w₀, comp_zero])

/-- The composite `F ⟶ F/N ⟶ V/N` is `F ⟶ V ⟶ V/N`. -/
theorem g_thirdIsoLeft : g₁ ≫ thirdIsoLeft f₁ g₁ w₁ h₁ f₀ = f₀ ≫ cokernel.π (f₁ ≫ f₀) :=
  have := h₁.epi_g
  h₁.exact.g_desc _ _

/-- The composite `F/N ⟶ V/N ⟶ V/F` is zero. -/
theorem thirdIsoLeft_comp_thirdIsoRight :
    thirdIsoLeft f₁ g₁ w₁ h₁ f₀ ≫ thirdIsoRight f₁ f₀ g₀ w₀ = 0 := by
  have := h₁.epi_g
  refine (cancel_epi g₁).1 ?_
  rw [← Category.assoc, g_thirdIsoLeft, Category.assoc, thirdIsoRight, cokernel.π_desc, w₀,
    comp_zero]

include h₀ in
/-- **The third isomorphism theorem for sheaves of modules**: for `N ⊆ F ⊆ V` the sequence
`0 → F/N → V/N → V/F → 0` is short exact. -/
theorem shortExact_thirdIso :
    (ShortComplex.mk (thirdIsoLeft f₁ g₁ w₁ h₁ f₀) (thirdIsoRight f₁ f₀ g₀ w₀)
      (thirdIsoLeft_comp_thirdIsoRight f₁ g₁ w₁ h₁ f₀ g₀ w₀)).ShortExact := by
  have := h₀.mono_f
  have := h₁.mono_f
  refine (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact _).2
    fun x => ?_
  have st := fun {S : ShortComplex X.Modules} (h : S.ShortExact) =>
    (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact _).1 h x
  have e₀ := st h₀
  have e₁ := st h₁
  have ec := st (shortExact_cokernelSequence_comp f₁ f₀)
  have mc : ∀ {A B D : X.Modules} (φ : A ⟶ B) (ψ : B ⟶ D) y,
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map (φ ≫ ψ)).hom y =
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map ψ).hom
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map φ).hom y) :=
    fun φ ψ y => congrArg (fun m => ModuleCat.Hom.hom m y)
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map_comp φ ψ)
  have key := LinearMap.third_iso_exact
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map f₁).hom
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map g₁).hom
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map f₀).hom
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map g₀).hom
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map (cokernel.π (f₁ ≫ f₀))).hom
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map
      (thirdIsoLeft f₁ g₁ w₁ h₁ f₀)).hom
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map (thirdIsoRight f₁ f₀ g₀ w₀)).hom
    e₀.moduleCat_injective_f e₁.moduleCat_surjective_g e₀.moduleCat_surjective_g
    (fun v hv => (ShortComplex.moduleCat_exact_iff _).1 e₀.exact v hv)
    (fun y => LinearMap.mem_ker.1
      (e₀.exact.moduleCat_range_eq_ker ▸ LinearMap.mem_range_self _ y))
    (fun n => LinearMap.mem_ker.1
      (e₁.exact.moduleCat_range_eq_ker ▸ LinearMap.mem_range_self _ n))
    ec.moduleCat_surjective_g
    (fun v hv => by
      obtain ⟨n, hn⟩ := (ShortComplex.moduleCat_exact_iff _).1 ec.exact v hv
      exact ⟨n, (mc f₁ f₀ n).symm.trans hn⟩)
    (fun y => (mc g₁ _ y).symm.trans ((congrArg
      (fun φ => ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map φ).hom y)
      (g_thirdIsoLeft f₁ g₁ w₁ h₁ f₀)).trans (mc f₀ _ y)))
    (fun v => (mc _ _ v).symm.trans (congrArg
      (fun φ => ((AlgebraicGeometry.SheafOfModules.stalkFunctor _ x).map φ).hom v)
      (cokernel.π_desc (f₁ ≫ f₀) g₀ (by rw [Category.assoc, w₀, comp_zero]))))
  obtain ⟨hinj, hsurj, -, hex⟩ := key
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 hinj)
    ((ModuleCat.epi_iff_surjective _).2 hsurj)
  exact (ShortComplex.moduleCat_exact_iff _).2 hex

end ThirdIso

/-- **The bottom step of a filtration with prescribed quotients.** If `ℰ` carries a filtration of
length `r + 1` with successive quotients `ℒ₀, …, ℒᵣ` (the first one on top), its bottom step is a
subsheaf `N ≅ ℒᵣ` whose quotient carries a filtration with successive quotients
`ℒ₀, …, ℒ_{r-1}`. -/
theorem exists_bottom_of_hasQuotients : ∀ (r : ℕ) (V : X.Modules) (L : Fin (r + 1) → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (L i) 1],
    HasQuotients X (r + 1) V L →
      ∃ (N : X.Modules) (_ : N ≅ L (Fin.last r)) (Q : X.Modules) (f : N ⟶ V) (g : V ⟶ Q)
        (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧
          HasQuotients X r Q (fun i => L i.castSucc) := by
  intro r
  induction r with
  | zero =>
      intro V L _ h
      obtain ⟨F, _, f₀, g₀, w₀, hS, hF⟩ := h
      have hf₀ : f₀ = 0 := IsZero.eq_of_src hF _ _
      have := hS.epi_g
      have : Mono g₀ := hS.exact.mono_g hf₀
      have : IsIso g₀ := isIso_of_mono_of_epi g₀
      refine ⟨L 0, Iso.refl _, F, inv g₀, 0, IsZero.eq_of_tgt hF _ _, ?_, hF⟩
      refine ShortComplex.ShortExact.mk' ?_ inferInstance (IsZero.epi hF _)
      exact (ShortComplex.exact_iff_epi _ rfl).2 inferInstance
  | succ r ih =>
      intro V L _ h
      obtain ⟨F, hF, f₀, g₀, w₀, h₀, hrec⟩ := h
      obtain ⟨N, eN, QF, f₁, g₁, w₁, h₁, hQF⟩ := ih F (fun i => L i.succ) hrec
      refine ⟨N, eN ≪≫ eqToIso (congrArg L (Fin.succ_last r)), cokernel (f₁ ≫ f₀), f₁ ≫ f₀,
        cokernel.π _, cokernel.condition _, ?_, ?_⟩
      · have := h₀.mono_f
        have := h₁.mono_f
        exact shortExact_cokernelSequence_comp f₁ f₀
      · have hQF' : HasQuotients X r QF (fun i => L i.succ.castSucc) := by
          simpa only [Fin.succ_castSucc] using hQF
        exact ⟨QF, isFiniteLocallyFreeOfRank_of_hasQuotients r QF _ hQF',
          thirdIsoLeft f₁ g₁ w₁ h₁ f₀, thirdIsoRight f₁ f₀ g₀ w₀,
          thirdIsoLeft_comp_thirdIsoRight f₁ g₁ w₁ h₁ f₀ g₀ w₀,
          shortExact_thirdIso f₁ g₁ w₁ h₁ f₀ g₀ w₀ h₀, hQF'⟩

end Stacks.Chow
