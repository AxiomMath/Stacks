module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent modules and coherent rings

Let `R` be a ring. An `R`-module `M` is *coherent* if it is finitely generated and every finitely
generated submodule of `M` is finitely presented over `R`. A ring `R` is *coherent* if it is
coherent as a module over itself.

## Main definitions

* `Module.IsCoherent`: coherent modules.
* `IsCoherentRing`: coherent rings.

## Main results

* `isCoherent_of_fg_submodule`: a finitely generated submodule of a coherent module is coherent.
* `finite_ker_and_coherent_range_coker`: for `φ : N →ₗ[R] M` with `N` finite and `M` coherent,
  `ker φ` is finite while `range φ` and `M ⧸ range φ` are coherent.
* `coherent_ker_and_coker_of_coherent`: the kernel and cokernel of a map of coherent modules are
  coherent.
* `isCoherent_two_out_of_three`: in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, coherence of
  two of the three modules implies coherence of the third.
* `coherent_iff_finitePresentation_of_coherentRing`: over a coherent ring, a module is coherent if
  and only if it is finitely presented.
* `isCoherentRing_of_isNoetherianRing`: a Noetherian ring is a coherent ring.
* `isCoherentRing_iff_forall_fg_ideal_finitePresentation`: a ring is coherent if and only if every
  finitely generated ideal is finitely presented.
-/

@[expose] public section

@[expose] public section

/-- An `R`-module `M` is *coherent* if it is finitely generated and every
finitely generated submodule of `M` is finitely presented over `R`. -/
@[stacks_fixed 05CV "(1) coherent module: finite, every f.g. submodule finitely presented",
  sga "6 I 3.1" "special case", sga "6 IV 2.1" "special case"]
class Module.IsCoherent (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    Prop where
  /-- A coherent module is finitely generated. -/
  finite : Module.Finite R M
  /-- Every finitely generated submodule of a coherent module is finitely
  presented. -/
  fg_submodule_finitePresentation :
    ∀ (N : Submodule R M), N.FG → Module.FinitePresentation R N

/-- A ring `R` is a *coherent ring* if it is coherent as a module over itself. -/
@[stacks_fixed 05CV "(2) coherent ring: coherent as a module over itself",
  ega "0 5.3.7" "special case"]
class IsCoherentRing (R : Type*) [Ring R] : Prop where
  /-- A coherent ring is coherent as a module over itself. -/
  isCoherent : Module.IsCoherent R R

/-- `M` is coherent if and only if it is finite and every finitely generated submodule of `M` is
finitely presented. -/
theorem Module.isCoherent_iff (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    Module.IsCoherent R M ↔
      Module.Finite R M ∧
        ∀ (N : Submodule R M), N.FG → Module.FinitePresentation R N :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

/-- A ring is coherent iff it is coherent as a module over itself. -/
theorem isCoherentRing_iff (R : Type*) [Ring R] :
    IsCoherentRing R ↔ Module.IsCoherent R R :=
  ⟨fun h ↦ h.isCoherent, fun h ↦ ⟨h⟩⟩

end
end

@[expose] public section

/-- A finitely generated submodule of a coherent module is coherent. -/
@[stacks 05CW "(1)", ega "0 5.3.2" "submodule clause, ring", ega "0 5.3.4" "special case"]
theorem isCoherent_of_fg_submodule
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Module.IsCoherent R M]
    (N : Submodule R M) (hN : N.FG) :
    Module.IsCoherent R N := by
  refine ⟨Module.Finite.of_fg hN, fun K hK => ?_⟩
  have := Module.IsCoherent.fg_submodule_finitePresentation _ (hK.map N.subtype)
  exact Module.FinitePresentation.of_equiv
    (Submodule.equivMapOfInjective N.subtype Subtype.coe_injective K).symm

/-- If `p : P →ₗ[R] M` is surjective, `P` is finite, `p.ker` is finitely generated,
and every finitely generated submodule of `P` is finitely presented, then `M` is coherent. -/
private theorem isCoherent_of_surjective_of_fg_ker
    {R P M : Type*} [Ring R] [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    [Module.Finite R P] (p : P →ₗ[R] M) (hp : Function.Surjective p)
    (hker : p.ker.FG)
    (hP : ∀ N : Submodule R P, N.FG → Module.FinitePresentation R N) :
    Module.IsCoherent R M := by
  refine ⟨Module.Finite.of_surjective p hp, fun N hN => ?_⟩
  set N' : Submodule R P := N.comap p
  have hmap : N'.map p = N := Submodule.map_comap_eq_of_surjective hp N
  have hinf : N' ⊓ p.ker = p.ker :=
    inf_eq_right.mpr fun x hx => show p x ∈ N from (LinearMap.mem_ker.mp hx) ▸ N.zero_mem
  have := hP N' (Submodule.fg_of_fg_map_of_fg_inf_ker p (by rwa [hmap]) (by rwa [hinf]))
  set g : N' →ₗ[R] N := LinearMap.codRestrict N (p ∘ₗ N'.subtype)
    fun x => Submodule.mem_comap.mp x.2 with hg
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hmap ▸ hy
    exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [g, LinearMap.codRestrict] using hxy)⟩
  have hgker : g.ker.FG := by
    refine (Submodule.fg_map_iff _ N'.injective_subtype).mp ?_
    rwa [hg, LinearMap.ker_codRestrict, LinearMap.ker_comp, Submodule.map_comap_subtype, hinf]
  exact Module.finitePresentation_of_surjective g hgsurj hgker

/-- The quotient of a coherent module by a finitely generated submodule is
coherent. -/
@[ega "0 5.3.4" "special case", ega "IV 11.9.11" "special case", sga "6 I 3.3" "Lemma 3.3 b)"]
theorem isCoherent_quotient_of_fg
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Module.IsCoherent R M]
    (P : Submodule R M) (hP : P.FG) :
    Module.IsCoherent R (M ⧸ P) := by
  have : Module.Finite R M := Module.IsCoherent.finite
  exact isCoherent_of_surjective_of_fg_ker P.mkQ P.mkQ_surjective (by rwa [Submodule.ker_mkQ])
    Module.IsCoherent.fg_submodule_finitePresentation

/-- If `φ : N → M` with `N` finite and `M` coherent, then the kernel of
`φ` is finite, the range of `φ` is coherent, and the cokernel `M ⧸ range φ` is
coherent. -/
@[stacks 05CW "(2)",
  ega "0 5.3.4" "special case",
  sga "6 I 3.3" "special case",
  sga "6 I 3.4" "partial"]
theorem finite_ker_and_coherent_range_coker
    {R N M : Type*} [Ring R] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [Module.Finite R N] [Module.IsCoherent R M]
    (φ : N →ₗ[R] M) :
    Module.Finite R (LinearMap.ker φ) ∧
      Module.IsCoherent R (LinearMap.range φ) ∧
      Module.IsCoherent R (M ⧸ LinearMap.range φ) := by
  have hrangeFG : (LinearMap.range φ).FG := Submodule.fg_range φ
  have := Module.IsCoherent.fg_submodule_finitePresentation _ hrangeFG
  refine ⟨?_, isCoherent_of_fg_submodule _ hrangeFG, isCoherent_quotient_of_fg _ hrangeFG⟩
  have hker := Module.FinitePresentation.fg_ker φ.rangeRestrict
    (LinearMap.surjective_rangeRestrict φ)
  rw [LinearMap.ker_rangeRestrict] at hker
  exact Module.Finite.of_fg hker

/-- If `φ : N → M` is a homomorphism of coherent modules, then its kernel
and cokernel are coherent. -/
@[stacks 05CW "(3)",
  ega "0 5.3.4" "special case",
  sga "6 I 3.3" "special case",
  sga "6 I 3.4" "partial",
  sga "6 IV 2.4" "partial"]
theorem coherent_ker_and_coker_of_coherent
    {R N M : Type*} [Ring R] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [Module.IsCoherent R N] [Module.IsCoherent R M]
    (φ : N →ₗ[R] M) :
    Module.IsCoherent R (LinearMap.ker φ) ∧
      Module.IsCoherent R (M ⧸ LinearMap.range φ) := by
  have : Module.Finite R N := Module.IsCoherent.finite
  obtain ⟨_, -, hcokerCoh⟩ := finite_ker_and_coherent_range_coker φ
  exact ⟨isCoherent_of_fg_submodule _ Submodule.FG.of_finite, hcokerCoh⟩

/-- Coherence transports across a linear equivalence. -/
theorem Module.IsCoherent.of_equiv
    {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.IsCoherent R M]
    (e : M ≃ₗ[R] M') : Module.IsCoherent R M' := by
  have : Module.Finite R M := Module.IsCoherent.finite
  refine ⟨Module.Finite.equiv e, fun N hN => ?_⟩
  have := Module.IsCoherent.fg_submodule_finitePresentation _ (hN.map (e.symm : M' →ₗ[R] M))
  exact Module.FinitePresentation.of_equiv
    (Submodule.equivMapOfInjective (e.symm : M' →ₗ[R] M) e.symm.injective N).symm

/-- The middle term of a short exact sequence `0 → M₁ → M₂ → M₃ → 0` with
`M₁` and `M₃` coherent is coherent. -/
theorem isCoherent_of_exact
    {R M₁ M₂ M₃ : Type*} [Ring R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] [Module.IsCoherent R M₁] [Module.IsCoherent R M₃]
    (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : LinearMap.range i = LinearMap.ker p) :
    Module.IsCoherent R M₂ := by
  have : Module.Finite R M₁ := Module.IsCoherent.finite
  have : Module.Finite R M₃ := Module.IsCoherent.finite
  have hExact : Function.Exact ⇑i ⇑p := by rw [LinearMap.exact_iff, hexact]
  refine ⟨Module.Finite.of_exact hExact hp, fun N₂ hN₂ => ?_⟩
  have : Module.Finite R N₂ := Module.Finite.of_fg hN₂
  set N₃ : Submodule R M₃ := Submodule.map p N₂ with hN₃
  have := Module.IsCoherent.fg_submodule_finitePresentation N₃ (hN₂.map p)
  set q' : N₂ →ₗ[R] N₃ := p.submoduleMap N₂ with hq'
  have hq'surj : Function.Surjective q' := p.submoduleMap_surjective N₂
  have hkerfg : (LinearMap.ker q').FG := Module.FinitePresentation.fg_ker q' hq'surj
  have hkereq : LinearMap.ker q' = Submodule.comap N₂.subtype (LinearMap.ker p) :=
    LinearMap.ker_submoduleMap ..
  set K : Submodule R M₂ := Submodule.map N₂.subtype (LinearMap.ker q') with hK
  have hKfg : K.FG := hkerfg.map N₂.subtype
  have hKeq : K = N₂ ⊓ LinearMap.ker p := by
    rw [hK, hkereq, Submodule.map_comap_subtype]
  have hKle : K ≤ LinearMap.range i := hKeq ▸ hexact ▸ inf_le_right
  set N₁ : Submodule R M₁ := Submodule.comap i K with hN₁
  have hmapN₁ : Submodule.map i N₁ = K := Submodule.map_comap_eq_self hKle
  have hN₁fg : N₁.FG := Submodule.fg_of_fg_map_injective i hi (by rwa [hmapN₁])
  have := Module.IsCoherent.fg_submodule_finitePresentation N₁ hN₁fg
  have e₁ : LinearMap.ker q' ≃ₗ[R] K :=
    Submodule.equivMapOfInjective N₂.subtype N₂.injective_subtype (LinearMap.ker q')
  have e₂ : N₁ ≃ₗ[R] K :=
    (Submodule.equivMapOfInjective i hi N₁).trans (LinearEquiv.ofEq _ _ hmapN₁)
  have : Module.FinitePresentation R (LinearMap.ker q') :=
    Module.FinitePresentation.of_equiv (e₁.trans e₂.symm).symm
  exact Module.finitePresentation_of_ker q' hq'surj

/-- Two-out-of-three for coherence in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, where `i` is
injective, `p` is surjective and `range i = ker p`: any two of `M₁`, `M₂`, `M₃` coherent imply
the third is coherent. -/
@[stacks 05CW "(4)", sga "6 I 3.3" "special case", sga "6 I 3.4" "special case"]
theorem isCoherent_two_out_of_three
    {R M₁ M₂ M₃ : Type*} [Ring R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : LinearMap.range i = LinearMap.ker p) :
    (Module.IsCoherent R M₁ → Module.IsCoherent R M₂ → Module.IsCoherent R M₃) ∧
    (Module.IsCoherent R M₁ → Module.IsCoherent R M₃ → Module.IsCoherent R M₂) ∧
    (Module.IsCoherent R M₂ → Module.IsCoherent R M₃ → Module.IsCoherent R M₁) := by
  refine ⟨fun _ _ => ?_, fun _ _ => isCoherent_of_exact i p hi hp hexact, fun _ _ => ?_⟩
  · have := (coherent_ker_and_coker_of_coherent i).right
    exact .of_equiv ((Submodule.quotEquivOfEq _ _ hexact).trans (p.quotKerEquivOfSurjective hp))
  · have := (coherent_ker_and_coker_of_coherent p).left
    exact .of_equiv ((LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hexact)).symm

end

@[expose] public section

/-- Coherence is preserved under linear equivalences. -/
theorem isCoherentModule_of_linearEquiv (R : Type*) [Ring R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : Module.IsCoherent R M) : Module.IsCoherent R N := by
  have := hM
  exact Module.IsCoherent.of_equiv e

variable (R : Type*) [CommRing R]

/-- If `p : P →ₗ[R] M` is surjective, `P` is finite, `p.ker` is finitely generated,
and every finitely generated submodule of `P` is finitely presented, then `M`
is coherent. -/
@[ega "0 5.3.4" "special case"]
theorem isCoherentModule_of_surjective
    {P M : Type*} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
    [Module.Finite R P] (p : P →ₗ[R] M) (hp : Function.Surjective p)
    (hker : p.ker.FG)
    (hP : ∀ N : Submodule R P, N.FG → Module.FinitePresentation R N) :
    Module.IsCoherent R M := by
  exact isCoherent_of_surjective_of_fg_ker p hp hker hP

/-- If `A` and `C` are coherent, so is `A × C`. -/
@[ega "0 5.3.2" "5.3.2, special case"]
theorem isCoherentModule_prod
    {A C : Type*} [AddCommGroup A] [Module R A] [AddCommGroup C] [Module R C]
    (hA : Module.IsCoherent R A) (hC : Module.IsCoherent R C) :
    Module.IsCoherent R (A × C) := by
  obtain ⟨hAfin, hAsub⟩ := hA
  obtain ⟨hCfin, hCsub⟩ := hC
  refine ⟨inferInstance, fun N hN => ?_⟩
  have := Module.Finite.iff_fg.mpr hN
  have := hCsub _ (hN.map (LinearMap.snd R A C))
  let s : N →ₗ[R] N.map (LinearMap.snd R A C) :=
    LinearMap.codRestrict _ (LinearMap.snd R A C ∘ₗ N.subtype) fun x => ⟨x, x.2, rfl⟩
  have hssurj : Function.Surjective s := by
    rintro ⟨y, x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [s, LinearMap.codRestrict] using hxy)⟩
  have := Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker s hssurj)
  let t : s.ker →ₗ[R] A := LinearMap.fst R A C ∘ₗ N.subtype ∘ₗ s.ker.subtype
  have hsnd (w : s.ker) : ((w : N) : A × C).2 = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp w.2)
  have ht_inj : Function.Injective t := fun u v h =>
    Subtype.ext (Subtype.ext (Prod.ext h ((hsnd u).trans (hsnd v).symm)))
  have := hAsub _ (Module.Finite.iff_fg.mp (Module.Finite.range t))
  have := Module.FinitePresentation.of_equiv (LinearEquiv.ofInjective t ht_inj).symm
  exact Module.finitePresentation_of_ker s hssurj

/-- The free module `Fin n → R` is coherent over a coherent ring. -/
@[ega "0 5.3.2" "5.3.2, special case"]
theorem isCoherentModule_pi_fin (hR : Module.IsCoherent R R) (n : ℕ) :
    Module.IsCoherent R (Fin n → R) := by
  induction n with
  | zero => exact ⟨inferInstance, fun _ _ => inferInstance⟩
  | succ n ih =>
    have e : ((Fin (n+1)) → R) ≃ₗ[R] R × (Fin n → R) :=
      (LinearEquiv.piCongrLeft R (fun _ : Fin (n+1) => R) (finSuccEquiv n).symm).symm ≪≫ₗ
        LinearEquiv.piOptionEquivProd R
    exact isCoherentModule_of_linearEquiv R e.symm (isCoherentModule_prod R hR ih)

/-- If `R` is a coherent ring, then an `R`-module `M` is coherent if and only if
it is finitely presented. -/
@[stacks 05CX, sga "6 I 3.5" "a) (i)⇔(ii)"]
theorem coherent_iff_finitePresentation_of_coherentRing
    (hR : Module.IsCoherent R R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    Module.IsCoherent R M ↔ Module.FinitePresentation R M := by
  refine ⟨fun ⟨hfin, hsub⟩ => ?_, fun _ => ?_⟩
  · have := hsub ⊤ (Module.finite_def.mp hfin)
    exact .of_equiv Submodule.topEquiv
  · obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
    exact isCoherentModule_of_surjective R φ hφ (Module.FinitePresentation.fg_ker φ hφ)
      (isCoherentModule_pi_fin R hR n).2

end

@[expose] public section

/-- Every left Noetherian ring is a coherent ring. -/
@[stacks 05CY, sga "6 I 3.6" "special case"]
theorem isCoherentRing_of_isNoetherianRing (R : Type*) [Ring R] [IsNoetherianRing R] :
    IsCoherentRing R :=
  ⟨⟨inferInstance, fun N hN =>
    have := Module.Finite.iff_fg.mpr hN
    Module.finitePresentation_of_finite R N⟩⟩

/-- A ring `R` is a coherent ring if and only if every finitely generated ideal
of `R` is finitely presented as an `R`-module. -/
theorem isCoherentRing_iff_forall_fg_ideal_finitePresentation (R : Type*) [Ring R] :
    IsCoherentRing R ↔ ∀ I : Ideal R, I.FG → Module.FinitePresentation R I :=
  ⟨fun h => h.isCoherent.fg_submodule_finitePresentation, fun h => ⟨⟨inferInstance, h⟩⟩⟩

end
