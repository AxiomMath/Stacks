module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Semisimple
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula

/-!
# The Brauer–Nesbitt theorem in characteristic zero

Let `A` be an algebra over a field `k` of characteristic zero, and let `M`, `N` be semisimple
`A`-modules which are finite-dimensional over `k`. If every `a ∈ A` has the same trace on `M`
and on `N`, then `M ≅ N` as `A`-modules.

This is the step "by Chebotarev density and Brauer–Nesbitt" of Drinfeld's construction of the
Galois representation attached to a cusp eigenform (Stacks Theorem 03VT): two semisimple
`ℓ`-adic representations with the same traces of Frobenius are isomorphic.

## The proof

By induction on `dim_k M`. If `M = 0` then `dim_k N = Tr(1 | N) = Tr(1 | M) = 0`. Otherwise
choose a simple submodule `S ⊆ M`. Some simple submodule of `N` is isomorphic to `S`: if not,
in the semisimple module `P = M × N` let `C` be the `S`-isotypic component and `D` the sum of
the other isotypic components. Both are fully invariant and `P = C ⊕ D`, so the projection
`π` onto `C` along `D` commutes with every `A`-endomorphism of `P`, and by the Jacobson density
theorem some `a ∈ A` acts on `P` as `π`. Then `a` kills `N ⊆ D`, so
`Tr(π | P) = Tr(a | M) + Tr(a | N) = 2 Tr(a | N) = 0`, while `π` is an idempotent with image
`C ⊇ S ≠ 0`, whose trace is `dim_k C ≠ 0`. Writing `M = S ⊕ M'` and `N = S' ⊕ N'` with
`S' ≅ S`, the modules `M'` and `N'` have equal traces and `dim_k M' < dim_k M`.

## Main results

* `Stacks.Drinfeld.exists_smul_eq_projection` — on a semisimple module finite over `k`, the
  projection onto a fully invariant submodule along a fully invariant complement is the action
  of an element of `A`.
* `Stacks.Drinfeld.exists_injective_of_trace_eq` — a simple submodule of `M` embeds in `N`.
* `Stacks.Drinfeld.nonempty_linearEquiv_of_trace_eq` — **Brauer–Nesbitt**.
* `Stacks.Drinfeld.nonempty_equiv_of_trace_eq` — the same for semisimple representations of a
  monoid: equal characters give equivalent representations.
* `Stacks.Drinfeld.isSemisimpleRepresentation_of_span_eq_top` — a homomorphism `G → GLₙ(k)`
  whose image spans all matrices (absolute irreducibility in Burnside's form) is semisimple.
* `Stacks.Drinfeld.exists_conj_of_trace_eq` — two semisimple homomorphisms `G → GLₙ(k)` with
  equal traces are conjugate by some `P ∈ GLₙ(k)`.
-/

@[expose] public noncomputable section

open Module LinearMap

namespace Stacks.Drinfeld

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The action of `a ∈ A` on an `A`-module `M`, as a `k`-linear endomorphism. -/
abbrev actionLin (k : Type*) {A : Type*} [Field k] [Ring A] [Algebra k A] (M : Type*)
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] (a : A) :
    M →ₗ[k] M :=
  DistribSMul.toLinearMap k M a

section Projection

variable {P : Type*} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]

/-- On a semisimple `A`-module `P` finite over `k`, the projection onto a fully invariant
submodule `C` along a fully invariant complement `D` is the action of an element of `A`. -/
theorem exists_smul_eq_projection [IsSemisimpleModule A P] [Module.Finite k P]
    {C D : Submodule A P} (hC : C.IsFullyInvariant) (hD : D.IsFullyInvariant) (h : IsCompl C D) :
    ∃ a : A, ∀ p : P, a • p = C.projection D h p := by
  classical
  let f : Module.End (Module.End A P) P :=
    { toFun := C.projection D h
      map_add' := map_add _
      map_smul' := fun φ p => by
        change C.projection D h (φ p) = φ (C.projection D h p)
        have h1 : φ (C.projection D h p) ∈ C := hC φ (Submodule.projection_apply_mem h p)
        have h2 : p - C.projection D h p ∈ D := by
          rw [← Submodule.projection_apply_eq_zero_iff h, map_sub,
            Submodule.projection_apply_of_mem_left h (Submodule.projection_apply_mem h p),
            sub_self]
        have h4 := Submodule.projection_apply_of_mem_right h (hD φ h2)
        rwa [map_sub, map_sub, Submodule.projection_apply_of_mem_left h h1, sub_eq_zero] at h4 }
  let b := Module.finBasis k P
  obtain ⟨a, ha⟩ := jacobson_density f (Finset.univ.image b)
  refine ⟨a, fun p => ?_⟩
  have hext : actionLin k P a = (C.projection D h).restrictScalars k :=
    b.ext fun i => (ha (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))).symm
  exact LinearMap.congr_fun hext p

/-- An isotypic component of a semisimple module is complementary to the sum of the others. -/
theorem isCompl_sSup_isotypicComponents_diff [IsSemisimpleModule A P] {C : Submodule A P}
    (hC : C ∈ isotypicComponents A P) : IsCompl C (sSup (isotypicComponents A P \ {C})) :=
  ⟨sSupIndep_isotypicComponents A P hC, codisjoint_iff.2 <| by
    rw [← sSup_insert, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hC,
      sSup_isotypicComponents]⟩

/-- A submodule of a semisimple module none of whose simple submodules lies in `C` is contained in
the sum of the isotypic components other than `C`. -/
theorem le_sSup_isotypicComponents_diff [IsSemisimpleModule A P] {C Q : Submodule A P}
    (hQ : ∀ T : Submodule A P, IsSimpleModule A T → T ≤ Q → ¬T ≤ C) :
    Q ≤ sSup (isotypicComponents A P \ {C}) := by
  rw [← IsSemisimpleModule.sSup_simples_le Q]
  refine sSup_le fun T ⟨hT, hTle⟩ => T.le_isotypicComponent.trans (le_sSup ⟨⟨T, hT, rfl⟩,
    fun hTC => hQ T hT hTle (T.le_isotypicComponent.trans_eq hTC)⟩)

end Projection

variable {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- A product of two semisimple modules is semisimple. -/
theorem isSemisimpleModule_prod [IsSemisimpleModule A M] [IsSemisimpleModule A N] :
    IsSemisimpleModule A (M × N) :=
  isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun b : Bool => Bool.rec (LinearMap.range (LinearMap.inr A M N))
      (LinearMap.range (LinearMap.inl A M N)) b)
    (fun b => by cases b <;> exact .range _)
    (by rw [iSup_bool_eq]; exact LinearMap.sup_range_inl_inr)

/-- On a submodule of `M × N` contained in `0 × N`, the second projection is injective. -/
theorem injective_snd_comp_subtype {T : Submodule A (M × N)}
    (hT : T ≤ LinearMap.range (LinearMap.inr A M N)) :
    Function.Injective (LinearMap.snd A M N ∘ₗ T.subtype) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  obtain ⟨n, hn⟩ := hT t.2
  have : n = 0 := by simpa [← hn] using ht
  ext1
  rw [← hn, this]
  simp

/-- The action of `a` on a product is the product of the actions. -/
theorem actionLin_prod (a : A) :
    actionLin k (M × N) a = (actionLin k M a).prodMap (actionLin k N a) :=
  LinearMap.ext fun _ => rfl

/-- The trace of the action is invariant under `A`-linear isomorphisms. -/
theorem trace_actionLin_congr [FiniteDimensional k M] [FiniteDimensional k N] (e : M ≃ₗ[A] N)
    (a : A) : trace k M (actionLin k M a) = trace k N (actionLin k N a) := by
  have : actionLin k N a = (e.restrictScalars k).conj (actionLin k M a) := by
    ext n
    simp [LinearEquiv.conj_apply, map_smul]
  rw [this, trace_conj']

/-- The trace of the action on `M` is the sum of the traces on two complementary submodules. -/
private theorem trace_actionLin_eq_add_of_isCompl [FiniteDimensional k M] {p q : Submodule A M}
    (h : IsCompl p q) (a : A) :
    trace k M (actionLin k M a) = trace k p (actionLin k p a) + trace k q (actionLin k q a) := by
  have (m : Submodule A M) : FiniteDimensional k m :=
    Module.Finite.of_injective (m.subtype.restrictScalars k) m.injective_subtype
  rw [← trace_actionLin_congr (Submodule.prodEquivOfIsCompl p q h) a, actionLin_prod,
    trace_prodMap']

variable [CharZero k]

/-- **Key step of Brauer–Nesbitt.** If `M` and `N` are semisimple, finite over `k`, with equal
traces, then every simple submodule of `M` embeds in `N`. -/
theorem exists_injective_of_trace_eq [IsSemisimpleModule A M] [IsSemisimpleModule A N]
    [FiniteDimensional k M] [FiniteDimensional k N]
    (htr : ∀ a : A, trace k M (actionLin k M a) = trace k N (actionLin k N a))
    (S : Submodule A M) [IsSimpleModule A S] :
    ∃ g : S →ₗ[A] N, Function.Injective g := by
  by_contra hno
  push Not at hno
  set P := M × N
  have : IsSemisimpleModule A P := isSemisimpleModule_prod
  let S' : Submodule A P := S.map (LinearMap.inl A M N)
  let eS : S ≃ₗ[A] S' := Submodule.equivMapOfInjective _ (LinearMap.inl_injective) S
  have : IsSimpleModule A S' := IsSimpleModule.congr eS.symm
  set C := isotypicComponent A P S'
  have hCmem : C ∈ isotypicComponents A P := ⟨S', inferInstance, rfl⟩
  set D := sSup (isotypicComponents A P \ {C})
  have hCfi : C.IsFullyInvariant := .of_mem_isotypicComponents hCmem
  have hDfi : D.IsFullyInvariant :=
    (fullyInvariantSubmodule A P).sSupClosed fun _ hm => .of_mem_isotypicComponents hm.1
  have hcompl : IsCompl C D := isCompl_sSup_isotypicComponents_diff hCmem
  obtain ⟨a, ha⟩ := exists_smul_eq_projection (k := k) hCfi hDfi hcompl
  -- `N`, embedded in `P` as `0 × N`, lies in `D`
  have hND : LinearMap.range (LinearMap.inr A M N) ≤ D :=
    le_sSup_isotypicComponents_diff fun T hT hTle hTC => by
      have := hT
      have : IsSimpleModule A (⊤ : Submodule A T) := IsSimpleModule.congr Submodule.topEquiv
      obtain ⟨e⟩ := le_isotypicComponent_iff.mp hTC (⊤ : Submodule A T)
      exact hno ((LinearMap.snd A M N ∘ₗ T.subtype) ∘ₗ Submodule.topEquiv.toLinearMap ∘ₗ
        e.symm.toLinearMap ∘ₗ eS.toLinearMap) ((injective_snd_comp_subtype hTle).comp
        (Submodule.topEquiv.injective.comp (e.symm.injective.comp eS.injective)))
  have haN : actionLin k N a = 0 := by
    ext n
    have h1 : a • ((0 : M), n) = C.projection D hcompl ((0 : M), n) := ha _
    rw [Submodule.projection_apply_of_mem_right hcompl
      (show ((0 : M), n) ∈ D from hND ⟨n, rfl⟩)] at h1
    exact congrArg Prod.snd h1
  have hP : trace k P (actionLin k P a) = 0 := by
    rw [actionLin_prod, trace_prodMap', htr a, haN, map_zero, add_zero]
  have hidem : IsIdempotentElem (actionLin k P a) := by
    refine LinearMap.ext fun p => ?_
    change a • a • p = a • p
    rw [ha p, ha (C.projection D hcompl p),
      Submodule.projection_apply_of_mem_left hcompl (Submodule.projection_apply_mem hcompl p)]
  have h0 := hidem.eq_zero_of_trace_eq_zero hP
  have : Nontrivial S' := IsSimpleModule.nontrivial A S'
  obtain ⟨s, hs⟩ := exists_ne (0 : S')
  have hsC : (s : P) ∈ C := S'.le_isotypicComponent s.2
  have : a • (s : P) = s := by
    rw [ha, Submodule.projection_apply_of_mem_left hcompl hsC]
  refine hs (Subtype.ext ?_)
  rw [← this]
  exact LinearMap.congr_fun h0 s

omit [CharZero k] in
/-- A submodule over `A` of a module finite over `k` is finite over `k`. -/
theorem finiteDimensional_submodule [FiniteDimensional k M] (m : Submodule A M) :
    FiniteDimensional k m :=
  Module.Finite.of_injective (m.subtype.restrictScalars k) m.injective_subtype

omit [CharZero k] in
/-- The action of `1 ∈ A` is the identity. -/
theorem actionLin_one : actionLin k M (1 : A) = LinearMap.id :=
  LinearMap.ext fun m => one_smul A m

/-- **The Brauer–Nesbitt theorem**, in characteristic zero. Let `A` be an algebra over a field
`k` of characteristic zero and `M`, `N` semisimple `A`-modules, finite-dimensional over `k`. If
every element of `A` has the same trace on `M` and on `N`, then `M` and `N` are isomorphic. -/
theorem nonempty_linearEquiv_of_trace_eq [IsSemisimpleModule A M] [IsSemisimpleModule A N]
    [FiniteDimensional k M] [FiniteDimensional k N]
    (htr : ∀ a : A, trace k M (actionLin k M a) = trace k N (actionLin k N a)) :
    Nonempty (M ≃ₗ[A] N) := by
  induction hn : finrank k M using Nat.strong_induction_on generalizing M N with
  | _ n ih =>
  rcases subsingleton_or_nontrivial M with hM | hM
  · have hN : finrank k N = 0 := by
      have h1 := htr 1
      rw [actionLin_one, actionLin_one, trace_id, trace_id, finrank_zero_of_subsingleton] at h1
      exact_mod_cast h1.symm
    have : Subsingleton N := Module.finrank_zero_iff.mp hN
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  · obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A M
    obtain ⟨g, hg⟩ := exists_injective_of_trace_eq htr S
    obtain ⟨M', hM'⟩ := exists_isCompl S
    obtain ⟨N', hN'⟩ := exists_isCompl (LinearMap.range g)
    have := finiteDimensional_submodule (k := k) S
    have := finiteDimensional_submodule (k := k) M'
    have := finiteDimensional_submodule (k := k) N'
    have := finiteDimensional_submodule (k := k) (LinearMap.range g)
    let eM : (S × M') ≃ₗ[A] M := Submodule.prodEquivOfIsCompl S M' hM'
    let eSg : S ≃ₗ[A] LinearMap.range g := LinearEquiv.ofInjective g hg
    have htr' : ∀ a : A, trace k M' (actionLin k M' a) = trace k N' (actionLin k N' a) := by
      intro a
      have h1 := trace_actionLin_eq_add_of_isCompl (k := k) hM' a
      have h2 := trace_actionLin_eq_add_of_isCompl (k := k) hN' a
      have h3 := trace_actionLin_congr (k := k) eSg a
      linear_combination h2 - h1 - h3 + htr a
    have : Nontrivial S := IsSimpleModule.nontrivial A S
    have hlt : finrank k M' < n := by
      rw [← hn, ← LinearEquiv.finrank_eq (eM.restrictScalars k), Module.finrank_prod]
      have : 0 < finrank k S := Module.finrank_pos
      omega
    obtain ⟨e'⟩ := ih _ hlt htr' rfl
    exact ⟨eM.symm ≪≫ₗ (eSg.prodCongr e') ≪≫ₗ Submodule.prodEquivOfIsCompl _ _ hN'⟩

section Representation

open scoped MonoidAlgebra

variable {G V W : Type*} [Monoid G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

omit [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W] in
/-- The trace of an element of `k[G]` acting on `ρ.asModule` is the trace of its image under
`ρ.asAlgebraHom`, and it is determined by the character of `ρ`. -/
theorem trace_actionLin_asModule_eq (ρ : Representation k G V) (σ : Representation k G W)
    (htr : ∀ g : G, trace k V (ρ g) = trace k W (σ g)) (a : k[G]) :
    trace k ρ.asModule (actionLin k ρ.asModule a) =
      trace k σ.asModule (actionLin k σ.asModule a) := by
  change trace k V (ρ.asAlgebraHom a) = trace k W (σ.asAlgebraHom a)
  have : (trace k V).comp ρ.asAlgebraHom.toLinearMap =
      (trace k W).comp σ.asAlgebraHom.toLinearMap := by
    refine MonoidAlgebra.lhom_ext' fun g => LinearMap.ext fun r => ?_
    simp [htr g]
  exact LinearMap.congr_fun this a

/-- **Brauer–Nesbitt for representations.** Two semisimple finite-dimensional representations
of a monoid `G` over a field of characteristic zero with the same character are equivalent. -/
theorem nonempty_equiv_of_trace_eq (ρ : Representation k G V) (σ : Representation k G W)
    (hρ : ρ.IsSemisimpleRepresentation) (hσ : σ.IsSemisimpleRepresentation)
    (htr : ∀ g : G, trace k V (ρ g) = trace k W (σ g)) : Nonempty (ρ.Equiv σ) := by
  have := (ρ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule).mp hρ
  have := (σ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule).mp hσ
  obtain ⟨e⟩ := nonempty_linearEquiv_of_trace_eq (k := k)
    (trace_actionLin_asModule_eq ρ σ htr)
  refine ⟨Representation.Equiv.mk (ρ.asModuleEquiv.symm ≪≫ₗ e.restrictScalars k ≪≫ₗ
    σ.asModuleEquiv) fun g => LinearMap.ext fun v => ?_⟩
  have := e.map_smul (MonoidAlgebra.of k G g) (ρ.asModuleEquiv.symm v)
  simp only [MonoidAlgebra.of_apply, Representation.single_smul, LinearEquiv.apply_symm_apply,
    one_smul] at this
  exact this

end Representation

section Matrix

open Stacks.EtaleCohomology

variable {G : Type*} [Group G] {n : ℕ}

omit [CharZero k] in
/-- The representation attached to `ρ : G →* GLₙ(k)` sends `g` to the linear map `kⁿ → kⁿ` given by
the matrix `ρ g`. -/
theorem matrixRepresentation_eq_toLin' (ρ : G →* Matrix.GeneralLinearGroup (Fin n) k) (g : G) :
    matrixRepresentation ρ g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k) := rfl

omit [CharZero k] in
/-- The trace of `g` acting through the representation attached to `ρ : G →* GLₙ(k)` is the trace
of the matrix `ρ g`. -/
theorem trace_matrixRepresentation (ρ : G →* Matrix.GeneralLinearGroup (Fin n) k) (g : G) :
    trace k (Fin n → k) (matrixRepresentation ρ g) =
      Matrix.trace (ρ g : Matrix (Fin n) (Fin n) k) := by
  rw [matrixRepresentation_eq_toLin', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

omit [CharZero k] in
/-- A homomorphism `G → GLₙ(k)` whose image spans all matrices (Burnside's criterion for
absolute irreducibility) gives an irreducible, hence semisimple, representation. -/
theorem isSemisimpleRepresentation_of_span_eq_top (ρ : G →* Matrix.GeneralLinearGroup (Fin n) k)
    (h : Submodule.span k (Set.range fun g => (ρ g : Matrix (Fin n) (Fin n) k)) = ⊤) :
    (matrixRepresentation ρ).IsSemisimpleRepresentation := by
  have hW : ∀ W : Subrepresentation (matrixRepresentation ρ), W = ⊥ ∨ W = ⊤ := by
    intro W
    let T : Submodule k (Matrix (Fin n) (Fin n) k) :=
      { carrier := {A | ∀ w ∈ W.toSubmodule, Matrix.toLin' A w ∈ W.toSubmodule}
        add_mem' := fun {A B} hA hB w hw => by
          rw [map_add, LinearMap.add_apply]
          exact add_mem (hA w hw) (hB w hw)
        zero_mem' := fun w _ => by
          rw [map_zero, LinearMap.zero_apply]
          exact zero_mem _
        smul_mem' := fun c A hA w hw => by
          rw [map_smul, LinearMap.smul_apply]
          exact Submodule.smul_mem _ c (hA w hw) }
    have hT : T = ⊤ := by
      refine eq_top_iff.2 (h ▸ Submodule.span_le.2 ?_)
      rintro _ ⟨g, rfl⟩ w hw
      exact W.apply_mem_toSubmodule g hw
    by_cases hbot : W.toSubmodule = ⊥
    · left
      exact Subrepresentation.toSubmodule_injective hbot
    · right
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := Function.ne_iff.mp hw0
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      let A : Matrix (Fin n) (Fin n) k := Matrix.vecMulVec v (Pi.single i (w i)⁻¹)
      have hA : Matrix.toLin' A w = v := by
        ext a
        simp [A, Matrix.toLin'_apply, Matrix.mulVec, Matrix.vecMulVec, dotProduct,
          Pi.single_apply, hi]
      rw [← hA]
      exact (hT ▸ Submodule.mem_top : A ∈ T) w hw
  exact ⟨fun W => (hW W).elim (fun hb => ⟨⊤, hb ▸ isCompl_bot_top⟩)
    (fun ht => ⟨⊥, ht ▸ isCompl_top_bot⟩)⟩

/-- **Brauer–Nesbitt for matrix representations.** Two homomorphisms `ρ, σ : G → GLₙ(k)`, `k`
of characteristic zero, which are semisimple and have the same traces are conjugate. -/
theorem exists_conj_of_trace_eq (ρ σ : G →* Matrix.GeneralLinearGroup (Fin n) k)
    (hρ : (matrixRepresentation ρ).IsSemisimpleRepresentation)
    (hσ : (matrixRepresentation σ).IsSemisimpleRepresentation)
    (htr : ∀ g : G, Matrix.trace (ρ g : Matrix (Fin n) (Fin n) k) =
      Matrix.trace (σ g : Matrix (Fin n) (Fin n) k)) :
    ∃ P : Matrix.GeneralLinearGroup (Fin n) k, ∀ g : G, σ g = P * ρ g * P⁻¹ := by
  obtain ⟨e⟩ := nonempty_equiv_of_trace_eq (matrixRepresentation ρ) (matrixRepresentation σ)
    hρ hσ fun g => by rw [trace_matrixRepresentation, trace_matrixRepresentation, htr g]
  let L : (Fin n → k) ≃ₗ[k] (Fin n → k) := e.toLinearEquiv
  have hL : ∀ g, L.toLinearMap ∘ₗ Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k) =
      Matrix.toLin' (σ g : Matrix (Fin n) (Fin n) k) ∘ₗ L.toLinearMap := fun g =>
    LinearMap.ext fun v => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
  let P : Matrix.GeneralLinearGroup (Fin n) k :=
    ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨P, fun g => Units.ext (Matrix.toLin'.injective ?_)⟩
  change Matrix.toLin' (σ g : Matrix (Fin n) (Fin n) k) =
    Matrix.toLin' (LinearMap.toMatrix' L.toLinearMap * (ρ g : Matrix (Fin n) (Fin n) k) *
      LinearMap.toMatrix' L.symm.toLinearMap)
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix',
    hL g]
  ext v
  simp

end Matrix

end Stacks.Drinfeld
