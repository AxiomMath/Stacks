module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Algebra.Module.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Pure.Defs
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Module.FinitePresentation.Colimit
public import StacksFrontier.RingTheory.Module.Finiteness.HomColimit
public import StacksFrontier.RingTheory.UniversallyExact

/-!
# Pure projective modules

A module is pure projective exactly when it is a retract of a direct sum of finitely presented
modules, and every module is the quotient of a pure projective one by a universally exact
surjection.

## References

* [Stacks Project, Tag 06ZZ](https://stacks.math.columbia.edu/tag/06ZZ)
-/

@[expose] public section

namespace Module

section

open scoped DirectSum

universe u v w x

/-- A retract of a direct sum of finitely presented modules is pure projective. -/
public theorem pureProjective_of_directSum_retract
    (A : Type u) [CommRing A]
    (P : Type v) [AddCommGroup P] [Module A P]
    (ι : Type w) (Q : ι → Type x)
    [∀ i, AddCommGroup (Q i)] [∀ i, Module A (Q i)]
    (hQ : ∀ i, Module.FinitePresentation A (Q i))
    (s : P →ₗ[A] ⨁ i, Q i) (r : (⨁ i, Q i) →ₗ[A] P)
    (h : r.comp s = LinearMap.id) :
    Module.PureProjective A P := by
  classical
  intro K M N _ _ _ _ _ _ f g hInj hSurj hRange hUni
  let _ : Small.{max u v} A := small_max.{max u v, u} A
  have hExact : Function.Exact f g := LinearMap.exact_iff.mpr hRange.symm
  have hTFAE := (hExact.universallyExact_tfae hInj hSurj)
  have hLiftSummand : ∀ i, Function.Surjective
      (LinearMap.compRight (M := Q i) A g) := by
    intro i
    let : Module.FinitePresentation A (Q i) := hQ i
    have hSmallQ : Small.{max u v} (Q i) := Module.Finite.small A (Q i)
    let : Small.{max u v} (Q i) := hSmallQ
    let eQ : Shrink.{max u v} (Q i) ≃ₗ[A] Q i := Shrink.linearEquiv A (Q i)
    let _ : Module.FinitePresentation A (Shrink.{max u v} (Q i)) :=
      Module.FinitePresentation.of_equiv eQ.symm
    have hLift := (hTFAE.out 1 5).mp hUni
    have hLift' : Function.Surjective
        (LinearMap.compRight (M := Shrink.{max u v} (Q i)) A g) := hLift _
    intro φ
    obtain ⟨ψ, hψ⟩ := hLift' (φ.comp eQ.toLinearMap)
    refine ⟨ψ.comp eQ.symm.toLinearMap, ?_⟩
    ext x
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hψ (eQ.symm x)
  have hSumSurj : Function.Surjective (LinearMap.compRight (M := ⨁ i, Q i) A g) := by
    intro φ
    choose ψ hψ using fun i => hLiftSummand i (φ.comp (DirectSum.lof A ι Q i))
    refine ⟨DirectSum.toModule A ι M ψ, ?_⟩
    show g.comp (DirectSum.toModule A ι M ψ) = φ
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
    exact LinearMap.congr_fun (hψ i) x
  have hRetractSurj : Function.Surjective (LinearMap.compRight (M := P) A g) := by
    intro φ
    obtain ⟨ψ, hψ⟩ := hSumSurj (φ.comp r)
    refine ⟨ψ.comp s, ?_⟩
    ext x
    have hx := LinearMap.congr_fun hψ (s x)
    have hsx : r (s x) = x := by
      have h' := LinearMap.congr_fun h x
      simpa [LinearMap.comp_apply] using h'
    simpa [LinearMap.comp_apply, hsx] using hx
  have hCompEqZero : g.comp f = 0 := hExact.linearMap_comp_eq_zero
  have hRangeKer : LinearMap.range f = LinearMap.ker g := hRange
  have hCompRange : LinearMap.range (LinearMap.compRight (M := P) A f) =
      LinearMap.ker (LinearMap.compRight (M := P) A g) := by
    apply le_antisymm
    · rintro φ ⟨ψ, rfl⟩
      show g.comp (f.comp ψ) = 0
      rw [← LinearMap.comp_assoc, hCompEqZero]
      simp
    · intro φ hφ
      let φ' : P →ₗ[A] LinearMap.range f :=
        LinearMap.codRestrict (LinearMap.range f) φ (fun x => by
          show φ x ∈ LinearMap.range f
          rw [hRangeKer]
          show g (φ x) = 0
          exact LinearMap.congr_fun hφ x)
      have hRangeRestrictInj : Function.Injective (LinearMap.rangeRestrict f) := by
        intro x y hxy
        exact hInj (congrArg Subtype.val hxy)
      have hRangeRestrictSurj : Function.Surjective (LinearMap.rangeRestrict f) := by
        rintro ⟨y, hy⟩
        obtain ⟨x, hx⟩ := hy
        exact ⟨x, by ext; exact hx⟩
      let e : K ≃ₗ[A] LinearMap.range f :=
        LinearEquiv.ofBijective (LinearMap.rangeRestrict f)
          ⟨hRangeRestrictInj, hRangeRestrictSurj⟩
      refine ⟨e.symm.toLinearMap.comp φ', ?_⟩
      ext x
      calc
        f (e.symm (φ' x)) = (φ' x).val :=
          congrArg Subtype.val (e.apply_symm_apply (φ' x))
        _ = φ x := rfl
  refine ⟨?_, hRetractSurj, hCompRange⟩
  intro φ ψ hφψ
  apply LinearMap.ext
  intro x
  exact hInj (LinearMap.congr_fun hφψ x)

end

section

open scoped DirectSum

universe u v w

private theorem finitePresentation_hom_factors_directLimit
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R N] {ι : Type w} [Preorder ι]
    [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι → Type w) [(i : ι) → AddCommGroup (G i)]
    [(i : ι) → Module R (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (fun i j h => f i j h)]
    (ψ : N →ₗ[R] Module.DirectLimit G f) :
    ∃ (j : ι) (φ : N →ₗ[R] G j),
      (Module.DirectLimit.of R ι G f j).comp φ = ψ := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.Finite.fg_top (R := R) (M := N))
  let p : (Fin n →₀ R) →ₗ[R] N := Finsupp.linearCombination R s
  have hpsurj : Function.Surjective p := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hs]
  obtain ⟨t, ht⟩ := Module.FinitePresentation.fg_ker p hpsurj
  choose ii xx hxx using fun k => Module.DirectLimit.exists_of (ψ (s k))
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image ii)
  let q : (Fin n →₀ R) →ₗ[R] G i := Finsupp.linearCombination R fun k =>
    f (ii k) i (hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) (xx k)
  have hcomp : (Module.DirectLimit.of R ι G f i).comp q = ψ.comp p := by
    ext k
    simp [q, p, hxx]
  have hqp (w) : Module.DirectLimit.of R ι G f i (q w) = ψ (p w) :=
    LinearMap.congr_fun hcomp w
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.exists_forall_map_eq_zero i
    (fun v : t => q v) fun v => by
      rw [hqp, (LinearMap.mem_ker.1 (ht ▸ Submodule.subset_span v.2 : v.1 ∈ p.ker)), map_zero]
  have hker : p.ker ≤ ((f i j hij).comp q).ker := by
    rw [← ht, Submodule.span_le]
    exact fun v hv => hj ⟨v, hv⟩
  let e := p.quotKerEquivOfSurjective hpsurj
  have he (w) : e.symm (p w) = p.ker.mkQ w := e.symm_apply_eq.2 rfl
  refine ⟨j, p.ker.liftQ _ hker ∘ₗ e.symm.toLinearMap, LinearMap.ext fun a => ?_⟩
  obtain ⟨w, rfl⟩ := hpsurj a
  simpa [he] using hqp w

/-- Every module is a filtered colimit of finitely presented modules such that
the canonical presentation by their direct sum is universally exact. -/
public theorem exists_finitelyPresented_directedSystem_universallyInjective_ker
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    ∃ (ι : Type (max u v)) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (_ : DecidableEq ι)
      (P : ι → Type (max u v)) (_ : (i : ι) → AddCommGroup (P i))
      (_ : (i : ι) → Module R (P i))
      (f : (i j : ι) → i ≤ j → (P i →ₗ[R] P j))
      (_ : DirectedSystem P (fun i j h => f i j h))
      (e : M ≃ₗ[R] Module.DirectLimit P f),
      (∀ i, Module.FinitePresentation R (P i)) ∧
        let p : (⨁ (i : ι), P i) →ₗ[R] M :=
          DirectSum.toModule R ι M fun i =>
            e.symm.toLinearMap.comp (Module.DirectLimit.of R ι P f i)
        Function.Surjective p ∧ UniversallyInjective p.ker.subtype := by
  classical
  obtain ⟨ι, hpre, hdirected, hnonempty, hdec, P, hadd, hmodule, f, hf, hfp,
      ⟨e⟩⟩ := Module.exists_linearEquiv_directLimit_finitePresentation_max R M
  let p : (⨁ (i : ι), P i) →ₗ[R] M :=
    DirectSum.toModule R ι M fun i =>
      e.symm.toLinearMap.comp (Module.DirectLimit.of R ι P f i)
  refine ⟨ι, hpre, hdirected, hnonempty, hdec, P, hadd, hmodule, f, hf, e, hfp, ?_⟩
  have hp : Function.Surjective p := by
    intro m
    obtain ⟨i, x, hx⟩ := Module.DirectLimit.exists_of (e m)
    refine ⟨DirectSum.lof R ι P i x, ?_⟩
    simp [p, DirectSum.toModule_lof, hx]
  refine ⟨hp, ?_⟩
  let p' : (⨁ (i : ι), P i) →ₗ[R] ULift.{max u v} M :=
    (ULift.moduleEquiv.{u, v, max u v} (R := R) (M := M)).symm.toLinearMap.comp p
  have hp' : Function.Surjective p' :=
    (ULift.moduleEquiv.{u, v, max u v} (R := R) (M := M)).symm.surjective.comp hp
  have hker : p'.ker = p.ker := by
    ext x
    simp [p', LinearMap.mem_ker]
  have hexact' : Function.Exact p'.ker.subtype p' :=
    LinearMap.exact_subtype_ker_map p'
  have hinj' : Function.Injective p'.ker.subtype := Subtype.val_injective
  have : Small.{max u v} R := small_max.{max u v, u} R
  have hcriterion := (hexact'.universallyExact_tfae hinj' hp').out 5 1
  have hcondition : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module R Q]
      [Module.FinitePresentation R Q],
      Function.Surjective (LinearMap.compRight (M := Q) R p') := by
    intro Q _ _ hQ φ
    let φ' : Q →ₗ[R] Module.DirectLimit P f :=
      e.toLinearMap.comp
        ((ULift.moduleEquiv.{u, v, max u v} (R := R) (M := M)).toLinearMap.comp φ)
    obtain ⟨i, g, hg⟩ := finitePresentation_hom_factors_directLimit
      (R := R) (N := Q) P f φ'
    refine ⟨(DirectSum.lof R ι P i).comp g, ?_⟩
    ext x
    have hx := congrArg e.symm (LinearMap.congr_fun hg x)
    simp only [p', p]
    simpa [φ'] using hx
  have huni' : UniversallyInjective p'.ker.subtype := hcriterion.mp hcondition
  let ek : p.ker ≃ₗ[R] p'.ker := LinearEquiv.ofEq _ _ hker.symm
  have hsub : p'.ker.subtype.comp ek.toLinearMap = p.ker.subtype := by
    ext x
    rfl
  intro Q _ _
  rw [← hsub, LinearMap.rTensor_comp]
  exact (huni' Q).comp (ek.rTensor Q).injective

end

section

open scoped DirectSum

universe u v

/-- An `A`-module is pure projective if and only if it is a retract of a direct
sum of finitely presented `A`-modules. -/
@[stacks 06ZZ "pure_projective_characterization"]
public theorem pureProjective_iff_directSum_finitelyPresented_retract
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    Module.PureProjective A M ↔
      ∃ (ι : Type (max u v)) (Q : ι → Type (max u v))
        (_ : (i : ι) → AddCommGroup (Q i))
        (_ : (i : ι) → Module A (Q i)),
        (∀ i, Module.FinitePresentation A (Q i)) ∧
          ∃ (s : M →ₗ[A] ⨁ i, Q i) (r : (⨁ i, Q i) →ₗ[A] M),
            r.comp s = LinearMap.id := by
  constructor
  · intro hM
    obtain ⟨ι, _, _, _, _, P, _, _, f, _, e, hFP, hSurj, hUI⟩ :=
      Module.exists_finitelyPresented_directedSystem_universallyInjective_ker A M
    let p : (⨁ i, P i) →ₗ[A] M := DirectSum.toModule A ι M fun i => e.symm.toLinearMap.comp
      (Module.DirectLimit.of A ι P f i)
    let up : M →ₗ[A] ULift.{max u v, v} M :=
      { toFun := ULift.up, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    let pUp : (⨁ i, P i) →ₗ[A] ULift.{max u v, v} M := up.comp p
    let inc : p.ker →ₗ[A] (⨁ i, P i) := p.ker.subtype
    have hSurjUp : Function.Surjective pUp := by
      intro y
      obtain ⟨x, hx⟩ := hSurj y.down
      exact ⟨x, ULift.ext _ _ (by simpa [pUp, up] using hx)⟩
    have hKer : LinearMap.ker p = LinearMap.ker pUp := by
      ext x
      show p x = 0 ↔ ULift.up (p x) = ULift.up 0
      simp
    have hRangeP : LinearMap.range inc = LinearMap.ker p := by ext x; simp [inc]
    have hRange : LinearMap.range inc = LinearMap.ker pUp := hRangeP.trans hKer
    obtain ⟨lift, hlift⟩ :=
      (hM p.ker (⨁ i, P i) (ULift.{max u v, v} M) inc pUp Subtype.val_injective hSurjUp hRange
      hUI).2.1 up
    have hlift' : pUp.comp lift = up := by simpa [LinearMap.compRight_apply] using hlift
    refine ⟨ι, P, inferInstance, inferInstance, hFP, lift, p, ?_⟩
    ext x
    simpa [pUp, up, LinearMap.comp_apply] using congrArg ULift.down (LinearMap.congr_fun hlift' x)
  · rintro ⟨ι, Q, _, _, hQ, ⟨s, r, hsr⟩⟩
    exact Module.pureProjective_of_directSum_retract A M ι Q hQ s r hsr

end

section

open scoped DirectSum

universe u v

/-- Every module is the quotient of a pure projective module in a universally exact short
exact sequence. -/
@[stacks 06ZZ "pure_projective_presentation"]
public theorem exists_pureProjective_universallyExact_presentation
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ (N P : Type (max u v))
      (_ : AddCommGroup N) (_ : Module A N)
      (_ : AddCommGroup P) (_ : Module A P)
      (f : N →ₗ[A] P) (g : P →ₗ[A] M),
      Function.Injective f ∧
        Function.Surjective g ∧
          LinearMap.range f = LinearMap.ker g ∧
            UniversallyInjective f ∧
              Module.PureProjective A P := by
  obtain ⟨ι, _, _, _, _, Q, hAddGroup, hModule, transition, _, e, hFinite, hPresentation⟩ :=
      Module.exists_finitelyPresented_directedSystem_universallyInjective_ker A M
  let : ∀ i, AddCommGroup (Q i) := hAddGroup; let : ∀ i, Module A (Q i) := hModule
  let p : (⨁ i, Q i) →ₗ[A] M := DirectSum.toModule A ι M fun i =>
    e.symm.toLinearMap.comp (Module.DirectLimit.of A ι Q transition i)
  exact ⟨p.ker, (⨁ i, Q i), inferInstance, inferInstance, inferInstance, inferInstance,
    p.ker.subtype, p, Subtype.val_injective, hPresentation.1, (by simp), hPresentation.2,
    Module.pureProjective_of_directSum_retract A (⨁ i, Q i) ι Q hFinite
      (LinearMap.id) (LinearMap.id) (by simp)⟩

end

end Module

end
