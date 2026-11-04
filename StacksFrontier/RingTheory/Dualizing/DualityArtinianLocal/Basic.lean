module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Ideal.Operations
public import StacksCore.Tactic.StacksAttribute

/-!
# Duality exchanges ideal torsion and quotient by an ideal

For an injective module `E` over a commutative ring `R`, linear duality into `E` exchanges the
submodule of elements annihilated by an ideal `I` with the operation of quotienting by `I`, and
vice versa. These are the two identifications used when computing Matlis duality over an
Artinian local ring.

## Main results

* `Dualizing.dualTorsionEquiv` identifies the dual of the `I`-annihilated submodule of `M` with
  the quotient of the dual of `M` by `I`.
* `Dualizing.dualQuotientEquiv` identifies the dual of `M / I M` with the `I`-annihilated
  submodule of the dual of `M`.

## Implementation notes

The two equalities of the source are expressed as linear equivalences. Each equivalence is
bundled together with its action on representatives, which pins down the canonical
identification rather than merely asserting that an abstract isomorphism exists.

The first identification requires only injectivity of the target and finite generation of the
ideal, not finiteness of the source module or Artinianity of the ring; the second needs
neither condition. Injectivity in the first identification is imposed on `ULift.{u} E`, in a
universe containing both the ring and the target: by Baer's criterion this yields the
extension property for modules in any universe while keeping the universes of `R`, `E` and `M`
independent. Injectivity of `E` in its own universe alone would not provide that property when
the ring lives in a larger universe.

## References

* [Stacks Project, Tag 08Z0](https://stacks.math.columbia.edu/tag/08Z0)
-/

@[expose] public section

namespace Dualizing

universe u v w

/-- An `R`-linear map into `E` extends along an injective `R`-linear map, when `ULift.{u} E` is
injective for the universe `u` of the ring. This transports Baer's criterion from the universe
of `E` to the universe of the modules being extended. -/
lemma extend_linearMap_of_injective_ulift
    (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E]
    [Module.Injective R (ULift.{u} E)]
    (P P' : Type w) [AddCommGroup P] [AddCommGroup P']
    [Module R P] [Module R P']
    (f : P →ₗ[R] P') (hf : Function.Injective f) (g : P →ₗ[R] E) :
    ∃ h : P' →ₗ[R] E, h.comp f = g := by
  let e : ULift.{u} E ≃ₗ[R] E := ULift.moduleEquiv
  let lift : E →ₗ[R] ULift.{u} E := e.symm.toLinearMap
  obtain ⟨h, hh⟩ :=
    Module.Injective.extension_property R (ULift.{u} E) P P' f hf (lift.comp g)
  refine ⟨e.toLinearMap.comp h, LinearMap.ext fun x => ?_⟩
  simpa [lift, e] using congrArg e (LinearMap.congr_fun hh x)

/-- **Stacks Project, Tag 08Z0.** Restricting a functional to the elements of `M` killed by `I`
induces the canonical identification of the quotient of the dual of `M` by `I` with the dual of
that submodule. -/
@[stacks 08Z0 "the dual of ideal torsion"]
noncomputable def dualTorsionEquiv
    (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E] [Module.Injective R (ULift.{u} E)]
    (M : Type w) [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) :
    { e : ((M →ₗ[R] E) ⧸ (I • (⊤ : Submodule R (M →ₗ[R] E)))) ≃ₗ[R]
        (Submodule.torsionBySet R M (I : Set R) →ₗ[R] E) //
      ∀ f : M →ₗ[R] E,
        e (Submodule.Quotient.mk f) =
          f.comp (Submodule.subtype (Submodule.torsionBySet R M (I : Set R))) } := by
  classical
  let T : Submodule R M := Submodule.torsionBySet R M (I : Set R)
  let P : Submodule R (M →ₗ[R] E) := I • (⊤ : Submodule R (M →ₗ[R] E))
  let res : (M →ₗ[R] E) →ₗ[R] (T →ₗ[R] E) :=
    { toFun := fun f => f.comp T.subtype
      map_add' := by intro f g; ext x; rfl
      map_smul' := by intro a f; ext x; rfl }
  have hsurj : Function.Surjective res :=
    extend_linearMap_of_injective_ulift R E T M T.subtype (Submodule.subtype_injective T)
  let s : Finset R := Classical.choose hI
  have hs : Ideal.span (s : Set R) = I := Classical.choose_spec hI
  let δ : M →ₗ[R] (↥s → M) :=
    LinearMap.pi fun i => (LinearMap.lsmul R M) (i : R)
  have hδker : δ.ker = T := by
    ext m
    constructor
    · intro hm
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      have hgen : ∀ i ∈ s, (i : R) • m = 0 := by
        intro i hi
        simpa [δ] using congrArg (fun f : ↥s → M => f ⟨i, hi⟩)
          (LinearMap.mem_ker.mp hm)
      have hI : I ≤ (LinearMap.toSpanSingleton R M m).ker := by
        rw [← hs]
        apply Ideal.span_le.mpr
        intro i hi
        exact LinearMap.mem_ker.mpr (by simpa using hgen i hi)
      exact LinearMap.mem_ker.mp (hI a.property)
    · intro hm
      rw [Submodule.mem_torsionBySet_iff] at hm
      rw [LinearMap.mem_ker]; ext i
      simpa [δ] using hm ⟨i.val, hs ▸ Ideal.subset_span i.property⟩
  have hker : res.ker = P := by
    apply le_antisymm
    · intro g hg
      have hgT : ∀ x : T, g x = 0 := by
        have hres : res g = 0 := LinearMap.mem_ker.mp hg
        intro x
        have hx := congrArg (fun k : T →ₗ[R] E => k x) hres
        simpa [res] using hx
      have hδg : δ.ker ≤ LinearMap.ker g := by
        intro m hm
        simpa using hgT ⟨m, hδker ▸ hm⟩
      let gbar : (M ⧸ δ.ker) →ₗ[R] E := δ.ker.liftQ g hδg
      let gR : δ.range →ₗ[R] E := gbar.comp δ.quotKerEquivRange.symm.toLinearMap
      obtain ⟨H, hH⟩ := extend_linearMap_of_injective_ulift R E δ.range (↥s → M)
        δ.range.subtype (Submodule.subtype_injective δ.range) gR
      let single (i : ↥s) : M →ₗ[R] (↥s → M) := LinearMap.single R (fun _ : ↥s => M) i
      have hδ : δ = ∑ i : ↥s, (single i).comp ((LinearMap.lsmul R M) i.val) := by
        ext m i
        simp [δ, single, LinearMap.pi_apply]
      have hsum : H.comp δ = ∑ i : ↥s, i.val • (H.comp (single i)) := by
        ext m
        rw [LinearMap.comp_apply, hδ, LinearMap.sum_apply]
        simp [single, LinearMap.comp_apply, LinearMap.single_apply, LinearMap.lsmul_apply]
      have hgH : g = H.comp δ := by
        ext m
        have hcomp := congrArg (fun k : δ.range →ₗ[R] E => k ⟨δ m, ⟨m, rfl⟩⟩) hH
        simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hcomp
        change g m = H (δ m)
        have hquot : δ.quotKerEquivRange.symm (⟨δ m, ⟨m, rfl⟩⟩ : δ.range) =
            δ.ker.mkQ m := by
          apply δ.quotKerEquivRange.injective
          simp only [LinearEquiv.apply_symm_apply]
          apply Subtype.ext
          simp
        rw [hcomp]
        change g m = gbar (δ.quotKerEquivRange.symm ⟨δ m, ⟨m, rfl⟩⟩)
        rw [hquot]
        simp [gbar, Submodule.liftQ_apply]
      rw [hgH, hsum]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem_smul (hs ▸ Ideal.subset_span i.property) (Submodule.mem_top)
    · refine Submodule.smul_le.mpr ?_
      intro a ha f hf
      rw [LinearMap.mem_ker]
      ext x
      change (a : R) • f x = 0
      have hx : (a : R) • (x : M) = 0 :=
        (Submodule.mem_torsionBySet_iff (I : Set R) x.1).mp x.2 ⟨a, ha⟩
      rw [← map_smul, hx, map_zero]
  let e : ((M →ₗ[R] E) ⧸ P) ≃ₗ[R] (T →ₗ[R] E) :=
    (Submodule.quotEquivOfEq P res.ker hker.symm).trans <|
      res.quotKerEquivOfSurjective hsurj
  exact ⟨e, fun f => by simp [e, res, P, T]⟩

/-- **Stacks Project, Tag 08Z0.** Precomposing with the quotient map identifies the dual of
`M / I M` with the submodule of functionals on `M` killed by `I`. -/
@[stacks 08Z0 "the dual of the quotient by an ideal"]
noncomputable def dualQuotientEquiv
    (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E]
    (M : Type w) [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    { e : ((M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R] E) ≃ₗ[R]
        Submodule.torsionBySet R (M →ₗ[R] E) (I : Set R) //
      ∀ (f : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R] E) (m : M),
        (e f : M →ₗ[R] E) m = f (Submodule.Quotient.mk m) } := by
  let P : Submodule R M := I • (⊤ : Submodule R M)
  let Q : Submodule R (M →ₗ[R] E) :=
    Submodule.torsionBySet R (M →ₗ[R] E) (I : Set R)
  let ψ : (M ⧸ P →ₗ[R] E) →ₗ[R] (M →ₗ[R] E) :=
    { toFun := fun f => f.comp P.mkQ
      map_add' := by intro f g; ext m; rfl
      map_smul' := by intro a f; ext m; rfl }
  have hψ : Function.Injective ψ := fun _ _ h => Submodule.linearMap_qext P h
  have hrange : ψ.range = Q := by
    ext g
    constructor
    · rintro ⟨f, rfl⟩
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      ext m
      change a.1 • f (P.mkQ m) = 0
      have ha : a.1 • (P.mkQ m) = (0 : M ⧸ P) :=
        (Submodule.Quotient.mk_eq_zero P).mpr
          (Submodule.smul_mem_smul a.2 (Submodule.mem_top : m ∈ (⊤ : Submodule R M)))
      rw [← map_smul, ha, map_zero]
    · intro hg
      have hP : P ≤ LinearMap.ker g := by
        change I • (⊤ : Submodule R M) ≤ LinearMap.ker g
        refine Submodule.smul_le.mpr ?_
        intro a ha m hm
        rw [LinearMap.mem_ker]
        have hga := (Submodule.mem_torsionBySet_iff (I : Set R) g).mp hg ⟨a, ha⟩
        change g (a • m) = 0
        rw [map_smul]
        simpa only [LinearMap.smul_apply, LinearMap.zero_apply] using
          congrArg (fun k : M →ₗ[R] E => k m) hga
      refine ⟨P.liftQ g hP, ?_⟩
      ext m
      simp [ψ, P]
  let e : (M ⧸ P →ₗ[R] E) ≃ₗ[R] Q :=
    (LinearEquiv.ofInjective ψ hψ).trans (LinearEquiv.ofEq ψ.range Q hrange)
  exact ⟨e, fun _ _ => rfl⟩

end Dualizing
