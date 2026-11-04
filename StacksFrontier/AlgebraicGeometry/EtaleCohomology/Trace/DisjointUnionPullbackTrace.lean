module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClopenDecompositionCohomology
public import StacksFrontier.LinearAlgebra.BlockTrace

/-!
# The trace of a pullback on the cohomology of a finite disjoint union

Let `Y` be the disjoint union of finitely many open subschemes `U_k`, and let `φ : Y ⟶ Y` send
each `U_k` either into itself, through `φ_k : U_k ⟶ U_k`, or into some other `U_m`. Under
`H^q(Y, μ_n) ≅ ∏_k H^q(U_k, μ_n)` the pullback `φ^*` is a block matrix whose diagonal block at a
component sent into itself is `φ_k^*`, and whose other diagonal blocks vanish. Hence its trace
(over `ℤ/n`, read through finite free models of the `H^q(U_k, μ_n)`) is the sum of the traces of
the `φ_k^*` over the components sent into themselves.

## Main definitions

* `Stacks.EtaleCohomology.modelTrace`: the trace over `ℤ/n` of an additive endomorphism, read
  through an additive equivalence with a finite free `ℤ/n`-module.

## Main results

* `Stacks.EtaleCohomology.modelTrace_eq_of_addEquiv`: independence of the model.
* `Stacks.EtaleCohomology.modelTrace_rootsOfUnityPullbackMap_eq_sum`: the block formula.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Kummer

universe w u v

namespace Stacks.EtaleCohomology

section Model

variable (N : ℕ) {A : Type*} [AddCommGroup A] {M : Type*} [AddCommGroup M] [Module (ZMod N) M]

/-- The trace over `ℤ/N` of an additive endomorphism `f` of `A`, read through an additive
equivalence `e : A ≃+ M` with a `ℤ/N`-module. -/
def modelTrace (e : A ≃+ M) (f : A →+ A) : ZMod N :=
  LinearMap.trace (ZMod N) M
    ((e.toAddMonoidHom.comp (f.comp e.symm.toAddMonoidHom)).toZModLinearMap N)

/-- **The model trace does not depend on the model** among finite free `ℤ/N`-modules. -/
theorem modelTrace_eq_of_addEquiv [Module.Free (ZMod N) M] [Module.Finite (ZMod N) M]
    {M' : Type*} [AddCommGroup M'] [Module (ZMod N) M'] (e : A ≃+ M) (e' : A ≃+ M')
    (f : A →+ A) : modelTrace N e f = modelTrace N e' f :=
  AddMonoidHom.trace_toZModLinearMap_eq_of_addEquiv (e.symm.trans e') _ _ fun x => by
    simp

end Model

variable {Y : Scheme.{u}} {ι : Type} [Fintype ι] [DecidableEq ι] {U : ι → Scheme.{u}}
  (j : ∀ k, U k ⟶ Y) [∀ k, IsOpenImmersion (j k)]
  (hdisj : Pairwise fun k m => Disjoint (Set.range (j k).base) (Set.range (j m).base))
  (hcov : ⋃ k, Set.range (j k).base = Set.univ)
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [∀ k, HasExt.{w} (Sheaf (U k).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {n : ℕ} (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) (q : ℕ)

/-- `H^q(Y, μ_n) ≃+ ∏_k H^q(U_k, μ_n)` through the pullbacks along the `j_k`. -/
def disjointUnionAddEquiv :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) q ≃+
      ∀ k, Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} (U k) n) q :=
  AddEquiv.ofBijective (AddMonoidHom.pi fun k => rootsOfUnityPullbackMap.{u, v, w} (j k) n q)
    (bijective_rootsOfUnityPullbackMap_pi j hdisj hcov hn q)

omit [DecidableEq ι] in
/-- The `k`-th component of `disjointUnionAddEquiv` is the pullback along `j k`. -/
@[simp]
theorem disjointUnionAddEquiv_apply (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) q) (k : ι) :
    disjointUnionAddEquiv j hdisj hcov hn q x k = rootsOfUnityPullbackMap.{u, v, w} (j k) n q x :=
  rfl

variable (φ : Y ⟶ Y) (P : ι → Prop) [DecidablePred P]
  (φfix : ∀ k, P k → (U k ⟶ U k)) (hφfix : ∀ k (h : P k), φfix k h ≫ j k = j k ≫ φ)
  (hmove : ∀ k, ¬ P k → ∃ m, m ≠ k ∧ ∃ ψ : U k ⟶ U m, ψ ≫ j m = j k ≫ φ)

omit [Fintype ι] [DecidableEq ι] [∀ k, IsOpenImmersion (j k)] [DecidablePred P] in
include hφfix in
/-- The block of `φ^*` at a component sent into itself. -/
theorem rootsOfUnityPullbackMap_block_fixed (k : ι) (h : P k)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) q) :
    rootsOfUnityPullbackMap.{u, v, w} (j k) n q (rootsOfUnityPullbackMap.{u, v, w} φ n q x) =
      rootsOfUnityPullbackMap.{u, v, w} (φfix k h) n q
        (rootsOfUnityPullbackMap.{u, v, w} (j k) n q x) := by
  rw [rootsOfUnityPullbackMap_comp φ (j k) _ rfl,
    rootsOfUnityPullbackMap_comp (j k) (φfix k h) _ rfl, hφfix k h]

omit [Fintype ι] [DecidableEq ι] [∀ k, IsOpenImmersion (j k)] [DecidablePred P] in
include hmove in
/-- The block of `φ^*` at a component sent into another one vanishes on classes supported
away from it. -/
theorem rootsOfUnityPullbackMap_block_move (k : ι) (h : ¬ P k)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) q)
    (hx : ∀ m, m ≠ k → rootsOfUnityPullbackMap.{u, v, w} (j m) n q x = 0) :
    rootsOfUnityPullbackMap.{u, v, w} (j k) n q (rootsOfUnityPullbackMap.{u, v, w} φ n q x) =
      0 := by
  obtain ⟨m, hmk, ψ, hψ⟩ := hmove k h
  rw [rootsOfUnityPullbackMap_comp φ (j k) _ rfl, ← hψ,
    ← rootsOfUnityPullbackMap_comp (j m) ψ _ rfl, hx m hmk, map_zero]

variable {M : ι → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module (ZMod n) (M k)]
  [∀ k, Module.Free (ZMod n) (M k)] [∀ k, Module.Finite (ZMod n) (M k)]
  (e : ∀ k, Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} (U k) n) q ≃+ M k)

/-- The model `H^q(Y, μ_n) ≃+ ∏_k M_k` assembled from models of the components. -/
def disjointUnionModel :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) q ≃+ ∀ k, M k :=
  (disjointUnionAddEquiv j hdisj hcov hn q).trans (AddEquiv.piCongrRight e)

omit [DecidableEq ι] in
include hφfix hmove in
/-- **The trace of `φ^*` on `H^q(Y, μ_n)` is the sum of the traces of the `φ_k^*` over the
components sent into themselves.** -/
theorem modelTrace_rootsOfUnityPullbackMap_eq_sum :
    modelTrace n (disjointUnionModel j hdisj hcov hn q e)
        (rootsOfUnityPullbackMap.{u, v, w} φ n q) =
      ∑ k, if h : P k then modelTrace n (e k) (rootsOfUnityPullbackMap.{u, v, w} (φfix k h) n q)
        else 0 := by
  classical
  rw [modelTrace, LinearMap.trace_pi_eq_sum_trace_proj_comp_single]
  refine Finset.sum_congr rfl fun k _ => ?_
  set E := disjointUnionModel j hdisj hcov hn q e
  have hEx : ∀ y : M k, ∀ m, rootsOfUnityPullbackMap.{u, v, w} (j m) n q
      (E.symm (Pi.single k y)) = (e m).symm (Pi.single k y m) := by
    intro y m
    have h1 : E (E.symm (Pi.single k y)) m = Pi.single k y m := by rw [AddEquiv.apply_symm_apply]
    change (e m) (rootsOfUnityPullbackMap.{u, v, w} (j m) n q (E.symm (Pi.single k y))) = _ at h1
    rw [← h1, AddEquiv.symm_apply_apply]
  have hblock : ∀ y : M k, E (rootsOfUnityPullbackMap.{u, v, w} φ n q (E.symm (Pi.single k y))) k =
      (e k) (rootsOfUnityPullbackMap.{u, v, w} (j k) n q
        (rootsOfUnityPullbackMap.{u, v, w} φ n q (E.symm (Pi.single k y)))) := fun _ => rfl
  split_ifs with h
  · rw [modelTrace]
    congr 1
    ext y
    refine (hblock y).trans ?_
    rw [rootsOfUnityPullbackMap_block_fixed j q φ P φfix hφfix k h, hEx, Pi.single_eq_same]
    rfl
  · have hzero : (LinearMap.proj k).comp
        (((E.toAddMonoidHom.comp
          ((rootsOfUnityPullbackMap.{u, v, w} φ n q).comp
            E.symm.toAddMonoidHom)).toZModLinearMap n).comp
          (LinearMap.single (ZMod n) M k)) = 0 := by
      ext y
      refine (hblock y).trans ?_
      rw [rootsOfUnityPullbackMap_block_move j q φ P hmove k h _ (fun m hm => by
        rw [hEx, Pi.single_eq_of_ne hm, map_zero]), map_zero]
      rfl
    rw [hzero, map_zero]

end Stacks.EtaleCohomology

end
