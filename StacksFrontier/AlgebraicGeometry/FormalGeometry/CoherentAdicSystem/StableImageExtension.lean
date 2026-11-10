module

public import StacksFrontier.Algebra.MittagLeffler.InverseSystem
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Assembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelStabilization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.LimitSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic

/-!
# A coherent adic system cut out of the stable images of an inverse system

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals and `P = (P_n)` an inverse
system of quasi-coherent `𝒪_X`-modules. This file produces, under conditions on the sections of `P`
over the affine opens of `X`, an object `G` of `Coh(X, ℐ)` which agrees with `P` on every open on
which `P` is already a coherent `ℐ`-adic system.

The construction is global and uses no glueing. Two increasing sequences of indices `m n ≤ k n` are
fixed, and

`E_n = Im(P_{k n} ⟶ P_{m n})`, `G_n = E_n / ℐ ⁿ⁺¹ E_n`,

with transitions induced by those of `P`. On an open `W` on which `P` is a coherent adic system the
transitions of `P` are epimorphisms, so `E_n|_W = P_{m n}|_W` and `G_n|_W = P_{m n}|_W / ℐ ⁿ⁺¹ =
P_n|_W` as soon as `m n ≥ n`; this is `Stacks.Coherent.isIso_stableImageQuotientRestrictHom`.

That `G` is a coherent adic system is checked on the sections over the members `V` of a finite
affine open cover. There the sections of `E_n` are the range `N_n` of
`Γ(V, P_{k n}) ⟶ Γ(V, P_{m n})`, and
`G` is a coherent adic system as soon as these ranges are finite modules, map onto one another, and
satisfy the lifting condition

`x ∈ N_{n+1}`, `t(x) ∈ ℐ(V) ⁿ⁺¹ N_n` `⟹` `x ∈ ℐ(V) ⁿ⁺¹ N_{n+1}`

(`Stacks.Coherent.isCoherentAdicSystem_stableImageQuotientSystem`). These hold when the inverse
system `Γ(V, P_n)` is Mittag-Leffler, the kernels of the projections out of its limit `M` are
eventually inside every `ℐ(V) ⁿ⁺¹ M`, and its terms are finite — the three conditions of the
Mittag-Leffler criterion of Stacks 0EHH, bundled as `Stacks.Coherent.IsStableAdicSystem` — and the
indices are chosen past the levels these conditions provide, uniformly over the finite cover
(`Stacks.Coherent.exists_uniform_indices`). Indeed under the Mittag-Leffler condition `N_n` is the
image of `M` (`Stacks.Coherent.exists_range_map_eq_range_limitπ`), and the lifting condition is
`Stacks.Coherent.mem_pow_smul_range_limitπ`.

The sections of `G_n` over a member `V` of the cover are `M/ℐ(V)ⁿ⁺¹M`.

## Main definitions

* `Stacks.Coherent.IsStableAdicSystem` — Mittag-Leffler, the `I`-adic limit topology condition and
  finiteness, for an inverse system of modules.
* `Stacks.Coherent.stableImageQuotientSystem` — the system `G`.

## Main results

* `Stacks.Coherent.exists_coherentAdicSystem_restrict_iso` — **the object `G` of `Coh(X, ℐ)`**,
  which agrees with `P` on every open on which `P` is a coherent adic system.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` is annihilated by `ℐ ⁿ⁺¹`, as in
`Stacks.Coherent.IsCoherentAdicSystem`.

## References

* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0EJV](https://stacks.math.columbia.edu/tag/0EJV)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Module theory -/

section ModuleTheory

variable {A : Type u} [CommRing A] (H : ℕᵒᵖ ⥤ ModuleCat.{u} A)

/-- The projections out of the limit are compatible with the transitions. -/
private theorem map_limitπ_apply {a b : ℕ} (hab : a ≤ b) (x : (limit H : ModuleCat.{u} A)) :
    (H.map (homOfLE hab).op).hom ((limit.π H (op b)).hom x) = (limit.π H (op a)).hom x :=
  congrArg (fun f => f.hom x) (limit.w H (homOfLE hab).op)

/-- **The limit maps onto the stable image.** If the inverse system of modules `H` is
Mittag-Leffler, then for every `m` there is a level `k ≥ m` past which every transition map into
`H_m` has the same range as the projection out of the limit. -/
theorem exists_range_map_eq_range_limitπ (hML : IsMittagLefflerCategorical H) (m : ℕ) :
    ∃ k : ℕ, ∃ hmk : m ≤ k, ∀ k' : ℕ, ∀ hkk' : k ≤ k',
      LinearMap.range (H.map (homOfLE (hmk.trans hkk')).op).hom =
        LinearMap.range (limit.π H (op m)).hom := by
  have hrange : ∀ i : ℕ, ∃ (j : ℕ) (h : i ≤ j), ∀ ⦃k : ℕ⦄ (hjk : j ≤ k),
      Set.range (H.map (homOfLE (h.trans hjk)).op).hom =
        Set.range (H.map (homOfLE h).op).hom := by
    intro i
    obtain ⟨c, hic, hc⟩ := hML.exists_range_eq i
    exact ⟨c, hic, fun k hck => by
      rw [← LinearMap.coe_range, ← LinearMap.coe_range, hc k hck]⟩
  choose c hc hcst using hrange
  let t : ∀ {i j : ℕ}, i ≤ j → H.obj (op j) →ₗ[A] H.obj (op i) :=
    fun h => (H.map (homOfLE h).op).hom
  have tcomp : ∀ {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) (z : H.obj (op l)),
      t hij (t hjl z) = t (hij.trans hjl) z := by
    intro i j l hij hjl z
    change (H.map (homOfLE hjl).op ≫ H.map (homOfLE hij).op).hom z = _
    rw [← H.map_comp]
    rfl
  have tid : ∀ {i : ℕ} (h : i ≤ i) (z : H.obj (op i)), t h z = z := by
    intro i h z
    change (H.map (𝟙 _)).hom z = z
    rw [H.map_id]
    rfl
  have hlift : ∀ (i : ℕ) (s : H.obj (op i)), s ∈ Set.range (t (hc i)) →
      ∃ s' : H.obj (op (i + 1)), s' ∈ Set.range (t (hc (i + 1))) ∧
        t (Nat.le_succ i) s' = s := by
    intro i s hs
    have h1 : c i ≤ max (c i) (c (i + 1)) := le_max_left _ _
    have h2 : c (i + 1) ≤ max (c i) (c (i + 1)) := le_max_right _ _
    rw [← hcst i h1] at hs
    obtain ⟨z, rfl⟩ := hs
    refine ⟨t ((hc (i + 1)).trans h2) z, ?_, tcomp _ _ z⟩
    rw [← hcst (i + 1) h2]
    exact ⟨z, rfl⟩
  refine ⟨c m, hc m, fun k' hkk' => le_antisymm ?_ ?_⟩
  · rintro x ⟨y, rfl⟩
    have hx : t ((hc m).trans hkk') y ∈ Set.range (t (hc m)) := by
      rw [← hcst m hkk']
      exact ⟨y, rfl⟩
    let a : (j : ℕ) → {s : H.obj (op (m + j)) // s ∈ Set.range (t (hc (m + j)))} :=
      fun j => Nat.rec ⟨t ((hc m).trans hkk') y, hx⟩
        (fun j s => ⟨(hlift (m + j) s.1 s.2).choose, (hlift (m + j) s.1 s.2).choose_spec.1⟩) j
    have hstep : ∀ j : ℕ, t (Nat.le_succ (m + j)) (a (j + 1)).1 = (a j).1 := fun j =>
      (hlift (m + j) (a j).1 (a j).2).choose_spec.2
    have hchain : ∀ (j j' : ℕ) (h : j ≤ j'),
        t (Nat.add_le_add_left h m) (a j').1 = (a j).1 := by
      intro j j' h
      induction j', h using Nat.le_induction with
      | base => exact tid _ _
      | succ j' hj ih =>
        rw [← ih, ← hstep j', tcomp]
    let f : (i : ℕ) → H.obj (op i) := fun i => t (Nat.le_add_left i m) (a i).1
    have hf : ∀ (i j : ℕ) (h : i ≤ j), t h (f j) = f i := by
      intro i j h
      simp only [f]
      rw [tcomp, ← hchain i j h, tcomp]
    let cone : Cone H :=
      { pt := ModuleCat.of A A
        π :=
          { app := fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton A _ (f i.unop))
            naturality := by
              intro i j g
              apply ModuleCat.hom_ext
              apply LinearMap.ext_ring
              have hij : j.unop ≤ i.unop := leOfHom g.unop
              have hg : g = (homOfLE hij).op := Subsingleton.elim _ _
              subst hg
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
                ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
              exact (hf j.unop i.unop hij).symm } }
    refine ⟨(limit.lift H cone).hom 1, ?_⟩
    have h1 := congrArg (fun g => g.hom (1 : A)) (limit.lift_π cone (op m))
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
    refine h1.trans ?_
    change LinearMap.toSpanSingleton A _ (f m) 1 = _
    rw [LinearMap.toSpanSingleton_apply, one_smul]
    exact hchain 0 m (Nat.zero_le m)
  · rintro x ⟨z, rfl⟩
    exact ⟨(limit.π H (op k')).hom z, map_limitπ_apply H ((hc m).trans hkk') z⟩

/-- **The stable-image lifting lemma.** Let `M = lim H` and suppose the kernel of the projection
`M → H_m` lies in `I ^ (n+1) M`. For `m ≤ m'`, an element of the image of `M` in `H_{m'}` whose
image in `H_m` lies in `I ^ (n+1)` times the image of `M` there itself lies in `I ^ (n+1)` times
the image of `M` in `H_{m'}`. -/
theorem mem_pow_smul_range_limitπ (I : Ideal A) {n m m' : ℕ} (hmm' : m ≤ m')
    (hker : LinearMap.ker (limit.π H (op m)).hom ≤
      I ^ (n + 1) • (⊤ : Submodule A (limit H : ModuleCat.{u} A)))
    {x : H.obj (op m')} (hx : x ∈ LinearMap.range (limit.π H (op m')).hom)
    (hy : (H.map (homOfLE hmm').op).hom x ∈
      I ^ (n + 1) • LinearMap.range (limit.π H (op m)).hom) :
    x ∈ I ^ (n + 1) • LinearMap.range (limit.π H (op m')).hom := by
  obtain ⟨y, rfl⟩ := hx
  rw [map_limitπ_apply H hmm', LinearMap.range_eq_map, ← Submodule.map_smul''] at hy
  obtain ⟨y', hy', hyy'⟩ := hy
  have hd : y - y' ∈ I ^ (n + 1) • (⊤ : Submodule A (limit H : ModuleCat.{u} A)) :=
    hker (by rw [LinearMap.mem_ker, map_sub, hyy', sub_self])
  have hmem : y ∈ I ^ (n + 1) • (⊤ : Submodule A (limit H : ModuleCat.{u} A)) := by
    simpa using Submodule.add_mem _ hd hy'
  rw [LinearMap.range_eq_map, ← Submodule.map_smul'']
  exact ⟨y, hmem, rfl⟩

/-- **The hypotheses on an inverse system of modules** under which its stable images give a
coherent adic system: it is Mittag-Leffler, the kernels of the projections out of its limit are
eventually inside every `J ⁿ⁺¹ lim H`, and its terms are finite modules. -/
def IsStableAdicSystem (J : Ideal A) : Prop :=
  IsMittagLefflerCategorical H ∧
    (∀ n : ℕ, ∃ a : ℕ, LinearMap.ker (limit.π H (op a)).hom ≤
      J ^ (n + 1) • (⊤ : Submodule A (limit H : ModuleCat.{u} A))) ∧
    ∀ j : ℕ, Module.Finite A (H.obj (op j))

/-- The kernels of the projections out of the limit of an inverse system decrease with the
index. -/
theorem ker_limitπ_antitone {a b : ℕ} (hab : a ≤ b) :
    LinearMap.ker (limit.π H (op b)).hom ≤ LinearMap.ker (limit.π H (op a)).hom := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← map_limitπ_apply H hab, hx, map_zero]

/-- **Uniform indices for finitely many Mittag-Leffler systems with `J`-adic limit topology.**
Only the first two conditions of `IsStableAdicSystem` are used. -/
theorem exists_uniform_indices_of_isMittagLeffler {ι : Type*} [Finite ι] (A' : ι → Type u)
    [∀ i, CommRing (A' i)] (J : ∀ i, Ideal (A' i)) (H' : ∀ i, ℕᵒᵖ ⥤ ModuleCat.{u} (A' i))
    (hML : ∀ i, IsMittagLefflerCategorical (H' i))
    (hker : ∀ i, ∀ n : ℕ, ∃ a : ℕ, LinearMap.ker (limit.π (H' i) (op a)).hom ≤
      J i ^ (n + 1) • (⊤ : Submodule (A' i) (limit (H' i) : ModuleCat.{u} (A' i)))) :
    ∃ (m k : ℕ → ℕ), Monotone m ∧ Monotone k ∧ ∃ hmk : ∀ n, m n ≤ k n,
      (∀ n, n ≤ m n) ∧
      (∀ i n, LinearMap.range ((H' i).map (homOfLE (hmk n)).op).hom =
        LinearMap.range (limit.π (H' i) (op (m n))).hom) ∧
      (∀ i n, LinearMap.ker (limit.π (H' i) (op (m n))).hom ≤
        J i ^ (n + 1) • (⊤ : Submodule (A' i) (limit (H' i) : ModuleCat.{u} (A' i)))) := by
  classical
  have := Fintype.ofFinite ι
  choose a ha using hker
  choose b hb hbstab using fun i => exists_range_map_eq_range_limitπ (H' i) (hML i)
  let m : ℕ → ℕ := fun n => n + ∑ j ∈ Finset.range (n + 1), ∑ i, a i j
  let k : ℕ → ℕ := fun n => m n + ∑ j ∈ Finset.range (n + 1), ∑ i, b i (m j)
  have hm : Monotone m := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [m]
    rw [Finset.sum_range_succ _ (n + 1)]
    omega
  have hk : Monotone k := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [k]
    rw [Finset.sum_range_succ _ (n + 1)]
    have : m n ≤ m (n + 1) := hm (Nat.le_add_right n 1)
    omega
  have hmk : ∀ n, m n ≤ k n := fun n => Nat.le_add_right _ _
  have hle_sum : ∀ (g : ι → ℕ → ℕ) (i : ι) (n : ℕ),
      g i n ≤ ∑ j ∈ Finset.range (n + 1), ∑ i', g i' j := fun g i n =>
    (Finset.single_le_sum (f := fun i' => g i' n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun j => ∑ i', g i' j) (fun _ _ => Nat.zero_le _)
        (Finset.self_mem_range_succ n))
  have ham : ∀ i n, a i n ≤ m n := fun i n => (hle_sum a i n).trans (Nat.le_add_left _ _)
  have hbk : ∀ i n, b i (m n) ≤ k n := fun i n =>
    (hle_sum (fun i j => b i (m j)) i n).trans (Nat.le_add_left _ _)
  exact ⟨m, k, hm, hk, hmk, fun n => Nat.le_add_right _ _,
    fun i n => hbstab i (m n) (k n) (hbk i n),
    fun i n => (ker_limitπ_antitone (H' i) (ham i n)).trans (ha i n)⟩

/-- **Uniform indices for finitely many stable adic systems.** -/
theorem exists_uniform_indices {ι : Type*} [Finite ι] (A' : ι → Type u) [∀ i, CommRing (A' i)]
    (J : ∀ i, Ideal (A' i)) (H' : ∀ i, ℕᵒᵖ ⥤ ModuleCat.{u} (A' i))
    (h : ∀ i, IsStableAdicSystem (H' i) (J i)) :
    ∃ (m k : ℕ → ℕ), Monotone m ∧ Monotone k ∧ ∃ hmk : ∀ n, m n ≤ k n,
      (∀ n, n ≤ m n) ∧
      (∀ i n, LinearMap.range ((H' i).map (homOfLE (hmk n)).op).hom =
        LinearMap.range (limit.π (H' i) (op (m n))).hom) ∧
      (∀ i n, LinearMap.ker (limit.π (H' i) (op (m n))).hom ≤
        J i ^ (n + 1) • (⊤ : Submodule (A' i) (limit (H' i) : ModuleCat.{u} (A' i)))) :=
  exists_uniform_indices_of_isMittagLeffler A' J H' (fun i => (h i).1) (fun i => (h i).2.1)

/-- The images of the transitions of isomorphic inverse systems correspond. -/
theorem range_map_eq_map_range_of_iso {H H' : ℕᵒᵖ ⥤ ModuleCat.{u} A} (e : H ≅ H') {i j : ℕ}
    (hij : i ≤ j) : LinearMap.range (H'.map (homOfLE hij).op).hom =
      Submodule.map (e.hom.app (op i)).hom (LinearMap.range (H.map (homOfLE hij).op).hom) := by
  have hnat : H'.map (homOfLE hij).op =
      e.inv.app (op j) ≫ H.map (homOfLE hij).op ≫ e.hom.app (op i) := by
    rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hsurj : LinearMap.range (e.inv.app (op j)).hom = ⊤ :=
    LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso (e.inv.app (op j))).2
  rw [hnat, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.range_comp, hsurj,
    ← LinearMap.range_eq_map, LinearMap.range_comp]

/-- The Mittag-Leffler condition is invariant under isomorphism of inverse systems. -/
theorem isMittagLefflerCategorical_of_iso {H H' : ℕᵒᵖ ⥤ ModuleCat.{u} A} (e : H ≅ H')
    (hML : IsMittagLefflerCategorical H) : IsMittagLefflerCategorical H' := by
  refine isMittagLefflerCategorical_of_forall_exists_range_eq H' fun i => ?_
  obtain ⟨c, hic, hc⟩ := hML.exists_range_eq i
  refine ⟨c, hic, fun k hck => ?_⟩
  rw [range_map_eq_map_range_of_iso e, range_map_eq_map_range_of_iso e, hc k hck]

/-- The condition that the kernels of the projections out of the limit are eventually inside
every `J ⁿ⁺¹ lim H` is invariant under isomorphism of inverse systems. -/
theorem exists_ker_limitπ_le_of_iso {H H' : ℕᵒᵖ ⥤ ModuleCat.{u} A} (e : H ≅ H') {J : Ideal A}
    (hker : ∀ n : ℕ, ∃ a : ℕ, LinearMap.ker (limit.π H (op a)).hom ≤
      J ^ (n + 1) • (⊤ : Submodule A (limit H : ModuleCat.{u} A))) (n : ℕ) :
    ∃ a : ℕ, LinearMap.ker (limit.π H' (op a)).hom ≤
      J ^ (n + 1) • (⊤ : Submodule A (limit H' : ModuleCat.{u} A)) := by
  obtain ⟨a, ha⟩ := hker n
  refine ⟨a, fun x hx => ?_⟩
  let L := HasLimit.isoOfNatIso e
  have hπ : (L.inv ≫ limit.π H (op a)) = limit.π H' (op a) ≫ e.inv.app (op a) := by
    simp [L]
  have hy : L.inv.hom x ∈ LinearMap.ker (limit.π H (op a)).hom := by
    rw [LinearMap.mem_ker]
    have := congrArg (fun g => g.hom x) hπ
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.mem_ker.mp hx, map_zero]
  have h2 := Submodule.mem_map_of_mem (f := L.hom.hom) (ha hy)
  rw [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso L.hom).2] at h2
  simpa using h2

/-- Finiteness of the images of the projections out of the limit is invariant under isomorphism
of inverse systems. -/
theorem finite_range_limitπ_of_iso {H H' : ℕᵒᵖ ⥤ ModuleCat.{u} A} (e : H ≅ H') (j : ℕ)
    (hfin : Module.Finite A (LinearMap.range (limit.π H (op j)).hom)) :
    Module.Finite A (LinearMap.range (limit.π H' (op j)).hom) := by
  let L := HasLimit.isoOfNatIso e
  have hπ : limit.π H' (op j) = L.inv ≫ limit.π H (op j) ≫ e.hom.app (op j) := by
    simp [L]
  rw [hπ, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso L.inv).2, Submodule.map_top,
    LinearMap.range_comp]
  exact Module.Finite.map _ _

/-- `IsStableAdicSystem` is invariant under isomorphism of inverse systems. -/
theorem IsStableAdicSystem.of_iso {H H' : ℕᵒᵖ ⥤ ModuleCat.{u} A} (e : H ≅ H') {J : Ideal A}
    (h : IsStableAdicSystem H J) : IsStableAdicSystem H' J :=
  ⟨isMittagLefflerCategorical_of_iso e h.1, exists_ker_limitπ_le_of_iso e h.2.1,
    fun j => have := h.2.2 j; Module.Finite.equiv (e.app (op j)).toLinearEquiv⟩

end ModuleTheory

/-! ### Sections over affine opens -/

section Sections

variable {X : Scheme.{u}}

/-- **An isomorphism of quasi-coherent modules may be detected on the sections over the members
of an affine open cover.** -/
theorem isIso_of_bijective_app_of_affineCover {ι : Type*} (T : ι → X.affineOpens)
    (hT : ⨆ i, (T i : X.Opens) = ⊤) {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) (h : ∀ i, Function.Bijective (φ.app (T i : X.Opens))) : IsIso φ := by
  let f : ∀ i, Spec Γ(X, (T i : X.Opens)) ⟶ X := fun i => (T i).2.fromSpec
  have hf : ∀ i, IsOpenImmersion (f i) := fun i => (T i).2.isOpenImmersion_fromSpec
  have hr : ⨆ i, (f i).opensRange = ⊤ :=
    (iSup_congr fun i => (T i).2.opensRange_fromSpec).trans hT
  have hiso : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (f i)).map φ) := by
    intro i
    have := Scheme.Modules.isQuasicoherent_restrictFunctor (f i) M
    have := Scheme.Modules.isQuasicoherent_restrictFunctor (f i) N
    refine isIso_of_bijective_evaluation_top _ ?_
    have hc : (Stacks.Algebraization.affineSectionsEquiv N (T i : X.Opens) (T i).2) ∘
        ((SheafOfModules.evaluation (Spec Γ(X, (T i : X.Opens))).ringCatSheaf (op ⊤)).map
          ((Scheme.Modules.restrictFunctor (f i)).map φ)).hom =
        φ.app (T i : X.Opens) ∘
          (Stacks.Algebraization.affineSectionsEquiv M (T i : X.Opens) (T i).2) :=
      funext (Stacks.Algebraization.affineSectionsEquiv_naturality φ (T i : X.Opens) (T i).2)
    have hb := (h i).comp
      (Stacks.Algebraization.affineSectionsEquiv M (T i : X.Opens) (T i).2).bijective
    rw [← hc] at hb
    exact (Function.Bijective.of_comp_iff' (LinearEquiv.bijective _) _).mp hb
  have hext : ∀ {P Q : X.Modules} {a b : P ⟶ Q},
      (∀ i, (Scheme.Modules.restrictFunctor (f i)).map a =
        (Scheme.Modules.restrictFunctor (f i)).map b) → a = b := fun hab =>
    Stacks.Descent.hom_ext_of_restrictFunctor_map_eq f hr hab
  have : Mono φ := ⟨fun {_} a b hab => hext fun i => by
    have := hiso i
    refine (cancel_mono ((Scheme.Modules.restrictFunctor (f i)).map φ)).mp ?_
    exact ((Scheme.Modules.restrictFunctor (f i)).map_comp a φ).symm.trans
      ((congrArg (Scheme.Modules.restrictFunctor (f i)).map hab).trans
        ((Scheme.Modules.restrictFunctor (f i)).map_comp b φ))⟩
  have : Epi φ := ⟨fun {_} a b hab => hext fun i => by
    have := hiso i
    refine (cancel_epi ((Scheme.Modules.restrictFunctor (f i)).map φ)).mp ?_
    exact ((Scheme.Modules.restrictFunctor (f i)).map_comp φ a).symm.trans
      ((congrArg (Scheme.Modules.restrictFunctor (f i)).map hab).trans
        ((Scheme.Modules.restrictFunctor (f i)).map_comp φ b))⟩
  exact isIso_of_mono_of_epi φ

/-- For a quasi-coherent `M`, the quotient projection `M ⟶ M / ℐ ʳ M` is surjective on the
sections over an affine open. -/
theorem surjective_app_idealPowerQuotient_π (I : X.IdealSheafData) (r : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] (V : X.affineOpens) :
    Function.Surjective
      ((cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple I r M).ι).app V) :=
  Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen _ V

/-- For a quasi-coherent `M`, the kernel of the quotient projection `M ⟶ M / ℐ ʳ M` on the
sections over an affine open `V` is `ℐ(V) ʳ • M(V)`. -/
theorem app_idealPowerQuotient_π_eq_zero_iff (I : X.IdealSheafData) (r : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] (V : X.affineOpens) (x : Γ(M, V)) :
    (cokernel.π (C := X.Modules) (Stacks.Algebraization.idealPowerMultiple I r M).ι).app V x = 0 ↔
      x ∈ I.ideal V ^ r • (⊤ : Submodule Γ(X, V) Γ(M, V)) := by
  rw [← Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine I r M V]
  exact Stacks.Algebraization.cokernel_π_app_eq_zero_iff M _ V.1 x

/-- Over an affine open, the image of a morphism of quasi-coherent modules has the range of the
morphism as its sections. -/
theorem range_app_image_ι {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (V : X.affineOpens) : Set.range ((image.ι f).app V) = Set.range (f.app V) := by
  have : (image (C := X.Modules) f).IsQuasicoherent := Stacks.Algebraization.isQuasicoherent_image f
  have hsurj : Function.Surjective ((factorThruImage f).app V) :=
    Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen _ V
  have hfac : f.app V = (image.ι f).app V ∘ (factorThruImage f).app V := by
    funext x
    exact congr($((congrArg (fun g => Scheme.Modules.Hom.app g (V : X.Opens))
      (image.fac f)).symm) x)
  rw [hfac, Set.range_comp, hsurj.range_eq, Set.image_univ]

end Sections

/-! ### The construction -/

section Construction

open Stacks.AlgebraicGeometry.QcohLimits (appₗ)
open Stacks.AlgebraicGeometry.CoherenceCriteria
  (isCoherent_of_exists_affineOpenCover_isFiniteTildeOn)
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent (isFiniteTildeOn_of_moduleFinite_sections)
open Stacks.Algebraization (idealPowerMultiple idealPowerQuotient idealPowerQuotientMap
  idealPowerQuotientDesc affineSectionFunctor)

variable {X : Scheme.{u}} (I : X.IdealSheafData) (P : ℕᵒᵖ ⥤ X.Modules)
  [hPq : ∀ n, (P.obj n).IsQuasicoherent]
  (m k : ℕ → ℕ) (hm : Monotone m) (hk : Monotone k) (hmk : ∀ n, m n ≤ k n)

/-- The image `E_n` of the transition `P_{k n} ⟶ P_{m n}`. -/
abbrev stableImage (n : ℕ) : X.Modules :=
  image (C := X.Modules) (P.map (homOfLE (hmk n)).op)

/-- The image `E_n` is quasi-coherent. -/
instance isQuasicoherent_stableImage (n : ℕ) : (stableImage P m k hmk n).IsQuasicoherent :=
  Stacks.Algebraization.isQuasicoherent_image _

/-- The map `E_{n+1} ⟶ E_n` induced by the transitions of `P`. -/
def stableImageMap (n : ℕ) : stableImage P m k hmk (n + 1) ⟶ stableImage P m k hmk n :=
  image.map (Arrow.homMk (f := Arrow.mk (P.map (homOfLE (hmk (n + 1))).op))
    (g := Arrow.mk (P.map (homOfLE (hmk n)).op))
    (P.map (homOfLE (hk n.le_succ)).op) (P.map (homOfLE (hm n.le_succ)).op)
    (by
      simp only [Arrow.mk_hom]
      rw [← P.map_comp, ← P.map_comp]
      rfl))

omit hPq in
/-- The map `E_{n+1} ⟶ E_n` commutes with the inclusions into `P_{m (n+1)}` and `P_{m n}` and the
transition between them. -/
@[reassoc]
theorem stableImageMap_ι (n : ℕ) :
    stableImageMap P m k hm hk hmk n ≫ image.ι (P.map (homOfLE (hmk n)).op) =
      image.ι (P.map (homOfLE (hmk (n + 1))).op) ≫ P.map (homOfLE (hm n.le_succ)).op :=
  image.map_ι _

/-- The term `G_n = E_n / ℐ ⁿ⁺¹ E_n`. -/
abbrev stableImageQuotient (n : ℕ) : X.Modules :=
  idealPowerQuotient I (n + 1) (stableImage P m k hmk n)

/-- The term `G_n` is annihilated by `ℐ ⁿ⁺¹`. -/
theorem idealPowerMultiple_stableImageQuotient (n : ℕ) :
    idealPowerMultiple I (n + 1) (stableImageQuotient I P m k hmk n) = ⊥ :=
  Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot I (n + 1) _

/-- The transition `G_{n+1} ⟶ G_n`. -/
def stableImageQuotientMap (n : ℕ) :
    stableImageQuotient I P m k hmk (n + 1) ⟶ stableImageQuotient I P m k hmk n :=
  idealPowerQuotientMap I I (n + 1 + 1) (n + 1)
    (Scheme.IdealSheafData.pow_le_pow_of_le I (Nat.le_succ _)) (stableImageMap P m k hm hk hmk n)

/-- The descent `G_{n+1} / ℐ ⁿ⁺¹ G_{n+1} ⟶ G_n` of the transition. -/
def stableImageQuotientDesc (n : ℕ) :
    idealPowerQuotient I (n + 1) (stableImageQuotient I P m k hmk (n + 1)) ⟶
      stableImageQuotient I P m k hmk n :=
  idealPowerQuotientDesc I (n + 1) (stableImageQuotientMap I P m k hm hk hmk n)
    (idealPowerMultiple_stableImageQuotient I P m k hmk n)

section Chart

open Stacks.AlgebraicGeometry.QcohLimits (appₗ)

variable (V : X.affineOpens)
  (N : ∀ n, Submodule Γ(X, V) Γ(P.obj (op (m n)), V))
  (hN : ∀ n, Set.range ((P.map (homOfLE (hmk n)).op).app V) = N n)

include hN in
/-- Over the chart `V`, the sections of `E_n` are `N n`. -/
theorem range_appₗ_image_ι (n : ℕ) :
    LinearMap.range (appₗ (image.ι (P.map (homOfLE (hmk n)).op)) V) = N n :=
  SetLike.coe_injective ((range_app_image_ι _ V).trans (hN n))

include hN in
/-- **Finiteness of the sections over a chart.** -/
theorem finite_app_stableImageQuotient (hfin : ∀ n, Module.Finite Γ(X, V) (N n)) (n : ℕ) :
    Module.Finite Γ(X, V) Γ(stableImageQuotient I P m k hmk n, V) := by
  have hinj := Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono
    (image.ι (P.map (homOfLE (hmk n)).op)) V
  have e := LinearEquiv.ofInjective (appₗ (image.ι (P.map (homOfLE (hmk n)).op)) V) hinj
  have : Module.Finite Γ(X, V) Γ(stableImage P m k hmk n, V) := by
    have h := hfin n
    rw [← range_appₗ_image_ι P m k hmk V N hN n] at h
    exact Module.Finite.equiv e.symm
  exact Module.Finite.of_surjective
    (appₗ (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1)
      (stableImage P m k hmk n)).ι) V)
    (surjective_app_idealPowerQuotient_π I (n + 1) _ V)

include hN in
/-- **The descended transition is bijective on the sections over a chart.** -/
theorem bijective_app_stableImageQuotientDesc
    (hsurj : ∀ n, Submodule.map (appₗ (P.map (homOfLE (hm n.le_succ)).op) V) (N (n + 1)) = N n)
    (hlift : ∀ n, ∀ x ∈ N (n + 1),
      (P.map (homOfLE (hm n.le_succ)).op).app V x ∈ I.ideal V ^ (n + 1) • N n →
        x ∈ I.ideal V ^ (n + 1) • N (n + 1))
    (n : ℕ) :
    Function.Bijective ((stableImageQuotientDesc I P m k hm hk hmk n).app V) := by
  set ι₀ := image.ι (P.map (homOfLE (hmk n)).op)
  set ι₁ := image.ι (P.map (homOfLE (hmk (n + 1))).op)
  set t := P.map (homOfLE (hm n.le_succ)).op
  set σ := stableImageMap P m k hm hk hmk n
  set π₀ := cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (stableImage P m k hmk n)).ι
  set π₁ := cokernel.π (C := X.Modules)
    (idealPowerMultiple I (n + 1 + 1) (stableImage P m k hmk (n + 1))).ι
  set q := cokernel.π (C := X.Modules)
    (idealPowerMultiple I (n + 1) (stableImageQuotient I P m k hmk (n + 1))).ι
  set d := stableImageQuotientDesc I P m k hm hk hmk n
  have hinj₀ : Function.Injective (ι₀.app V) :=
    Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono ι₀ V
  have hinj₁ : Function.Injective (ι₁.app V) :=
    Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono ι₁ V
  have hσ : ∀ e, ι₀.app V (σ.app V e) = t.app V (ι₁.app V e) := fun e =>
    congr($(congrArg (fun g => Scheme.Modules.Hom.app g (V : X.Opens))
      (stableImageMap_ι P m k hm hk hmk n)) e)
  have hdq : ∀ e, d.app V (q.app V (π₁.app V e)) = π₀.app V (σ.app V e) := by
    intro e
    have h1 : q ≫ d = stableImageQuotientMap I P m k hm hk hmk n :=
      Stacks.Algebraization.idealPowerQuotientDesc_π I (n + 1) _ _
    have h2 : π₁ ≫ stableImageQuotientMap I P m k hm hk hmk n = σ ≫ π₀ :=
      Stacks.Algebraization.idealPowerQuotientMap_π I I _ _ _ σ
    have := congrArg (fun g => Scheme.Modules.Hom.app g (V : X.Opens)) (h1 ▸ h2 :
      π₁ ≫ q ≫ d = σ ≫ π₀)
    exact congr($this e)
  have hq : Function.Surjective (q.app V) := surjective_app_idealPowerQuotient_π I (n + 1) _ V
  have hπ₁ : Function.Surjective (π₁.app V) := surjective_app_idealPowerQuotient_π I _ _ V
  have hπ₀ : Function.Surjective (π₀.app V) := surjective_app_idealPowerQuotient_π I _ _ V
  have hR₀ := range_appₗ_image_ι P m k hmk V N hN n
  have hR₁ := range_appₗ_image_ι P m k hmk V N hN (n + 1)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨w', rfl⟩ := hq w
    obtain ⟨e, rfl⟩ := hπ₁ w'
    rw [hdq, app_idealPowerQuotient_π_eq_zero_iff] at hw
    have h1 : ι₀.app V (σ.app V e) ∈ I.ideal V ^ (n + 1) • N n := by
      rw [← hR₀, LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem (f := appₗ ι₀ V) hw
    rw [hσ] at h1
    have h2 := hlift n (ι₁.app V e) (by rw [← hR₁]; exact ⟨e, rfl⟩) h1
    rw [← hR₁, LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
    obtain ⟨e', he', hee'⟩ := h2
    obtain rfl := hinj₁ hee'
    have h3 : π₁.app V e' ∈ I.ideal V ^ (n + 1) •
        (⊤ : Submodule Γ(X, V) Γ(stableImageQuotient I P m k hmk (n + 1), V)) := by
      have := Submodule.mem_map_of_mem (f := appₗ π₁ V) he'
      rw [Submodule.map_smul'', Submodule.map_top] at this
      exact Submodule.smul_mono le_rfl le_top this
    exact (app_idealPowerQuotient_π_eq_zero_iff I (n + 1) _ V _).mpr h3
  · intro z
    obtain ⟨e, rfl⟩ := hπ₀ z
    have h1 : ι₀.app V e ∈ N n := by rw [← hR₀]; exact ⟨e, rfl⟩
    rw [← hsurj n] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rw [← hR₁] at hy
    obtain ⟨e', rfl⟩ := hy
    exact ⟨q.app V (π₁.app V e'), by rw [hdq, hinj₀ ((hσ e').trans hyx)]⟩

end Chart

/-- **The system `G_n = E_n / ℐ ⁿ⁺¹ E_n`**, with the transitions induced by those of `P`. -/
def stableImageQuotientSystem : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (stableImageQuotientMap I P m k hm hk hmk)

omit hPq in
/-- The term `n` of the system `G` is `G_n`. -/
theorem stableImageQuotientSystem_obj (n : ℕ) :
    (stableImageQuotientSystem I P m k hm hk hmk).obj (op n) =
      stableImageQuotient I P m k hmk n := rfl

omit hPq in
/-- The transition `n + 1 ⟶ n` of the system `G` is `G_{n+1} ⟶ G_n`. -/
theorem stableImageQuotientSystem_map_succ (n : ℕ) :
    (stableImageQuotientSystem I P m k hm hk hmk).map (homOfLE (Nat.le_succ n)).op =
      stableImageQuotientMap I P m k hm hk hmk n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- **The system `G` is a coherent adic system**, as soon as on the members `V` of an affine open
cover the images `N n ⊆ Γ(P_{m n}, V)` of the transitions `P_{k n} ⟶ P_{m n}` are finite,
map onto one another, and satisfy the lifting condition for the ideal-power multiples. -/
theorem isCoherentAdicSystem_stableImageQuotientSystem [IsLocallyNoetherian X]
    {ι : Type u} (T : ι → X.affineOpens) (hT : ⨆ i, (T i : X.Opens) = ⊤)
    (N : ∀ i n, Submodule Γ(X, T i) Γ(P.obj (op (m n)), T i))
    (hN : ∀ i n, Set.range ((P.map (homOfLE (hmk n)).op).app (T i)) = N i n)
    (hfin : ∀ i n, Module.Finite Γ(X, T i) (N i n))
    (hsurj : ∀ i n,
      Submodule.map (appₗ (P.map (homOfLE (hm n.le_succ)).op) (T i)) (N i (n + 1)) = N i n)
    (hlift : ∀ i n, ∀ x ∈ N i (n + 1),
      (P.map (homOfLE (hm n.le_succ)).op).app (T i) x ∈ I.ideal (T i) ^ (n + 1) • N i n →
        x ∈ I.ideal (T i) ^ (n + 1) • N i (n + 1)) :
    IsCoherentAdicSystem I (stableImageQuotientSystem I P m k hm hk hmk) := by
  refine ⟨fun n => ?_, fun n => idealPowerMultiple_stableImageQuotient I P m k hmk n,
    fun n => ?_⟩
  · change _root_.SheafOfModules.IsCoherent.{u} (stableImageQuotient I P m k hmk n)
    refine isCoherent_of_exists_affineOpenCover_isFiniteTildeOn _
        ⟨ι, fun i => (T i : X.Opens), IsOpenCover.mk hT, fun i => ⟨(T i).2, ?_⟩⟩
    exact isFiniteTildeOn_of_moduleFinite_sections _ (T i)
        (finite_app_stableImageQuotient I P m k hmk (T i) (N i) (hN i) (hfin i) n)
  · have hiso : IsIso (stableImageQuotientDesc I P m k hm hk hmk n) :=
      isIso_of_bijective_app_of_affineCover T hT _ fun i =>
        bijective_app_stableImageQuotientDesc I P m k hm hk hmk (T i) (N i) (hN i) (hsurj i)
          (hlift i) n
    refine ⟨@asIso _ _ _ _ (stableImageQuotientDesc I P m k hm hk hmk n) hiso, ?_⟩
    rw [stableImageQuotientSystem_map_succ]
    exact Stacks.Algebraization.idealPowerQuotientDesc_π I (n + 1) _
      (idealPowerMultiple_stableImageQuotient I P m k hmk n)

/-! ### The restriction to an open on which `P` is a coherent adic system -/

section Restriction

variable {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (F : ℕᵒᵖ ⥤ W.Modules)
  (hF : IsCoherentAdicSystem (I.comap j) F) (ε : P ⋙ Scheme.Modules.restrictFunctor j ≅ F)
  (hnm : ∀ n, n ≤ m n)

/-- The map `E_n|_W ⟶ F_n`: the inclusion of `E_n` into `P_{m n}`, restricted to `W`, followed
by the identification of `P|_W` with `F` and the transition `F_{m n} ⟶ F_n`. -/
def stableImageRestrictMap (n : ℕ) :
    (Scheme.Modules.restrictFunctor j).obj (stableImage P m k hmk n) ⟶ F.obj (op n) :=
  (Scheme.Modules.restrictFunctor j).map (image.ι (P.map (homOfLE (hmk n)).op)) ≫
    ε.hom.app (op (m n)) ≫ F.map (homOfLE (hnm n)).op

/-- The comparison `G_n|_W ⟶ F_n`. -/
def stableImageQuotientRestrictMap (n : ℕ) :
    (Scheme.Modules.restrictFunctor j).obj (stableImageQuotient I P m k hmk n) ⟶ F.obj (op n) :=
  (Stacks.Algebraization.restrictIdealPowerQuotientIso j I (n + 1) _).inv ≫
    idealPowerQuotientDesc (I.comap j) (n + 1) (stableImageRestrictMap P m k hmk j F ε hnm n)
      (hF.idealPowerMultiple_eq_bot n)

/-- The comparison `G_n|_W ⟶ F_n` restricts, along the quotient map `E_n|_W ⟶ G_n|_W`, to the
map `E_n|_W ⟶ F_n`. -/
theorem restrict_π_comp_stableImageQuotientRestrictMap (n : ℕ) :
    (Scheme.Modules.restrictFunctor j).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (stableImage P m k hmk n)).ι) ≫
      stableImageQuotientRestrictMap I P m k hmk j F hF ε hnm n =
      stableImageRestrictMap P m k hmk j F ε hnm n := by
  have h := Stacks.Algebraization.cokernel_π_comp_restrictIdealPowerQuotientIso j I (n + 1)
    (stableImage P m k hmk n)
  refine Eq.trans (congrArg (fun g => g ≫ stableImageQuotientRestrictMap I P m k hmk j F hF ε hnm n)
    h.symm) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun g => _ ≫ g) (Iso.hom_inv_id_assoc _ _)).trans ?_
  exact Stacks.Algebraization.idealPowerQuotientDesc_π _ _ _ _

include hF in
/-- The comparisons `G_n|_W ⟶ F_n` commute with the transitions of `G` and of `F`. -/
theorem stableImageQuotientRestrictMap_naturality (n : ℕ) :
    (Scheme.Modules.restrictFunctor j).map (stableImageQuotientMap I P m k hm hk hmk n) ≫
        stableImageQuotientRestrictMap I P m k hmk j F hF ε hnm n =
      stableImageQuotientRestrictMap I P m k hmk j F hF ε hnm (n + 1) ≫
        F.map (homOfLE (n.le_add_right 1)).op := by
  have : Epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1 + 1) (stableImage P m k hmk (n + 1))).ι) :=
    Stacks.Algebraization.epi_cokernel_π_submodule_ι _
  refine (cancel_epi ((Scheme.Modules.restrictFunctor j).map (cokernel.π (C := X.Modules)
    (idealPowerMultiple I (n + 1 + 1) (stableImage P m k hmk (n + 1))).ι))).1 ?_
  have h1 : cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1 + 1) (stableImage P m k hmk (n + 1))).ι ≫
        stableImageQuotientMap I P m k hm hk hmk n =
      stableImageMap P m k hm hk hmk n ≫
        cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (stableImage P m k hmk n)).ι :=
    Stacks.Algebraization.idealPowerQuotientMap_π I I _ _ _ _
  rw [← Category.assoc, ← Functor.map_comp, h1, Functor.map_comp, Category.assoc,
    restrict_π_comp_stableImageQuotientRestrictMap, ← Category.assoc,
    restrict_π_comp_stableImageQuotientRestrictMap]
  simp only [stableImageRestrictMap, Category.assoc]
  rw [← Functor.map_comp_assoc, stableImageMap_ι, Functor.map_comp_assoc]
  congr 1
  have hε := ε.hom.naturality (homOfLE (hm (Nat.le_succ n))).op
  simp only [Functor.comp_map] at hε
  rw [reassoc_of% hε, ← F.map_comp, ← F.map_comp]
  rfl

/-- **The comparison `G|_W ⟶ F`**, as a morphism of inverse systems. -/
def stableImageQuotientRestrictHom :
    stableImageQuotientSystem I P m k hm hk hmk ⋙ Scheme.Modules.restrictFunctor j ⟶ F :=
  NatTrans.ofOpSequence (fun n => stableImageQuotientRestrictMap I P m k hmk j F hF ε hnm n)
    (fun n => by
      simp only [Functor.comp_map]
      rw [stableImageQuotientSystem_map_succ]
      exact stableImageQuotientRestrictMap_naturality I P m k hm hk hmk j F hF ε hnm n)

include hF in
/-- Each comparison `G_n|_W ⟶ F_n` is an isomorphism. -/
theorem isIso_stableImageQuotientRestrictMap (n : ℕ) :
    IsIso (stableImageQuotientRestrictMap I P m k hmk j F hF ε hnm n) := by
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.preservesFiniteLimits_restrictFunctor j
  let τ := (Scheme.Modules.restrictFunctor j).map (image.ι (P.map (homOfLE (hmk n)).op)) ≫
    ε.hom.app (op (m n))
  have hτm : Mono τ := mono_comp _ _
  have hτe : Epi τ := by
    have hfac : (Scheme.Modules.restrictFunctor j).map
        (factorThruImage (P.map (homOfLE (hmk n)).op)) ≫ τ =
        ε.hom.app (op (k n)) ≫ F.map (homOfLE (hmk n)).op := by
      simp only [τ]
      rw [← Category.assoc, ← Functor.map_comp, image.fac]
      exact ε.hom.naturality (homOfLE (hmk n)).op
    have : Epi (F.map (homOfLE (hmk n)).op) := hF.epi_map (hmk n)
    have : Epi ((Scheme.Modules.restrictFunctor j).map
        (factorThruImage (P.map (homOfLE (hmk n)).op)) ≫ τ) := by
      rw [hfac]; infer_instance
    exact epi_of_epi ((Scheme.Modules.restrictFunctor j).map
      (factorThruImage (P.map (homOfLE (hmk n)).op))) τ
  have hτi : IsIso τ := isIso_of_mono_of_epi τ
  have hπF : IsIso (cokernel.π (C := W.Modules)
      (idealPowerMultiple (I.comap j) (n + 1) (F.obj (op n))).ι) :=
    Stacks.Algebraization.isIso_cokernel_π_of_idealPowerMultiple_eq_bot (I.comap j) (n + 1) _
      (hF.idealPowerMultiple_eq_bot n)
  have hmap : IsIso (idealPowerQuotientMap (I.comap j) (I.comap j) (n + 1) (n + 1) le_rfl
      (F.map (homOfLE (hnm n)).op)) :=
    hF.isIso_idealPowerQuotientMap_map (I.comap j) (n + 1) (hnm n) le_rfl
  have hτmap : IsIso (idealPowerQuotientMap (I.comap j) (I.comap j) (n + 1) (n + 1) le_rfl τ) :=
    Stacks.Algebraization.isIso_idealPowerQuotientMap (I.comap j) (n + 1) (asIso τ)
  have hdesc : idealPowerQuotientDesc (I.comap j) (n + 1)
      (stableImageRestrictMap P m k hmk j F ε hnm n) (hF.idealPowerMultiple_eq_bot n) =
      idealPowerQuotientMap (I.comap j) (I.comap j) (n + 1) (n + 1) le_rfl τ ≫
        idealPowerQuotientMap (I.comap j) (I.comap j) (n + 1) (n + 1) le_rfl
          (F.map (homOfLE (hnm n)).op) ≫
          inv (cokernel.π (C := W.Modules)
            (idealPowerMultiple (I.comap j) (n + 1) (F.obj (op n))).ι) := by
    refine (cancel_epi (cokernel.π (C := W.Modules) (idealPowerMultiple (I.comap j) (n + 1)
      ((Scheme.Modules.restrictFunctor j).obj (stableImage P m k hmk n))).ι)).1 ?_
    rw [Stacks.Algebraization.idealPowerQuotientDesc_π,
      Stacks.Algebraization.idealPowerQuotientMap_π_assoc,
      Stacks.Algebraization.idealPowerQuotientMap_π_assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [stableImageRestrictMap, τ, Category.assoc]
  rw [stableImageQuotientRestrictMap, hdesc]
  infer_instance

include hF in
/-- **On `W`, the system `G` is `F`.** -/
theorem isIso_stableImageQuotientRestrictHom :
    IsIso (stableImageQuotientRestrictHom I P m k hm hk hmk j F hF ε hnm) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n =>
    isIso_stableImageQuotientRestrictMap I P m k hmk j F hF ε hnm n.unop

end Restriction

/-! ### The main statement -/

/-- **A coherent adic system cut out of an inverse system of quasi-coherent modules, from a
finite affine open cover.** Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf, `P`
an inverse system of quasi-coherent `𝒪_X`-modules and `T` a finite family of affine opens
covering `X`. Suppose that over every `T i` the inverse system of sections `Γ(T i, P_n)` is
Mittag-Leffler, the kernels of the projections out of its limit `M` are eventually inside every
`ℐ(T i)ⁿ⁺¹ M`, and the images of `M` in its terms are finite: the three conditions (a), (b), (c)
of the Mittag-Leffler criterion of Stacks 0EHH. Then there is an object `G` of `Coh(X, ℐ)` which
agrees with `P` on every open `W` on which `P` is itself a coherent adic system. -/
theorem exists_coherentAdicSystem_restrict_iso_of_affineCover [IsNoetherian X]
    {ι : Type u} [Finite ι] (T : ι → X.affineOpens) (hT : ⨆ i, (T i : X.Opens) = ⊤)
    (hML : ∀ i, IsMittagLefflerCategorical (P ⋙ affineSectionFunctor (T i)))
    (hker : ∀ i, ∀ n : ℕ, ∃ a : ℕ,
      LinearMap.ker (limit.π (P ⋙ affineSectionFunctor (T i)) (op a)).hom ≤
        I.ideal (T i) ^ (n + 1) •
          (⊤ : Submodule Γ(X, T i) (limit (P ⋙ affineSectionFunctor (T i)) :
            ModuleCat.{u} Γ(X, T i))))
    (hfin : ∀ i, ∀ j : ℕ, Module.Finite Γ(X, T i)
      (LinearMap.range (limit.π (P ⋙ affineSectionFunctor (T i)) (op j)).hom)) :
    ∃ G : CoherentAdicSystems I, ∀ {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
      (F : ℕᵒᵖ ⥤ W.Modules), IsCoherentAdicSystem (I.comap j) F →
      (P ⋙ Scheme.Modules.restrictFunctor j ≅ F) →
        Nonempty (G.obj ⋙ Scheme.Modules.restrictFunctor j ≅ F) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨m, k, hm, hk, hmk, hnm, hrange, hker⟩ := exists_uniform_indices_of_isMittagLeffler
    (fun i => Γ(X, (T i : X.Opens))) (fun i => I.ideal (T i))
    (fun i => P ⋙ affineSectionFunctor (T i)) hML hker
  let N : ∀ i n, Submodule Γ(X, T i) Γ(P.obj (op (m n)), T i) := fun i n =>
    LinearMap.range (limit.π (P ⋙ affineSectionFunctor (T i)) (op (m n))).hom
  have hN : ∀ i n, Set.range ((P.map (homOfLE (hmk n)).op).app (T i)) = N i n :=
    fun i n => Set.ext (SetLike.ext_iff.mp (hrange i n))
  have hsurj : ∀ i n,
      Submodule.map (appₗ (P.map (homOfLE (hm n.le_succ)).op) (T i)) (N i (n + 1)) = N i n := by
    intro i n
    have hw := map_limitπ_apply (P ⋙ affineSectionFunctor (T i)) (hm n.le_succ)
    apply le_antisymm
    · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (hw z).symm⟩
    · rintro _ ⟨z, rfl⟩
      exact ⟨_, ⟨z, rfl⟩, hw z⟩
  have hlift : ∀ i n, ∀ x ∈ N i (n + 1),
      (P.map (homOfLE (hm n.le_succ)).op).app (T i) x ∈ I.ideal (T i) ^ (n + 1) • N i n →
        x ∈ I.ideal (T i) ^ (n + 1) • N i (n + 1) :=
    fun i n x hx hy => mem_pow_smul_range_limitπ (P ⋙ affineSectionFunctor (T i)) (I.ideal (T i))
      (hm n.le_succ) (hker i n) hx hy
  refine ⟨⟨stableImageQuotientSystem I P m k hm hk hmk,
    isCoherentAdicSystem_stableImageQuotientSystem I P m k hm hk hmk T hT N hN
      (fun i n => hfin i (m n)) hsurj hlift⟩, fun j _ F hF ε => ?_⟩
  have := isIso_stableImageQuotientRestrictHom I P m k hm hk hmk j F hF ε hnm
  exact ⟨asIso (stableImageQuotientRestrictHom I P m k hm hk hmk j F hF ε hnm)⟩

/-- **A coherent adic system cut out of an inverse system of quasi-coherent modules.** Let `X` be
a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf and `P` an inverse system of
quasi-coherent `𝒪_X`-modules. Suppose that over every affine open `V` the inverse system of
sections `Γ(V, P_n)` is Mittag-Leffler, the limit topology on its limit is the `ℐ(V)`-adic one in
the sense of `IsStableAdicSystem`, and its terms are finite.
Then there is an object `G` of `Coh(X, ℐ)` which agrees with `P` on every open `W` on which `P`
is itself a coherent adic system. -/
theorem exists_coherentAdicSystem_restrict_iso [IsNoetherian X]
    (hP : ∀ V : X.affineOpens,
      IsStableAdicSystem (P ⋙ affineSectionFunctor V) (I.ideal V)) :
    ∃ G : CoherentAdicSystems I, ∀ {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
      (F : ℕᵒᵖ ⥤ W.Modules), IsCoherentAdicSystem (I.comap j) F →
      (P ⋙ Scheme.Modules.restrictFunctor j ≅ F) →
        Nonempty (G.obj ⋙ Scheme.Modules.restrictFunctor j ≅ F) := by
  classical
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by simpa using isCompact_univ (X := X))
  have : Finite s := hs.to_subtype
  refine exists_coherentAdicSystem_restrict_iso_of_affineCover I P (fun i : s => i.1)
    (by rw [hsU, iSup_subtype']) (fun i => (hP i.1).1) (fun i => (hP i.1).2.1) fun i j => ?_
  have : Module.Finite Γ(X, (i.1 : X.Opens)) ((P ⋙ affineSectionFunctor i.1).obj (op j)) :=
    (hP i.1).2.2 j
  have : IsNoetherianRing Γ(X, (i.1 : X.Opens)) := IsLocallyNoetherian.component_noetherian i.1
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)

end Construction

end Stacks.Coherent

end
