module

public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull.Endomorphisms
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull.PowerTorsionFiltration

/-!
# Chain conditions over a Noetherian local ring via the injective hull of the residue field

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and residue field `κ`, and let `E` be an
injective hull of `κ`.  Using the action of `End_R(E) ≃ R^∧` on Matlis duals `Hom_R(N, E)`, this
file shows that a torsion module whose Matlis dual is finite over `R^∧` is Artinian, that `E`
itself is Artinian, and the two chain conditions: over a Noetherian local ring the ascending chain
condition on a module is finite generation, and the descending chain condition is `𝔪`-power
torsion together with a finite-dimensional socle, equivalently a finite copresentation by copies
of `E`.

It was split from `StacksFrontier.RingTheory.Dualizing.ResidueFieldHull`, which re-exports it.

## Main definitions

* `Dualizing.HasFiniteSocle` — the socle `M[𝔪]` is finite-dimensional over `κ`.
* `Dualizing.matlisDualPostcompRingHom` and `Dualizing.matlisDualAdicCompletionModule` — the
  action of `End_R(E) ≃ R^∧` on a Matlis dual `Hom_R(N, E)` by postcomposition.

## Main results

* `Dualizing.isArtinian_of_finite_matlisDual` — a torsion module with Matlis dual finite over
  `R^∧` satisfies the descending chain condition.
* `Dualizing.isArtinian_of_isInjectiveHull_residueField` — `E` is an Artinian `R`-module.
* `Dualizing.isNoetherian_iff_module_finite`,
  `Dualizing.module_finite_iff_exists_finite_presentation`,
  `Dualizing.isArtinian_iff_powerTorsion_and_finiteSocle` and
  `Dualizing.powerTorsion_and_finiteSocle_iff_exists_finite_copresentation` — the chain
  conditions.

## Implementation notes

Tag 0EGL is proved as in the source, by embedding the lattice of submodules of `N` into the
lattice of `R^∧`-submodules of `Hom_R(N, E)` by `N' ↦ Hom_R(N / N', E)`; this is independent of
Tag 08Z8, which in turn is what makes Tag 08Z7 — and with it the backward direction of Tag 08Z8 —
available.

## References

* [Stacks Project, Tag 0EGL](https://stacks.math.columbia.edu/tag/0EGL)
* [Stacks Project, Tag 08Z7](https://stacks.math.columbia.edu/tag/08Z7)
* [Stacks Project, Tag 08Z8](https://stacks.math.columbia.edu/tag/08Z8)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Dualizing

section Socle

open IsLocalRing

/-- The socle of `M`, i.e. the submodule annihilated by the maximal ideal, is finite-dimensional
over the residue field. -/
public def HasFiniteSocle (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  let S := Submodule.torsionBySet R M (maximalIdeal R : Set R)
  let hS : Module.IsTorsionBySet R S (maximalIdeal R : Set R) :=
    Submodule.torsionBySet_isTorsionBySet _
  letI : Module (ResidueField R) S := hS.module
  Module.Finite (ResidueField R) S

end Socle

section MatlisDual

private lemma finiteSocle_of_finite
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    HasFiniteSocle R M := by
  unfold HasFiniteSocle
  let S := Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R : Set R)
  let hS : Module.IsTorsionBySet R S (IsLocalRing.maximalIdeal R : Set R) :=
    Submodule.torsionBySet_isTorsionBySet _
  let : Module (IsLocalRing.ResidueField R) S := hS.module
  let : IsScalarTower R (IsLocalRing.ResidueField R) S := hS.isScalarTower
  have : Module.Finite R S := inferInstance
  exact Module.Finite.of_restrictScalars_finite R _ _

private lemma exists_hom_ne_zero
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Type v) [AddCommGroup N] [Module R N]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (hN : IsIPowerTorsion R N (IsLocalRing.maximalIdeal R))
    (x : N) (hx : x ≠ 0) : ∃ g : N →ₗ[R] E, g x ≠ 0 := by
  let C : Submodule R N := R ∙ x
  have : Module.Finite R C := Module.Finite.span_singleton R x
  have hC : ∀ y : C, ∃ k : ℕ, ∀ r ∈ (IsLocalRing.maximalIdeal R ^ k : Ideal R),
      r • y = 0 := by
    intro y
    obtain ⟨k, _, hk⟩ := hN y.1
    exact ⟨k, fun r hr ↦ Subtype.ext (hk r hr)⟩
  have : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R)
      (Submodule.torsionBySet R C (IsLocalRing.maximalIdeal R)) :=
    finiteSocle_of_finite R C
  let n := Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
    (Submodule.torsionBySet R C (IsLocalRing.maximalIdeal R))
  obtain ⟨f, hf⟩ := exists_injective_to_pi_injectiveHull
    R C E i hi hC n rfl
  have hcx : (⟨x, Submodule.mem_span_singleton_self x⟩ : C) ≠ 0 :=
    fun h ↦ hx (congrArg Subtype.val h)
  have hfx : f (⟨x, Submodule.mem_span_singleton_self x⟩ : C) ≠ 0 :=
    fun h ↦ hcx (hf (h.trans (map_zero f).symm))
  obtain ⟨j, hj⟩ : ∃ j : Fin n,
      f (⟨x, Submodule.mem_span_singleton_self x⟩ : C) j ≠ 0 := by
    by_contra h
    apply hfx
    ext j
    by_contra hj
    exact h ⟨j, hj⟩
  let g : C →ₗ[R] E := LinearMap.proj j ∘ₗ f
  have hE : Module.Baer R E :=
    Module.Baer.of_injective (Module.injective_module_of_injective_object R E (inj := hi.1))
  obtain ⟨g', hg'⟩ := hE.extension_property C.subtype C.subtype_injective g
  refine ⟨g', ?_⟩
  have h := LinearMap.congr_fun hg' (⟨x, Submodule.mem_span_singleton_self x⟩ : C)
  exact fun hzero ↦ hj (by simpa [g] using h.symm.trans hzero)

/-- Endomorphisms of the target act on linear maps by postcomposition. -/
public def matlisDualPostcompRingHom (R : Type u) [CommRing R]
    (N : Type v) [AddCommGroup N] [Module R N]
    (E : Type u) [AddCommGroup E] [Module R E] :
    Module.End R E →+* Module.End R (N →ₗ[R] E) where
  toFun f :=
    { toFun := fun g ↦ f.comp g
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

/-- The canonical action of the completion of a Noetherian local ring on a Matlis dual, obtained
from its canonical identification with the endomorphism algebra of the injective hull. -/
@[instance_reducible]
public noncomputable def matlisDualAdicCompletionModule
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Type v) [AddCommGroup N] [Module R N]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    Module (AdicCompletion (IsLocalRing.maximalIdeal R) R) (N →ₗ[R] E) :=
  Module.compHom (N →ₗ[R] E)
    ((matlisDualPostcompRingHom R N E).comp
      (endAlgEquivAdicCompletion R E i hi).symm.toRingEquiv.toRingHom)

private lemma adic_smul_apply
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Type v) [AddCommGroup N] [Module R N]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (a : AdicCompletion (IsLocalRing.maximalIdeal R) R) (g : N →ₗ[R] E) (x : N) :
    (letI := matlisDualAdicCompletionModule R N E i hi; a • g) x =
      ((endAlgEquivAdicCompletion R E i hi).symm a) (g x) := by
  rfl

/-- A nonzero element of a maximal-ideal-power torsion module stays nonzero under some linear map
into an injective hull of the residue field, even after a prescribed submodule is killed. -/
private lemma exists_hom_eq_zero_on_ne_zero
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Type v) [AddCommGroup N] [Module R N]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (hN : IsIPowerTorsion R N (IsLocalRing.maximalIdeal R))
    (P : Submodule R N) (x : N) (hx : x ∉ P) :
    ∃ g : N →ₗ[R] E, (∀ y ∈ P, g y = 0) ∧ g x ≠ 0 := by
  have hQ : IsIPowerTorsion R (N ⧸ P) (IsLocalRing.maximalIdeal R) := by
    intro z
    obtain ⟨y, rfl⟩ := P.mkQ_surjective z
    obtain ⟨n, hn, hkill⟩ := hN y
    exact ⟨n, hn, fun a ha ↦ by
      rw [← map_smul, hkill a ha, map_zero]⟩
  obtain ⟨g, hg⟩ := exists_hom_ne_zero R (N ⧸ P) E i hi hQ (P.mkQ x)
    (fun h ↦ hx ((Submodule.Quotient.mk_eq_zero P).mp h))
  refine ⟨g ∘ₗ P.mkQ, fun y hy ↦ ?_, hg⟩
  have hzero : P.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hy
  rw [LinearMap.comp_apply, hzero, map_zero]

/-- **Stacks Project, Tag 0EGL.** A maximal-ideal-power torsion module whose Matlis dual is finite
over the completion satisfies the descending chain condition. -/
@[stacks 0EGL]
public theorem isArtinian_of_finite_matlisDual
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : Type v) [AddCommGroup N] [Module R N]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (hN : IsIPowerTorsion R N (IsLocalRing.maximalIdeal R))
    (hfinite : letI := matlisDualAdicCompletionModule R N E i hi
      Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal R) R) (N →ₗ[R] E)) :
    IsArtinian R N := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let := matlisDualAdicCompletionModule R N E i hi
  have : Module.Finite A (N →ₗ[R] E) := hfinite
  have hNoeth : IsNoetherian A (N →ₗ[R] E) :=
    isNoetherian_of_isNoetherianRing_of_finite A (N →ₗ[R] E)
  let ann : Submodule R N → Submodule A (N →ₗ[R] E) := fun P =>
    { carrier := {g | ∀ y ∈ P, g y = 0}
      zero_mem' := fun _ _ ↦ rfl
      add_mem' := fun hg hh y hy ↦ by
        rw [LinearMap.add_apply, hg y hy, hh y hy, add_zero]
      smul_mem' := fun a g hg y hy ↦ by
        rw [adic_smul_apply R N E i hi, hg y hy, map_zero] }
  have hle : ∀ P Q : Submodule R N, P ≤ Q ↔ ann Q ≤ ann P := by
    intro P Q
    refine ⟨fun h g hg y hy ↦ hg y (h hy), fun h x hx ↦ ?_⟩
    by_contra hxQ
    obtain ⟨g, hgQ, hgx⟩ := exists_hom_eq_zero_on_ne_zero R N E i hi hN Q x hxQ
    exact hgx (h hgQ x hx)
  have hlt : ∀ P Q : Submodule R N, P < Q ↔ ann Q < ann P := by
    intro P Q
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle P Q, hle Q P]
  exact RelEmbedding.wellFounded (r := (· < ·)) (s := (· > ·))
    { toFun := ann
      inj' := fun {P Q} h ↦
        le_antisymm ((hle P Q).2 (le_of_eq h.symm)) ((hle Q P).2 (le_of_eq h))
      map_rel_iff' := fun {P Q} ↦ (hlt P Q).symm }
    ((isNoetherian_iff' (R := A) (M := (N →ₗ[R] E))).mp hNoeth)

end MatlisDual

section ArtinianHull

/-- **Stacks Project, Tag 08Z7.** An injective hull of the residue field of a
Noetherian local ring is an Artinian module. -/
@[stacks 08Z7]
public lemma isArtinian_of_isInjectiveHull_residueField
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    IsArtinian R E := by
  let j : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ ModuleCat.of R E := i
  let : Mono j := show Mono i from inferInstance
  have hj : Module.IsInjectiveHull j := hi
  let := matlisDualAdicCompletionModule R E E j hj
  have htorsion : IsIPowerTorsion R E (IsLocalRing.maximalIdeal R) := by
    intro x
    obtain ⟨n, hn⟩ := exists_maximalIdealPowTorsion_mem R E j hj x
    simp only [maximalIdealPowTorsion,
      Submodule.mem_torsionBySet_iff] at hn
    exact ⟨n + 1, Nat.zero_lt_succ n, fun a ha ↦ hn ⟨a, ha⟩⟩
  have hfinite : Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (E →ₗ[R] E) := by
    apply Module.finite_def.mpr
    have hspan : (AdicCompletion (IsLocalRing.maximalIdeal R) R) ∙
        (LinearMap.id : E →ₗ[R] E) = ⊤ := by
      apply top_unique
      intro f _
      let a := (endAlgEquivAdicCompletion R E j hj) f
      have hf : a • (LinearMap.id : E →ₗ[R] E) = f := by
        ext x
        change ((endAlgEquivAdicCompletion R E j hj).symm a) x = f x
        simp [a]
      rw [← hf]
      exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _))
    rw [← hspan]
    exact Submodule.fg_span_singleton _
  exact isArtinian_of_finite_matlisDual R E E j hj htorsion hfinite

end ArtinianHull

section ChainConditions

open IsLocalRing

/-- **Stacks Project, Tag 08Z8, part (1).** Over a Noetherian ring, the ascending chain condition
on submodules is equivalent to finite generation. -/
@[stacks 08Z8 "part (1): ascending chain condition and finite generation"]
public lemma isNoetherian_iff_module_finite (R : Type u) [Ring R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsNoetherian R M ↔ Module.Finite R M :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isNoetherian_of_isNoetherianRing_of_finite R M⟩

/-- **Stacks Project, Tag 08Z8, part (1).** A finite module over a Noetherian ring admits a
presentation by two finite free modules. -/
@[stacks 08Z8 "part (1): finite presentation"]
public lemma module_finite_iff_exists_finite_presentation
    (R : Type u) [Ring R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module.Finite R M ↔
      ∃ (n m : ℕ) (f : (Fin n → R) →ₗ[R] M) (g : (Fin m → R) →ₗ[R] (Fin n → R)),
        Function.Surjective f ∧ Function.Exact g f := by
  constructor
  · intro _
    have := Module.finitePresentation_of_finite R M
    exact Module.FinitePresentation.exists_fin' R M
  · rintro ⟨n, m, f, g, hf, hg⟩
    exact Module.Finite.of_surjective f hf

private lemma artinian_power_torsion
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (h : IsArtinian R M) : IsIPowerTorsion R M (maximalIdeal R) := by
  intro x
  let N : ℕ → Submodule R M := fun n => (maximalIdeal R) ^ n • Submodule.span R {x}
  have ha : Antitone N := fun a b hab => Submodule.smul_le.mpr fun r hr y hy =>
    Submodule.smul_mem_smul (Ideal.pow_le_pow_right hab hr) hy
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes
    (⟨N, fun a b hab => ha hab⟩ : ℕ →o (Submodule R M)ᵒᵈ)
  have hn' : N n = N (n + 1) := hn (n + 1) (Nat.le_succ n)
  have heq : N n = (maximalIdeal R) • N n := by
    calc
      N n = N (n + 1) := hn'
      _ = (maximalIdeal R) • N n := by
        simp only [N, pow_succ, Submodule.mul_smul]
        rw [← Submodule.mul_smul, ← Submodule.mul_smul, mul_comm]
  have hfg : (N n).FG :=
    Submodule.FG.of_le (Submodule.fg_span_singleton x) Submodule.smul_le_right
  have hbot : N n = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (N n) hfg
      heq.le (maximalIdeal_le_jacobson ⊥)
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  intro a ha'
  have hmem : a • x ∈ N (n + 1) :=
    Submodule.smul_mem_smul ha' (Submodule.subset_span (by simp))
  rw [← hn', hbot] at hmem
  simpa using hmem

private lemma artinian_finite_socle
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (h : IsArtinian R M) : HasFiniteSocle R M := by
  let S := Submodule.torsionBySet R M (maximalIdeal R : Set R)
  let hS : Module.IsTorsionBySet R S (maximalIdeal R : Set R) :=
    Submodule.torsionBySet_isTorsionBySet _
  let : Module (ResidueField R) S := hS.module
  let : IsScalarTower R (ResidueField R) S := hS.isScalarTower
  let : IsArtinian R M := h
  exact ((IsArtinianRing.tfae (R := ResidueField R) (M := S)).out 3 1).mp
    (isArtinian_of_tower R (show IsArtinian R S from inferInstance))

/-- A power torsion module with finite socle embeds into a finite power of an injective hull of
the residue field. -/
private lemma exists_injective_to_pi_of_powerTorsion_finiteSocle
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (ResidueField R) ⟶ ModuleCat.of R E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (ht : IsIPowerTorsion R M (maximalIdeal R)) (hs : HasFiniteSocle R M) :
    ∃ (n : ℕ) (f : M →ₗ[R] (Fin n → E)), Function.Injective f := by
  have : Module.Finite (R ⧸ maximalIdeal R)
      (Submodule.torsionBySet R M (maximalIdeal R)) := hs
  let j : ModuleCat.of R (R ⧸ maximalIdeal R) ⟶ ModuleCat.of R E := i
  let : Mono j := show Mono i from inferInstance
  obtain ⟨f, hf⟩ := exists_injective_to_pi_injectiveHull R M E j hi (fun x => by
    obtain ⟨n, -, hn⟩ := ht x
    exact ⟨n, hn⟩) _ rfl
  exact ⟨_, f, hf⟩

private lemma artinian_of_power_torsion_finite_socle
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (ht : IsIPowerTorsion R M (maximalIdeal R)) (hs : HasFiniteSocle R M) :
    IsArtinian R M := by
  obtain ⟨E, i, _, hi⟩ :=
    Module.exists_isInjectiveHull R (ModuleCat.of R (ResidueField R))
  obtain ⟨n, f, hf⟩ := exists_injective_to_pi_of_powerTorsion_finiteSocle R M E i hi ht hs
  have : IsArtinian R E := isArtinian_of_isInjectiveHull_residueField R E i hi
  exact isArtinian_of_injective f hf

/-- **Stacks Project, Tag 08Z8, part (2).** A module has the descending chain condition exactly
when it is maximal-ideal-power torsion and has finite-dimensional socle. -/
@[stacks 08Z8 "part (2): descending chain condition and torsion"]
public lemma isArtinian_iff_powerTorsion_and_finiteSocle
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔
      (IsIPowerTorsion R M (maximalIdeal R) ∧ HasFiniteSocle R M) :=
  ⟨fun h => ⟨artinian_power_torsion R M h, artinian_finite_socle R M h⟩,
    fun ⟨ht, hs⟩ => artinian_of_power_torsion_finite_socle R M ht hs⟩

/-- **Stacks Project, Tag 08Z8, part (2).** The torsion and finite-socle condition is equivalent to
the existence of a copresentation by finite sums of an injective hull of the residue field. -/
@[stacks 08Z8 "part (2): finite copresentation"]
public lemma powerTorsion_and_finiteSocle_iff_exists_finite_copresentation
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : ResidueField R →ₗ[R] E) [Mono (ModuleCat.ofHom i)]
    (hi : Module.IsInjectiveHull (ModuleCat.ofHom i)) :
    (IsIPowerTorsion R M (maximalIdeal R) ∧ HasFiniteSocle R M) ↔
      ∃ (n m : ℕ) (f : M →ₗ[R] (Fin n → E))
        (g : (Fin n → E) →ₗ[R] (Fin m → E)),
        Function.Injective f ∧ Function.Exact f g := by
  have : IsArtinian R E :=
    isArtinian_of_isInjectiveHull_residueField R E (ModuleCat.ofHom i) hi
  constructor
  · rintro ⟨ht, hs⟩
    obtain ⟨n, f, hf⟩ := exists_injective_to_pi_of_powerTorsion_finiteSocle R M E
      (ModuleCat.ofHom i) hi ht hs
    let P := Fin n → E
    let Q := P ⧸ LinearMap.range f
    have hQ : IsArtinian R Q :=
      isArtinian_of_surjective P (LinearMap.range f).mkQ
        (Submodule.mkQ_surjective (LinearMap.range f))
    obtain ⟨hQt, hQs⟩ := (isArtinian_iff_powerTorsion_and_finiteSocle R Q).mp hQ
    obtain ⟨m, j, hj⟩ := exists_injective_to_pi_of_powerTorsion_finiteSocle R Q E
      (ModuleCat.ofHom i) hi hQt hQs
    let g : P →ₗ[R] (Fin m → E) := j.comp (LinearMap.range f).mkQ
    refine ⟨n, m, f, g, hf, ?_⟩
    rw [LinearMap.exact_iff]
    simp only [LinearMap.ker_eq_bot.mpr hj, LinearMap.ker_comp_of_ker_eq_bot, g]
    exact Submodule.ker_mkQ (p := LinearMap.range f)
  · rintro ⟨n, m, f, g, hf, hg⟩
    exact (isArtinian_iff_powerTorsion_and_finiteSocle R M).mp
      (isArtinian_of_injective f hf)

end ChainConditions

end Dualizing
