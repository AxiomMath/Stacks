module

public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Homology.DerivedCategory.UniformProInverse
import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Uniform inverses onto a system concentrated in degree zero

Let `φ : Z ⟶ W` be a morphism of inverse sequences in `D(𝒜)` whose target `W` is concentrated
in degree `0` and whose source `Z` has no cohomology above degree `0`, such that `φ` induces
isomorphisms on `H⁰`.  This file shows that `φ` has *uniform inverses* — inverses `W_m ⟶ Z_n`
for all `m ≥ n + c` with `c` independent of `n`, the notion of isomorphism of the strict
pro-category of [Stacks, Tag 0GA5] — as soon as

* the transitions of `Z` over a fixed number of steps kill every map out of an object without
  cohomology above some `e < 0`, and
* in each degree `e < d < 0` the transitions of `Z` over a fixed number of steps vanish on `H^d`.

This is the argument the source sketches for the system `A ⊗ᴸ_P P/Jⁿ`: its transitions factor
through a truncation (via [Stacks, Tag 0GA3]) and vanish on the finitely many remaining
cohomology modules (via [Stacks, Tag 0911]), so by [Stacks, Tag 08Q2] a fixed composite of
transitions factors through `τ_{≥ 0}`, which is the target system.

## Main results

* `DerivedCategory.exists_forall_mem_homologyFunctor_map_tr_eq_zero`: finitely many degrees of
  vanishing on cohomology hold with a common number of steps.
* `DerivedCategory.hasUniformInverses_of_isLE_zero`: **the criterion.**

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 08Q2](https://stacks.math.columbia.edu/tag/08Q2)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Opposite CategoryTheory.InverseSequence

namespace DerivedCategory

universe w v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

open TStructure

/-- Vanishing of a transition on `H^d` over `c` steps persists over more steps. -/
theorem homologyFunctor_map_tr_eq_zero_mono (Z : ℕᵒᵖ ⥤ DerivedCategory 𝒜) {d : ℤ} {c c' : ℕ}
    (hcc' : c ≤ c') (h : ∀ n : ℕ, (homologyFunctor 𝒜 d).map (tr Z (Nat.le_add_right n c)) = 0)
    (n : ℕ) : (homologyFunctor 𝒜 d).map (tr Z (Nat.le_add_right n c')) = 0 := by
  rw [← tr_comp Z (Nat.le_add_right n c) (by omega : n + c ≤ n + c'), Functor.map_comp, h,
    comp_zero]

/-- Finitely many degrees of vanishing on cohomology hold with a common number of steps. -/
theorem exists_forall_mem_homologyFunctor_map_tr_eq_zero (Z : ℕᵒᵖ ⥤ DerivedCategory 𝒜)
    (S : Finset ℤ) (h : ∀ d ∈ S, ∃ c : ℕ, ∀ n : ℕ,
      (homologyFunctor 𝒜 d).map (tr Z (Nat.le_add_right n c)) = 0) :
    ∃ c : ℕ, ∀ d ∈ S, ∀ n : ℕ, (homologyFunctor 𝒜 d).map (tr Z (Nat.le_add_right n c)) = 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨c, hc⟩ := ih (fun d hd => h d (Finset.mem_insert_of_mem hd))
    obtain ⟨c', hc'⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨max c c', fun d hd n => ?_⟩
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact homologyFunctor_map_tr_eq_zero_mono Z (le_max_right _ _) hc' n
    · exact homologyFunctor_map_tr_eq_zero_mono Z (le_max_left _ _) (hc d hd) n

/-- **Uniform inverses onto a system concentrated in degree zero.**  Let `φ : Z ⟶ W` be a
morphism of inverse sequences in `D(𝒜)` with `Z` in `D^{≤ 0}`, `W` concentrated in degree `0`
and `H⁰(φ)` invertible.  Suppose the transitions of `Z` over `c₀` steps kill every map out of
an object of `D^{≤ e}` for some `e < 0`, and that in every degree `e < d < 0` some fixed number
of steps of transitions of `Z` vanishes on `H^d`.  Then `φ` has uniform inverses. -/
theorem hasUniformInverses_of_isLE_zero {Z W : ℕᵒᵖ ⥤ DerivedCategory 𝒜} (φ : Z ⟶ W)
    (hZ : ∀ n, (Z.obj n).IsLE 0) (hWge : ∀ n, (W.obj n).IsGE 0) (hWle : ∀ n, (W.obj n).IsLE 0)
    (hφ : ∀ n, IsIso ((homologyFunctor 𝒜 0).map (φ.app n)))
    (e : ℤ) (he : e < 0)
    (htail : ∃ c₀ : ℕ, ∀ n m : ℕ, (h : n ≤ m) → n + c₀ ≤ m → ∀ (V : DerivedCategory 𝒜),
      V.IsLE e → ∀ g : V ⟶ Z.obj (op m), g ≫ tr Z h = 0)
    (hH : ∀ d : ℤ, e < d → d < 0 → ∃ c : ℕ, ∀ n : ℕ,
      (homologyFunctor 𝒜 d).map (tr Z (Nat.le_add_right n c)) = 0) :
    HasUniformInverses φ := by
  obtain ⟨c₀, hc₀⟩ := htail
  let Z' := Z ⋙ t.truncLT 0
  have hnat : ∀ {n m : ℕ} (h : n ≤ m),
      tr Z' h ≫ (t.truncLTι 0).app (Z.obj (op n)) =
        (t.truncLTι 0).app (Z.obj (op m)) ≫ tr Z h := fun h =>
    (t.truncLTι 0).naturality (tr Z h)
  have hZ' : ∀ n, 0 ≤ n → (Z'.obj (op n)).IsLE (-1) := fun n _ =>
    t.isLE_truncLT_obj _ _ _ (by omega)
  obtain ⟨C, hC⟩ := exists_forall_mem_homologyFunctor_map_tr_eq_zero Z (Finset.Ioo e 0)
    (fun d hd => hH d (Finset.mem_Ioo.1 hd).1 (Finset.mem_Ioo.1 hd).2)
  have hH' : ∀ d : ℤ, e < d → d ≤ -1 → ∀ n, 0 ≤ n →
      (homologyFunctor 𝒜 d).map (tr Z' (Nat.le_add_right n C)) = 0 := by
    intro d hd₁ hd₂ n _
    have : IsIso ((homologyFunctor 𝒜 d).map ((t.truncLTι 0).app (Z.obj (op n)))) :=
      isIso_homologyFunctor_map_truncLTι 0 d (by omega) _
    rw [← cancel_mono ((homologyFunctor 𝒜 d).map ((t.truncLTι 0).app (Z.obj (op n)))),
      zero_comp, ← Functor.map_comp, hnat, Functor.map_comp,
      hC d (Finset.mem_Ioo.2 ⟨hd₁, by omega⟩) n, comp_zero]
  have htail' : ∀ n, 0 ≤ n → ∀ (V : DerivedCategory 𝒜), V.IsLE e →
      ∀ g : V ⟶ Z'.obj (op (n + c₀)), g ≫ tr Z' (Nat.le_add_right n c₀) = 0 := by
    intro n _ V hV g
    have : t.IsLE V (0 - 1) := t.isLE_of_le V e (0 - 1) (by omega)
    refine t.to_truncLT_obj_ext ?_
    rw [Category.assoc, hnat, ← Category.assoc, zero_comp]
    exact hc₀ n (n + c₀) _ le_rfl V hV _
  have hzero := tr_eq_zero_of_homology Z' (-1) e 0 C c₀ (hZ' · ·) hH' htail'
  refine ⟨c₀ + (-1 - e).toNat * C, fun n m hm => ?_⟩
  have hnm : n ≤ m := by omega
  have hk : ((t.triangleLTGE 0).obj (Z.obj (op m))).mor₁ ≫ tr Z hnm = 0 := by
    show (t.truncLTι 0).app (Z.obj (op m)) ≫ tr Z hnm = 0
    rw [← hnat, hzero n m (Nat.zero_le _) hnm (by omega), zero_comp]
  obtain ⟨u, hu⟩ : ∃ u : (t.truncGE 0).obj (Z.obj (op m)) ⟶ Z.obj (op n),
      tr Z hnm = (t.truncGEπ 0).app (Z.obj (op m)) ≫ u :=
    Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished 0 (Z.obj (op m))) (tr Z hnm) hk
  have : (W.obj (op m)).IsGE 0 := hWge (op m)
  have : (W.obj (op n)).IsGE 0 := hWge (op n)
  have : (Z.obj (op m)).IsLE 0 := hZ (op m)
  let v := t.descTruncGE (φ.app (op m)) 0
  have hv : (t.truncGEπ 0).app (Z.obj (op m)) ≫ v = φ.app (op m) := t.π_descTruncGE _ 0
  have hviso : IsIso v := by
    rw [isIso_iff]
    intro d
    rcases lt_trichotomy d 0 with hd | rfl | hd
    · exact (isZero_of_isGE _ 0 d hd).isIso (isZero_of_isGE _ 0 d hd) _
    · have : IsIso ((homologyFunctor 𝒜 0).map ((t.truncGEπ 0).app (Z.obj (op m)))) :=
        isIso_homologyFunctor_map_truncGEπ 0 0 le_rfl _
      have h₂ := hφ (op m)
      rw [← hv, Functor.map_comp] at h₂
      exact IsIso.of_isIso_comp_left
        ((homologyFunctor 𝒜 0).map ((t.truncGEπ 0).app (Z.obj (op m))))
        ((homologyFunctor 𝒜 0).map v)
    · have : IsIso ((homologyFunctor 𝒜 d).map ((t.truncGEπ 0).app (Z.obj (op m)))) :=
        isIso_homologyFunctor_map_truncGEπ 0 d hd.le _
      have : (W.obj (op m)).IsLE 0 := hWle (op m)
      have hs : IsZero ((homologyFunctor 𝒜 d).obj ((t.truncGE 0).obj (Z.obj (op m)))) :=
        (isZero_of_isLE (Z.obj (op m)) 0 d hd).of_iso
          (asIso ((homologyFunctor 𝒜 d).map ((t.truncGEπ 0).app (Z.obj (op m))))).symm
      exact hs.isIso (isZero_of_isLE _ 0 d hd) _
  refine ⟨inv v ≫ u, hnm, ?_, ?_⟩
  · rw [← hv, Category.assoc, IsIso.hom_inv_id_assoc, hu]
  · have key : (t.truncGEπ 0).app (Z.obj (op m)) ≫ (v ≫ inv v ≫ u ≫ φ.app (op n)) =
        (t.truncGEπ 0).app (Z.obj (op m)) ≫ (v ≫ tr W hnm) := by
      rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ← hu, ← Category.assoc, hv]
      exact tr_naturality φ hnm
    rw [← cancel_epi v]
    simpa only [Category.assoc] using t.from_truncGE_obj_ext key

end DerivedCategory

end
