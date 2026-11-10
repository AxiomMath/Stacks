module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The long exact cohomology sequence of the Kummer sequence

Let `X` be a scheme on which the integer `n ≥ 1` is invertible. The Kummer sequence
`0 → μ_n → 𝐆_m →ⁿ 𝐆_m → 0` is a short exact sequence of abelian sheaves on `X_étale`
(Stacks 03PL, `Stacks.Kummer.kummerSequence_shortExact`), so étale cohomology gives the long
exact sequence

`⋯ → H^q(X, μ_n) → H^q(X, 𝐆_m) →ⁿ H^q(X, 𝐆_m) →δ H^{q+1}(X, μ_n) → H^{q+1}(X, 𝐆_m) → ⋯`.

In the additive notation of the coefficient category the `n`-th power map induces multiplication
by `n` on cohomology.

## Main definitions

* `Stacks.Kummer.kummerδ`: the coboundary `H^q(X, 𝐆_m) → H^{q+1}(X, μ_n)`.

## Main results

* `Stacks.Kummer.sheafH_map_powMap`: the `n`-th power map acts on `H^q(X, 𝐆_m)` as `n •`.
* `Stacks.Kummer.mem_range_sheafH_map_rootsOfUnityι_iff`,
  `Stacks.Kummer.mem_range_sheafH_map_powMap_iff`, `Stacks.Kummer.mem_range_kummerδ_iff`:
  exactness of the long exact sequence at its three kinds of terms.
* `Stacks.Kummer.surjective_sheafH_map_powMap_zero`: if every global unit is an `n`-th power,
  the `n`-th power map is surjective on `H⁰(X, 𝐆_m)`.
* `Stacks.Kummer.injective_sheafH_map_rootsOfUnityι_one`: then `H¹(X, μ_n) → H¹(X, 𝐆_m)` is
  injective, so `H¹(X, μ_n)` is the `n`-torsion of `H¹(X, 𝐆_m)`.
* `Stacks.Kummer.surjective_kummerδ_one`: if `H²(X, 𝐆_m) = 0` the coboundary
  `H¹(X, 𝐆_m) → H²(X, μ_n)` is surjective, so `H²(X, μ_n)` is `H¹(X, 𝐆_m) / n`.
* `Stacks.Kummer.subsingleton_sheafH_rootsOfUnitySheaf`: `H^{q+1}(X, μ_n) = 0` when
  `H^q(X, 𝐆_m)` and `H^{q+1}(X, 𝐆_m)` vanish.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe w u v

namespace Stacks.Kummer


section General

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {S : ShortComplex C}

/-- For a short exact sequence `S`, composing a class in `Ext Y S.X₂ q` with `S.g` and then with
the extension class of `S` gives zero. -/
lemma comp_g_comp_extClass (hS : S.ShortExact) {Y : C} {q : ℕ} (y : Ext.{w} Y S.X₂ q) :
    (y.comp (Ext.mk₀ S.g) (add_zero q)).comp hS.extClass rfl = 0 := by
  rw [Ext.comp_assoc _ _ _ (add_zero q) (zero_add 1) rfl, hS.comp_extClass, Ext.comp_zero]

/-- For a short exact sequence `S`, composing a class in `Ext Y S.X₃ q` with the extension class
of `S` and then with `S.f` gives zero. -/
lemma comp_extClass_comp_f (hS : S.ShortExact) {Y : C} {q : ℕ} (y : Ext.{w} Y S.X₃ q) :
    (y.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (q + 1)) = 0 := by
  rw [Ext.comp_assoc _ _ _ rfl (add_zero 1) (by lia), hS.extClass_comp, Ext.comp_zero]

end General

variable (X : Scheme.{u}) (n : ℕ)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The `n`-th power map induces multiplication by `n` on the étale cohomology of `𝐆_m`. -/
public theorem sheafH_map_powMap (q : ℕ) (x : Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) q) :
    Sheaf.H.map (powMap.{u, v} X n) q x = n • x := by
  change x.comp (Ext.mk₀ (n • 𝟙 _)) (add_zero q) = n • x
  induction n with
  | zero => simp
  | succ m ih => rw [succ_nsmul, Ext.mk₀_add, Ext.comp_add, ih, Ext.comp_mk₀_id, succ_nsmul]

/-- If every invertible global function on `X` is an `n`-th power, the `n`-th power map is
surjective on `H⁰(X, 𝐆_m)`, which is the group of global units. -/
public theorem surjective_sheafH_map_powMap_zero
    (hroot : ∀ a : (Γ(X, ⊤))ˣ, ∃ b, b ^ n = a) :
    Function.Surjective (Sheaf.H.map.{w} (powMap.{u, v} X n) 0) := by
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  let e := Sheaf.H.equiv₀.{w} (multiplicativeSheaf.{u, v} X) hT
  intro y
  obtain ⟨a, ha⟩ := ofUnit_surjective (e y)
  obtain ⟨b, rfl⟩ := hroot a
  refine ⟨e.symm (ofUnit b), e.injective ?_⟩
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply, ← ha]
  exact powMap_app_ofUnit.{u, v} X n (Scheme.Etale.mk (𝟙 X)) b

variable {n} (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤)))

/-- The Kummer coboundary `H^q(X, 𝐆_m) ⟶ H^{q+1}(X, μ_n)` of the long exact cohomology sequence
of the Kummer sequence. -/
public def kummerδ (q : ℕ) :
    Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) q →+
      Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) (q + 1) :=
  (kummerSequence_shortExact.{u, v} X hn0 hX).extClass.postcomp _ rfl

include hn0 hX in
/-- **Exactness at `H^q(X, 𝐆_m)`, on the right.** A class is killed by the `n`-th power map
exactly when it comes from `H^q(X, μ_n)`. -/
@[sga "4 IX 4.6" "Exactness at H^q(X", sga "7 XI 1.9" "partial"]
public theorem mem_range_sheafH_map_rootsOfUnityι_iff (q : ℕ)
    (x : Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) q) :
    x ∈ (Sheaf.H.map (rootsOfUnityι.{u, v} X n) q).range ↔
      Sheaf.H.map (powMap.{u, v} X n) q x = 0 := by
  have hS := kummerSequence_shortExact.{u, v} X hn0 hX
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Sheaf.H.map_comp_apply, rootsOfUnityι_comp_powMap, Sheaf.H.map_apply, Ext.mk₀_zero,
      Ext.comp_zero]
  · exact fun h => Ext.covariant_sequence_exact₂ _ hS x h

include hn0 hX in
/-- **Exactness at `H^q(X, 𝐆_m)`, on the left.** A class is in the image of the `n`-th power map
exactly when its Kummer coboundary vanishes. -/
public theorem mem_range_sheafH_map_powMap_iff (q : ℕ)
    (x : Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) q) :
    x ∈ (Sheaf.H.map (powMap.{u, v} X n) q).range ↔ kummerδ X hn0 hX q x = 0 := by
  have hS := kummerSequence_shortExact.{u, v} X hn0 hX
  constructor
  · rintro ⟨y, rfl⟩
    exact comp_g_comp_extClass hS y
  · exact fun h => Ext.covariant_sequence_exact₃ _ hS x rfl h

include hn0 hX in
/-- **Exactness at `H^{q+1}(X, μ_n)`.** A class maps to zero in `H^{q+1}(X, 𝐆_m)` exactly when
it is a Kummer coboundary. -/
public theorem mem_range_kummerδ_iff (q : ℕ)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) (q + 1)) :
    x ∈ (kummerδ X hn0 hX q).range ↔
      Sheaf.H.map (rootsOfUnityι.{u, v} X n) (q + 1) x = 0 := by
  have hS := kummerSequence_shortExact.{u, v} X hn0 hX
  constructor
  · rintro ⟨y, rfl⟩
    exact comp_extClass_comp_f hS y
  · exact fun h => Ext.covariant_sequence_exact₁ _ hS x h rfl

include hn0 hX in
/-- **`H¹(X, μ_n)` is the `n`-torsion of `H¹(X, 𝐆_m)`** when every global unit of `X` is an
`n`-th power in degree zero cohomology: the map `H¹(X, μ_n) ⟶ H¹(X, 𝐆_m)` is injective. -/
public theorem injective_sheafH_map_rootsOfUnityι_one
    (hsurj : Function.Surjective (Sheaf.H.map.{w} (powMap.{u, v} X n) 0)) :
    Function.Injective (Sheaf.H.map.{w} (rootsOfUnityι.{u, v} X n) 1) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := (mem_range_kummerδ_iff X hn0 hX 0 x).2 hx
  exact (mem_range_sheafH_map_powMap_iff X hn0 hX 0 y).1 (hsurj y)

include hn0 hX in
/-- The Kummer coboundary `H¹(X, 𝐆_m) ⟶ H²(X, μ_n)` is surjective when `H²(X, 𝐆_m) = 0`. -/
public theorem surjective_kummerδ_one
    (h2 : Subsingleton (Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 2)) :
    Function.Surjective (kummerδ X hn0 hX 1) := fun x =>
  (mem_range_kummerδ_iff X hn0 hX 1 x).2 (Subsingleton.elim _ _)

include hn0 hX in
/-- `H^{q+1}(X, μ_n) = 0` as soon as `H^q(X, 𝐆_m)` and `H^{q+1}(X, 𝐆_m)` vanish. -/
public theorem subsingleton_sheafH_rootsOfUnitySheaf (q : ℕ)
    (hq : Subsingleton (Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) q))
    (hq' : Subsingleton (Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) (q + 1))) :
    Subsingleton (Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) (q + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, rfl⟩ := (mem_range_kummerδ_iff X hn0 hX q x).2 (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero]

end Stacks.Kummer

end
