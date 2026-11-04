module

public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.BasicOpenLocalization
import all StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.BasicOpenLocalization

/-!
# Pushforward of quasi-coherent modules: quasi-compact opens and the pushforward

Part 4 of the proof of `AlgebraicGeometry.pushforward_isQuasicoherent`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_res_eq_zero_of_isCompact` and
  `AlgebraicGeometry.Scheme.Modules.exists_res_eq_pow_smul_of_isCompact`: the torsion and
  surjectivity halves of section localization over a quasi-compact open.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen_of_isCompact`: over a
  quasi-compact, quasi-separated open `W`, the section restriction `Γ(M, W) → Γ(M, D(g))` is a
  localization at `powers g`.
* `AlgebraicGeometry.pushforward_isQuasicoherent` states that pushforward along a
  quasi-compact and quasi-separated morphism preserves quasi-coherence.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u


namespace AlgebraicGeometry

open CategoryTheory Limits

section BasicOpenPresentationDescent

open CategoryTheory Limits TopologicalSpace Topology

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- Restriction maps of the underlying abelian presheaf of a sheaf of modules compose:
restricting `A → B → C` equals the direct restriction `A → C`.

Definitionally `TopCat.Presheaf.restrict_restrict`, restated in the explicit
`F.map (homOfLE _).op` spelling the rewrites below need: Mathlib states it through
`restrictOpen`, so its left-hand side is `restrictOpen`-headed and neither `rw` nor `simp only`
finds an occurrence of it in a goal written with `map`. -/
private lemma res_res (M : X.Modules) {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
    (hCA : C ≤ A) (x : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op x)
      = M.presheaf.map (homOfLE hCA).op x :=
  TopCat.Presheaf.restrict_restrict hCB hBA x

/-- Structure-sheaf version of `res_res`: `TopCat.Presheaf.restrict_restrict` for `X.presheaf`,
in the explicit `map` spelling the rewrites below need. -/
private lemma resRing_res {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B)
    (hCA : C ≤ A) (g : Γ(X, A)) :
    X.presheaf.map (homOfLE hCB).op (X.presheaf.map (homOfLE hBA).op g)
      = X.presheaf.map (homOfLE hCA).op g :=
  TopCat.Presheaf.restrict_restrict hCB hBA g

/-- A section of a sheaf of modules over an open contained in `⊥` vanishes (separation over
the empty cover). -/
private lemma section_eq_zero_of_le_bot (M : X.Modules) {V : X.Opens} (hV : V ≤ ⊥)
    (x : Γ(M, V)) : x = 0 :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : PEmpty.{u + 1} => i.elim) V (fun i => i.elim) (hV.trans bot_le) x 0
    (fun i => i.elim)

/-- Two sections of a sheaf of modules agree if they agree on two opens covering their domain. -/
private lemma section_eq_of_res_eq_sup (M : X.Modules) {A B C : X.Opens} (hA : A ≤ C)
    (hB : B ≤ C) (hC : C ≤ A ⊔ B) {s t : Γ(M, C)}
    (hsA : M.presheaf.map (homOfLE hA).op s = M.presheaf.map (homOfLE hA).op t)
    (hsB : M.presheaf.map (homOfLE hB).op s = M.presheaf.map (homOfLE hB).op t) : s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun b : Bool => cond b A B) C (fun b => homOfLE (by cases b; exacts [hB, hA]))
    (hC.trans (sup_le (le_iSup (fun b : Bool => cond b A B) true)
      (le_iSup (fun b : Bool => cond b A B) false))) s t ?_
  intro b
  cases b
  exacts [hsB, hsA]

/-- **Torsion half of qcqs section localization** (Stacks 01P0-style, `exists_of_eq` engine).
For a quasi-coherent sheaf of modules `M` on a scheme `X`, a section `g` of the structure sheaf
over an open `W`, and a *quasi-compact* open `U ≤ W`, any section `x ∈ Γ(M, U)` that restricts
to zero on `U ⊓ D(g)` is killed by a power of `g|_U`. Induction on the compact open `U`
(`compact_open_induction_on`): the affine case is the the open-immersion case keystone
`isLocalizedModule_basicOpen`, and the step glues by sheaf separation over the two-element
cover `{S, V}`.  (Mathlib has no qcqs section-localization). -/
public theorem exists_pow_smul_res_eq_zero_of_isCompact
    (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens} (g : Γ(X, W))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∀ (hUW : U ≤ W) (x : Γ(M, U)),
      M.presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op x = 0 →
      ∃ n : ℕ, X.presheaf.map (homOfLE hUW).op g ^ n • x = 0 := by
  refine compact_open_induction_on (P := fun U => ∀ (hUW : U ≤ W) (x : Γ(M, U)),
      M.presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op x = 0 →
      ∃ n : ℕ, X.presheaf.map (homOfLE hUW).op g ^ n • x = 0) U hU ?_ ?_
  · intro _ x _
    exact ⟨0, by rw [pow_zero, one_smul]; exact section_eq_zero_of_le_bot M le_rfl x⟩
  · intro S hS V IH hUW x hx
    have hSW : S ≤ W := le_sup_left.trans hUW
    have hVW : V.1 ≤ W := le_sup_right.trans hUW
    set gV : Γ(X, V.1) := X.presheaf.map (homOfLE hVW).op g with hgV
    have hB1eq : X.basicOpen gV = V.1 ⊓ X.basicOpen g := X.basicOpen_res g (homOfLE hVW).op
    set xS : Γ(M, S) := M.presheaf.map (homOfLE (le_sup_left : S ≤ S ⊔ V.1)).op x with hxS
    set xV : Γ(M, V.1) := M.presheaf.map (homOfLE (le_sup_right : V.1 ≤ S ⊔ V.1)).op x
      with hxV
    -- the restriction of `xS` to `S ⊓ D(g)` vanishes
    have hxS0 : M.presheaf.map (homOfLE (inf_le_left : S ⊓ X.basicOpen g ≤ S)).op xS = 0 := by
      have h1 := res_res M (le_sup_left : S ≤ S ⊔ V.1)
        (inf_le_left : S ⊓ X.basicOpen g ≤ S) (inf_le_left.trans le_sup_left) x
      have h2 := res_res M (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)
        (inf_le_inf le_sup_left le_rfl : S ⊓ X.basicOpen g ≤ (S ⊔ V.1) ⊓ X.basicOpen g)
        (inf_le_left.trans le_sup_left) x
      rw [hxS, h1, ← h2, hx, map_zero]
    obtain ⟨n₁, hn₁⟩ := IH hSW xS hxS0
    -- affine keystone on `V`
    let : Module Γ(X, V.1) Γ(M, X.basicOpen gV) :=
      Module.compHom _ (algebraMap Γ(X, V.1) Γ(X, X.basicOpen gV))
    have : IsScalarTower Γ(X, V.1) Γ(X, X.basicOpen gV) Γ(M, X.basicOpen gV) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    have := isLocalizedModule_basicOpen M V.2 gV
    have hB1A : X.basicOpen gV ≤ (S ⊔ V.1) ⊓ X.basicOpen g :=
      hB1eq.trans_le (inf_le_inf le_sup_right le_rfl)
    have hxV0 : restrictBasicOpenₗ M gV xV = 0 := by
      have h1 := res_res M (le_sup_right : V.1 ≤ S ⊔ V.1)
        (X.basicOpen_le gV) ((X.basicOpen_le gV).trans le_sup_right) x
      have h2 := res_res M (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)
        hB1A ((X.basicOpen_le gV).trans le_sup_right) x
      show M.presheaf.map (homOfLE (X.basicOpen_le gV)).op xV = 0
      rw [hxV, h1, ← h2, hx, map_zero]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers gV) (f := restrictBasicOpenₗ M gV)
      (x₁ := xV) (x₂ := 0) (by rw [hxV0, map_zero])
    have hn₂ : gV ^ c.2.choose = (c : Γ(X, V.1)) := c.2.choose_spec
    have hcV : gV ^ c.2.choose • xV = 0 := by
      rw [hn₂]
      rwa [smul_zero] at hc
    set n₂ := c.2.choose with hn₂def
    -- combine over the two-element cover
    refine ⟨max n₁ n₂, ?_⟩
    refine section_eq_of_res_eq_sup M (le_sup_left : S ≤ S ⊔ V.1) le_sup_right le_rfl ?_ ?_
    · -- on S
      rw [map_zero, map_smul, map_pow, resRing_res hUW le_sup_left hSW g, ← hxS,
        ← Nat.sub_add_cancel (le_max_left n₁ n₂), pow_add, mul_smul, hn₁, smul_zero]
    · -- on V
      rw [map_zero, map_smul, map_pow, resRing_res hUW le_sup_right hVW g, ← hgV,
        ← hxV, ← Nat.sub_add_cancel (le_max_right n₁ n₂), pow_add, mul_smul, hcV, smul_zero]

/-- **Surjectivity half of qcqs section localization** (Stacks 01P0-style, `surj` engine).
For a quasi-coherent `M` on `X`, `g ∈ Γ(X, W)`, and a quasi-compact open `U ≤ W` inside the
quasi-separated open `W`, every section `y ∈ Γ(M, U ⊓ D(g))` is, after multiplication by a
power of `g`, the restriction of a section over `U`. Induction on the compact open `U`: the
affine case is the the open-immersion case keystone's `surj`, and the step glues the two normalized
candidate
sections over `{S, V}` after killing their difference on the quasi-compact overlap `S ⊓ V`
with the torsion half. -/
public theorem exists_res_eq_pow_smul_of_isCompact
    (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens} (g : Γ(X, W))
    (hsep : IsQuasiSeparated (W : Set X))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∀ (hUW : U ≤ W) (y : Γ(M, U ⊓ X.basicOpen g)),
      ∃ (x : Γ(M, U)) (n : ℕ),
        M.presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op x
          = X.presheaf.map (homOfLE ((inf_le_left : U ⊓ X.basicOpen g ≤ U).trans hUW)).op g ^ n
            • y := by
  refine compact_open_induction_on (P := fun U => ∀ (hUW : U ≤ W)
      (y : Γ(M, U ⊓ X.basicOpen g)),
      ∃ (x : Γ(M, U)) (n : ℕ),
        M.presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op x
          = X.presheaf.map (homOfLE ((inf_le_left : U ⊓ X.basicOpen g ≤ U).trans hUW)).op g ^ n
            • y) U hU ?_ ?_
  · intro _ y
    refine ⟨0, 0, ?_⟩
    rw [map_zero, pow_zero, one_smul]
    exact (section_eq_zero_of_le_bot M inf_le_left y).symm
  · intro S hS V IH hUW y
    have hSW : S ≤ W := le_sup_left.trans hUW
    have hVW : V.1 ≤ W := le_sup_right.trans hUW
    set gV : Γ(X, V.1) := X.presheaf.map (homOfLE hVW).op g with hgV
    have hB1eq : X.basicOpen gV = V.1 ⊓ X.basicOpen g := X.basicOpen_res g (homOfLE hVW).op
    have hB1W : X.basicOpen gV ≤ W := (X.basicOpen_le gV).trans hVW
    have hB1A : X.basicOpen gV ≤ (S ⊔ V.1) ⊓ X.basicOpen g :=
      hB1eq.trans_le (inf_le_inf le_sup_right le_rfl)
    -- S side: the induction hypothesis
    set yS : Γ(M, S ⊓ X.basicOpen g) :=
      M.presheaf.map (homOfLE (inf_le_inf le_sup_left le_rfl :
        S ⊓ X.basicOpen g ≤ (S ⊔ V.1) ⊓ X.basicOpen g)).op y with hyS
    obtain ⟨xS, n₁, hn₁⟩ := IH hSW yS
    -- V side: the affine keystone's surjectivity
    let : Module Γ(X, V.1) Γ(M, X.basicOpen gV) :=
      Module.compHom _ (algebraMap Γ(X, V.1) Γ(X, X.basicOpen gV))
    have : IsScalarTower Γ(X, V.1) Γ(X, X.basicOpen gV) Γ(M, X.basicOpen gV) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    have := isLocalizedModule_basicOpen M V.2 gV
    set yV : Γ(M, X.basicOpen gV) := M.presheaf.map (homOfLE hB1A).op y with hyV
    obtain ⟨⟨xV, c⟩, hc⟩ := IsLocalizedModule.surj (S := Submonoid.powers gV)
      (f := restrictBasicOpenₗ M gV) yV
    have hn₂ : gV ^ c.2.choose = (c : Γ(X, V.1)) := c.2.choose_spec
    set n₂ := c.2.choose with hn₂def
    -- the compHom action unfolds to the restricted scalar acting through the native action
    have hc' : X.presheaf.map (homOfLE (X.basicOpen_le gV)).op (c : Γ(X, V.1)) • yV
        = M.presheaf.map (homOfLE (X.basicOpen_le gV)).op xV := hc
    have hres : X.presheaf.map (homOfLE (X.basicOpen_le gV)).op gV
        = X.presheaf.map (homOfLE hB1W).op g :=
      (congrArg (X.presheaf.map (homOfLE (X.basicOpen_le gV)).op) hgV).trans
        (resRing_res hVW (X.basicOpen_le gV) hB1W g)
    have hcV : X.presheaf.map (homOfLE hB1W).op g ^ n₂ • yV
        = M.presheaf.map (homOfLE (X.basicOpen_le gV)).op xV := by
      rw [← hc', ← hn₂, map_pow, hres]
    -- normalize both candidates to the common exponent `n = max n₁ n₂`
    set n := max n₁ n₂ with hn
    set xS' : Γ(M, S) := X.presheaf.map (homOfLE hSW).op g ^ (n - n₁) • xS with hxS'
    set xV' : Γ(M, V.1) := gV ^ (n - n₂) • xV with hxV'
    have hS' : M.presheaf.map (homOfLE (inf_le_left : S ⊓ X.basicOpen g ≤ S)).op xS'
        = X.presheaf.map (homOfLE ((inf_le_left : S ⊓ X.basicOpen g ≤ S).trans hSW)).op g ^ n
          • yS := by
      rw [hxS', map_smul, map_pow,
        resRing_res hSW (inf_le_left : S ⊓ X.basicOpen g ≤ S)
          ((inf_le_left : S ⊓ X.basicOpen g ≤ S).trans hSW) g,
        hn₁, ← mul_smul, ← pow_add, Nat.sub_add_cancel (le_max_left n₁ n₂)]
    have hV' : M.presheaf.map (homOfLE (X.basicOpen_le gV)).op xV'
        = X.presheaf.map (homOfLE hB1W).op g ^ n • yV := by
      rw [hxV', map_smul, map_pow, hres, ← hcV, ← mul_smul, ← pow_add,
        Nat.sub_add_cancel (le_max_right n₁ n₂)]
    clear_value xS' xV'
    -- the overlap `O = S ⊓ V` is quasi-compact inside the quasi-separated `W`
    have hO : IsCompact ((S ⊓ V.1 : X.Opens) : Set X) := by
      rw [TopologicalSpace.Opens.coe_inf]
      exact hsep (S : Set X) (V.1 : Set X) (fun a ha => hSW ha) S.isOpen hS
        (fun a ha => hVW ha) V.1.isOpen V.2.isCompact
    have hOW : S ⊓ V.1 ≤ W := inf_le_left.trans hSW
    -- the difference of the two normalized candidates dies on `O ⊓ D(g)` …
    set δ : Γ(M, S ⊓ V.1) :=
      M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op xS'
        - M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op xV' with hδ
    have hODB1 : (S ⊓ V.1) ⊓ X.basicOpen g ≤ X.basicOpen gV :=
      (inf_le_inf inf_le_right le_rfl).trans hB1eq.ge
    have hδ0 : M.presheaf.map
        (homOfLE (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)).op δ = 0 := by
      rw [hδ, map_sub]
      have eS : M.presheaf.map
          (homOfLE (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)).op
            (M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op xS')
          = X.presheaf.map (homOfLE ((inf_le_left.trans hOW) :
              (S ⊓ V.1) ⊓ X.basicOpen g ≤ W)).op g ^ n
            • M.presheaf.map (homOfLE ((inf_le_inf inf_le_left le_rfl).trans
                (inf_le_inf le_sup_left le_rfl)) :
                (S ⊓ V.1) ⊓ X.basicOpen g ⟶ (S ⊔ V.1) ⊓ X.basicOpen g).op y := by
        rw [res_res M (inf_le_left : S ⊓ V.1 ≤ S)
          (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)
          ((inf_le_inf inf_le_left le_rfl).trans inf_le_left), ← res_res M
          (inf_le_left : S ⊓ X.basicOpen g ≤ S)
          (inf_le_inf inf_le_left le_rfl :
            (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ X.basicOpen g)
          ((inf_le_inf inf_le_left le_rfl).trans inf_le_left), hS', map_smul, map_pow,
          resRing_res (inf_le_left.trans hSW) (inf_le_inf inf_le_left le_rfl)
            (inf_le_left.trans hOW) g, hyS, res_res M _ _ ((inf_le_inf inf_le_left le_rfl).trans
              (inf_le_inf le_sup_left le_rfl))]
      have eV : M.presheaf.map
          (homOfLE (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)).op
            (M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op xV')
          = X.presheaf.map (homOfLE ((inf_le_left.trans hOW) :
              (S ⊓ V.1) ⊓ X.basicOpen g ≤ W)).op g ^ n
            • M.presheaf.map (homOfLE ((inf_le_inf inf_le_left le_rfl).trans
                (inf_le_inf le_sup_left le_rfl)) :
                (S ⊓ V.1) ⊓ X.basicOpen g ⟶ (S ⊔ V.1) ⊓ X.basicOpen g).op y := by
        rw [res_res M (inf_le_right : S ⊓ V.1 ≤ V.1)
          (inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1)
          ((inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1).trans inf_le_right), ← res_res M
          (X.basicOpen_le gV) hODB1
          ((inf_le_left : (S ⊓ V.1) ⊓ X.basicOpen g ≤ S ⊓ V.1).trans inf_le_right), hV',
          map_smul, map_pow,
          resRing_res hB1W hODB1 (inf_le_left.trans hOW) g, hyV,
          res_res M hB1A hODB1 ((inf_le_inf inf_le_left le_rfl).trans
            (inf_le_inf le_sup_left le_rfl))]
      rw [eS, eV, sub_self]
    -- … so a power of `g` equalizes them on the overlap (torsion half)
    obtain ⟨m, hm⟩ := exists_pow_smul_res_eq_zero_of_isCompact M g (S ⊓ V.1) hO hOW δ hδ0
    have hglue : M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op
          (X.presheaf.map (homOfLE hSW).op g ^ m • xS')
        = M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op
          (gV ^ m • xV') := by
      have h1 : X.presheaf.map (homOfLE hOW).op g ^ m
            • M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op xS'
          - X.presheaf.map (homOfLE hOW).op g ^ m
            • M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op xV' = 0 := by
        rwa [← smul_sub, ← hδ]
      have h2 := sub_eq_zero.mp h1
      have hL : M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op
            (X.presheaf.map (homOfLE hSW).op g ^ m • xS')
          = X.presheaf.map (homOfLE hOW).op g ^ m
            • M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op xS' := by
        rw [map_smul, map_pow, resRing_res hSW (inf_le_left : S ⊓ V.1 ≤ S) hOW g]
      have hR : M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op
            (gV ^ m • xV')
          = X.presheaf.map (homOfLE hOW).op g ^ m
            • M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op xV' := by
        rw [map_smul, map_pow,
          (congrArg (X.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op) hgV).trans
            (resRing_res hVW (inf_le_right : S ⊓ V.1 ≤ V.1) hOW g)]
      rw [hL, hR]
      exact h2
    -- compatibility of the two candidates on the overlaps
    have hcompat : TopCat.Presheaf.IsCompatible M.presheaf
        (fun b : Bool => cond b S V.1)
        (fun b => Bool.rec (motive := fun b => Γ(M, cond b S V.1))
          (gV ^ m • xV') (X.presheaf.map (homOfLE hSW).op g ^ m • xS') b) := by
      intro i j
      cases i <;> cases j
      · exact congrArg (fun (h : V.1 ⊓ V.1 ⟶ V.1) => M.presheaf.map h.op (gV ^ m • xV'))
          (Subsingleton.elim _ _)
      · -- `V` against `S`: transport `hglue` along `V ⊓ S ≤ S ⊓ V`
        show M.presheaf.map (homOfLE (inf_le_left : V.1 ⊓ S ≤ V.1)).op (gV ^ m • xV')
          = M.presheaf.map (homOfLE (inf_le_right : V.1 ⊓ S ≤ S)).op
              (X.presheaf.map (homOfLE hSW).op g ^ m • xS')
        rw [← res_res M (inf_le_right : S ⊓ V.1 ≤ V.1)
            (le_inf inf_le_right inf_le_left : V.1 ⊓ S ≤ S ⊓ V.1) inf_le_left,
          ← res_res M (inf_le_left : S ⊓ V.1 ≤ S)
            (le_inf inf_le_right inf_le_left : V.1 ⊓ S ≤ S ⊓ V.1) inf_le_right, hglue]
      · -- `S` against `V`: `hglue`
        show M.presheaf.map (homOfLE (inf_le_left : S ⊓ V.1 ≤ S)).op
              (X.presheaf.map (homOfLE hSW).op g ^ m • xS')
          = M.presheaf.map (homOfLE (inf_le_right : S ⊓ V.1 ≤ V.1)).op (gV ^ m • xV')
        exact hglue
      · exact congrArg (fun (h : S ⊓ S ⟶ S) => M.presheaf.map h.op
            (X.presheaf.map (homOfLE hSW).op g ^ m • xS'))
          (Subsingleton.elim _ _)
    -- glue the two candidates over the cover `{S, V}` of `S ⊔ V`
    obtain ⟨x', hx', -⟩ := TopCat.Sheaf.existsUnique_gluing'
      (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun b : Bool => cond b S V.1) (S ⊔ V.1)
      (fun b => homOfLE (show cond b S V.1 ≤ S ⊔ V.1 by
        cases b
        · exact le_sup_right
        · exact le_sup_left))
      (sup_le (le_iSup (fun b : Bool => cond b S V.1) true)
        (le_iSup (fun b : Bool => cond b S V.1) false))
      (fun b => Bool.rec (motive := fun b => Γ(M, cond b S V.1))
        (gV ^ m • xV') (X.presheaf.map (homOfLE hSW).op g ^ m • xS') b) hcompat
    -- the glued section is the required witness at exponent `n + m`
    refine ⟨x', n + m, ?_⟩
    have hxS'' := hx' true
    have hxV'' := hx' false
    refine section_eq_of_res_eq_sup M
      (inf_le_inf le_sup_left le_rfl : S ⊓ X.basicOpen g ≤ (S ⊔ V.1) ⊓ X.basicOpen g) hB1A
      (by rw [hB1eq, inf_sup_right]) ?_ ?_
    · -- on `S ⊓ D(g)`
      show M.presheaf.map (homOfLE (inf_le_inf le_sup_left le_rfl :
            S ⊓ X.basicOpen g ≤ (S ⊔ V.1) ⊓ X.basicOpen g)).op
          (M.presheaf.map (homOfLE (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)).op x')
        = M.presheaf.map (homOfLE (inf_le_inf le_sup_left le_rfl)).op
          (X.presheaf.map (homOfLE ((inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1).trans
            hUW)).op g ^ (n + m) • y)
      rw [res_res M (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)
          (inf_le_inf le_sup_left le_rfl) (inf_le_left.trans le_sup_left),
        ← res_res M (le_sup_left : S ≤ S ⊔ V.1)
          (inf_le_left : S ⊓ X.basicOpen g ≤ S) (inf_le_left.trans le_sup_left)]
      rw [show M.presheaf.map (homOfLE (le_sup_left : S ≤ S ⊔ V.1)).op x'
        = X.presheaf.map (homOfLE hSW).op g ^ m • xS' from hxS'']
      rw [map_smul, map_pow,
        resRing_res hSW (inf_le_left : S ⊓ X.basicOpen g ≤ S)
          ((inf_le_left : S ⊓ X.basicOpen g ≤ S).trans hSW) g,
        hS', ← mul_smul, ← pow_add, map_smul, map_pow,
        resRing_res ((inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1).trans hUW)
          (inf_le_inf le_sup_left le_rfl)
          ((inf_le_left : S ⊓ X.basicOpen g ≤ S).trans hSW) g, ← hyS, Nat.add_comm m n]
    · -- on `D(g|_V)`
      show M.presheaf.map (homOfLE hB1A).op
          (M.presheaf.map (homOfLE (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1)).op x')
        = M.presheaf.map (homOfLE hB1A).op
          (X.presheaf.map (homOfLE ((inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1).trans
            hUW)).op g ^ (n + m) • y)
      rw [res_res M (inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1) hB1A
          ((X.basicOpen_le gV).trans le_sup_right),
        ← res_res M (le_sup_right : V.1 ≤ S ⊔ V.1) (X.basicOpen_le gV)
          ((X.basicOpen_le gV).trans le_sup_right)]
      rw [show M.presheaf.map (homOfLE (le_sup_right : V.1 ≤ S ⊔ V.1)).op x'
        = gV ^ m • xV' from hxV'']
      rw [map_smul, map_pow, hres, hV', ← mul_smul, ← pow_add, map_smul, map_pow,
        resRing_res ((inf_le_left : (S ⊔ V.1) ⊓ X.basicOpen g ≤ S ⊔ V.1).trans hUW) hB1A
          hB1W g, ← hyV, Nat.add_comm m n]

/-- The identity restriction acts as the identity on sections. -/
private lemma res_self (M : X.Modules) {A : X.Opens} (x : Γ(M, A)) :
    M.presheaf.map (homOfLE (le_rfl : A ≤ A)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_rfl : A ≤ A)) (𝟙 A), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Structure-sheaf version of `res_self`. -/
private lemma resRing_self {A : X.Opens} (g : Γ(X, A)) :
    X.presheaf.map (homOfLE (le_rfl : A ≤ A)).op g = g := by
  rw [Subsingleton.elim (homOfLE (le_rfl : A ≤ A)) (𝟙 A), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- If `r` maps to a unit of `S`, it acts invertibly on any module in a scalar tower
`R → S → N`. Pure algebra helper for the `map_units` field. -/
private lemma isUnit_algebraMap_end_of_isUnit_algebraMap
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {r : R} (h : IsUnit (algebraMap R S r)) :
    IsUnit (algebraMap R (Module.End R N) r) := by
  obtain ⟨u, hu⟩ := h
  have hcomm : ∀ (c : R) (m : N), (↑u⁻¹ : S) • c • m = c • (↑u⁻¹ : S) • m := by
    intro c m
    rw [← algebraMap_smul S c ((↑u⁻¹ : S) • m), ← mul_smul, mul_comm, mul_smul,
      algebraMap_smul S c m]
  refine isUnit_iff_exists.mpr
    ⟨{ toFun := fun m => (↑u⁻¹ : S) • m,
       map_add' := fun a b => smul_add _ a b,
       map_smul' := fun c m => by simpa using hcomm c m }, ?_, ?_⟩
  · ext m
    show algebraMap R (Module.End R N) r ((↑u⁻¹ : S) • m) = m
    rw [Module.algebraMap_end_apply, ← algebraMap_smul S r, ← hu, ← mul_smul,
      Units.mul_inv, one_smul]
  · ext m
    show (↑u⁻¹ : S) • (algebraMap R (Module.End R N) r m) = m
    rw [Module.algebraMap_end_apply, ← algebraMap_smul S r m, ← hu, ← mul_smul,
      Units.inv_mul, one_smul]

/-- The `map_units` field of basic-open section localization: a power of `g` acts invertibly on
any module over `Γ(Z, D(g))`, restricted to `Γ(Z, W)`. -/
private lemma isUnit_algebraMap_end_powers {Z : Scheme.{u}} {W : Z.Opens} (g : Γ(Z, W))
    {N : Type*} [AddCommGroup N] [Module Γ(Z, W) N] [Module Γ(Z, Z.basicOpen g) N]
    [IsScalarTower Γ(Z, W) Γ(Z, Z.basicOpen g) N] (s : Submonoid.powers g) :
    IsUnit (algebraMap Γ(Z, W) (Module.End Γ(Z, W) N) s) := by
  obtain ⟨k, hk⟩ := s.2
  refine isUnit_algebraMap_end_of_isUnit_algebraMap (S := Γ(Z, Z.basicOpen g)) ?_
  rw [← hk, map_pow]
  exact (Z.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g).pow k

/-- **qcqs section localization** (the quasi-compact generalization of the the open-immersion case
keystone;
Stacks 01P0 / `lemma-invert-f-sections` beyond the affine case). For a quasi-coherent sheaf
of modules `M` on a scheme `X` and a *quasi-compact, quasi-separated* open `W ⊆ X`, the
section restriction `Γ(M, W) → Γ(M, D(g))` at any `g : Γ(X, W)` exhibits the target as the
localization `Γ(M, W)[1/g]` over `Γ(X, W)`. `map_units` holds because `g` restricts to a
unit of `Γ(X, D(g))` (`RingedSpace.isUnit_res_basicOpen`); `surj`/`exists_of_eq` are the
Mayer–Vietoris induction engines `exists_res_eq_pow_smul_of_isCompact` /
`exists_pow_smul_res_eq_zero_of_isCompact` instantiated at `U := W`. :
Mathlib has no qcqs section-localization at the pinned commit. -/
theorem isLocalizedModule_basicOpen_of_isCompact
    (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsCompact (W : Set X)) (hsep : IsQuasiSeparated (W : Set X))
    (g : Γ(X, W))
    [Module Γ(X, W) Γ(M, X.basicOpen g)]
    [IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) Γ(M, X.basicOpen g)] :
    IsLocalizedModule (Submonoid.powers g) (restrictBasicOpenₗ M g) where
  map_units := isUnit_algebraMap_end_powers g
  surj y := by
    have hDW : X.basicOpen g ≤ W ⊓ X.basicOpen g := le_inf (X.basicOpen_le g) le_rfl
    obtain ⟨x, k, hx⟩ := exists_res_eq_pow_smul_of_isCompact M g hsep W hW le_rfl
      (M.presheaf.map (homOfLE (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g)).op y)
    refine ⟨⟨x, ⟨g ^ k, k, rfl⟩⟩, ?_⟩
    have e1 : (g ^ k : Γ(X, W)) • y
        = X.presheaf.map (homOfLE (X.basicOpen_le g)).op g ^ k • y := by
      rw [← algebraMap_smul Γ(X, X.basicOpen g) (g ^ k) y, map_pow]
      rfl
    have e2 := congrArg (M.presheaf.map (homOfLE hDW).op) hx
    rw [res_res M (inf_le_left : W ⊓ X.basicOpen g ≤ W) hDW (X.basicOpen_le g) x,
      map_smul, map_pow,
      resRing_res ((inf_le_left : W ⊓ X.basicOpen g ≤ W).trans le_rfl) hDW
        (X.basicOpen_le g) g,
      res_res M (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g) hDW le_rfl y,
      res_self M y] at e2
    show (g ^ k : Γ(X, W)) • y = M.presheaf.map (homOfLE (X.basicOpen_le g)).op x
    rw [e1, e2]
  exists_of_eq {x₁ x₂} h := by
    have h' := congrArg
      (M.presheaf.map (homOfLE (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g)).op) h
    rw [show restrictBasicOpenₗ M g x₁
        = M.presheaf.map (homOfLE (X.basicOpen_le g)).op x₁ from rfl,
      show restrictBasicOpenₗ M g x₂
        = M.presheaf.map (homOfLE (X.basicOpen_le g)).op x₂ from rfl,
      res_res M (X.basicOpen_le g) (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g)
        (inf_le_left : W ⊓ X.basicOpen g ≤ W) x₁,
      res_res M (X.basicOpen_le g) (inf_le_right : W ⊓ X.basicOpen g ≤ X.basicOpen g)
        (inf_le_left : W ⊓ X.basicOpen g ≤ W) x₂] at h'
    have h0 : M.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen g ≤ W)).op
        (x₁ - x₂) = 0 := by
      rw [map_sub, h', sub_self]
    obtain ⟨k, hk⟩ := exists_pow_smul_res_eq_zero_of_isCompact M g W hW le_rfl (x₁ - x₂) h0
    rw [resRing_self g, smul_sub] at hk
    exact ⟨⟨g ^ k, k, rfl⟩, sub_eq_zero.mp hk⟩

variable {Y : Scheme.{u}}

/-- For opens `C ≤ B ≤ A`, restricting a section `g : Γ(Y, A)` first to `B` and
then to `C` agrees with restricting it directly to `C`. -/
private lemma resRing_res_hom {A B C : Y.Opens} (hBA : B ≤ A) (i : C ⟶ B)
    (hCA : C ≤ A) (g : Γ(Y, A)) :
    Y.presheaf.map i.op (Y.presheaf.map (homOfLE hBA).op g)
      = Y.presheaf.map (homOfLE hCA).op g := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun (k : C ⟶ A) => Y.presheaf.map k.op g) (Subsingleton.elim _ _)

/-- Additive section transport across an equality of opens, by mutual restriction. -/
private noncomputable def resAddEquivOfEq (N : Y.Modules) {A B : Y.Opens} (h : A = B) :
    Γ(N, A) ≃+ Γ(N, B) where
  toFun := N.presheaf.map (homOfLE h.ge).op
  invFun := N.presheaf.map (homOfLE h.le).op
  left_inv x := by rw [res_res N h.ge h.le le_rfl, res_self N x]
  right_inv x := by rw [res_res N h.le h.ge le_rfl, res_self N x]
  map_add' := map_add _

/-- Inverse-direction semilinearity of the pullback section transport. -/
private lemma gammaPullbackImageIso_symm_semilinear {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (V : X.Opens) (a : Γ(X, V))
    (t : ToType Γ(M, j ''ᵁ V)) :
    (gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.symm
        (gammaImageRingEquiv j V a • t)
      = a • (gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.symm t := by
  apply (gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.injective
  rw [AddEquiv.apply_symm_apply]
  exact ((gammaPullbackImageIso_hom_semilinear j M V a
    ((gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.symm t)).trans
    (congrArg (gammaImageRingEquiv j V a • ·)
      ((gammaPullbackImageIso j M V).addCommGroupIsoToAddEquiv.apply_symm_apply t))).symm

/-- **Converse transport: section localization on the ambient scheme forces the datum.**
For an affine open `U ⊆ Y` with `j = hU.fromSpec` and a sheaf of modules `N` on `Y`, if for
every `f' : Γ(Y, U)` the section restriction `Γ(N, U) → Γ(N, D(f'))` is
`IsLocalizedModule (powers f')` over `Γ(Y, U)`, then the tilde–Γ counit of the pullback
`j^* N` is an isomorphism. This is the reverse of the the open-immersion case chain
(`section_localization_hfr_aux_general` + `isLocalizedModule_basicOpen_of_hP1` run backwards):
the `gammaPullbackImageIso` section comparisons and the `fromSpec` open identifications
(`fromSpec_image_basicOpen`, `image_top = U`) transport the localization to the `Spec`-side
sections, where the affine engine `isIso_fromTildeΓ_of_isLocalizedModule_restrict` applies. -/
private theorem isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule
    (N : Y.Modules) {U : Y.Opens} (hU : IsAffineOpen U)
    (H : ∀ f' : Γ(Y, U),
      letI : Module Γ(Y, U) Γ(N, Y.basicOpen f') :=
        Module.compHom _ (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f'))
      letI : IsScalarTower Γ(Y, U) Γ(Y, Y.basicOpen f') Γ(N, Y.basicOpen f') :=
        IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      IsLocalizedModule (Submonoid.powers f') (restrictBasicOpenₗ N f')) :
    IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pullback hU.fromSpec).obj N)) := by
  set j := hU.fromSpec with hj
  apply isIso_fromTildeΓ_of_isLocalizedModule_restrict
  intro f'
  set M' := (Scheme.Modules.pullback j).obj N with hM'
  have eT : (j ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens)) = U :=
    (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
  have eB : (j ''ᵁ (PrimeSpectrum.basicOpen f')) = Y.basicOpen f' :=
    hU.fromSpec_image_basicOpen f'
  -- module instances on the ambient side
  let : Module Γ(Y, U) Γ(N, Y.basicOpen f') :=
    Module.compHom _ (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f'))
  have : IsScalarTower Γ(Y, U) Γ(Y, Y.basicOpen f') Γ(N, Y.basicOpen f') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hloc := H f'
  -- the additive section comparisons
  let E₁ : ToType Γ(N, U) ≃+
      ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op ⊤)) :=
    ((resAddEquivOfEq N eT.symm).trans
      (gammaPullbackImageIso j N ⊤).addCommGroupIsoToAddEquiv.symm)
  let E₂ : ToType Γ(N, Y.basicOpen f') ≃+
      ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op (PrimeSpectrum.basicOpen f'))) :=
    ((resAddEquivOfEq N eB.symm).trans
      (gammaPullbackImageIso j N (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv.symm)
  -- the Spec-side restriction, R-linearly
  let h : ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op ⊤))
      →ₗ[Γ(Y, U)]
        ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op (PrimeSpectrum.basicOpen f'))) :=
    ((modulesSpecToSheaf.obj M').presheaf.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op).hom
  -- semilinearity (over the identity of `Γ(Y, U)`)
  -- the top-level coherence: `Y`-restriction `U → j''ᵁ⊤` matches the ring comparison
  have C1 : ∀ a : Γ(Y, U), Y.presheaf.map (homOfLE eT.le).op a
      = (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(Y, U)).inv a) := by
    intro a
    have hcoh := fromSpec_image_top_section_coherence hU eT
    have happ := congrArg (fun (φ : Γ(Y, j ''ᵁ (⊤ : (Spec Γ(Y, U)).Opens)) ⟶ Γ(Y, U)) =>
      φ.hom (Y.presheaf.map (homOfLE eT.le).op a)) hcoh
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at happ
    have hres : (Y.presheaf.map (eqToHom eT.symm).op).hom
        (Y.presheaf.map (homOfLE eT.le).op a) = a := by
      rw [Subsingleton.elim (eqToHom eT.symm) (homOfLE eT.ge)]
      show Y.presheaf.map (homOfLE eT.ge).op (Y.presheaf.map (homOfLE eT.le).op a) = a
      rw [resRing_res eT.le eT.ge le_rfl a, resRing_self a]
    rw [hres] at happ
    -- happ : a = ΓSpecIso.hom (appIso.hom (res a))
    refine (gammaImageRingEquiv j ⊤).symm.injective ?_
    rw [RingEquiv.symm_apply_apply]
    refine (Scheme.ΓSpecIso Γ(Y, U)).commRingCatIsoToRingEquiv.injective ?_
    have hcancel := congrArg (fun (φ : Γ(Y, U) ⟶ Γ(Y, U)) => φ.hom a)
      (Scheme.ΓSpecIso Γ(Y, U)).inv_hom_id
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] at hcancel
    show (Scheme.ΓSpecIso Γ(Y, U)).hom.hom ((j.appIso ⊤).hom.hom
        (Y.presheaf.map (homOfLE eT.le).op a))
      = (Scheme.ΓSpecIso Γ(Y, U)).hom.hom ((Scheme.ΓSpecIso Γ(Y, U)).inv.hom a)
    rw [← happ, hcancel]
  have he₁ : ∀ (a : Γ(Y, U)) (x : ToType Γ(N, U)),
      E₁ (a • x) = a • E₁ x := by
    intro a x
    have hN : (N.resAddEquivOfEq eT.symm) (a • x)
        = (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(Y, U)).inv a)
          • (N.resAddEquivOfEq eT.symm) x := by
      show N.presheaf.map (homOfLE eT.le).op (a • x)
        = _ • N.presheaf.map (homOfLE eT.le).op x
      rw [Scheme.Modules.map_smul N (homOfLE eT.le) a x, C1 a]
    -- Term mode throughout. The goal mixes `Γ(N, U)` with
    -- `(modulesSpecToSheaf.obj M').presheaf.obj (op ⊤)`, so it is not type-correct at `implicit`
    -- transparency: `AddEquiv.trans_apply` does not fire and the `rw [hN]` that followed it then
    -- reported its own pattern as absent. `AddEquiv.trans` composes its two functions, so
    -- `congrArg` of the second applied to `hN` is the same step with no rewriting.
    exact (congrArg (gammaPullbackImageIso j N ⊤).addCommGroupIsoToAddEquiv.symm hN).trans
      (gammaPullbackImageIso_symm_semilinear j N ⊤ ((Scheme.ΓSpecIso Γ(Y, U)).inv a) _)
  have hjDU : (j ''ᵁ (PrimeSpectrum.basicOpen f')) ≤ U := eB.trans_le (Y.basicOpen_le f')
  have hsub : (j.opensFunctor.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)))
      = homOfLE (leOfHom (j.opensFunctor.map (homOfLE le_top))) := Subsingleton.elim _ _
  have C2 : ∀ a : Γ(Y, U), Y.presheaf.map (homOfLE hjDU).op a
      = (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
          ((Spec Γ(Y, U)).presheaf.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op
            ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) := by
    intro a
    have key0 := j.appIso_inv_naturality (U := (⊤ : (Spec Γ(Y, U)).Opens))
      (V := PrimeSpectrum.basicOpen f') (homOfLE le_top).op
    have key : (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
        ((Spec Γ(Y, U)).presheaf.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op
          ((Scheme.ΓSpecIso Γ(Y, U)).inv a))
        = (Y.presheaf.map (j.opensFunctor.map (homOfLE le_top)).op).hom
          ((gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) :=
      congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) key0
    rw [key, ← C1 a]
    exact (resRing_res_hom eT.le (j.opensFunctor.map (homOfLE le_top)) hjDU a).symm
  have he₂ : ∀ (a : Γ(Y, U)) (x : ToType Γ(N, Y.basicOpen f')),
      E₂ (a • x) = a • E₂ x := by
    intro a x
    have hN : (N.resAddEquivOfEq eB.symm) (a • x)
        = (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
            ((Spec Γ(Y, U)).presheaf.map
              (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op
              ((Scheme.ΓSpecIso Γ(Y, U)).inv a))
          • (N.resAddEquivOfEq eB.symm) x := by
      show N.presheaf.map (homOfLE eB.le).op
          ((Y.presheaf.map (homOfLE (Y.basicOpen_le f')).op a) • x)
        = _ • N.presheaf.map (homOfLE eB.le).op x
      rw [Scheme.Modules.map_smul N (homOfLE eB.le), resRing_res (Y.basicOpen_le f')
        eB.le hjDU a, C2 a]
    -- Term mode, for the reason given on `he₁`.
    exact (congrArg (gammaPullbackImageIso j N
        (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv.symm hN).trans
      (gammaPullbackImageIso_symm_semilinear j N (PrimeSpectrum.basicOpen f')
        ((Spec Γ(Y, U)).presheaf.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op
          ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) _)
  -- intertwining
  have hh : ∀ x, h (E₁ x) = E₂ (restrictBasicOpenₗ N f' x) := by
    intro x
    apply (gammaPullbackImageIso j N
      (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv.injective
    have hn := ConcreteCategory.congr_hom
      (gammaPullbackImageIso_hom_naturality j N
        (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)))
      (((gammaPullbackImageIso j N ⊤).addCommGroupIsoToAddEquiv.symm
        ((N.resAddEquivOfEq eT.symm) x)))
    -- No `simp only [comp_apply] at hn`: `hn` is not type-correct at `implicit` transparency, so
    -- `simp` refuses silently. `refine hn.trans ?_` below unfolds the composition in its own
    -- defeq check instead.
    -- LHS: naturality then the unit-cancellation of `gamma ∘ gamma.symm`
    have hL : (gammaPullbackImageIso j N
        (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv (h (E₁ x))
        = N.presheaf.map (homOfLE (leOfHom (j.opensFunctor.map
            (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤))))).op
          ((N.resAddEquivOfEq eT.symm) x) := by
      refine hn.trans ?_
      rw [hsub]
      exact congrArg _ ((gammaPullbackImageIso j
        N ⊤).addCommGroupIsoToAddEquiv.apply_symm_apply _)
    have hR : (gammaPullbackImageIso j N
        (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv
          (E₂ (restrictBasicOpenₗ N f' x))
        = (N.resAddEquivOfEq eB.symm) (restrictBasicOpenₗ N f' x) := by
      simp only [E₂]
      exact (gammaPullbackImageIso j N
        (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv.apply_symm_apply _
    rw [hL, hR]
    show N.presheaf.map (homOfLE (leOfHom (j.opensFunctor.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤))))).op
        (N.presheaf.map (homOfLE eT.le).op x)
      = N.presheaf.map (homOfLE eB.le).op
        (N.presheaf.map (homOfLE (Y.basicOpen_le f')).op x)
    exact (res_res N eT.le (leOfHom (j.opensFunctor.map (homOfLE le_top))) hjDU x).trans
      (res_res N (Y.basicOpen_le f') eB.le hjDU x).symm
  have RESULT : IsLocalizedModule
      ((Submonoid.powers f').map ((RingEquiv.refl Γ(Y, U)) : Γ(Y, U) →+* Γ(Y, U))) h :=
    isLocalizedModule_of_ringEquiv_semilinear (RingEquiv.refl Γ(Y, U))
      (Submonoid.powers f') (restrictBasicOpenₗ N f') E₁ E₂ he₁ he₂ h hh
  have key : (Submonoid.powers f').map ((RingEquiv.refl Γ(Y, U)) : Γ(Y, U) →+* Γ(Y, U))
      = Submonoid.powers f' := by
    rw [Submonoid.map_powers]
    rfl
  rw [key] at RESULT
  exact RESULT

/-- Restriction along an arbitrary poset hom equals restriction along `homOfLE`. -/
private lemma res_hom_eq_res (N : Y.Modules) {A B : Y.Opens} (i : B ⟶ A) (x : Γ(N, A)) :
    N.presheaf.map i.op x = N.presheaf.map (homOfLE (leOfHom i)).op x :=
  congrArg (fun (k : B ⟶ A) => N.presheaf.map k.op x) (Subsingleton.elim _ _)

private lemma resRing_hom_eq_res {A B : Y.Opens} (i : B ⟶ A) (g : Γ(Y, A)) :
    Y.presheaf.map i.op g = Y.presheaf.map (homOfLE (leOfHom i)).op g :=
  congrArg (fun (k : B ⟶ A) => Y.presheaf.map k.op g) (Subsingleton.elim _ _)

/-- **Pushforward-level basic-open section localization.** For a quasi-compact
quasi-separated `π : X ⟶ S`, a quasi-coherent `F` on `X`, and an affine open `U ⊆ S`, the
section restriction of the pushforward `Γ(π_*F, U) → Γ(π_*F, D(f'))` at any `f' : Γ(S, U)` is
a localization at `powers f'` over `Γ(S, U)`. The qcqs section-localization engine
`isLocalizedModule_basicOpen_of_isCompact` applies on `X` at `g = π♯ f'` over the compact
quasi-separated preimage `π ⁻¹ᵁ U`, and `π ⁻¹ᵁ D_S(f') = D_X(g)` (`preimage_basicOpen`)
identifies the two restriction maps.  (the sheaf-level heart of Stacks 01XJ). -/
@[ega "I 1.4.1" "more general"]
private theorem isLocalizedModule_basicOpen_pushforward
    {X S : Scheme.{u}} (π : X ⟶ S) [QuasiCompact π] [QuasiSeparated π]
    (F : X.Modules) [F.IsQuasicoherent]
    {U : S.Opens} (hU : IsAffineOpen U) (f' : Γ(S, U)) :
    letI : Module Γ(S, U) Γ((Scheme.Modules.pushforward π).obj F, S.basicOpen f') :=
      Module.compHom _ (algebraMap Γ(S, U) Γ(S, S.basicOpen f'))
    letI : IsScalarTower Γ(S, U) Γ(S, S.basicOpen f')
        Γ((Scheme.Modules.pushforward π).obj F, S.basicOpen f') :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsLocalizedModule (Submonoid.powers f')
      (restrictBasicOpenₗ ((Scheme.Modules.pushforward π).obj F) f') := by
  let : Module Γ(S, U) Γ((Scheme.Modules.pushforward π).obj F, S.basicOpen f') :=
    Module.compHom _ (algebraMap Γ(S, U) Γ(S, S.basicOpen f'))
  let : IsScalarTower Γ(S, U) Γ(S, S.basicOpen f')
      Γ((Scheme.Modules.pushforward π).obj F, S.basicOpen f') :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hW : IsCompact ((π ⁻¹ᵁ U : X.Opens) : Set X) :=
    π.isCompact_preimage hU.isCompact
  have hsep : IsQuasiSeparated ((π ⁻¹ᵁ U : X.Opens) : Set X) :=
    π.isQuasiSeparated_preimage hU.isQuasiSeparated
  set g : Γ(X, π ⁻¹ᵁ U) := π.app U f' with hg
  let : Module Γ(X, π ⁻¹ᵁ U) Γ(F, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, π ⁻¹ᵁ U) Γ(X, X.basicOpen g))
  have : IsScalarTower Γ(X, π ⁻¹ᵁ U) Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hXloc := isLocalizedModule_basicOpen_of_isCompact F hW hsep g
  have hpre : π ⁻¹ᵁ (S.basicOpen f') = X.basicOpen g := Scheme.preimage_basicOpen π f'
  have hle : π ⁻¹ᵁ (S.basicOpen f') ≤ π ⁻¹ᵁ U := hpre.le.trans (X.basicOpen_le g)
  -- ring coherence: restricting `π♯ f'` matches `π♯` of the restriction
  have hring : X.presheaf.map (homOfLE hle).op g
      = π.app (S.basicOpen f') (algebraMap Γ(S, U) Γ(S, S.basicOpen f') f') := by
    show X.presheaf.map (homOfLE hle).op g
      = π.app (S.basicOpen f') (S.presheaf.map (homOfLE (S.basicOpen_le f')).op f')
    have hnat := congrArg
      (fun (φ : Γ(S, U) ⟶ Γ(X, π ⁻¹ᵁ (S.basicOpen f'))) => φ.hom f')
      (π.naturality (homOfLE (S.basicOpen_le f')).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
    rw [hg]
    refine Eq.trans ?_ hnat.symm
    exact (resRing_hom_eq_res ((Opens.map π.base).map (homOfLE (S.basicOpen_le f')))
      (π.app U f')).symm
  refine ⟨?_, ?_, ?_⟩
  · exact isUnit_algebraMap_end_powers f'
  · -- surj
    intro y
    let yF : ToType Γ(F, π ⁻¹ᵁ (S.basicOpen f')) := y
    obtain ⟨⟨x, c⟩, hc⟩ := IsLocalizedModule.surj (S := Submonoid.powers g)
      (f := restrictBasicOpenₗ F g) (F.presheaf.map (homOfLE hpre.ge).op yF)
    have hk : g ^ c.2.choose = (c : Γ(X, π ⁻¹ᵁ U)) := c.2.choose_spec
    refine ⟨⟨x, ⟨f' ^ c.2.choose, c.2.choose, rfl⟩⟩, ?_⟩
    -- push `hc` back along the opens identity `π ⁻¹ᵁ D_S(f') = D_X(g)`
    have hc0 : (c : Γ(X, π ⁻¹ᵁ U)) • (F.presheaf.map (homOfLE hpre.ge).op yF)
        = restrictBasicOpenₗ F g x := hc
    have hc' := congrArg (F.presheaf.map (homOfLE hpre.le).op) hc0
    -- expand the compHom action of `c` on the `X`-side
    have hcL : F.presheaf.map (homOfLE hpre.le).op
        ((c : Γ(X, π ⁻¹ᵁ U)) • (F.presheaf.map (homOfLE hpre.ge).op yF))
        = (X.presheaf.map (homOfLE hle).op (c : Γ(X, π ⁻¹ᵁ U))) • yF := by
      show F.presheaf.map (homOfLE hpre.le).op
          ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op (c : Γ(X, π ⁻¹ᵁ U)))
            • (F.presheaf.map (homOfLE hpre.ge).op yF))
        = (X.presheaf.map (homOfLE hle).op (c : Γ(X, π ⁻¹ᵁ U))) • yF
      rw [Scheme.Modules.map_smul F (homOfLE hpre.le),
        resRing_res (X.basicOpen_le g) hpre.le hle (c : Γ(X, π ⁻¹ᵁ U)),
        res_res F hpre.ge hpre.le le_rfl yF, res_self F yF]
    have hcR : F.presheaf.map (homOfLE hpre.le).op (restrictBasicOpenₗ F g x)
        = F.presheaf.map (homOfLE hle).op x := by
      show F.presheaf.map (homOfLE hpre.le).op
          (F.presheaf.map (homOfLE (X.basicOpen_le g)).op x)
        = F.presheaf.map (homOfLE hle).op x
      exact res_res F (X.basicOpen_le g) hpre.le hle x
    rw [hcL, hcR] at hc'
    -- identify with the pushforward-side statement
    show (f' ^ c.2.choose : Γ(S, U)) • y
      = ((Scheme.Modules.pushforward π).obj F).presheaf.map
          (homOfLE (S.basicOpen_le f')).op x
    have hact : (f' ^ c.2.choose : Γ(S, U)) • y
        = (X.presheaf.map (homOfLE hle).op (c : Γ(X, π ⁻¹ᵁ U))) • yF := by
      show (π.app (S.basicOpen f')
          (algebraMap Γ(S, U) Γ(S, S.basicOpen f') (f' ^ c.2.choose))) • yF
        = (X.presheaf.map (homOfLE hle).op (c : Γ(X, π ⁻¹ᵁ U))) • yF
      rw [map_pow, map_pow, ← hring, ← map_pow]
      exact congrArg (fun t => (X.presheaf.map (homOfLE hle).op t) • yF) hk
    rw [hact, hc']
    exact (show ((Scheme.Modules.pushforward π).obj F).presheaf.map
        (homOfLE (S.basicOpen_le f')).op x = F.presheaf.map (homOfLE hle).op x from
      res_hom_eq_res F ((Opens.map π.base).map (homOfLE (S.basicOpen_le f'))) x).symm
  · -- exists_of_eq
    intro x₁ x₂ h
    have h' : F.presheaf.map (homOfLE hle).op x₁ = F.presheaf.map (homOfLE hle).op x₂ := by
      have e1 : ((Scheme.Modules.pushforward π).obj F).presheaf.map
          (homOfLE (S.basicOpen_le f')).op x₁ = F.presheaf.map (homOfLE hle).op x₁ :=
        res_hom_eq_res F ((Opens.map π.base).map (homOfLE (S.basicOpen_le f'))) x₁
      have e2 : ((Scheme.Modules.pushforward π).obj F).presheaf.map
          (homOfLE (S.basicOpen_le f')).op x₂ = F.presheaf.map (homOfLE hle).op x₂ :=
        res_hom_eq_res F ((Opens.map π.base).map (homOfLE (S.basicOpen_le f'))) x₂
      exact e1.symm.trans (h.trans e2)
    have h'' : restrictBasicOpenₗ F g x₁ = restrictBasicOpenₗ F g x₂ := by
      show F.presheaf.map (homOfLE (X.basicOpen_le g)).op x₁
        = F.presheaf.map (homOfLE (X.basicOpen_le g)).op x₂
      have r1 := res_res F hle hpre.ge (X.basicOpen_le g) x₁
      have r2 := res_res F hle hpre.ge (X.basicOpen_le g) x₂
      rw [← r1, ← r2, h']
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers g) (f := restrictBasicOpenₗ F g) h''
    have hk : g ^ c.2.choose = (c : Γ(X, π ⁻¹ᵁ U)) := c.2.choose_spec
    refine ⟨⟨f' ^ c.2.choose, c.2.choose, rfl⟩, ?_⟩
    let xF₁ : ToType Γ(F, π ⁻¹ᵁ U) := x₁
    let xF₂ : ToType Γ(F, π ⁻¹ᵁ U) := x₂
    show (π.app U (f' ^ c.2.choose)) • xF₁ = (π.app U (f' ^ c.2.choose)) • xF₂
    rw [map_pow]
    show (g : Γ(X, π ⁻¹ᵁ U)) ^ c.2.choose • xF₁ = g ^ c.2.choose • xF₂
    rw [hk]
    exact hc

/-- The family of all affine opens covers a scheme (for the opens Grothendieck topology). -/
private theorem coversTop_affineOpens (S : Scheme.{u}) :
    (Opens.grothendieckTopology ↥S).CoversTop
      (fun U : S.affineOpens => U.1) := by
  intro W y hy
  obtain ⟨V, hVaff, hyV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S) hy
  refine ⟨V, homOfLE hVW, ?_, hyV⟩
  rw [CategoryTheory.Sieve.mem_ofObjects_iff]
  exact ⟨⟨V, hVaff⟩, ⟨𝟙 V⟩⟩

-- The affine pushforward slice proof combines localization with the tilde counit transport.
/-- **Per-affine slice quasi-coherence of a qcqs pushforward.** For qcqs `π : X ⟶ S`, `F`
quasi-coherent on `X`, and an affine open `U ⊆ S`, the slice `(π_* F).over U` is
quasi-coherent: the pushforward-level section localization
(`isLocalizedModule_basicOpen_pushforward`) feeds the converse transport
(`isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule`) to produce the datum, whose
tilde presentation transports along `U.ι = isoSpec.hom ≫ fromSpec` back to the geometric
restriction and then to the slice (`overRestrictPresentationInv`). -/
private theorem pushforward_isQuasicoherent_over_affine
    {X S : Scheme.{u}} (π : X ⟶ S) [QuasiCompact π] [QuasiSeparated π]
    (F : X.Modules) [F.IsQuasicoherent] {U : S.Opens} (hU : IsAffineOpen U) :
    (((Scheme.Modules.pushforward π).obj F).over U).IsQuasicoherent := by
  set N := (Scheme.Modules.pushforward π).obj F with hN
  have hP1 : IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pullback hU.fromSpec).obj N)) :=
    isIso_fromTildeΓ_pullback_fromSpec_of_isLocalizedModule N hU
      (fun f' => isLocalizedModule_basicOpen_pushforward π F hU f')
  -- global presentation of the `fromSpec`-pullback, via the tilde presentation
  let eT' : tilde ((modulesSpecToSheaf.obj
        ((Scheme.Modules.pullback hU.fromSpec).obj N)).presheaf.obj (Opposite.op ⊤))
      ≅ (Scheme.Modules.pullback hU.fromSpec).obj N :=
    @asIso _ _ _ _
      (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback hU.fromSpec).obj N)) hP1
  -- `IsIso` passed explicitly at both `ofIsIso` below: search has to unify `Iso.hom ?e` against
  -- the goal, which means assigning `?e` through the instance arguments of `Iso`, and that
  -- assignment happens at reducible transparency.
  have P_M' : ((Scheme.Modules.pullback hU.fromSpec).obj N).Presentation :=
    @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ eT'.hom eT'.isIso_hom
      (AlgebraicGeometry.presentationTilde.{u} _ Set.univ (by simp) _ (Submodule.span_eq _))
  -- transport along `U.ι = isoSpec.hom ≫ fromSpec`
  have hcomp : hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
    rw [← hU.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  let eι := (Scheme.Modules.pullbackComp hU.isoSpec.hom hU.fromSpec).app N ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app N
  have P_ι : ((Scheme.Modules.pullback U.ι).obj N).Presentation :=
    @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ eι.hom eι.isIso_hom
      (presentationPullbackOfSchemeIso hU.isoSpec.symm
        ((Scheme.Modules.pullback hU.fromSpec).obj N) P_M')
  exact (Scheme.Modules.overRestrictPresentationInv U N P_ι).isQuasicoherent

end Scheme.Modules

end BasicOpenPresentationDescent

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01LC.** Pushforward along a quasi-compact and
quasi-separated morphism of schemes preserves quasi-coherence. -/
@[stacks 01LC, ega "III 1.4.10" "q = 0"]
public instance pushforward_isQuasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  have : ∀ U : S.affineOpens,
      (((Scheme.Modules.pushforward f).obj F).over U.1).IsQuasicoherent :=
    fun U => AlgebraicGeometry.Scheme.Modules.pushforward_isQuasicoherent_over_affine f F U.2
  exact SheafOfModules.IsQuasicoherent.of_coversTop
    ((Scheme.Modules.pushforward f).obj F)
    (fun U : S.affineOpens => U.1)
    (AlgebraicGeometry.Scheme.Modules.coversTop_affineOpens S)

end AlgebraicGeometry
