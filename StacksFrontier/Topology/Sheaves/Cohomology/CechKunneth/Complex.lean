module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Čech complexes of presheaves of modules on a complete lattice

Let `k` be a commutative ring, `L` a complete lattice, `P : Lᵒᵖ ⥤ ModuleCat k` a presheaf of
`k`-modules on `L` and `U : ι → L` a family of elements. The Čech complex of `P` with respect to
`U` has in degree `p` the product `∏_{s} P(U_{s₀} ⊓ ⋯ ⊓ U_{s_p})` over all tuples
`s : Fin (p + 1) → ι`, with the usual alternating differential
`(d c)_s = ∑_j (-1)^j c_{s ∘ δ_j}|`. When `L` is the lattice of opens of a space this is the
Čech complex of [Stacks, Tag 01ED]; the generality of an arbitrary complete lattice is what lets
the product `L₁ × L₂` of two lattices of opens carry the Čech complex of the product covering used
in the Künneth formula [Stacks, Tag 0BED].

This file builds the complex, its cohomology as an explicit quotient of cocycles by coboundaries,
the maps induced by morphisms of presheaves, and the long exact sequence attached to a sequence
of presheaves which is short exact on the members of the nerve of `U`.

## Main definitions

* `Stacks.CechKunneth.Cochain`: the Čech cochains of degree `p`.
* `Stacks.CechKunneth.d`: the Čech differential.
* `Stacks.CechKunneth.H`: Čech cohomology, the quotient of the cocycles by the coboundaries.
* `Stacks.CechKunneth.Hmap`: the map on Čech cohomology induced by a morphism of presheaves.
* `Stacks.CechKunneth.IsNerveSES`: a sequence of presheaves short exact on the nerve of `U`.
* `Stacks.CechKunneth.IsNerveSES.δ`: the connecting map of the long exact sequence.

## Main results

* `Stacks.CechKunneth.d_d`: `d ∘ d = 0`.
* `Stacks.CechKunneth.IsNerveSES.exact₁`, `exact₂`, `exact₃`: the long exact sequence, together
  with `Stacks.CechKunneth.IsNerveSES.injective_Hmap_zero` at its start.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.CechKunneth

section Lattice

variable {L : Type u} [CompleteLattice L] {ι : Type u} (U : ι → L)

/-- The member `U_{s₀} ⊓ ⋯ ⊓ U_{s_p}` of the nerve of `U` selected by a tuple of indices. -/
def inter {p : ℕ} (s : Fin (p + 1) → ι) : L := ⨅ j, U (s j)

/-- Reindexing a tuple along `θ` gives a larger member of the nerve. -/
theorem inter_le_comp {p q : ℕ} (θ : Fin (p + 1) → Fin (q + 1)) (s : Fin (q + 1) → ι) :
    inter U s ≤ inter U (s ∘ θ) :=
  le_iInf fun j => iInf_le (fun j => U (s j)) (θ j)

/-- The member of the nerve selected by `s` is contained in each `U (s j)`. -/
theorem inter_le_apply {p : ℕ} (s : Fin (p + 1) → ι) (j : Fin (p + 1)) : inter U s ≤ U (s j) :=
  iInf_le (fun j => U (s j)) j

end Lattice

variable {k : Type u} [CommRing k] {L : Type u} [CompleteLattice L] {ι : Type u}

section Res

variable (P : Lᵒᵖ ⥤ ModuleCat.{u} k)

/-- The restriction map of a presheaf along `Z ≤ Z'`. -/
def res {Z Z' : L} (h : Z ≤ Z') : P.obj (op Z') →ₗ[k] P.obj (op Z) :=
  (P.map (homOfLE h).op).hom

/-- Restriction is transitive: restricting along `Z ≤ Z'` after `Z' ≤ Z''` is restricting along
`Z ≤ Z''`. -/
theorem res_res {Z Z' Z'' : L} (h₁ : Z' ≤ Z'') (h₂ : Z ≤ Z') (x : P.obj (op Z'')) :
    res P h₂ (res P h₁ x) = res P (h₂.trans h₁) x := by
  change (P.map (homOfLE h₁).op ≫ P.map (homOfLE h₂).op).hom x = _
  rw [← Functor.map_comp]
  rfl

/-- Restriction along `Z ≤ Z` is the identity. -/
theorem res_self {Z : L} (h : Z ≤ Z) (x : P.obj (op Z)) : res P h x = x := by
  change (P.map (𝟙 (op Z))).hom x = x
  rw [P.map_id]
  rfl

/-- Restriction from two (equal) elements to a common smaller one agrees, after transport. -/
theorem res_congr {Z : L} {p : ℕ} {U : ι → L} {s s' : Fin (p + 1) → ι} (e : s = s')
    (c : ∀ t : Fin (p + 1) → ι, P.obj (op (inter U t))) (h : Z ≤ inter U s)
    (h' : Z ≤ inter U s') : res P h (c s) = res P h' (c s') := by
  subst e
  rfl

/-- A morphism of presheaves commutes with restriction. -/
theorem app_res {P' : Lᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ P') {Z Z' : L} (h : Z ≤ Z')
    (x : P.obj (op Z')) : (f.app (op Z)).hom (res P h x) = res P' h ((f.app (op Z')).hom x) := by
  change (P.map (homOfLE h).op ≫ f.app (op Z)).hom x = (f.app (op Z') ≫ P'.map _).hom x
  rw [f.naturality]

end Res

variable (P : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L)

/-- **Čech cochains of degree `p`**: a section of `P` over every member of the nerve selected by a
tuple of length `p + 1`. -/
abbrev Cochain (p : ℕ) : Type u := ∀ s : Fin (p + 1) → ι, P.obj (op (inter U s))

/-- **The Čech differential** `(d c)_s = ∑_j (-1)^j c_{s ∘ δ_j}|`. -/
def d (p : ℕ) : Cochain P U p →ₗ[k] Cochain P U (p + 1) where
  toFun c s := ∑ j : Fin (p + 2),
    ((-1 : ℤ) ^ (j : ℕ)) • res P (inter_le_comp U j.succAbove s) (c (s ∘ j.succAbove))
  map_add' c c' := funext fun s => by
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r c := funext fun s => by
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/-- The value of the Čech differential at a tuple `s`. -/
theorem d_apply (p : ℕ) (c : Cochain P U p) (s : Fin (p + 2) → ι) :
    d P U p c s = ∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • res P (inter_le_comp U j.succAbove s) (c (s ∘ j.succAbove)) :=
  rfl

/-- The involution `(k, j) ↦ (k.succAbove j, j.predAbove k)` reverses the sign `(-1)^k (-1)^j`. -/
theorem neg_one_pow_mul_succAbove_predAbove (n : ℕ) (k : Fin (n + 2)) (j : Fin (n + 1)) :
    ((-1 : ℤ) ^ (k : ℕ)) * ((-1 : ℤ) ^ (j : ℕ)) =
      -(((-1 : ℤ) ^ ((k.succAbove j : Fin (n + 2)) : ℕ)) *
        ((-1 : ℤ) ^ ((j.predAbove k : Fin (n + 1)) : ℕ))) := by
  rw [← pow_add, ← pow_add]
  rcases lt_or_ge j.castSucc k with h | h
  · rw [Fin.succAbove_of_castSucc_lt k j h, Fin.predAbove_of_castSucc_lt j k h,
      Fin.val_castSucc, Fin.val_pred]
    have hk : 0 < (k : ℕ) := by
      have h0 : j.castSucc.val < k.val := h
      omega
    rw [show (k : ℕ) + (j : ℕ) = ((j : ℕ) + ((k : ℕ) - 1)) + 1 by omega, pow_succ]
    ring
  · rw [Fin.succAbove_of_le_castSucc k j h, Fin.predAbove_of_le_castSucc j k h,
      Fin.val_succ, Fin.coe_castPred]
    rw [show (j : ℕ) + 1 + (k : ℕ) = ((k : ℕ) + (j : ℕ)) + 1 by omega, pow_succ]
    ring

/-- **`d ∘ d = 0`**: the Čech differential squares to zero. -/
theorem d_d (p : ℕ) (c : Cochain P U p) : d P U (p + 1) (d P U p c) = 0 := by
  funext i
  rw [d_apply, Pi.zero_apply]
  have step : ∀ k : Fin (p + 3),
      ((-1 : ℤ) ^ (k : ℕ)) • res P (inter_le_comp U k.succAbove i) (d P U p c (i ∘ k.succAbove))
        = ∑ j : Fin (p + 2), (((-1 : ℤ) ^ (k : ℕ)) * ((-1 : ℤ) ^ (j : ℕ))) •
            res P ((inter_le_comp U k.succAbove i).trans
              (inter_le_comp U j.succAbove (i ∘ k.succAbove)))
              (c ((i ∘ k.succAbove) ∘ j.succAbove)) := by
    intro k
    rw [d_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, res_res, smul_smul]
  rw [Finset.sum_congr rfl (fun k _ => step k),
    Finset.sum_sigma' (Finset.univ : Finset (Fin (p + 3)))
      (fun _ => (Finset.univ : Finset (Fin (p + 2))))]
  apply Finset.sum_involution
    (g := fun (x : (_ : Fin (p + 3)) × Fin (p + 2)) _ =>
      (⟨x.fst.succAbove x.snd, x.snd.predAbove x.fst⟩ : (_ : Fin (p + 3)) × Fin (p + 2)))
  · rintro ⟨k, j⟩ _
    have hface : ((i ∘ (k.succAbove j).succAbove) ∘ (j.predAbove k).succAbove) =
        ((i ∘ k.succAbove) ∘ j.succAbove) := by
      funext x
      simp only [Function.comp_apply]
      rw [Fin.succAbove_succAbove_succAbove_predAbove]
    simp only
    rw [neg_one_pow_mul_succAbove_predAbove (p + 1) k j, neg_smul,
      res_congr P hface c _ ((inter_le_comp U k.succAbove i).trans
        (inter_le_comp U j.succAbove (i ∘ k.succAbove)))]
    abel
  · rintro ⟨k, j⟩ _ _ h
    exact Fin.succAbove_ne k j (congrArg Sigma.fst h)
  · rintro ⟨k, j⟩ _
    exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  · rintro ⟨k, j⟩ _
    refine Sigma.ext (Fin.succAbove_succAbove_predAbove k j) ?_
    rw [Fin.succAbove_succAbove_predAbove k j]
    exact heq_of_eq (Fin.predAbove_predAbove_succAbove k j)

/-- The composite of two consecutive Čech differentials is zero. -/
theorem d_comp_d (p : ℕ) : d P U (p + 1) ∘ₗ d P U p = 0 :=
  LinearMap.ext (d_d P U p)

/-! ### Functoriality in the presheaf -/

section Map

variable {P} {P' P'' : Lᵒᵖ ⥤ ModuleCat.{u} k}

/-- The map of cochains induced by a morphism of presheaves. -/
def mapCochain (f : P ⟶ P') (p : ℕ) : Cochain P U p →ₗ[k] Cochain P' U p where
  toFun c s := (f.app (op (inter U s))).hom (c s)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _

/-- The value of `mapCochain U f p c` at `s` is `f` applied to `c s`. -/
theorem mapCochain_apply (f : P ⟶ P') (p : ℕ) (c : Cochain P U p) (s : Fin (p + 1) → ι) :
    mapCochain U f p c s = (f.app (op (inter U s))).hom (c s) :=
  rfl

/-- The map of cochains induced by a morphism of presheaves commutes with the differential. -/
theorem mapCochain_d (f : P ⟶ P') (p : ℕ) (c : Cochain P U p) :
    mapCochain U f (p + 1) (d P U p c) = d P' U p (mapCochain U f p c) := by
  funext s
  rw [mapCochain_apply, d_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, app_res]
  rfl

/-- The map of cochains induced by `f ≫ g` is the composite of those induced by `f` and `g`. -/
theorem mapCochain_comp (f : P ⟶ P') (g : P' ⟶ P'') (p : ℕ) (c : Cochain P U p) :
    mapCochain U (f ≫ g) p c = mapCochain U g p (mapCochain U f p c) :=
  rfl

end Map

/-! ### Čech cohomology -/

/-- The Čech cocycles of degree `p`. -/
def cocycles (p : ℕ) : Submodule k (Cochain P U p) := LinearMap.ker (d P U p)

/-- The Čech coboundaries of degree `p`, as a submodule of the cocycles. -/
def coboundaries : (p : ℕ) → Submodule k (cocycles P U p)
  | 0 => ⊥
  | p + 1 => (LinearMap.range (d P U p)).comap (cocycles P U (p + 1)).subtype

/-- **Čech cohomology** `Ȟ^p(U, P)`, the cocycles modulo the coboundaries. -/
abbrev H (p : ℕ) : Type u := cocycles P U p ⧸ coboundaries P U p

/-- The class of a cocycle. -/
def Hmk {p : ℕ} (z : Cochain P U p) (hz : d P U p z = 0) : H P U p :=
  Submodule.Quotient.mk ⟨z, hz⟩

/-- Every Čech cohomology class is the class of a cocycle. -/
theorem Hmk_surjective {p : ℕ} (x : H P U p) : ∃ z hz, Hmk P U z hz = x := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨z, hz, rfl⟩

/-- The class of a sum of cocycles is the sum of their classes. -/
theorem Hmk_add {p : ℕ} (z z' : Cochain P U p) (hz : d P U p z = 0) (hz' : d P U p z' = 0) :
    Hmk P U (z + z') (by rw [map_add, hz, hz', add_zero]) = Hmk P U z hz + Hmk P U z' hz' :=
  rfl

/-- The class of `r • z` is `r` times the class of `z`, for `r : k`. -/
theorem Hmk_smul {p : ℕ} (r : k) (z : Cochain P U p) (hz : d P U p z = 0) :
    Hmk P U (r • z) (by rw [map_smul, hz, smul_zero]) = r • Hmk P U z hz :=
  rfl

/-- The class of `r • z` is `r` times the class of `z`, for `r : ℤ`. -/
theorem Hmk_zsmul {p : ℕ} (r : ℤ) (z : Cochain P U p) (hz : d P U p z = 0) :
    Hmk P U (r • z) (by rw [map_zsmul, hz, smul_zero]) = r • Hmk P U z hz := by
  change (coboundaries P U p).mkQ ⟨r • z, _⟩ = r • (coboundaries P U p).mkQ ⟨z, hz⟩
  rw [← map_zsmul]
  rfl

/-- Equal cocycles have equal classes. -/
theorem Hmk_congr {p : ℕ} {z z' : Cochain P U p} (e : z = z') (hz : d P U p z = 0)
    (hz' : d P U p z' = 0) : Hmk P U z hz = Hmk P U z' hz' := by
  subst e; rfl

/-- The class of the zero cocycle is zero. -/
theorem Hmk_zero (p : ℕ) : Hmk P U (0 : Cochain P U p) (map_zero _) = 0 := rfl

/-- The class of a coboundary is zero. -/
theorem Hmk_d {p : ℕ} (w : Cochain P U p) : Hmk P U (d P U p w) (d_d P U p w) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩

/-- In positive degree, the class of a cocycle vanishes if and only if it is a coboundary. -/
theorem Hmk_eq_zero_iff_succ {p : ℕ} (z : Cochain P U (p + 1)) (hz : d P U (p + 1) z = 0) :
    Hmk P U z hz = 0 ↔ ∃ w, d P U p w = z :=
  Submodule.Quotient.mk_eq_zero _

/-- In degree zero, the class of a cocycle vanishes if and only if the cocycle is zero. -/
theorem Hmk_eq_zero_iff_zero (z : Cochain P U 0) (hz : d P U 0 z = 0) :
    Hmk P U z hz = 0 ↔ z = 0 := by
  rw [Hmk, Submodule.Quotient.mk_eq_zero]
  change _ ∈ (⊥ : Submodule k _) ↔ _
  rw [Submodule.mem_bot, Subtype.ext_iff]
  rfl

/-- The class of a difference of cocycles is the difference of their classes. -/
theorem Hmk_sub {p : ℕ} (z z' : Cochain P U p) (hz : d P U p z = 0) (hz' : d P U p z' = 0) :
    Hmk P U (z - z') (by rw [map_sub, hz, hz', sub_zero]) = Hmk P U z hz - Hmk P U z' hz' :=
  rfl

/-- Two cocycles of positive degree differing by a coboundary have the same class. -/
theorem Hmk_eq_of_succ {p : ℕ} (z z' : Cochain P U (p + 1)) (hz : d P U (p + 1) z = 0)
    (hz' : d P U (p + 1) z' = 0) (w : Cochain P U p) (e : z = z' + d P U p w) :
    Hmk P U z hz = Hmk P U z' hz' := by
  rw [← sub_eq_zero, ← Hmk_sub, Hmk_eq_zero_iff_succ]
  exact ⟨w, by rw [e, add_sub_cancel_left]⟩

section Map

variable {P} {P' P'' : Lᵒᵖ ⥤ ModuleCat.{u} k}

/-- **The map on Čech cohomology induced by a morphism of presheaves.** -/
def Hmap (f : P ⟶ P') (p : ℕ) : H P U p →ₗ[k] H P' U p :=
  Submodule.mapQ _ _ ((mapCochain U f p).restrict fun z (hz : d P U p z = 0) => by
      change d P' U p _ = 0
      rw [← mapCochain_d, hz, map_zero]) (by
    cases p with
    | zero =>
      intro z hz
      simp only [coboundaries, Submodule.mem_bot] at hz
      subst hz
      exact Submodule.zero_mem _
    | succ p =>
      rintro ⟨z, hz⟩ ⟨w, rfl⟩
      exact ⟨mapCochain U f p w, (mapCochain_d U f p w).symm⟩)

/-- `Hmap U f p` sends the class of a cocycle `z` to the class of its image under `f`. -/
theorem Hmap_Hmk (f : P ⟶ P') {p : ℕ} (z : Cochain P U p) (hz : d P U p z = 0) :
    Hmap U f p (Hmk P U z hz) =
      Hmk P' U (mapCochain U f p z) (by rw [← mapCochain_d, hz, map_zero]) :=
  rfl

end Map

/-! ### The long exact sequence -/

section LES

variable {P P' P'' : Lᵒᵖ ⥤ ModuleCat.{u} k}

/-- A sequence `P ⟶ P' ⟶ P''` of presheaves which is short exact on every member of the nerve of
`U`. -/
structure IsNerveSES (f : P ⟶ P') (g : P' ⟶ P'') : Prop where
  /-- `f` is injective on every member of the nerve. -/
  injective : ∀ {p : ℕ} (s : Fin (p + 1) → ι), Function.Injective (f.app (op (inter U s))).hom
  /-- `P ⟶ P' ⟶ P''` is exact on every member of the nerve. -/
  exact : ∀ {p : ℕ} (s : Fin (p + 1) → ι),
    Function.Exact (f.app (op (inter U s))).hom (g.app (op (inter U s))).hom
  /-- `g` is surjective on every member of the nerve. -/
  surjective : ∀ {p : ℕ} (s : Fin (p + 1) → ι), Function.Surjective (g.app (op (inter U s))).hom

namespace IsNerveSES

variable {U} {f : P ⟶ P'} {g : P' ⟶ P''} (h : IsNerveSES U f g)
include h

/-- The map of cochains induced by `f` is injective. -/
theorem injective_mapCochain (p : ℕ) : Function.Injective (mapCochain U f p) :=
  fun _ _ e => funext fun s => h.injective s (congr_fun e s)

/-- The map of cochains induced by `g` is surjective. -/
theorem surjective_mapCochain (p : ℕ) : Function.Surjective (mapCochain U g p) := by
  intro c
  choose y hy using fun s : Fin (p + 1) → ι => h.surjective s (c s)
  exact ⟨y, funext hy⟩

/-- The composite of the maps of cochains induced by `f` and `g` is zero. -/
theorem mapCochain_comp_eq_zero (p : ℕ) (c : Cochain P U p) :
    mapCochain U g p (mapCochain U f p c) = 0 :=
  funext fun s => (h.exact s).apply_apply_eq_zero (c s)

/-- A cochain of `P'` killed by `g` is the image of a cochain of `P` under `f`. -/
theorem exact_mapCochain (p : ℕ) (c : Cochain P' U p) (hc : mapCochain U g p c = 0) :
    ∃ x, mapCochain U f p x = c := by
  choose x hx using fun s : Fin (p + 1) → ι => ((h.exact s) (c s)).1 (congr_fun hc s)
  exact ⟨x, funext hx⟩

/-- A lift of a cocycle of `P''` to a cochain of `P'`. -/
noncomputable def lift {p : ℕ} (z : Cochain P'' U p) : Cochain P' U p :=
  (h.surjective_mapCochain p z).choose

/-- The image of `h.lift z` under `g` is `z`. -/
theorem mapCochain_lift {p : ℕ} (z : Cochain P'' U p) : mapCochain U g p (h.lift z) = z :=
  (h.surjective_mapCochain p z).choose_spec

/-- For a cocycle `z` of `P''`, the differential of `h.lift z` is the image of a cochain of `P`
under `f`. -/
theorem exists_d_lift {p : ℕ} (z : Cochain P'' U p) (hz : d P'' U p z = 0) :
    ∃ x, mapCochain U f (p + 1) x = d P' U p (h.lift z) :=
  h.exact_mapCochain (p + 1) _ (by rw [mapCochain_d, h.mapCochain_lift, hz])

/-- A cochain of `P` whose image under `f` is a cocycle is a cocycle. -/
private theorem d_eq_zero_of_d_mapCochain {p : ℕ} (x : Cochain P U p)
    (hx : d P' U p (mapCochain U f p x) = 0) : d P U p x = 0 :=
  h.injective_mapCochain _ (by rw [mapCochain_d, hx, map_zero])

/-- A cochain of `P` whose image under `f` is a coboundary is a cocycle. -/
theorem d_eq_zero_of_mapCochain {p : ℕ} (y : Cochain P' U p) (x : Cochain P U (p + 1))
    (hx : mapCochain U f (p + 1) x = d P' U p y) : d P U (p + 1) x = 0 :=
  h.d_eq_zero_of_d_mapCochain x (by rw [hx, d_d])

/-- The connecting map on cocycles. -/
noncomputable def δcocycle {p : ℕ} (z : Cochain P'' U p) (hz : d P'' U p z = 0) : H P U (p + 1) :=
  Hmk P U (h.exists_d_lift z hz).choose
    (h.d_eq_zero_of_mapCochain _ _ (h.exists_d_lift z hz).choose_spec)

/-- **The connecting map is computed by any lift.** -/
theorem δcocycle_eq {p : ℕ} (z : Cochain P'' U p) (hz : d P'' U p z = 0) (y : Cochain P' U p)
    (hy : mapCochain U g p y = z) (x : Cochain P U (p + 1))
    (hx : mapCochain U f (p + 1) x = d P' U p y) :
    h.δcocycle z hz = Hmk P U x (h.d_eq_zero_of_mapCochain y x hx) := by
  set x₀ := (h.exists_d_lift z hz).choose
  have hx₀ := (h.exists_d_lift z hz).choose_spec
  obtain ⟨w, hw⟩ := h.exact_mapCochain p (h.lift z - y)
    (by rw [map_sub, h.mapCochain_lift, hy, sub_self])
  refine Hmk_eq_of_succ P U _ _ _ _ w (h.injective_mapCochain (p + 1) ?_)
  rw [map_add, hx₀, hx, mapCochain_d, hw, map_sub, add_sub_cancel]

/-- The connecting map on cocycles is additive. -/
theorem δcocycle_add {p : ℕ} (z z' : Cochain P'' U p) (hz : d P'' U p z = 0)
    (hz' : d P'' U p z' = 0) :
    h.δcocycle (z + z') (by rw [map_add, hz, hz', add_zero]) =
      h.δcocycle z hz + h.δcocycle z' hz' := by
  obtain ⟨x, hx⟩ := h.exists_d_lift z hz
  obtain ⟨x', hx'⟩ := h.exists_d_lift z' hz'
  rw [h.δcocycle_eq z hz _ (h.mapCochain_lift z) x hx,
    h.δcocycle_eq z' hz' _ (h.mapCochain_lift z') x' hx',
    h.δcocycle_eq _ _ (h.lift z + h.lift z') (by rw [map_add, h.mapCochain_lift,
      h.mapCochain_lift]) (x + x') (by rw [map_add, map_add, hx, hx']), ← Hmk_add]

/-- The connecting map on cocycles is `k`-linear. -/
theorem δcocycle_smul {p : ℕ} (r : k) (z : Cochain P'' U p) (hz : d P'' U p z = 0) :
    h.δcocycle (r • z) (by rw [map_smul, hz, smul_zero]) = r • h.δcocycle z hz := by
  obtain ⟨x, hx⟩ := h.exists_d_lift z hz
  rw [h.δcocycle_eq z hz _ (h.mapCochain_lift z) x hx,
    h.δcocycle_eq _ _ (r • h.lift z) (by rw [map_smul, h.mapCochain_lift]) (r • x)
      (by rw [map_smul, map_smul, hx]), ← Hmk_smul]

/-- The connecting map vanishes on coboundaries. -/
theorem δcocycle_d {p : ℕ} (w : Cochain P'' U p) :
    h.δcocycle (d P'' U p w) (d_d P'' U p w) = 0 := by
  rw [h.δcocycle_eq _ _ (d P' U p (h.lift w)) (by rw [mapCochain_d, h.mapCochain_lift]) 0
    (by rw [map_zero, d_d]), Hmk_zero]

/-- **The connecting map** `Ȟ^p(U, P'') ⟶ Ȟ^{p+1}(U, P)` of the long exact sequence. -/
noncomputable def δ (p : ℕ) : H P'' U p →ₗ[k] H P U (p + 1) :=
  Submodule.liftQ _
    { toFun := fun z => h.δcocycle z.1 z.2
      map_add' := fun z z' => h.δcocycle_add z.1 z'.1 z.2 z'.2
      map_smul' := fun r z => h.δcocycle_smul r z.1 z.2 }
    (by
      cases p with
      | zero =>
        intro z hz
        simp only [coboundaries, Submodule.mem_bot] at hz
        subst hz
        exact (h.δcocycle_eq 0 (map_zero _) 0 (map_zero _) 0 (by rw [map_zero, map_zero])).trans
          (Hmk_zero P U _)
      | succ p =>
        rintro ⟨z, hz⟩ ⟨w, rfl⟩
        exact h.δcocycle_d w)

/-- The connecting map sends the class of `z` to the class of `x`, for any lift `y` of `z` and any
`x` with `f x = d y`. -/
theorem δ_Hmk {p : ℕ} (z : Cochain P'' U p) (hz : d P'' U p z = 0) (y : Cochain P' U p)
    (hy : mapCochain U g p y = z) (x : Cochain P U (p + 1))
    (hx : mapCochain U f (p + 1) x = d P' U p y) :
    h.δ p (Hmk P'' U z hz) = Hmk P U x (h.d_eq_zero_of_mapCochain y x hx) :=
  h.δcocycle_eq z hz y hy x hx

/-- The composite `Ȟ^p(U, P) ⟶ Ȟ^p(U, P') ⟶ Ȟ^p(U, P'')` is zero. -/
theorem Hmap_g_comp_Hmap_f (p : ℕ) (x : H P U p) : Hmap U g p (Hmap U f p x) = 0 := by
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P U x
  rw [Hmap_Hmk, Hmap_Hmk]
  exact (Hmk_congr P'' U (h.mapCochain_comp_eq_zero p z) _ _).trans (Hmk_zero P'' U p)

/-- The composite `Ȟ^p(U, P') ⟶ Ȟ^p(U, P'') ⟶ Ȟ^{p+1}(U, P)` is zero. -/
theorem δ_comp_Hmap_g (p : ℕ) (x : H P' U p) : h.δ p (Hmap U g p x) = 0 := by
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P' U x
  rw [Hmap_Hmk, h.δ_Hmk _ _ z rfl 0 (by rw [map_zero, hz]), Hmk_zero]

/-- **Exactness at `Ȟ^p(U, P')`.** -/
theorem exact_Hmap_g (p : ℕ) (x : H P' U p) (hx : Hmap U g p x = 0) :
    ∃ y, Hmap U f p y = x := by
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P' U x
  rw [Hmap_Hmk] at hx
  cases p with
  | zero =>
    rw [Hmk_eq_zero_iff_zero] at hx
    obtain ⟨y, hy⟩ := h.exact_mapCochain 0 z hx
    refine ⟨Hmk P U y (h.d_eq_zero_of_d_mapCochain y (by rw [hy, hz])), ?_⟩
    · rw [Hmap_Hmk]; exact Hmk_congr P' U hy _ _
  | succ p =>
    obtain ⟨w, hw⟩ := (Hmk_eq_zero_iff_succ P'' U _ _).1 hx
    obtain ⟨y, hy⟩ := h.exact_mapCochain (p + 1) (z - d P' U p (h.lift w))
      (by rw [map_sub, mapCochain_d, h.mapCochain_lift, hw, sub_self])
    refine ⟨Hmk P U y (h.d_eq_zero_of_d_mapCochain y (by rw [hy, map_sub, hz, d_d, sub_zero])), ?_⟩
    rw [Hmap_Hmk]
    exact Hmk_eq_of_succ P' U _ _ _ _ (-(h.lift w)) (by rw [hy, map_neg, sub_eq_add_neg])

/-- **Exactness at `Ȟ^{p+1}(U, P)`.** -/
theorem exact_δ (p : ℕ) (x : H P U (p + 1)) (hx : Hmap U f (p + 1) x = 0) :
    ∃ y, h.δ p y = x := by
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P U x
  rw [Hmap_Hmk, Hmk_eq_zero_iff_succ] at hx
  obtain ⟨w, hw⟩ := hx
  refine ⟨Hmk P'' U (mapCochain U g p w) ?_, ?_⟩
  · rw [← mapCochain_d, hw, h.mapCochain_comp_eq_zero]
  · exact h.δ_Hmk _ _ w rfl z hw.symm

/-- **Exactness at `Ȟ^p(U, P'')`.** -/
theorem exact_Hmap_f (p : ℕ) (x : H P'' U p) (hx : h.δ p x = 0) :
    ∃ y, Hmap U g p y = x := by
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P'' U x
  obtain ⟨x₀, hx₀⟩ := h.exists_d_lift z hz
  rw [h.δ_Hmk z hz _ (h.mapCochain_lift z) x₀ hx₀, Hmk_eq_zero_iff_succ] at hx
  obtain ⟨w, hw⟩ := hx
  refine ⟨Hmk P' U (h.lift z - mapCochain U f p w) ?_, ?_⟩
  · rw [map_sub, ← hx₀, ← mapCochain_d, hw, sub_self]
  · rw [Hmap_Hmk]
    exact Hmk_congr P'' U (by rw [map_sub, h.mapCochain_lift, h.mapCochain_comp_eq_zero,
      sub_zero]) _ _

/-- The composite `Ȟ^p(U, P'') ⟶ Ȟ^{p+1}(U, P) ⟶ Ȟ^{p+1}(U, P')` is zero. -/
theorem Hmap_f_comp_δ (p : ℕ) (x : H P'' U p) : Hmap U f (p + 1) (h.δ p x) = 0 := by
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P'' U x
  obtain ⟨x₀, hx₀⟩ := h.exists_d_lift z hz
  rw [h.δ_Hmk z hz _ (h.mapCochain_lift z) x₀ hx₀, Hmap_Hmk]
  exact (Hmk_congr P' U hx₀ _ _).trans (Hmk_d P' U _)

/-- The long exact sequence, at `Ȟ^p(U, P')`. -/
theorem exact₁ (p : ℕ) : Function.Exact (Hmap U f p) (Hmap U g p) := fun y =>
  ⟨h.exact_Hmap_g p y, by rintro ⟨x, rfl⟩; exact h.Hmap_g_comp_Hmap_f p x⟩

/-- The long exact sequence, at `Ȟ^p(U, P'')`. -/
theorem exact₂ (p : ℕ) : Function.Exact (Hmap U g p) (h.δ p) := fun y =>
  ⟨h.exact_Hmap_f p y, by rintro ⟨x, rfl⟩; exact h.δ_comp_Hmap_g p x⟩

/-- The long exact sequence, at `Ȟ^{p+1}(U, P)`. -/
theorem exact₃ (p : ℕ) : Function.Exact (h.δ p) (Hmap U f (p + 1)) := fun y =>
  ⟨h.exact_δ p y, by rintro ⟨x, rfl⟩; exact h.Hmap_f_comp_δ p x⟩

/-- **In degree zero the map induced by `f` is injective.** -/
theorem injective_Hmap_zero : Function.Injective (Hmap U f 0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective P U x
  rw [Hmap_Hmk, Hmk_eq_zero_iff_zero] at hx
  rw [Hmk_eq_zero_iff_zero]
  exact h.injective_mapCochain 0 (by rw [hx, map_zero])

end IsNerveSES

end LES

end Stacks.CechKunneth

end
