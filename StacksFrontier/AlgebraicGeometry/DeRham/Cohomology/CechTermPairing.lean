module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionNaturality

/-!
# Pairing the extended alternating Čech complex with a second coefficient module

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions and let
`μ : ℳ × 𝒩 ⟶ 𝒫` be a pairing of `𝒪_X`-modules, given on sections as a `Stacks.BilinearMap`.
This file pairs the first argument with the extended alternating Čech complex of
[Stacks, Tag 0G7I] in the second: it builds a `Stacks.BilinearMap`

`ℳ × 𝓝^n ⟶ 𝓟^n`

on each term of the complex, and proves that it commutes with the differentials.

The construction needs nothing but the shape of the terms. The degree-`(p+1)` term is
`∏_{i₀ < ⋯ < i_p} 𝒩_{i₀…i_p}` with `𝒩_{i₀…i_p} = j_*j^*𝒩` for the open immersion `j` of the
principal intersection, so a section of it over `V` *is* an ordered Čech cochain
(`Stacks.Perfect.ExtendedAlternatingCech.secIso`): a section of `𝒩` on each
`V ∩ X_{f_{i₀}} ∩ ⋯ ∩ X_{f_{i_p}}`. The pairing restricts the first argument to that
intersection and applies `μ` there. No excision and no base change for the class map is
involved, because the first argument is restricted along `j` rather than the complex being
transported; this is why the pairing is available in this model.

## Main definitions

* `Stacks.Perfect.CechPairing.pairCochain`: the ordered Čech cochain `q ↦ μ(m|_{U_q}, x_q)`.
* `Stacks.Perfect.CechPairing.cechPair`: the pairing `ℳ × 𝓝^{p+1} ⟶ 𝓟^{p+1}` on a
  positive-degree term, as a `Stacks.BilinearMap`.
* `Stacks.Perfect.CechPairing.termPair`: the pairing on every term of the complex, `μ` itself
  in degree zero and `cechPair` above it.

## Main results

* `Stacks.Perfect.CechPairing.pairVal_difSucc` and `Stacks.Perfect.CechPairing.pairVal_difZero`:
  the pairing commutes with the positive-degree differentials and with the augmentation. The
  differentials are the signed alternating sums of the restriction maps `canR` and of the
  augmentation `augR`, and the pairing commutes with restriction because `μ` does.
* `Stacks.Perfect.CechPairing.termPair_dif`: the same statement for the differentials of the
  complex, including the last one, whose cokernel carries the class map of
  [Stacks, Tag 0G7Q].

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction (secIso_smul secIso_restrict interMonoOpen)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechPairing

/-- An additive map carries a signed finite sum to the signed sum of the images. Stated for
bare abelian groups: the scheme-theoretic spellings of the groups of sections obstruct the
corresponding rewrite. -/
private theorem map_sum_zsmul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (h : A →+ B)
    {ι : Type*} [Fintype ι] (k : ι → ℤ) (a : ι → A) :
    h (∑ j, k j • a j) = ∑ j, k j • h (a j) :=
  (map_sum h _ Finset.univ).trans (Finset.sum_congr rfl fun j _ => h.map_zsmul (k j) (a j))

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))
variable {M N P : X.Modules} (μ : Stacks.BilinearMap M.val N.val P.val)

/-! ### The paired cochain -/

/-- `μ` commutes with restriction along `g`, given that `m''` is the restriction of `m'`. -/
private theorem app_restrict_eq {U₁ U₂ : X.Opens} (g : U₂ ⟶ U₁) (m' : Γ(M, U₁))
    (m'' : Γ(M, U₂)) (hm : M.presheaf.map g.op m' = m'') (y : Γ(N, U₁)) :
    μ.app (op U₂) m'' (N.presheaf.map g.op y) =
      P.presheaf.map g.op (μ.app (op U₁) m' y) :=
  hm ▸ (μ.naturality g.op m' y).symm

/-- **The pairing on ordered Čech cochains.** On the intersection belonging to an increasing
tuple it is `μ` applied to the restriction of the first argument and to the component of the
cochain. -/
def cochainMap (p : ℕ) (V : X.Opens) (m : Γ(M, V))
    (cc : CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf N) p) :
    CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i)) (Scheme.Modules.presheaf P) p :=
  fun q => μ.app (op (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1))
    (M.presheaf.map (homOfLE (interLe f p q V)).op m) (cc q)

/-- **The pairing commutes with the ordered Čech differential.** The differential is the
signed alternating sum of the restriction maps, and `μ` commutes with restriction. -/
theorem cochainMap_ordD (p : ℕ) (V : X.Opens) (m : Γ(M, V))
    (cc : CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i))
      (Scheme.Modules.presheaf N) p) :
    cochainMap f μ (p + 1) V m
        (CechCochains.ordD (fun i => V ⊓ X.basicOpen (f i))
          (Scheme.Modules.presheaf N) p cc) =
      CechCochains.ordD (fun i => V ⊓ X.basicOpen (f i)) (Scheme.Modules.presheaf P) p
        (cochainMap f μ p V m cc) := by
  funext t
  show μ.app (op (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) t.1))
      (M.presheaf.map (homOfLE (interLe f (p + 1) t V)).op m)
      (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr (Scheme.Modules.presheaf N)
          (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (f i)) t.1 j)
          (cc ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩)) =
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr (Scheme.Modules.presheaf P)
        (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (f i)) t.1 j)
        (cochainMap f μ p V m cc ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩)
  refine Eq.trans (map_sum_zsmul
    (μ.app (op (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) t.1))
      (M.presheaf.map (homOfLE (interLe f (p + 1) t V)).op m))
    (fun j : Fin (p + 2) => ((-1 : ℤ) ^ (j : ℕ)))
    (fun j : Fin (p + 2) => CechCochains.restr (Scheme.Modules.presheaf N)
      (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (f i)) t.1 j)
      (cc ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩))) ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) • z) ?_
  exact app_restrict_eq μ (homOfLE (CechCochains.inter_le_omit
    (fun i => V ⊓ X.basicOpen (f i)) t.1 j)) _ _
    (collapse2 M (homOfLE (interLe f p ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩ V))
      (homOfLE (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (f i)) t.1 j))
      (homOfLE (interLe f (p + 1) t V)) m) _

/-- **The ordered Čech cochain of the pairing.** On the intersection belonging to an
increasing tuple it is `μ` applied to the restriction of the first argument and to the
component of the second. -/
def pairCochain (p : ℕ) (V : X.Opens) (m : Γ(M, V)) (x : Γ(prodTerm f N p, V)) :
    CechCochains.OrdCochain (fun i => V ⊓ X.basicOpen (f i)) (Scheme.Modules.presheaf P) p :=
  cochainMap f μ p V m (secIso f N p V x)

/-- The component of `pairCochain f μ p V m x` at an increasing tuple `q` is `μ` applied to
the restriction of `m` and to the `q`-component of `x`. -/
theorem pairCochain_apply (p : ℕ) (V : X.Opens) (m : Γ(M, V)) (x : Γ(prodTerm f N p, V))
    (q : CechCochains.OrdIndex (I := Fin c) p) :
    pairCochain f μ p V m x q =
      μ.app (op (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1))
        (M.presheaf.map (homOfLE (interLe f p q V)).op m) (secIso f N p V x q) := rfl

/-- **The pairing on a positive-degree term, on sections.** -/
def pairVal (p : ℕ) (V : X.Opens) (m : Γ(M, V)) (x : Γ(prodTerm f N p, V)) :
    Γ(prodTerm f P p, V) :=
  (secIso f P p V).symm (pairCochain f μ p V m x)

/-- Under `secIso`, `pairVal f μ p V m x` is the cochain `pairCochain f μ p V m x`. -/
@[simp]
theorem secIso_pairVal (p : ℕ) (V : X.Opens) (m : Γ(M, V)) (x : Γ(prodTerm f N p, V)) :
    secIso f P p V (pairVal f μ p V m x) = pairCochain f μ p V m x :=
  (secIso f P p V).apply_symm_apply _

/-! ### The pairing laws -/

/-- `pairVal` is additive in the first argument. -/
theorem pairVal_add_left (p : ℕ) (V : X.Opens) (m m' : Γ(M, V)) (x : Γ(prodTerm f N p, V)) :
    pairVal f μ p V (m + m') x = pairVal f μ p V m x + pairVal f μ p V m' x := by
  refine (secIso f P p V).injective ?_
  rw [map_add, secIso_pairVal, secIso_pairVal, secIso_pairVal]
  funext q
  rw [CechCochains.OrdCochain.add_apply, pairCochain_apply, pairCochain_apply,
    pairCochain_apply, map_add]
  exact μ.map_add_left _ _ _ _

/-- `pairVal` is additive in the second argument. -/
theorem pairVal_add_right (p : ℕ) (V : X.Opens) (m : Γ(M, V)) (x x' : Γ(prodTerm f N p, V)) :
    pairVal f μ p V m (x + x') = pairVal f μ p V m x + pairVal f μ p V m x' := by
  refine (secIso f P p V).injective ?_
  rw [map_add, secIso_pairVal, secIso_pairVal, secIso_pairVal]
  funext q
  rw [CechCochains.OrdCochain.add_apply, pairCochain_apply, pairCochain_apply,
    pairCochain_apply, map_add]
  exact map_add _ _ _

/-- `pairVal` is `Γ(X, V)`-linear in the first argument. -/
theorem pairVal_smul_left (p : ℕ) (V : X.Opens) (ρ : Γ(X, V)) (m : Γ(M, V))
    (x : Γ(prodTerm f N p, V)) :
    pairVal f μ p V (ρ • m) x = ρ • pairVal f μ p V m x := by
  refine (secIso f P p V).injective ?_
  rw [secIso_pairVal]
  funext q
  rw [secIso_smul, secIso_pairVal, pairCochain_apply, pairCochain_apply,
    Scheme.Modules.map_smul M (homOfLE (interLe f p q V))]
  exact μ.map_smul_left _ _ _ _

/-- `pairVal` is `Γ(X, V)`-linear in the second argument. -/
theorem pairVal_smul_right (p : ℕ) (V : X.Opens) (ρ : Γ(X, V)) (m : Γ(M, V))
    (x : Γ(prodTerm f N p, V)) :
    pairVal f μ p V m (ρ • x) = ρ • pairVal f μ p V m x := by
  refine (secIso f P p V).injective ?_
  rw [secIso_pairVal]
  funext q
  rw [secIso_smul, secIso_pairVal, pairCochain_apply, pairCochain_apply, secIso_smul]
  exact μ.map_smul_right _ _ _ _

/-- `pairVal` commutes with restriction from `V` to an open `W ≤ V`. -/
theorem pairVal_restrict (p : ℕ) {W V : X.Opens} (hWV : W ≤ V) (m : Γ(M, V))
    (x : Γ(prodTerm f N p, V)) :
    pairVal f μ p W (M.presheaf.map (homOfLE hWV).op m)
        ((prodTerm f N p).presheaf.map (homOfLE hWV).op x) =
      (prodTerm f P p).presheaf.map (homOfLE hWV).op (pairVal f μ p V m x) := by
  refine (secIso f P p W).injective ?_
  rw [secIso_pairVal]
  funext q
  rw [secIso_restrict, secIso_pairVal, pairCochain_apply, pairCochain_apply, secIso_restrict]
  exact app_restrict_eq μ (homOfLE (interMonoOpen f p q hWV)) _ _
    (collapse2_eq M (homOfLE (interLe f p q V)) (homOfLE (interMonoOpen f p q hWV))
      (homOfLE hWV) (homOfLE (interLe f p q W)) m) _

/-! ### The pairing as a bilinear map -/

/-- **The pairing on a positive-degree term of the extended alternating Čech complex.** -/
def cechPair (p : ℕ) :
    Stacks.BilinearMap M.val (prodTerm f N p).val (prodTerm f P p).val where
  app V :=
    AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun x => pairVal f μ p V.unop m x)
        (pairVal_add_right f μ p V.unop m))
      (fun m m' => by ext x; exact pairVal_add_left f μ p V.unop m m' x)
  map_smul_left _ r m x := pairVal_smul_left f μ p _ r m x
  map_smul_right _ r m x := pairVal_smul_right f μ p _ r m x
  naturality {V W} g m x := by
    rw [show g = (homOfLE (leOfHom g.unop)).op from
      congrArg Quiver.Hom.op (Subsingleton.elim _ _)]
    exact (pairVal_restrict f μ p (leOfHom g.unop) m x).symm

/-- On sections over `V`, `cechPair f μ p` is `pairVal f μ p V`. -/
@[simp]
theorem cechPair_app (p : ℕ) (V : X.Opens) (m : Γ(M, V)) (x : Γ(prodTerm f N p, V)) :
    (cechPair f μ p).app (op V) m x = pairVal f μ p V m x := rfl

/-! ### Commutation with the differentials -/

/-- **The pairing commutes with the differential in positive degrees.** -/
theorem pairVal_difSucc (p : ℕ) (V : X.Opens) (m : Γ(M, V)) (x : Γ(prodTerm f N p, V)) :
    pairVal f μ (p + 1) V m ((difSucc f N p).app V x) =
      (difSucc f P p).app V (pairVal f μ p V m x) := by
  refine (secIso f P (p + 1) V).injective ?_
  refine Eq.trans (secIso_pairVal f μ (p + 1) V m _) ?_
  refine Eq.trans ?_ (secIso_difSucc f P p V (pairVal f μ p V m x)).symm
  refine Eq.trans ?_ (congrArg
    (CechCochains.ordD (fun i => V ⊓ X.basicOpen (f i)) (Scheme.Modules.presheaf P) p)
    (secIso_pairVal f μ p V m x)).symm
  exact Eq.trans
    (congrArg (cochainMap f μ (p + 1) V m) (secIso_difSucc f N p V x))
    (cochainMap_ordD f μ p V m (secIso f N p V x))

/-- **The pairing commutes with the augmentation.** -/
theorem pairVal_difZero (V : X.Opens) (m : Γ(M, V)) (y : Γ(N, V)) :
    pairVal f μ 0 V m ((difZero f N).app V y) =
      (difZero f P).app V (μ.app (op V) m y) := by
  refine (secIso f P 0 V).injective ?_
  refine Eq.trans (secIso_pairVal f μ 0 V m _) (funext fun s => ?_)
  refine Eq.trans ?_ (secIso_difZero f P V (μ.app (op V) m y) s).symm
  refine Eq.trans (congrArg
    (fun z => μ.app (op (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) s.1))
      (M.presheaf.map (homOfLE (interLe f 0 s V)).op m) z)
    (secIso_difZero f N V y s)) ?_
  exact (μ.naturality (homOfLE (interLe f 0 s V)).op m y).symm

/-! ### The pairing on every term -/

/-- **The pairing on the terms of the extended alternating Čech complex**: the given pairing
in degree zero, and the paired Čech cochains above it. -/
def termPair : ∀ n : ℕ, Stacks.BilinearMap M.val (term f N n).val (term f P n).val
  | 0 => μ
  | (p + 1) => cechPair f μ p

/-- In degree zero, `termPair f μ` is `μ`. -/
theorem termPair_zero : termPair f μ 0 = μ := rfl

/-- In degree `p + 1`, `termPair f μ` is `cechPair f μ p`. -/
theorem termPair_succ (p : ℕ) : termPair f μ (p + 1) = cechPair f μ p := rfl

/-- **The pairing commutes with every differential of the complex.** -/
theorem termPair_dif (n : ℕ) (V : X.Opens) (m : Γ(M, V)) (x : Γ(term f N n, V)) :
    (termPair f μ (n + 1)).app (op V) m ((dif f N n).app V x) =
      (dif f P n).app V ((termPair f μ n).app (op V) m x) := by
  cases n with
  | zero => exact pairVal_difZero f μ V m x
  | succ p => exact pairVal_difSucc f μ p V m x

end Stacks.Perfect.CechPairing

end
