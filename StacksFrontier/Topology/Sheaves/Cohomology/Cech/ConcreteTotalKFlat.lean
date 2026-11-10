module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotal
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ChainHomotopy
public import StacksFrontier.Algebra.Homology.KFlat
import all StacksFrontier.AlgebraicGeometry.Perfect.Coherator.KunnethTotalCech
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Flat.Basic
import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleFlat

/-!
# K-flatness of the total Čech complex of a finite cover

Let `U : ι → Opens X` be a finite family of opens of a topological space and `P` a complex,
indexed by `ℕ`, of presheaves of `R`-modules on `X`. The total Čech complex `Tot(Č(U, P))`
(`Stacks.CategoryTheory.CechComplex.cechTot`) uses all tuples of indices, so it is not bounded
above. After choosing a linear order on `ι`, sorting the tuples (with the sign of the sorting
permutation, and killing the tuples with a repeated index) is an idempotent endomorphism of
`Tot(Č(U, P))` which is homotopic to the identity and vanishes in Čech degrees `≥ #ι`
(`Stacks.Cech.ChainHomotopy`). Hence, if `P` is bounded above and its values on the Čech
intersections are flat, `Tot(Č(U, P))` is K-flat: it is homotopy equivalent to a bounded above
complex of flat modules.

The chain-level homotopy of `Stacks.Cech.ChainHomotopy` is transported to cochains by evaluating
cochains on supported chains (`Stacks.CategoryTheory.CechComplex.CochainSorting.eval`), which is
`R`-linear in the cochain and natural in the presheaf; the homotopy on the total complex has no
sign, because it commutes with the differentials of `P`.

## Main results

* `Stacks.CategoryTheory.CechComplex.CochainSorting.homotopy_identity`: `hδ + δh = 1 - π` on
  cochains.
* `Stacks.CategoryTheory.CechComplex.CochainSorting.totHomotopy`: the homotopy from the identity of
  `Tot(Č(U, P))` to the sorting projection.
* `Stacks.CategoryTheory.CechComplex.kFlat_cechTot`: `Tot(Č(U, P))` is K-flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cech.ChainHomotopy (SupportedChain SupportedTuple boundary projection chainMap
  chainHomotopy chainMap_of chainMap_homotopy chainMap_projection chainHomotopy_identity
  boundary_projection projection_zero projection_idempotent projection_eq_zero)

universe w u r

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X)

/-- The infimum of the opens selected by a tuple lies in their categorical product. -/
theorem iInf_le_inter {m : ℕ} (t : Fin m → ι) : CechCochains.inter U t ≤ inter U t :=
  le_of_eq (inter_eq_iInf U t).symm

/-- The categorical product of the opens selected by a tuple lies in their infimum. -/
theorem inter_le_iInf {m : ℕ} (t : Fin m → ι) : inter U t ≤ CechCochains.inter U t :=
  le_of_eq (inter_eq_iInf U t)

namespace CochainSorting

variable {R : Type r} [Ring R] (F : (Opens X)ᵒᵖ ⥤ ModuleCat.{w} R)

/-- The restriction of sections along an inclusion of opens. -/
abbrev restrict {V W : Opens X} (h : V ≤ W) : F.obj (op W) →ₗ[R] F.obj (op V) :=
  (F.map (homOfLE h).op).hom

/-- `F` sends any two morphisms `V ⟶ W` of opens to the same restriction map. -/
theorem map_op_eq {V W : Opens X} (i j : V ⟶ W) : F.map i.op = F.map j.op := by
  rw [Subsingleton.elim i j]

/-- Restricting from `V` to `W` and then to `Z` is restricting from `V` to `Z`. -/
theorem restrict_restrict {V W Z : Opens X} (h₁ : W ≤ V) (h₂ : Z ≤ W) (x : F.obj (op V)) :
    restrict F h₂ (restrict F h₁ x) = restrict F (h₂.trans h₁) x := by
  change (F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op).hom x = _
  rw [← F.map_comp, ← op_comp]
  rfl

/-- Restricting a section of `F` over `V` to `V` itself is the identity. -/
theorem restrict_self {V : Opens X} (h : V ≤ V) (x : F.obj (op V)) : restrict F h x = x := by
  change (F.map (homOfLE h).op).hom x = x
  rw [map_op_eq F (homOfLE h) (𝟙 V), op_id, F.map_id, ModuleCat.id_apply]

/-- Restricting the face map `cres U F φ t x` to `V ≤ U_t` is restricting `x` to `V`. -/
theorem restrict_cres {m n : ℕ} (φ : Fin m → Fin n) (t : Fin n → ι) {V : Opens X}
    (h : V ≤ inter U t) (x : F.obj (op (inter U (t ∘ φ)))) :
    restrict F h (cres U F φ t x) = restrict F (h.trans (leOfHom (interMap U t φ))) x := by
  change (F.map (interMap U t φ).op ≫ F.map (homOfLE h).op).hom x = _
  rw [← F.map_comp, ← op_comp]
  exact congrArg (fun g : V ⟶ inter U (t ∘ φ) => (F.map g.op).hom x) (Subsingleton.elim _ _)

/-- **Evaluation of cochains on supported chains**: a formal combination of tuples `t` with
`V ≤ U_t` sends a cochain `s` to the corresponding combination of the restrictions of the `s_t`
to `V`. It is `R`-linear in the cochain. -/
def eval (V : Opens X) (p : ℕ) : SupportedChain U V p →+ (Cochain U F p →ₗ[R] F.obj (op V)) :=
  FreeAbelianGroup.lift fun t =>
    restrict F (t.2.trans (iInf_le_inter U t.1)) ∘ₗ LinearMap.proj t.1

/-- Evaluating a cochain `s` on a single tuple `t` with `V ≤ U_t` is restricting `s_t` to `V`. -/
theorem eval_of (V : Opens X) (p : ℕ) (t : SupportedTuple U V p) (s : Cochain U F p) :
    eval U F V p (FreeAbelianGroup.of t) s =
      restrict F (t.2.trans (iInf_le_inter U t.1)) (s t.1) := by
  simp [eval]

/-- Evaluating a cochain `s` on the tuple `t` supported on `U_t` itself gives `s_t`. -/
theorem eval_self {p : ℕ} (t : Fin (p + 1) → ι) (h : inter U t ≤ CechCochains.inter U t)
    (s : Cochain U F p) : eval U F (inter U t) p (FreeAbelianGroup.of ⟨t, h⟩) s = s t := by
  rw [eval_of]
  exact restrict_self F _ _

/-- Evaluation turns the boundary of chains into the Čech differential of cochains. -/
theorem eval_boundary (V : Opens X) (p : ℕ) (a : SupportedChain U V (p + 1))
    (s : Cochain U F p) :
    eval U F V p (boundary U V p a) s = eval U F V (p + 1) a (cechD U F p s) := by
  induction a using FreeAbelianGroup.induction_on with
  | of t =>
    simp only [boundary, FreeAbelianGroup.lift_apply_of, map_sum, map_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply, eval_of, cechD_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [restrict_cres]
    rfl
  | _ => simp_all

/-- Evaluation is compatible with restricting the support. -/
theorem eval_chainMap {V W : Opens X} (h : V ≤ W) (p : ℕ) (a : SupportedChain U W p)
    (s : Cochain U F p) :
    eval U F V p (chainMap U h p a) s = restrict F h (eval U F W p a s) := by
  induction a using FreeAbelianGroup.induction_on with
  | of t =>
    rw [chainMap_of, eval_of, eval_of, restrict_restrict]
  | _ => simp_all

/-- Evaluation is natural in the presheaf. -/
theorem eval_cochainMap {G : (Opens X)ᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ G) (V : Opens X) (p : ℕ)
    (a : SupportedChain U V p) (s : Cochain U F p) :
    eval U G V p a (cochainMap U φ p s) = (φ.app (op V)).hom (eval U F V p a s) := by
  induction a using FreeAbelianGroup.induction_on with
  | of t =>
    rw [eval_of, eval_of, cochainMap_apply]
    exact (ConcreteCategory.congr_hom (φ.naturality _) _).symm
  | _ => simp_all

/-- If `L` is the cochain map whose component at `t` evaluates on `T t`, for an operation `T` on
supported chains commuting with `chainMap`, then evaluating `L s` on `a` is evaluating `s` on
`T a`. -/
private theorem eval_of_pi_eval {p q : ℕ}
    (T : ∀ V : Opens X, SupportedChain U V p →+ SupportedChain U V q)
    (hT : ∀ {V W : Opens X} (h : V ≤ W) (a : SupportedChain U W p),
      chainMap U h q (T W a) = T V (chainMap U h p a))
    (L : Cochain U F q →ₗ[R] Cochain U F p)
    (hL : ∀ (s : Cochain U F q) (t : Fin (p + 1) → ι), L s t =
      eval U F (inter U t) q (T _ (FreeAbelianGroup.of ⟨t, inter_le_iInf U t⟩)) s)
    (V : Opens X) (a : SupportedChain U V p) (s : Cochain U F q) :
    eval U F V p a (L s) = eval U F V q (T V a) s := by
  induction a using FreeAbelianGroup.induction_on with
  | of t => rw [eval_of, hL, ← eval_chainMap, hT, chainMap_of]
  | _ => simp_all

variable [LinearOrder ι]

/-- **The sorting projection** on Čech cochains: `(π s)_t` is `sign(σ) s_{t ∘ σ}` for the
permutation `σ` sorting `t` when `t` is injective, and `0` otherwise. -/
def sort (p : ℕ) : Cochain U F p →ₗ[R] Cochain U F p :=
  LinearMap.pi fun t => eval U F (inter U t) p
    (projection U (inter U t) p (FreeAbelianGroup.of ⟨t, inter_le_iInf U t⟩))

/-- **The homotopy** `h : Č^{p+1} ⟶ Č^p` between the identity and the sorting projection. -/
def homotopy (p : ℕ) : Cochain U F (p + 1) →ₗ[R] Cochain U F p :=
  LinearMap.pi fun t => eval U F (inter U t) (p + 1)
    (chainHomotopy U (inter U t) p (FreeAbelianGroup.of ⟨t, inter_le_iInf U t⟩))

/-- The component of `π s` at `t` is the evaluation of `s` on the sorting projection of `t`. -/
theorem sort_apply (p : ℕ) (s : Cochain U F p) (t : Fin (p + 1) → ι) :
    sort U F p s t = eval U F (inter U t) p
      (projection U (inter U t) p (FreeAbelianGroup.of ⟨t, inter_le_iInf U t⟩)) s :=
  rfl

/-- The component of `h s` at `t` is the evaluation of `s` on the chain homotopy applied to `t`. -/
theorem homotopy_apply (p : ℕ) (s : Cochain U F (p + 1)) (t : Fin (p + 1) → ι) :
    homotopy U F p s t = eval U F (inter U t) (p + 1)
      (chainHomotopy U (inter U t) p (FreeAbelianGroup.of ⟨t, inter_le_iInf U t⟩)) s :=
  rfl

/-- Evaluating `π s` on a chain `a` is evaluating `s` on the sorting projection of `a`. -/
theorem eval_sort (V : Opens X) (p : ℕ) (a : SupportedChain U V p) (s : Cochain U F p) :
    eval U F V p a (sort U F p s) = eval U F V p (projection U V p a) s :=
  eval_of_pi_eval U F (fun V => projection U V p) (fun h a => chainMap_projection U h p a)
    (sort U F p) (sort_apply U F p) V a s

/-- Evaluating `h s` on a chain `a` is evaluating `s` on the chain homotopy applied to `a`. -/
theorem eval_homotopy (V : Opens X) (p : ℕ) (a : SupportedChain U V p)
    (s : Cochain U F (p + 1)) :
    eval U F V p a (homotopy U F p s) = eval U F V (p + 1) (chainHomotopy U V p a) s :=
  eval_of_pi_eval U F (fun V => chainHomotopy U V p) (fun h a => chainMap_homotopy U h p a)
    (homotopy U F p) (homotopy_apply U F p) V a s

/-- **The homotopy identity** `hδ + δh = 1 - π` in positive degrees. -/
theorem homotopy_identity (p : ℕ) (s : Cochain U F (p + 1)) :
    homotopy U F (p + 1) (cechD U F (p + 1) s) + cechD U F p (homotopy U F p s) =
      s - sort U F (p + 1) s := by
  funext t
  have h := congrArg (fun a => eval U F (inter U t) (p + 1) a s)
    (chainHomotopy_identity U (inter U t) p (FreeAbelianGroup.of ⟨t, inter_le_iInf U t⟩))
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h
  rw [eval_boundary, ← eval_homotopy, ← eval_homotopy, eval_boundary] at h
  simp only [eval_self] at h
  rw [Pi.add_apply, Pi.sub_apply, sort_apply]
  exact h

/-- The homotopy `h : Č^1 ⟶ Č^0` vanishes. -/
theorem homotopy_zero (s : Cochain U F 1) : homotopy U F 0 s = 0 := by
  funext t
  rw [homotopy_apply]
  simp [chainHomotopy]

/-- The sorting projection is the identity on `Č^0`. -/
theorem sort_zero (s : Cochain U F 0) : sort U F 0 s = s := by
  funext t
  rw [sort_apply, projection_zero, eval_self]

/-- The sorting projection commutes with the Čech differential. -/
theorem sort_cechD (p : ℕ) (s : Cochain U F p) :
    sort U F (p + 1) (cechD U F p s) = cechD U F p (sort U F p s) := by
  funext t
  rw [sort_apply, ← eval_boundary, boundary_projection, ← eval_sort, eval_boundary, eval_self]

/-- The sorting projection is idempotent. -/
theorem sort_sort (p : ℕ) (s : Cochain U F p) : sort U F p (sort U F p s) = sort U F p s := by
  funext t
  rw [sort_apply, eval_sort, projection_idempotent, ← sort_apply]

/-- The sorting projection vanishes on `Č^p` for `#ι ≤ p`. -/
theorem sort_eq_zero [Finite ι] (p : ℕ) (hp : Nat.card ι ≤ p) (s : Cochain U F p) :
    sort U F p s = 0 := by
  funext t
  rw [sort_apply, projection_eq_zero U _ p hp]
  rfl

/-- The sorting projection is natural in the presheaf. -/
theorem sort_cochainMap {G : (Opens X)ᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ G) (p : ℕ)
    (s : Cochain U F p) : sort U G p (cochainMap U φ p s) = cochainMap U φ p (sort U F p s) := by
  funext t
  rw [sort_apply, eval_cochainMap]
  rfl

/-- The homotopy `h` is natural in the presheaf. -/
theorem homotopy_cochainMap {G : (Opens X)ᵒᵖ ⥤ ModuleCat.{w} R} (φ : F ⟶ G) (p : ℕ)
    (s : Cochain U F (p + 1)) :
    homotopy U G p (cochainMap U φ (p + 1) s) = cochainMap U φ p (homotopy U F p s) := by
  funext t
  rw [homotopy_apply, eval_cochainMap]
  rfl

/-! ### The sorting projection of the total complex -/

variable (P : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{w} R) ℕ)

/-- The sorting projection on `Tot^n`, summand by summand. -/
def totSort (n : ℤ) : TotX U P n →ₗ[R] TotX U P n :=
  LinearMap.pi fun i => sort U (P.X i.1.2) i.1.1 ∘ₗ LinearMap.proj i

/-- The component of `totSort U P n x` at the summand `(p, a)` is `π` applied to `x_{(p, a)}`. -/
theorem totSort_apply (n : ℤ) (x : TotX U P n) (i : TotIndex n) :
    totSort U P n x i = sort U (P.X i.1.2) i.1.1 (x i) :=
  rfl

/-- The homotopy `Tot^n ⟶ Tot^m` (for `m + 1 = n`): on the summand `(p, a)` it is `h` applied
to the component `(p + 1, a)`. -/
def totHomotopyMap (n m : ℤ) (h : m + 1 = n) : TotX U P n →ₗ[R] TotX U P m :=
  LinearMap.pi fun i => homotopy U (P.X i.1.2) i.1.1 ∘ₗ
    LinearMap.proj (⟨(i.1.1 + 1, i.1.2), by have := i.2; push_cast; omega⟩ : TotIndex n)

/-- The component of the total homotopy at the summand `(p, a)` is `h` applied to
`x_{(p + 1, a)}`. -/
theorem totHomotopyMap_apply (n m : ℤ) (h : m + 1 = n) (x : TotX U P n) (i : TotIndex m) :
    totHomotopyMap U P n m h x i = homotopy U (P.X i.1.2) i.1.1
      (x ⟨(i.1.1 + 1, i.1.2), by have := i.2; push_cast; omega⟩) :=
  rfl

/-- The sorting projection on the total complex commutes with the total differential. -/
theorem totSort_totDTo (n m : ℤ) (h : n + 1 = m) (x : TotX U P n) :
    totSort U P m (totDTo U P n m h x) = totDTo U P n m h (totSort U P n x) := by
  funext ⟨⟨p, a⟩, hpa⟩
  rcases p with _ | q <;> rcases a with _ | b <;>
    simp only [totSort_apply, totDTo_apply, totDCech_zero, totDCech_succ, totDCoef_zero,
      totDCoef_succ, map_add, map_zsmul, add_zero, zero_add, map_zero, sort_cechD,
      sort_cochainMap]

/-- **The homotopy identity on the total complex**: `hD + Dh + π = 1`. -/
theorem totHomotopy_identity (k n m : ℤ) (h₁ : k + 1 = n) (h₂ : n + 1 = m) (x : TotX U P n) :
    totHomotopyMap U P m n h₂ (totDTo U P n m h₂ x) +
      totDTo U P k n h₁ (totHomotopyMap U P n k h₁ x) + totSort U P n x = x := by
  funext ⟨⟨p, a⟩, hpa⟩
  rcases p with _ | q <;> rcases a with _ | b <;>
    simp only [Pi.add_apply, totSort_apply, totHomotopyMap_apply, totDTo_apply, totDCech_zero,
      totDCech_succ, totDCoef_zero, totDCoef_succ, map_add, map_zsmul, add_zero, zero_add,
      map_zero, homotopy_zero, sort_zero, smul_zero, ← homotopy_cochainMap]
  · exact eq_sub_iff_add_eq.mp (homotopy_identity U (P.X 0) q (x ⟨(q + 1, 0), hpa⟩))
  · have key := homotopy_identity U (P.X (b + 1)) q (x ⟨(q + 1, b + 1), hpa⟩)
    rw [eq_sub_iff_add_eq] at key
    conv_rhs => rw [← key]
    simp only [pow_succ, mul_neg, mul_one, neg_smul]
    abel

/-- **The sorting projection** of the total Čech complex, a map of complexes. -/
def totSortHom : cechTot U P ⟶ cechTot U P where
  f n := ModuleCat.ofHom (totSort U P n)
  comm' := by
    rintro n _ rfl
    ext x : 2
    revert x
    intro (x : TotX U P n)
    change ((cechTot U P).d n (n + 1)).hom (totSort U P n x) =
      totSort U P (n + 1) (((cechTot U P).d n (n + 1)).hom x)
    rw [cechTot_d_apply, cechTot_d_apply]
    exact (totSort_totDTo U P n (n + 1) rfl x).symm

/-- The sorting projection of the total Čech complex is idempotent. -/
theorem totSortHom_idempotent : totSortHom U P ≫ totSortHom U P = totSortHom U P := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : TotX U P n) => ?_)
  funext i
  exact sort_sort U _ _ _

/-- **The sorting projection of the total Čech complex is homotopic to the identity.** -/
def totHomotopy : Homotopy (𝟙 (cechTot U P)) (totSortHom U P) where
  hom i j := if h : j + 1 = i then ModuleCat.ofHom (totHomotopyMap U P i j h) else 0
  zero i j hij := dite_eq_right hij
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1),
      dite_eq_left rfl, dite_eq_left (sub_add_cancel i 1)]
    ext x : 2
    revert x
    intro (x : TotX U P i)
    change x = totHomotopyMap U P (i + 1) i rfl (((cechTot U P).d i (i + 1)).hom x) +
      ((cechTot U P).d (i - 1) i).hom (totHomotopyMap U P i (i - 1) (sub_add_cancel i 1) x) +
        totSort U P i x
    rw [cechTot_d_apply' U P rfl, cechTot_d_apply' U P (sub_add_cancel i 1)]
    exact (totHomotopy_identity U P (i - 1) i (i + 1) (sub_add_cancel i 1) rfl x).symm

end CochainSorting

/-- **The total Čech complex of a finite cover is K-flat** when the complex of presheaves is
bounded above and its values on the Čech intersections are flat: the sorting projection is an
idempotent endomorphism homotopic to the identity which vanishes in degrees `> #ι + b`. -/
theorem kFlat_cechTot [Finite ι] {R : Type w} [CommRing R]
    (P : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{w} R) ℕ) (b : ℕ)
    (hb : ∀ a, b < a → ∀ {m : ℕ} (t : Fin (m + 1) → ι),
      Subsingleton ((P.X a).obj (op (inter U t))))
    (hflat : ∀ a {m : ℕ} (t : Fin (m + 1) → ι), Module.Flat R ((P.X a).obj (op (inter U t)))) :
    CochainComplex.KFlat.{w, w} (cechTot U P) := by
  classical
  let := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  refine AlgebraicGeometry.kFlat_of_bounded_idempotent (cechTot U P)
    (CochainSorting.totSortHom U P) (CochainSorting.totSortHom_idempotent U P)
    (CochainSorting.totHomotopy U P).symm (Nat.card ι + b) ?_ ?_
  · intro n hn
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : TotX U P n) => ?_)
    funext ⟨⟨p, a⟩, hpa⟩
    change CochainSorting.sort U (P.X a) p (x ⟨(p, a), hpa⟩) = 0
    by_cases hp : Nat.card ι ≤ p
    · exact CochainSorting.sort_eq_zero U _ p hp _
    · exact funext fun t => (hb a (by omega) t).allEq _ _
  · intro n
    have := finite_totIndex n
    have (i : TotIndex n) : Module.Flat R (Cochain U (P.X i.1.2) i.1.1) := by
      have (t : Fin (i.1.1 + 1) → ι) := hflat i.1.2 t
      exact Stacks.Cech.flat_pi_of_finite _
    exact Stacks.Cech.flat_pi_of_finite _

end

end Stacks.CategoryTheory.CechComplex

end
