module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.SetTheory.Cardinal.Finite
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups

/-!
# A chain homotopy for the ordered Čech comparison

Let `U : I → Opens X` be a family of opens of a topological space indexed by a linearly ordered
type, and `F` a presheaf of abelian groups on `X`. The composite `c ∘ π` of the projection
`CechCochains.pi` onto ordered cochains with the comparison `CechCochains.c` is homotopic to the
identity on Čech cochains. The homotopy is built on chains: over an open `V`, the free abelian
group on tuples whose intersection contains `V`, with face and boundary maps, the signed sorting
projection and the cone on an index `x` with `V ≤ U x`.

## Main definitions

* `SupportedChain`: The free abelian group on the tuples of indices supported over `V`.
* `boundary`: The alternating sum of faces.
* `projection`: The signed sorting projection.
* `cone`: Prepending an index whose open contains `V`.
* `chainHomotopy`: A homotopy between the sorting projection and the identity on chains.
* `cochainHomotopy`: The induced homotopy on Čech cochains.

## Main results

* `chainHomotopy_identity`: `∂ h + h ∂ = id - projection` in positive degree.
* `cochainHomotopy_identity`: `h d + d h = id - c ∘ π` in positive degree.
* `comparison_zero`: In degree `0`, `c (π s) = s`.
* `projection_eq_zero`: The sorting projection vanishes in degrees at least the cardinality of
  `I`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.Cech.ChainHomotopy

universe u v w

variable {X : TopCat.{u}} {I : Type v} [LinearOrder I]
  (U : I → Opens X) (F : TopCat.Presheaf Ab.{w} X)

/-- The tuples `t : Fin (p + 1) → I` whose intersection `⋂ₖ U (t k)` contains `V`. -/
abbrev SupportedTuple (U : I → Opens X) (V : Opens X) (p : ℕ) :=
  {t : Fin (p + 1) → I // V ≤ CechCochains.inter U t}

/-- The chains of degree `p` supported over `V`: the free abelian group on the tuples of length
`p + 1` whose intersection contains `V`. -/
abbrev SupportedChain (U : I → Opens X) (V : Opens X) (p : ℕ) :=
  FreeAbelianGroup (SupportedTuple U V p)

/-- The `j`-th face of a supported tuple: the tuple with its `j`-th entry omitted. -/
def face {V : Opens X} {p : ℕ} (t : SupportedTuple U V (p + 1))
    (j : Fin (p + 2)) : SupportedTuple U V p :=
  ⟨t.1 ∘ j.succAbove, t.2.trans (CechCochains.inter_le_omit U t.1 j)⟩

/-- The boundary map on supported chains, `∂ t = ∑ⱼ (-1) ^ j • face t j`. -/
def boundary (V : Opens X) (p : ℕ) :
    SupportedChain U V (p + 1) →+ SupportedChain U V p :=
  FreeAbelianGroup.lift fun t =>
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • FreeAbelianGroup.of (face U t j)

/-- The signed sorting projection on supported chains: an injective tuple `t` is sent to
`sgn σ • (t ∘ σ)`, where `σ = Tuple.sort t`, and a tuple with a repeated index to `0`. -/
noncomputable def projection (V : Opens X) (p : ℕ) :
    SupportedChain U V p →+ SupportedChain U V p :=
  FreeAbelianGroup.lift fun t =>
    if Function.Injective t.1 then
      (Equiv.Perm.sign (Tuple.sort t.1) : ℤ) • FreeAbelianGroup.of
        ⟨t.1 ∘ Tuple.sort t.1, by simpa only [CechCochains.inter_comp_perm] using t.2⟩
    else 0

/-- For `V ≤ W`, the map from chains supported over `W` to chains supported over `V` that is the
identity on underlying tuples. -/
def chainMap {V W : Opens X} (h : V ≤ W) (p : ℕ) :
    SupportedChain U W p →+ SupportedChain U V p :=
  FreeAbelianGroup.lift fun t => FreeAbelianGroup.of ⟨t.1, h.trans t.2⟩

/-- The evaluation of a cochain `s` on chains supported over `V`: a tuple `t` is sent to the
restriction of `s t` to `V`. -/
def chainEval (V : Opens X) (p : ℕ) (s : CechCochains.Cochain U F p) :
    SupportedChain U V p →+ F.obj (op V) :=
  FreeAbelianGroup.lift fun t => CechCochains.restr F t.2 (s t.1)

/-- The presheaf whose sections over `W` are the functions from proofs of `V ≤ W` to `A`, with
restriction given by precomposition. -/
def probePresheaf (V : Opens X) (A : Type*) [AddCommGroup A] :
    TopCat.Presheaf Ab X where
  obj W := AddCommGrpCat.of (PLift (V ≤ W.unop) → A)
  map f := AddCommGrpCat.ofHom
    { toFun := fun s h => s ⟨h.down.trans (leOfHom f.unop)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The cochain with values in `probePresheaf V (SupportedChain U V p)` whose value at a tuple `t`
is the generator `t` of `SupportedChain U V p`, wherever `t` is supported over `V`. -/
def probeCochain (V : Opens X) (p : ℕ) :
    CechCochains.Cochain U (probePresheaf (X := X) V (SupportedChain U V p)) p :=
  fun t h => FreeAbelianGroup.of ⟨t, h.down⟩

/-- Two composites of additive maps out of a free abelian group agree if they agree on
generators. -/
private theorem comp_apply_eq_of_forall_of {α B C M : Type*} [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup M] {φ : B →+ M} {ψ : FreeAbelianGroup α →+ B} {χ : C →+ M}
    {ω : FreeAbelianGroup α →+ C}
    (h : ∀ t, φ (ψ (FreeAbelianGroup.of t)) = χ (ω (FreeAbelianGroup.of t)))
    {a : FreeAbelianGroup α} : φ (ψ a) = χ (ω a) :=
  DFunLike.congr_fun (FreeAbelianGroup.lift_ext (φ.comp ψ) (χ.comp ω) h) a

omit [LinearOrder I] in
/-- Evaluating a cochain on a boundary is evaluating its Čech differential:
`⟨s, ∂ a⟩ = ⟨d s, a⟩`. -/
theorem eval_boundary (V : Opens X) (p : ℕ) (s : CechCochains.Cochain U F p)
    (a : SupportedChain U V (p + 1)) :
    chainEval U F V p s (boundary U V p a) =
      chainEval U F V (p + 1) (CechCochains.cechD U F p s) a := by
  suffices (chainEval U F V p s).comp (boundary U V p) =
      chainEval U F V (p + 1) (CechCochains.cechD U F p s) from
    DFunLike.congr_fun this a
  apply FreeAbelianGroup.lift_ext
  intro t
  simp only [AddMonoidHom.comp_apply, boundary, chainEval, FreeAbelianGroup.lift_apply_of,
    map_sum, map_zsmul, CechCochains.cechD, AddMonoidHom.coe_mk]
  change (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    CechCochains.restr F (face U t j).2 (s (face U t j).1)) =
    CechCochains.restr F t.2 (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      CechCochains.restr F (CechCochains.inter_le_omit U t.1 j) (s (t.1 ∘ j.succAbove)))
  rw [map_sum]
  simp only [map_zsmul]
  apply Finset.sum_congr rfl
  intro j _
  rw [CechCochains.restr_restr]
  rfl

/-- Evaluating a cochain on the sorting projection of a chain is evaluating `c (π s)`:
`⟨s, projection a⟩ = ⟨c (π s), a⟩`. -/
theorem eval_projection (V : Opens X) (p : ℕ) (s : CechCochains.Cochain U F p)
    (a : SupportedChain U V p) :
    chainEval U F V p s (projection U V p a) =
      chainEval U F V p (CechCochains.c U F p (CechCochains.pi U F p s)) a := by
  classical
  suffices (chainEval U F V p s).comp (projection U V p) =
      chainEval U F V p (CechCochains.c U F p (CechCochains.pi U F p s)) from
    DFunLike.congr_fun this a
  apply FreeAbelianGroup.lift_ext
  intro t
  simp only [AddMonoidHom.comp_apply, projection, chainEval, FreeAbelianGroup.lift_apply_of]
  by_cases ht : Function.Injective t.1
  · rw [ite_eq_left ht, map_zsmul, FreeAbelianGroup.lift_apply_of,
      CechCochains.c_apply_injective _ _ _ _ ht, map_zsmul]
    congr 1
    change CechCochains.restr F _ (s _) = CechCochains.restr F _ (F.map _ (s _))
    simp only [CechCochains.restr, ← CategoryTheory.comp_apply, ← F.map_comp]
    rfl
  · rw [ite_eq_right ht, map_zero, CechCochains.c_apply_not_injective _ _ _ _ ht, map_zero]

omit [LinearOrder I] in
/-- Evaluating the probe cochain on a chain `a` supported over `V`, at `V` itself, returns `a`. -/
theorem eval_probe (V : Opens X) (p : ℕ) (a : SupportedChain U V p) :
    chainEval U (probePresheaf (X := X) V (SupportedChain U V p)) V p
      (probeCochain U V p) a ⟨le_rfl⟩ = a := by
  have h : (Pi.evalAddMonoidHom _ (PLift.up (le_refl V))).comp
      (chainEval U (probePresheaf (X := X) V (SupportedChain U V p)) V p
        (probeCochain U V p)) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro t
    rfl
  exact DFunLike.congr_fun h a

omit [LinearOrder I] in
/-- The boundary of a boundary is zero. -/
theorem boundary_boundary (V : Opens X) (p : ℕ)
    (a : SupportedChain U V (p + 2)) :
    boundary U V p (boundary U V (p + 1) a) = 0 := by
  rw [← eval_probe U V p (boundary U V p (boundary U V (p + 1) a)), eval_boundary, eval_boundary,
    CechCochains.cechD_cechD]
  have : chainEval U (probePresheaf (X := X) V (SupportedChain U V p)) V (p + 2) 0 = 0 := by
    apply FreeAbelianGroup.lift_ext
    intro t
    simp [chainEval, CechCochains.Cochain.zero_apply]
  rw [this]
  rfl

/-- The boundary map commutes with the sorting projection. -/
theorem boundary_projection (V : Opens X) (p : ℕ)
    (a : SupportedChain U V (p + 1)) :
    boundary U V p (projection U V (p + 1) a) =
      projection U V p (boundary U V p a) := by
  rw [← eval_probe U V p (boundary U V p _), eval_boundary, eval_projection,
    ← eval_probe U V p (projection U V p _), eval_projection, eval_boundary]
  rw [← CechCochains.c_chainMap U _ p _]
  rfl

/-- In degree `0` the sorting projection is the identity. -/
theorem projection_zero (V : Opens X) (a : SupportedChain U V 0) :
    projection U V 0 a = a := by
  suffices projection U V 0 = AddMonoidHom.id _ from DFunLike.congr_fun this a
  apply FreeAbelianGroup.lift_ext
  intro t
  have hi : Function.Injective t.1 := fun _ _ _ => Fin.ext (by omega)
  have hs : Tuple.sort t.1 = 1 := by
    apply Equiv.ext
    intro j
    apply Fin.ext
    omega
  simp [projection, hi, hs]

/-- The tuple `(x, t₀, …, tₚ)` obtained from a supported tuple `t` by prepending an index `x`
with `V ≤ U x`. -/
def coneTuple {V : Opens X} (x : I) (hx : V ≤ U x) {p : ℕ}
    (t : SupportedTuple U V p) : SupportedTuple U V (p + 1) :=
  ⟨Fin.cons x t.1, le_iInf fun j => Fin.cases hx
    (fun k => t.2.trans (iInf_le _ k)) j⟩

/-- The cone operator on supported chains with apex `x`, sending a tuple `t` to `coneTuple x t`. -/
def cone {V : Opens X} (x : I) (hx : V ≤ U x) (p : ℕ) :
    SupportedChain U V p →+ SupportedChain U V (p + 1) :=
  FreeAbelianGroup.lift fun t => FreeAbelianGroup.of (coneTuple U x hx t)

omit [LinearOrder I] in
/-- The `0`-th face of `coneTuple x t` is `t`. -/
theorem face_cone_zero {V : Opens X} (x : I) (hx : V ≤ U x) {p : ℕ}
    (t : SupportedTuple U V (p + 1)) :
    face U (coneTuple U x hx t) 0 = t := by
  apply Subtype.ext; funext j; simp [face, coneTuple]

omit [LinearOrder I] in
/-- The `(j + 1)`-th face of `coneTuple x t` is the cone on the `j`-th face of `t`. -/
theorem face_cone_succ {V : Opens X} (x : I) (hx : V ≤ U x) {p : ℕ}
    (t : SupportedTuple U V (p + 1)) (j : Fin (p + 2)) :
    face U (coneTuple U x hx t) j.succ = coneTuple U x hx (face U t j) := by
  apply Subtype.ext; exact Fin.cons_comp_succ_succAbove x t.1 j

omit [LinearOrder I] in
/-- In positive degree, `∂ (cone x a) = a - cone x (∂ a)`. -/
theorem boundary_cone {V : Opens X} (x : I) (hx : V ≤ U x) (p : ℕ)
    (a : SupportedChain U V (p + 1)) :
    boundary U V (p + 1) (cone U x hx (p + 1) a) =
      a - cone U x hx p (boundary U V p a) := by
  suffices (boundary U V (p + 1)).comp (cone U x hx (p + 1)) =
      AddMonoidHom.id _ - (cone U x hx p).comp (boundary U V p) from
    DFunLike.congr_fun this a
  apply FreeAbelianGroup.lift_ext
  intro t
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    cone, boundary, FreeAbelianGroup.lift_apply_of, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, face_cone_zero, face_cone_succ,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]

omit [LinearOrder I] in
/-- `chainMap` commutes with the boundary map. -/
theorem chainMap_boundary {V W : Opens X} (h : V ≤ W) (p : ℕ)
    (a : SupportedChain U W (p + 1)) :
    chainMap U h p (boundary U W p a) =
      boundary U V p (chainMap U h (p + 1) a) := by
  apply comp_apply_eq_of_forall_of
  intro t
  simp only [chainMap, boundary, FreeAbelianGroup.lift_apply_of,
    map_sum, map_zsmul]
  rfl

/-- `chainMap` commutes with the sorting projection. -/
theorem chainMap_projection {V W : Opens X} (h : V ≤ W) (p : ℕ)
    (a : SupportedChain U W p) :
    chainMap U h p (projection U W p a) =
      projection U V p (chainMap U h p a) := by
  classical
  apply comp_apply_eq_of_forall_of
  intro t
  simp only [chainMap, projection, FreeAbelianGroup.lift_apply_of]
  split_ifs <;> simp only [map_zsmul, map_zero, FreeAbelianGroup.lift_apply_of]

omit [LinearOrder I] in
/-- `chainMap` commutes with the cone operator. -/
theorem chainMap_cone {V W : Opens X} (h : V ≤ W) (x : I) (hx : W ≤ U x)
    (p : ℕ) (a : SupportedChain U W p) :
    chainMap U h (p + 1) (cone U x hx p a) =
      cone U x (h.trans hx) p (chainMap U h p a) := by
  apply comp_apply_eq_of_forall_of
  intro t
  simp only [chainMap, cone, FreeAbelianGroup.lift_apply_of]
  rfl

omit [LinearOrder I] in
/-- For `V ≤ W`, evaluating a cochain on `chainMap h a` over `V` is restricting to `V` its
evaluation on `a` over `W`. -/
theorem eval_chainMap {V W : Opens X} (h : V ≤ W) (p : ℕ)
    (s : CechCochains.Cochain U F p) (a : SupportedChain U W p) :
    chainEval U F V p s (chainMap U h p a) =
      CechCochains.restr F h (chainEval U F W p s a) := by
  apply comp_apply_eq_of_forall_of
  intro t
  simp only [chainMap, chainEval, FreeAbelianGroup.lift_apply_of,
    CechCochains.restr_restr]

/-- A chain homotopy between the sorting projection and the identity on supported chains. It is
zero in degree `0`, and in degree `p + 1` sends a tuple `t` to the cone with apex `t 0` on
`t - projection t - chainHomotopy (∂ t)`. -/
noncomputable def chainHomotopy (V : Opens X) :
    (p : ℕ) → (SupportedChain U V p →+ SupportedChain U V (p + 1))
  | 0 => 0
  | p + 1 => FreeAbelianGroup.lift fun t =>
      cone U (t.1 0) (t.2.trans (iInf_le _ 0)) (p + 1)
        (FreeAbelianGroup.of t - projection U V (p + 1) (FreeAbelianGroup.of t) -
          chainHomotopy V p (boundary U V p (FreeAbelianGroup.of t)))

omit [LinearOrder I] in
/-- `chainMap` sends the generator `t` to the generator with the same underlying tuple. -/
theorem chainMap_of {V W : Opens X} (h : V ≤ W) (p : ℕ)
    (t : SupportedTuple U W p) :
    chainMap U h p (FreeAbelianGroup.of t) = FreeAbelianGroup.of ⟨t.1, h.trans t.2⟩ :=
  FreeAbelianGroup.lift_apply_of _ _

/-- In degree `p + 1`, `chainHomotopy` sends a generator `t` to the cone with apex `t 0` on
`t - projection t - chainHomotopy (∂ t)`. -/
theorem chainHomotopy_succ_of (V : Opens X) (p : ℕ)
    (t : SupportedTuple U V (p + 1)) :
    chainHomotopy U V (p + 1) (FreeAbelianGroup.of t) =
      cone U (t.1 0) (t.2.trans (iInf_le _ 0)) (p + 1)
        (FreeAbelianGroup.of t - projection U V (p + 1) (FreeAbelianGroup.of t) -
          chainHomotopy U V p (boundary U V p (FreeAbelianGroup.of t))) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- `chainMap` commutes with `chainHomotopy`. -/
theorem chainMap_homotopy {V W : Opens X} (h : V ≤ W) (p : ℕ)
    (a : SupportedChain U W p) :
    chainMap U h (p + 1) (chainHomotopy U W p a) =
      chainHomotopy U V p (chainMap U h p a) := by
  induction p with
  | zero => simp only [chainHomotopy, AddMonoidHom.zero_apply, map_zero]
  | succ p ih =>
    apply comp_apply_eq_of_forall_of
    intro t
    simp only [chainMap_of, chainHomotopy_succ_of]
    rw [chainMap_cone]
    simp only [map_sub, chainMap_projection, ih, chainMap_boundary, chainMap_of]

/-- `chainHomotopy` is a homotopy between the sorting projection and the identity: in positive
degree, `∂ h + h ∂ = id - projection`. -/
theorem chainHomotopy_identity (V : Opens X) (p : ℕ)
    (a : SupportedChain U V (p + 1)) :
    boundary U V (p + 1) (chainHomotopy U V (p + 1) a) +
        chainHomotopy U V p (boundary U V p a) =
      a - projection U V (p + 1) a := by
  induction p with
  | zero =>
    suffices (boundary U V 1).comp (chainHomotopy U V 1) +
        (chainHomotopy U V 0).comp (boundary U V 0) =
        AddMonoidHom.id _ - projection U V 1 from DFunLike.congr_fun this a
    apply FreeAbelianGroup.lift_ext
    intro t
    simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, chainHomotopy, FreeAbelianGroup.lift_apply_of,
      AddMonoidHom.zero_apply, sub_zero, add_zero]
    have hc : boundary U V 0 (FreeAbelianGroup.of t -
        projection U V 1 (FreeAbelianGroup.of t)) = 0 := by
      rw [map_sub, boundary_projection, projection_zero, sub_self]
    rw [boundary_cone, hc, map_zero, sub_zero]
  | succ p ih =>
    suffices (boundary U V (p + 2)).comp (chainHomotopy U V (p + 2)) +
        (chainHomotopy U V (p + 1)).comp (boundary U V (p + 1)) =
        AddMonoidHom.id _ - projection U V (p + 2) from DFunLike.congr_fun this a
    apply FreeAbelianGroup.lift_ext
    intro t
    simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, chainHomotopy_succ_of]
    have hi := ih (boundary U V (p + 1) (FreeAbelianGroup.of t))
    rw [boundary_boundary, map_zero, add_zero] at hi
    have hc : boundary U V (p + 1)
        (FreeAbelianGroup.of t - projection U V (p + 2) (FreeAbelianGroup.of t) -
          chainHomotopy U V (p + 1) (boundary U V (p + 1) (FreeAbelianGroup.of t))) = 0 := by
      simp only [map_sub, boundary_projection, hi, sub_self]
    rw [boundary_cone, hc, map_zero, sub_zero]
    abel

omit [LinearOrder I] in
/-- Evaluating a cochain `s` on the generator `t` gives the restriction of `s t` to `V`. -/
theorem chainEval_of (V : Opens X) (p : ℕ) (s : CechCochains.Cochain U F p)
    (t : SupportedTuple U V p) :
    chainEval U F V p s (FreeAbelianGroup.of t) = CechCochains.restr F t.2 (s t.1) :=
  FreeAbelianGroup.lift_apply_of _ _

omit [LinearOrder I] in
/-- Evaluating a cochain `s` over the intersection `U_t` on the generator `t` gives `s t`. -/
theorem chainEval_self (p : ℕ) (s : CechCochains.Cochain U F p)
    (t : Fin (p + 1) → I) :
    chainEval U F (CechCochains.inter U t) p s (FreeAbelianGroup.of ⟨t, le_rfl⟩) = s t :=
  by simp [chainEval_of, CechCochains.restr]

/-- The evaluation `chainEval` of cochains on chains supported over `V`, as a group homomorphism
in the cochain. -/
def chainPairing (V : Opens X) (p : ℕ) :
    CechCochains.Cochain U F p →+ (SupportedChain U V p →+ F.obj (op V)) where
  toFun := chainEval U F V p
  map_zero' := by
    apply FreeAbelianGroup.lift_ext
    intro t
    simp only [chainEval_of, CechCochains.Cochain.zero_apply, map_zero, AddMonoidHom.zero_apply]
  map_add' s t := by
    apply FreeAbelianGroup.lift_ext
    intro i
    simp only [AddMonoidHom.add_apply, chainEval_of, CechCochains.Cochain.add_apply, map_add]

/-- The homotopy `Č^{p+1} → Č^p` on Čech cochains dual to `chainHomotopy`: its value at a tuple
`t` is the evaluation of `s`, over `U_t`, on `chainHomotopy t`. -/
noncomputable def cochainHomotopy (p : ℕ) :
    CechCochains.Cochain U F (p + 1) →+ CechCochains.Cochain U F p :=
  AddMonoidHom.pi fun t =>
    (AddMonoidHom.eval (chainHomotopy U (CechCochains.inter U t) p
      (FreeAbelianGroup.of ⟨t, le_rfl⟩))).comp
        (chainPairing U F (CechCochains.inter U t) (p + 1))

/-- The value of `cochainHomotopy s` at `t` is the evaluation of `s`, over `U_t`, on
`chainHomotopy t`. -/
theorem cochainHomotopy_apply (p : ℕ) (s : CechCochains.Cochain U F (p + 1))
    (t : Fin (p + 1) → I) :
    cochainHomotopy U F p s t =
      chainEval U F (CechCochains.inter U t) (p + 1) s
        (chainHomotopy U (CechCochains.inter U t) p (FreeAbelianGroup.of ⟨t, le_rfl⟩)) := rfl

/-- The cochain homotopy `Č^1 → Č^0` is zero. -/
theorem cochainHomotopy_zero (s : CechCochains.Cochain U F 1) :
    cochainHomotopy U F 0 s = 0 := by
  funext t; rw [cochainHomotopy_apply]; exact map_zero _

/-- Evaluating `cochainHomotopy s` on a chain `a` is evaluating `s` on `chainHomotopy a`. -/
theorem eval_homotopy (V : Opens X) (p : ℕ)
    (s : CechCochains.Cochain U F (p + 1)) (a : SupportedChain U V p) :
    chainEval U F V p (cochainHomotopy U F p s) a =
      chainEval U F V (p + 1) s (chainHomotopy U V p a) := by
  suffices chainEval U F V p (cochainHomotopy U F p s) =
      (chainEval U F V (p + 1) s).comp (chainHomotopy U V p) from
    DFunLike.congr_fun this a
  apply FreeAbelianGroup.lift_ext
  intro t
  simp only [chainEval_of, AddMonoidHom.comp_apply]
  rw [cochainHomotopy_apply, ← eval_chainMap, chainMap_homotopy]
  rfl

/-- `cochainHomotopy` is a homotopy between `c ∘ π` and the identity on Čech cochains: in
positive degree, `h d + d h = id - c ∘ π`. -/
theorem cochainHomotopy_identity (p : ℕ) (s : CechCochains.Cochain U F (p + 1)) :
    cochainHomotopy U F (p + 1) (CechCochains.cechD U F (p + 1) s) +
        CechCochains.cechD U F p (cochainHomotopy U F p s) =
      s - CechCochains.c U F (p + 1) (CechCochains.pi U F (p + 1) s) := by
  funext t
  have h := congrArg (chainEval U F (CechCochains.inter U t) (p + 1) s)
    (chainHomotopy_identity U (CechCochains.inter U t) p
      (FreeAbelianGroup.of ⟨t, le_rfl⟩))
  simp only [map_add, map_sub, eval_boundary, ← eval_homotopy, eval_projection,
    chainEval_self] at h
  exact h

/-- In degree `0`, `c (π s) = s` for every Čech cochain `s`. -/
theorem comparison_zero (s : CechCochains.Cochain U F 0) :
    CechCochains.c U F 0 (CechCochains.pi U F 0 s) = s := by
  funext t
  have h := eval_projection U F (CechCochains.inter U t) 0 s
    (FreeAbelianGroup.of ⟨t, le_rfl⟩)
  rw [projection_zero] at h
  simpa only [chainEval, FreeAbelianGroup.lift_apply_of, CechCochains.restr,
    homOfLE_refl, op_id, F.map_id, AddCommGrpCat.hom_id, AddMonoidHom.id_apply] using h.symm

/-- The sorting projection is idempotent. -/
theorem projection_idempotent (V : Opens X) (p : ℕ)
    (a : SupportedChain U V p) :
    projection U V p (projection U V p a) = projection U V p a := by
  rw [← eval_probe U V p (projection U V p _), eval_projection, eval_projection,
    CechCochains.pi_c, ← eval_projection, eval_probe]

/-- If `I` is finite with at most `p` elements, the sorting projection vanishes in degree `p`. -/
theorem projection_eq_zero [Finite I] (V : Opens X) (p : ℕ)
    (hp : Nat.card I ≤ p) : projection U V p = 0 := by
  classical
  apply FreeAbelianGroup.lift_ext
  intro tuple
  have not_injective : ¬ Function.Injective tuple.1 := by
    intro injective
    have inequality := Nat.card_le_card_of_injective tuple.1 injective
    rw [Nat.card_fin] at inequality
    omega
  simp [projection, not_injective]

end Stacks.Cech.ChainHomotopy

end
