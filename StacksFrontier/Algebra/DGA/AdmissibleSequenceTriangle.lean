module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Analysis.Normed.Ring.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The triangle associated to an admissible short exact sequence

Let `R` be a commutative ring and `(A, d)` a differential graded algebra over `R`. For a
differential graded `A`-module `N`, the shift `N[1]` has `N[1]^n = N^{n+1}`, differential
`d_{N[1]} = -d_N`, and `A`-action twisted by the Koszul sign `(-1)^{|a|}`.

Given an admissible short exact sequence `0 → K → L → M → 0` of differential graded
`A`-modules and a pair of compatible splittings `(s, π)`, the connecting map
`δ = π ∘ d_L ∘ s : M → K[1]` is a homomorphism of differential graded `A`-modules, and gives
a triangle `K → L → M → K[1]`. For two pairs of compatible splittings the connecting maps are
homotopic, so the two associated triangles are isomorphic in the homotopy category
`K(Mod_{(A,d)})` via the identity morphisms of `K`, `L` and `M`.

## Main definitions

* `DGAlgebra`: a differential graded algebra over `R`.
* `DGModule`: a differential graded module over a differential graded algebra.
* `DGModule.shift`: the shift `N[1]` of a differential graded module.
* `DGModule.Homotopy`: a homotopy between two morphisms of differential graded modules.
* `DGModule.AdmissibleSES`: an admissible short exact sequence of differential graded modules.
* `DGModule.AdmissibleSES.CompatibleSplittings`: a pair of compatible splittings of an
  admissible short exact sequence.
* `DGModule.AdmissibleSES.CompatibleSplittings.connectingMap`: the connecting map
  `δ = π ∘ d_L ∘ s : M ⟶ K[1]`.
* `DGModule.AdmissibleSES.CompatibleSplittings.associatedTriangle`: the triangle
  `K → L → M → K[1]`.

## Main results

* `DGModule.connectingMap_homotopic`: the connecting maps of two pairs of compatible
  splittings are homotopic.
* `DGModule.associatedTriangle_iso_of_compatibleSplittings`: the triangles associated to two
  pairs of compatible splittings are isomorphic in the homotopy category.

## Implementation notes

A graded `A`-module map of degree `k` commutes with the `A`-action up to the Koszul sign
`(-1)^{|a| k}`, that is `f^{i+n}(a · x) = (-1)^{|a| k} a · f^n(x)`. For `k = 0` this is
ordinary `A`-linearity; a homotopy is a map of degree `-1`, so it satisfies
`H(a · x) = (-1)^{|a|} a · H(x)`. The index bookkeeping of `ℤ`-graded objects is handled by
`gcast`.

## References

* [Stacks Project, Tag 09K6](https://stacks.math.columbia.edu/tag/09K6)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace DifferentialGradedModule.AdmissibleTriangle

universe u
variable {R : Type u} [CommRing R]

/-- The `R`-linear map `obj m → obj n` transporting an element of a graded component along a
degree equality `m = n`. -/
def gcast {obj : ℤ → Type u} [∀ n, AddCommGroup (obj n)] [∀ n, Module R (obj n)]
    {m n : ℤ} (h : m = n) : obj m →ₗ[R] obj n := h ▸ LinearMap.id

/-- Transport along `m = m` is the identity. -/
@[simp] theorem gcast_rfl {obj : ℤ → Type u} [∀ n, AddCommGroup (obj n)]
    [∀ n, Module R (obj n)] {m : ℤ} (h : m = m) (x : obj m) :
    gcast (R := R) (obj := obj) h x = x := by
  unfold gcast; simp

/-- A **differential graded `R`-algebra** `(A, d)` (Stacks Tag 09JK): a `ℤ`-graded family
of `R`-modules `A^n`, with an associative, unital graded multiplication
`A^i ⊗ A^j → A^{i+j}` (unit in degree `0`) and a degree `+1` differential `d` with
`d² = 0` satisfying the graded Leibniz rule `d(ab) = d(a)·b + (-1)^{|a|} a·d(b)`. -/
@[sga "6 VII 2.1"]
structure DGAlgebra (R : Type u) [CommRing R] where
  /-- the graded components `A^n`. -/
  obj : ℤ → Type u
  [addCommGroup : ∀ n, AddCommGroup (obj n)]
  [module : ∀ n, Module R (obj n)]
  /-- graded multiplication `A^i ⊗ A^j → A^{i+j}`. -/
  mul : ∀ i j, obj i →ₗ[R] obj j →ₗ[R] obj (i + j)
  /-- the multiplicative unit, in degree `0`. -/
  one : obj 0
  /-- the degree `+1` differential. -/
  d : ∀ n, obj n →ₗ[R] obj (n + 1)
  /-- `d² = 0`. -/
  d_comp_d : ∀ n (a : obj n), d (n + 1) (d n a) = 0
  /-- associativity `(ab)c = a(bc)`. -/
  mul_assoc : ∀ (i j k : ℤ) (a : obj i) (b : obj j) (c : obj k),
      gcast (R := R) (by ring) (mul (i + j) k (mul i j a b) c) = mul i (j + k) a (mul j k b c)
  /-- left unit `1·a = a`. -/
  one_mul : ∀ (i : ℤ) (a : obj i), gcast (R := R) (by ring) (mul 0 i one a) = a
  /-- right unit `a·1 = a`. -/
  mul_one : ∀ (i : ℤ) (a : obj i), gcast (R := R) (by ring) (mul i 0 a one) = a
  /-- graded Leibniz rule `d(ab) = d(a)·b + (-1)^{|a|} a·d(b)`. -/
  d_mul : ∀ (i j : ℤ) (a : obj i) (b : obj j),
      d (i + j) (mul i j a b)
        = gcast (R := R) (by ring) (mul (i + 1) j (d i a) b)
          + (Int.negOnePow i) • gcast (R := R) (by ring) (mul i (j + 1) a (d j b))

attribute [instance] DGAlgebra.addCommGroup DGAlgebra.module

variable (A : DGAlgebra R)

/-- A **differential graded `A`-module** `N` (Stacks Tag 09JK): a `ℤ`-graded family of
`R`-modules `N^n` with a graded `A`-action `A^i ⊗ N^j → N^{i+j}` that is associative and
unital, and a degree `+1` differential `d` with `d² = 0` satisfying the graded Leibniz
rule `d(a·x) = d(a)·x + (-1)^{|a|} a·d(x)` (compatibility of the differential with the
`A`-action). -/
structure DGModule where
  /-- the graded components `N^n`. -/
  obj : ℤ → Type u
  [addCommGroup : ∀ n, AddCommGroup (obj n)]
  [module : ∀ n, Module R (obj n)]
  /-- graded `A`-action `A^i ⊗ N^j → N^{i+j}`. -/
  smul : ∀ i j, A.obj i →ₗ[R] obj j →ₗ[R] obj (i + j)
  /-- the degree `+1` differential. -/
  d : ∀ n, obj n →ₗ[R] obj (n + 1)
  /-- `d² = 0`. -/
  d_comp_d : ∀ n (x : obj n), d (n + 1) (d n x) = 0
  /-- action associativity `(ab)·x = a·(b·x)`. -/
  mul_smul : ∀ (i j k : ℤ) (a : A.obj i) (b : A.obj j) (x : obj k),
      gcast (R := R) (by ring) (smul (i + j) k (A.mul i j a b) x) = smul i (j + k) a (smul j k b x)
  /-- unit action `1·x = x`. -/
  one_smul : ∀ (k : ℤ) (x : obj k), gcast (R := R) (by ring) (smul 0 k A.one x) = x
  /-- graded Leibniz rule `d(a·x) = d(a)·x + (-1)^{|a|} a·d(x)`. -/
  d_smul : ∀ (i k : ℤ) (a : A.obj i) (x : obj k),
      d (i + k) (smul i k a x)
        = gcast (R := R) (by ring) (smul (i + 1) k (A.d i a) x)
          + (Int.negOnePow i) • gcast (R := R) (by ring) (smul i (k + 1) a (d k x))

attribute [instance] DGModule.addCommGroup DGModule.module

/-- Transport along `m = n` followed by transport along `n = p` is transport along `m = p`. -/
theorem gcast_gcast {obj : ℤ → Type u} [∀ n, AddCommGroup (obj n)] [∀ n, Module R (obj n)]
    {m n p : ℤ} (h1 : m = n) (h2 : n = p) (x : obj m) :
    gcast (R:=R) (obj:=obj) h2 (gcast (R:=R) (obj:=obj) h1 x) = gcast (R:=R) (obj:=obj) (h1.trans
        h2) x := by
  subst h1; subst h2; rfl

/-- Transport along `m = n` followed by transport along `n = p` is transport along any proof
of `m = p`. -/
theorem gcast_gcast' {obj : ℤ → Type u} [∀ n, AddCommGroup (obj n)] [∀ n, Module R (obj n)]
    {m n p : ℤ} (h1 : m = n) (h2 : n = p) (h3 : m = p) (x : obj m) :
    gcast (R:=R) (obj:=obj) h2 (gcast (R:=R) (obj:=obj) h1 x) = gcast (R:=R) (obj:=obj) h3 x := by
  subst h1; subst h2; rfl

/-- Transport along a degree equality commutes with the action of a unit of `ℤ`. -/
@[simp] theorem gcast_smul_negOnePow {obj : ℤ → Type u} [∀ n, AddCommGroup (obj n)] [∀ n, Module R
    (obj n)]
    {m n : ℤ} (h : m = n) (u : ℤˣ) (x : obj m) :
    gcast (R:=R) (obj:=obj) h (u • x) = u • gcast (R:=R) (obj:=obj) h x := by
  subst h; rfl

namespace DGModule
variable {A}

/-- Move a `gcast` of the codomain index through `N.smul`. -/
theorem gcast_smul_cod (N : DGModule A) {j j' : ℤ} (h : j = j') (i : ℤ)
    (a : A.obj i) (x : N.obj j) :
    gcast (R := R) (obj := N.obj) (show i + j = i + j' by rw [h]) (N.smul i j a x)
      = N.smul i j' a (gcast (R := R) (obj := N.obj) h x) := by
  subst h; rfl

/-- Move a `gcast` of the domain index through `N.smul` (the action degree). -/
theorem gcast_smul_dom (N : DGModule A) {i i' : ℤ} (h : i = i') (j : ℤ)
    (a : A.obj i) (x : N.obj j) :
    gcast (R := R) (obj := N.obj) (show i + j = i' + j by rw [h])
        (N.smul i j a x)
      = N.smul i' j (gcast (R := R) (obj := A.obj) h a) x := by
  subst h; rfl

/-- Move a `gcast` of the index through `N.d`. -/
theorem gcast_d_cod (N : DGModule A) {n n' : ℤ} (h : n = n') (x : N.obj n) :
    gcast (R := R) (obj := N.obj) (show n + 1 = n' + 1 by rw [h]) (N.d n x)
      = N.d n' (gcast (R := R) (obj := N.obj) h x) := by
  subst h; rfl

/-- Compose two `gcast`s on `N.obj` into one. -/
theorem gcast_gcast_obj (N : DGModule A) {m n p : ℤ} (h1 : m = n) (h2 : n = p) (h3 : m = p)
    (x : N.obj m) :
    gcast (R := R) (obj := N.obj) h2 (gcast (R := R) (obj := N.obj) h1 x)
      = gcast (R := R) (obj := N.obj) h3 x := by
  subst h1; subst h2; rfl

/-- A `gcast` is heterogeneously equal to its argument. -/
theorem gcast_heq {obj : ℤ → Type u} [∀ n, AddCommGroup (obj n)] [∀ n, Module R (obj n)]
    {m n : ℤ} (h : m = n) (x : obj m) : gcast (R := R) (obj := obj) h x ≍ x := by
  subst h; rfl

/-- The **shift** `N[1]` of a DG `A`-module `N` (Stacks Tag 09JK): the underlying graded
pieces are reindexed by `N[1]^n = N^{n+1}`, the differential is `d_{N[1]} = -d_N`, and the
`A`-action is twisted by the Koszul sign: `a ·_{N[1]} x = (-1)^{|a|} (a ·_N x)`. -/
def shift (N : DGModule A) : DGModule A where
  obj n := N.obj (n + 1)
  addCommGroup n := N.addCommGroup (n + 1)
  module n := N.module (n + 1)
  smul i j :=
    { toFun := fun a =>
        (Int.negOnePow i) •
          (gcast (R := R) (obj := N.obj) (show i + (j + 1) = (i + j) + 1 by ring)).comp
            (N.smul i (j + 1) a)
      map_add' := by intro a b; ext x; simp [map_add]
      map_smul' := by
        intro c a; ext x
        simp only [LinearMap.coe_comp, Function.comp_apply, map_smul, RingHom.id_apply,
          LinearMap.smul_apply]
        rw [smul_comm] }
  d n := -((N.d (n + 1)))
  d_comp_d := by intro n x; simp [N.d_comp_d]
  mul_smul := by
    intro i j k a b x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, gcast_smul_negOnePow]
    rw [LinearMap.CompatibleSMul.map_smul, gcast_smul_negOnePow]
    rw [← gcast_smul_cod N (show j + (k + 1) = j + k + 1 by ring) i a]
    rw [← N.mul_smul i j (k + 1) a b x]
    rw [Int.negOnePow_add, smul_smul]
    congr 1
    apply eq_of_heq
    refine HEq.trans (gcast_heq _ _) (HEq.trans (gcast_heq _ _) ?_)
    exact ((gcast_heq _ _).trans ((gcast_heq _ _).trans (gcast_heq _ _))).symm
  one_smul := by
    intro k x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      Int.negOnePow_zero, LinearMap.smul_apply, gcast_smul_negOnePow]
    rw [_root_.one_smul]
    apply eq_of_heq
    refine HEq.trans (gcast_heq _ _) ?_
    refine HEq.trans (gcast_heq _ _) ?_
    exact (gcast_heq _ _).symm.trans (heq_of_eq (N.one_smul (k + 1) x))
  d_smul := by
    intro i k a x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.neg_apply, map_neg, LinearMap.smul_apply]
    rw [LinearMap.CompatibleSMul.map_smul, ← gcast_d_cod N (show i + (k + 1) = i + k + 1 by ring),
      N.d_smul i (k + 1) a x, map_add, gcast_smul_negOnePow, smul_add, neg_add,
      Int.negOnePow_succ, gcast_smul_negOnePow, Units.neg_smul, gcast_smul_negOnePow, smul_neg,
      smul_smul, smul_smul]
    refine congrArg₂ (· + ·) ?_ ?_ <;>
    · rw [neg_inj]
      congr 1
      apply eq_of_heq
      refine HEq.trans (gcast_heq _ _) (HEq.trans (gcast_heq _ _) (HEq.symm ?_))
      exact HEq.trans (gcast_heq _ _) (gcast_heq _ _)

/-- `gcast` along a degree equality is injective. -/
theorem gcast_injective {obj : ℤ → Type u} [∀ n, AddCommGroup (obj n)] [∀ n, Module R (obj n)]
    {m n : ℤ} (h : m = n) : Function.Injective (gcast (R := R) (obj := obj) h) := by
  subst h
  intro x y hxy
  simpa using hxy

/-- A **graded `A`-module map of degree `k`** from `M` to `N`: a family of `R`-linear maps
`M^n → N^{n+k}` that is compatible with the graded `A`-action **up to the Koszul sign**
`(-1)^{|a|·k}`:
`f^{i+n}(a · x) = (-1)^{|a|·k} a · f^n(x)`.
It is **not** required to commute with the differentials.  For `k = 0` this is ordinary
`A`-linearity; for `k = -1` (the degree of a chain homotopy) it is the signed compatibility
`f(a·x) = (-1)^{|a|} a·f(x)`, equivalently `f` is a degree-`0` graded map `M → N[-1]`. -/
structure GradedHom (M N : DGModule A) (k : ℤ) where
  /-- the component `M^n → N^{n+k}` in each degree `n`. -/
  toFun : ∀ n, M.obj n →ₗ[R] N.obj (n + k)
  /-- compatibility with the `A`-action up to the Koszul sign `(-1)^{|a|·k}`. -/
  map_smul : ∀ (i n : ℤ) (a : A.obj i) (x : M.obj n),
      toFun (i + n) (M.smul i n a x)
        = (Int.negOnePow (i * k)) •
            gcast (R := R) (obj := N.obj) (by ring) (N.smul i (n + k) a (toFun n x))

namespace GradedHom

/-- Two graded maps of the same degree are equal if their components agree in every degree. -/
@[ext] theorem ext {M N : DGModule A} {k : ℤ} {f g : GradedHom M N k}
    (h : ∀ n, f.toFun n = g.toFun n) : f = g := by
  cases f
  cases g
  simp only [GradedHom.mk.injEq]
  exact funext h

/-- A degree-`0` graded hom applied at degree `n`, with codomain normalized to `N.obj n`. -/
def app {M N : DGModule A} (f : GradedHom M N 0) (n : ℤ) : M.obj n →ₗ[R] N.obj n :=
  (gcast (R := R) (obj := N.obj) (add_zero n)).comp (f.toFun n)

/-- Two degree-`0` graded maps are equal if and only if their normalized components `app n`
agree in every degree. -/
theorem app_eq_iff {M N : DGModule A} {f g : GradedHom M N 0} :
    (∀ n, f.app n = g.app n) ↔ f = g := by
  constructor
  · intro h; apply GradedHom.ext; intro n
    have hn := h n
    apply LinearMap.ext; intro x
    apply gcast_injective (R := R) (obj := N.obj) (add_zero n)
    have := LinearMap.congr_fun hn x
    simpa only [GradedHom.app, LinearMap.coe_comp, Function.comp_apply] using this
  · intro h; subst h; intro n; rfl

/-- A degree-`0` graded map is `A`-linear in normalized form: `f(a · x) = a · f(x)`. -/
theorem app_smul {M N : DGModule A} (f : GradedHom M N 0) (i n : ℤ)
    (a : A.obj i) (x : M.obj n) :
    f.app (i + n) (M.smul i n a x) = N.smul i n a (f.app n x) := by
  have h := f.map_smul i n a x
  rw [mul_zero, Int.negOnePow_zero, _root_.one_smul] at h
  simp only [GradedHom.app, LinearMap.coe_comp, Function.comp_apply]
  rw [h, ← gcast_smul_cod N (show n + 0 = n by ring) i a (f.toFun n x)]
  exact eq_of_heq ((gcast_heq _ _).trans ((gcast_heq _ _).trans (gcast_heq _ _).symm))

/-- Move a `gcast` of the index through `f.app` for a degree-`0` graded map. -/
theorem app_gcast {M N : DGModule A} (f : GradedHom M N 0) {m m' : ℤ} (h : m = m')
    (x : M.obj m) :
    f.app m' (gcast (R := R) (obj := M.obj) h x)
      = gcast (R := R) (obj := N.obj) h (f.app m x) := by
  subst h; rfl

/-- A degree-`0` graded hom is a **chain map** (morphism of DG modules) if it commutes
with the differentials: `f^{n+1} ∘ d_M = d_N ∘ f^n`. -/
def IsChainMap {M N : DGModule A} (f : GradedHom M N 0) : Prop :=
  ∀ n (x : M.obj n), f.app (n + 1) (M.d n x) = N.d n (f.app n x)

end GradedHom

/-- A **homomorphism of differential graded `A`-modules** `M ⟶ N` (Stacks Tag 09JK): a
degree-`0`, `A`-linear graded map that commutes with the differentials. -/
structure Hom (M N : DGModule A) where
  /-- the underlying degree-`0` graded `A`-module map. -/
  graded : GradedHom M N 0
  /-- the underlying graded map commutes with the differentials. -/
  chain : graded.IsChainMap

namespace Hom

/-- Apply a DG-module morphism at degree `n`. -/
def app {M N : DGModule A} (f : Hom M N) (n : ℤ) : M.obj n →ₗ[R] N.obj n := f.graded.app n

/-- Two morphisms of DG `A`-modules are equal if their components agree in every degree. -/
@[ext] theorem ext {M N : DGModule A} {f g : Hom M N} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g
  simp only [Hom.mk.injEq]
  exact (GradedHom.app_eq_iff).1 h

/-- The identity morphism of DG `A`-modules. -/
def id (M : DGModule A) : Hom M M where
  graded :=
    { toFun := fun n => gcast (R := R) (obj := M.obj) (by ring)
      map_smul := by
        intro i n a x
        rw [mul_zero, Int.negOnePow_zero, _root_.one_smul]
        rw [← gcast_smul_cod M (show n = n + 0 by ring) i a x, gcast_gcast'] }
  chain := by
    intro n x
    simp only [GradedHom.app, LinearMap.coe_comp, Function.comp_apply]
    rw [gcast_gcast' (show n = n + 0 by ring) (show n + 0 = n by ring) rfl, gcast_rfl,
      gcast_gcast' (show n + 1 = (n + 1) + 0 by ring) (show (n + 1) + 0 = n + 1 by ring) rfl,
      gcast_rfl]

/-- `A`-linearity of a DG-module morphism in normalized (`app`) form. -/
theorem app_smul {M N : DGModule A} (f : Hom M N) (i n : ℤ) (a : A.obj i) (x : M.obj n) :
    f.app (i + n) (M.smul i n a x) = N.smul i n a (f.app n x) :=
  f.graded.app_smul i n a x

/-- The differential-compatibility of a DG-module morphism in `app` form. -/
theorem app_d {M N : DGModule A} (f : Hom M N) (n : ℤ) (x : M.obj n) :
    f.app (n + 1) (M.d n x) = N.d n (f.app n x) := f.chain n x

/-- Build a DG-module morphism from normalized per-degree maps, an `A`-linearity law,
and a chain-map law. -/
def ofApp {M N : DGModule A} (φ : ∀ n, M.obj n →ₗ[R] N.obj n)
    (hsmul : ∀ (i n : ℤ) (a : A.obj i) (x : M.obj n),
      φ (i + n) (M.smul i n a x) = N.smul i n a (φ n x))
    (hd : ∀ (n : ℤ) (x : M.obj n), φ (n + 1) (M.d n x) = N.d n (φ n x)) : Hom M N where
  graded :=
    { toFun := fun n => (gcast (R := R) (obj := N.obj) (by ring : n = n + 0)).comp (φ n)
      map_smul := by
        intro i n a x
        rw [mul_zero, Int.negOnePow_zero, _root_.one_smul]
        simp only [LinearMap.coe_comp, Function.comp_apply]
        rw [hsmul i n a x, ← gcast_smul_cod N (show n = n + 0 by ring) i a (φ n x)]
        exact eq_of_heq ((gcast_heq _ _).trans ((gcast_heq _ _).trans (gcast_heq _ _)).symm) }
  chain := by
    intro n x
    simp only [GradedHom.app, LinearMap.coe_comp, Function.comp_apply]
    rw [gcast_gcast' (show n = n + 0 by ring) (show n + 0 = n by ring) rfl, gcast_rfl,
      gcast_gcast' (show n + 1 = (n + 1) + 0 by ring) (show (n + 1) + 0 = n + 1 by ring) rfl,
      gcast_rfl, hd n x]

/-- The components of `ofApp φ hsmul hd` are the maps `φ n`. -/
@[simp] theorem ofApp_app {M N : DGModule A} (φ : ∀ n, M.obj n →ₗ[R] N.obj n)
    (hsmul) (hd) (n : ℤ) : (ofApp φ hsmul hd).app n = φ n := by
  apply LinearMap.ext; intro x
  simp only [Hom.app, GradedHom.app, ofApp, LinearMap.coe_comp, Function.comp_apply]
  rw [gcast_gcast' (show n = n + 0 by ring) (show n + 0 = n by ring) rfl, gcast_rfl]

/-- Composition of DG-module morphisms. -/
def comp {K L M : DGModule A} (g : Hom L M) (f : Hom K L) : Hom K M :=
  ofApp (fun n => (g.app n).comp (f.app n))
    (by
      intro i n a x
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [Hom.app_smul f i n a x, Hom.app_smul g i n a (f.app n x)])
    (by
      intro n x
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [Hom.app_d f n x, Hom.app_d g n (f.app n x)])

/-- The components of a composite are the composites of the components. -/
@[simp] theorem comp_app {K L M : DGModule A} (g : Hom L M) (f : Hom K L) (n : ℤ) :
    (g.comp f).app n = (g.app n).comp (f.app n) := by
  simp only [comp, ofApp_app]

/-- The components of the identity morphism are identity maps. -/
@[simp] theorem id_app (M : DGModule A) (n : ℤ) : (Hom.id M).app n = LinearMap.id := by
  apply LinearMap.ext; intro x
  simp only [Hom.app, GradedHom.app, Hom.id, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.id_coe, id_eq]
  rw [gcast_gcast' (show n = n + 0 by ring) (show n + 0 = n by ring) rfl, gcast_rfl]

/-- Move a `gcast` of the index through `f.app`. -/
theorem app_gcast {M N : DGModule A} (f : Hom M N) {m m' : ℤ} (h : m = m') (x : M.obj m) :
    f.app m' (gcast (R := R) (obj := M.obj) h x)
      = gcast (R := R) (obj := N.obj) h (f.app m x) := by
  subst h; rfl

/-- The action of the shift functor `[1]` on a DG-module morphism: `(f[1])^n = f^{n+1}`. -/
def shiftMap {M N : DGModule A} (f : Hom M N) : Hom M.shift N.shift :=
  ofApp (fun n => f.app (n + 1))
    (by
      intro i n a x
      change f.app (i + n + 1) _ = _
      simp only [DGModule.shift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.smul_apply]
      rw [LinearMap.CompatibleSMul.map_smul]
      rw [app_gcast f (show i + (n + 1) = (i + n) + 1 by ring)]
      rw [Hom.app_smul f i (n + 1) a x])
    (by
      intro n x
      change f.app (n + 1 + 1) _ = _
      simp only [DGModule.shift, LinearMap.neg_apply, map_neg]
      rw [Hom.app_d f (n + 1) x])

end Hom

/-- A **homotopy** between two DG-module morphisms `f, g : M ⟶ N` (Stacks Tag 011J): a
degree `-1` graded `A`-module map `H : M → N` (a family `M^n → N^{n-1}` satisfying the
**signed** `A`-linearity `H(a·x) = (-1)^{|a|} a·H(x)`, and **not** required to commute with
the differentials) such that, in each degree, `f - g = d_N ∘ H + H ∘ d_M`. -/
structure Homotopy {M N : DGModule A} (f g : Hom M N) where
  /-- the chain homotopy, a degree `-1` graded `A`-module map (signed `A`-linearity). -/
  H : GradedHom M N (-1)
  /-- the homotopy relation `f - g = d_N ∘ H + H ∘ d_M` in each degree. -/
  rel : ∀ (n : ℤ) (x : M.obj n),
      f.app n x - g.app n x
        = (gcast (R := R) (obj := N.obj) (by ring)) (N.d (n + -1) (H.toFun n x))
          + (gcast (R := R) (obj := N.obj) (by ring)) (H.toFun (n + 1) (M.d n x))

/-- Two DG-module morphisms are **homotopic** (become equal in the homotopy category
`K(Mod_{(A,d)})`) if there is a homotopy between them. -/
def Homotopic {M N : DGModule A} (f g : Hom M N) : Prop := Nonempty (Homotopy f g)

/-- A **homotopy equivalence** of DG `A`-modules: a morphism with a two-sided homotopy
inverse (an isomorphism in the homotopy category `K(Mod_{(A,d)})`). -/
structure HtpyEquiv (M N : DGModule A) where
  /-- the forward morphism `M ⟶ N`. -/
  hom : Hom M N
  /-- the homotopy inverse `N ⟶ M`. -/
  inv : Hom N M
  /-- `inv ∘ hom` is homotopic to the identity of `M`. -/
  hom_inv : Homotopic (inv.comp hom) (Hom.id M)
  /-- `hom ∘ inv` is homotopic to the identity of `N`. -/
  inv_hom : Homotopic (hom.comp inv) (Hom.id N)

/-- The identity is a homotopy equivalence. -/
def HtpyEquiv.id (M : DGModule A) : HtpyEquiv M M where
  hom := Hom.id M
  inv := Hom.id M
  hom_inv := ⟨{ H := { toFun := fun n => 0, map_smul := by intro i n a x; simp }
                rel := by intro n x; simp }⟩
  inv_hom := ⟨{ H := { toFun := fun n => 0, map_smul := by intro i n a x; simp }
                rel := by intro n x; simp }⟩

/-- A **triangle** `K → L → M → K[1]` of DG `A`-modules: three vertices together with
morphisms `mor₁ : K ⟶ L`, `mor₂ : L ⟶ M`, and a connecting morphism `mor₃ : M ⟶ K[1]`. -/
structure Triangle where
  /-- the first vertex `K`. -/
  obj₁ : DGModule A
  /-- the second vertex `L`. -/
  obj₂ : DGModule A
  /-- the third vertex `M`. -/
  obj₃ : DGModule A
  /-- the morphism `K ⟶ L`. -/
  mor₁ : Hom obj₁ obj₂
  /-- the morphism `L ⟶ M`. -/
  mor₂ : Hom obj₂ obj₃
  /-- the connecting morphism `M ⟶ K[1]`. -/
  mor₃ : Hom obj₃ obj₁.shift

/-- An **isomorphism of triangles in the homotopy category** `K(Mod_{(A,d)})`: vertex
homotopy equivalences `u₁, u₂, u₃` whose connecting squares commute up to homotopy. -/
structure TriangleHtpyIso (T T' : Triangle (A := A)) where
  /-- the homotopy equivalence between the first vertices. -/
  u₁ : HtpyEquiv T.obj₁ T'.obj₁
  /-- the homotopy equivalence between the second vertices. -/
  u₂ : HtpyEquiv T.obj₂ T'.obj₂
  /-- the homotopy equivalence between the third vertices. -/
  u₃ : HtpyEquiv T.obj₃ T'.obj₃
  /-- the `mor₁`-square commutes up to homotopy. -/
  comm₁ : Homotopic (u₂.hom.comp T.mor₁) (T'.mor₁.comp u₁.hom)
  /-- the `mor₂`-square commutes up to homotopy. -/
  comm₂ : Homotopic (u₃.hom.comp T.mor₂) (T'.mor₂.comp u₂.hom)
  /-- the `mor₃`-square, with `u₁.hom[1]` on the shift, commutes up to homotopy. -/
  comm₃ : Homotopic ((Hom.shiftMap u₁.hom).comp T.mor₃) (T'.mor₃.comp u₃.hom)

/-- `A`-linearity of a degree-`0` graded map in normalized (`app`) form. -/
alias GradedHom.app_smul' := GradedHom.app_smul

/-- The action on the shift in terms of the original action. -/
theorem shift_smul_apply (N : DGModule A) (i n : ℤ) (a : A.obj i) (x : (N.shift).obj n) :
    (N.shift).smul i n a x
      = (Int.negOnePow i) • gcast (R := R) (obj := N.obj)
          (show i + (n + 1) = (i + n) + 1 by ring) (N.smul i (n + 1) a x) := by
  rfl

/-- The differential on the shift in terms of the original differential. -/
theorem shift_d_apply (N : DGModule A) (n : ℤ) (x : (N.shift).obj n) :
    (N.shift).d n x = -(N.d (n + 1) x) := rfl

/-- An **admissible short exact sequence** `0 → K → L → M → 0` of DG `A`-modules
(Stacks Tag 09JT): morphisms `α : K ⟶ L`, `β : L ⟶ M` of DG `A`-modules which form, in
each degree, a short exact sequence of `R`-modules that splits as graded `A`-modules.
The graded splitness is recorded as the existence of a graded (`A`-linear, degree `0`, not
necessarily chain) section of `β`. -/
structure AdmissibleSES (K L M : DGModule A) where
  /-- the morphism `K ⟶ L`. -/
  α : Hom K L
  /-- the morphism `L ⟶ M`. -/
  β : Hom L M
  /-- `α` is injective in each degree (admissible monomorphism). -/
  α_inj : ∀ n, Function.Injective (α.app n)
  /-- `β` is surjective in each degree (admissible epimorphism). -/
  β_surj : ∀ n, Function.Surjective (β.app n)
  /-- exactness in the middle: `im α = ker β` in each degree. -/
  exact : ∀ n, LinearMap.range (α.app n) = LinearMap.ker (β.app n)
  /-- the sequence is split as a sequence of graded `A`-modules: there is a graded
  `A`-linear (degree `0`) section of `β` (not required to commute with the differentials). -/
  graded_split : ∃ σ : GradedHom M L 0, ∀ n, (β.app n).comp (σ.app n) = LinearMap.id

namespace AdmissibleSES
variable {K L M : DGModule A}

/-- A **pair of compatible splittings** for an admissible short exact sequence
(Stacks Tag 09JU): graded `A`-module maps `s : M → L` and `π : L → K` (degree `0`,
`A`-linear, **not** required to commute with the differentials) such that
`β ∘ s = id`, `π ∘ α = id`, `π ∘ s = 0`, together with the direct-sum decomposition
`s ∘ β + α ∘ π = id` of `L = α(K) ⊕ s(M)`. -/
structure CompatibleSplittings (E : AdmissibleSES K L M) where
  /-- the graded section `s : M → L` of `β`. -/
  s : GradedHom M L 0
  /-- the graded retraction `π : L → K` of `α`. -/
  π : GradedHom L K 0
  /-- `β ∘ s = id`. -/
  βs : ∀ n (x : M.obj n), E.β.app n (s.app n x) = x
  /-- `π ∘ α = id`. -/
  πα : ∀ n (x : K.obj n), π.app n (E.α.app n x) = x
  /-- `π ∘ s = 0`. -/
  πs : ∀ n (x : M.obj n), π.app n (s.app n x) = 0
  /-- `s ∘ β + α ∘ π = id`. -/
  decomp : ∀ n (y : L.obj n),
    s.app n (E.β.app n y) + E.α.app n (π.app n y) = y

namespace CompatibleSplittings
variable {E : AdmissibleSES K L M}

/-- The underlying degree-`+1` family of the **connecting map**
`δ = π ∘ d_L ∘ s : M → K[1]` for a pair of compatible splittings (Stacks Tag 09JU),
as a family of `R`-linear maps `M^n → K^{n+1} = K[1]^n`. -/
def deltaFun (P : E.CompatibleSplittings) (n : ℤ) : M.obj n →ₗ[R] (K.shift).obj n :=
  (P.π.app (n + 1)).comp ((L.d n).comp (P.s.app n))

/-- `δ x = π (d_L (s x))`. -/
theorem deltaFun_apply (P : E.CompatibleSplittings) (n : ℤ) (x : M.obj n) :
    P.deltaFun n x = P.π.app (n + 1) (L.d n (P.s.app n x)) := rfl

/-- An element of `L` killed by `β` is recovered from its `π`-component: `α (π y) = y`. -/
private theorem alpha_pi_of_beta_eq_zero (P : E.CompatibleSplittings) {n : ℤ} {y : L.obj n}
    (h : E.β.app n y = 0) : E.α.app n (P.π.app n y) = y := by
  have := P.decomp n y
  rwa [h, map_zero, zero_add] at this

/-- `d_L (s x) = s (d_M x) + α (δ x)` in degree `n+1`. -/
theorem deltaFun_key (P : E.CompatibleSplittings) (n : ℤ) (x : M.obj n) :
    L.d n (P.s.app n x)
      = P.s.app (n + 1) (M.d n x) + E.α.app (n + 1) (P.deltaFun n x) := by
  set w : L.obj (n + 1) := L.d n (P.s.app n x) - P.s.app (n + 1) (M.d n x) with hw
  have hβw : E.β.app (n + 1) w = 0 := by
    rw [hw, map_sub]
    rw [Hom.app_d E.β n (P.s.app n x), P.βs n x, P.βs (n + 1) (M.d n x), sub_self]
  have hπw : P.π.app (n + 1) w = P.deltaFun n x := by
    rw [hw, map_sub, P.πs (n + 1) (M.d n x), sub_zero]
    rfl
  rw [← hπw, P.alpha_pi_of_beta_eq_zero hβw, hw]; abel

/-- `s (d_M x) = d_L (s x) - α (δ x)` in degree `n+1`. -/
theorem deltaFun_key' (P : E.CompatibleSplittings) (n : ℤ) (x : M.obj n) :
    P.s.app (n + 1) (M.d n x)
      = L.d n (P.s.app n x) - E.α.app (n + 1) (P.deltaFun n x) := by
  rw [deltaFun_key P n x]; abel

/-- The **connecting map** `δ = π ∘ d_L ∘ s : M ⟶ K[1]` of an admissible short exact
sequence with a pair of compatible splittings, as a homomorphism of DG `A`-modules into the
shift (Stacks Tag 09JU). -/
def connectingMap (P : E.CompatibleSplittings) : Hom M (K.shift) :=
  Hom.ofApp P.deltaFun
    (by
      intro i n a x
      rw [shift_smul_apply]
      simp only [deltaFun_apply]
      rw [GradedHom.app_smul P.s i n a x]
      rw [L.d_smul i n a (P.s.app n x)]
      rw [map_add]
      rw [GradedHom.app_gcast P.π (show (i + 1) + n = (i + n) + 1 by ring)]
      rw [GradedHom.app_smul P.π (i + 1) n (A.d i a) (P.s.app n x)]
      rw [P.πs n x, map_zero, map_zero]
      rw [zero_add]
      rw [LinearMap.CompatibleSMul.map_smul]
      rw [GradedHom.app_gcast P.π (show i + (n + 1) = (i + n) + 1 by ring)]
      rw [GradedHom.app_smul P.π i (n + 1) a (L.d n (P.s.app n x))])
    (by
      intro n x
      rw [shift_d_apply]
      rw [deltaFun_apply P (n + 1) (M.d n x)]
      rw [deltaFun_key' P n x]
      rw [map_sub, map_sub]
      rw [← Hom.app_d E.α (n + 1) (P.deltaFun n x)]
      rw [L.d_comp_d n (P.s.app n x)]
      rw [map_zero, zero_sub]
      rw [P.πα (n + 1 + 1) (K.d (n + 1) (P.deltaFun n x))])

/-- The components of the connecting map are `deltaFun`. -/
@[simp] theorem connectingMap_app (P : E.CompatibleSplittings) (n : ℤ) :
    (P.connectingMap).app n = P.deltaFun n := by
  simp [connectingMap]

/-- The **triangle associated** to an admissible short exact sequence with respect to a
pair of compatible splittings (Stacks Tag 09K7/09K8):
`K → L → M → K[1]` in the homotopy category `K(Mod_{(A,d)})`. -/
def associatedTriangle (P : E.CompatibleSplittings) : Triangle (A := A) where
  obj₁ := K
  obj₂ := L
  obj₃ := M
  mor₁ := E.α
  mor₂ := E.β
  mor₃ := P.connectingMap

end CompatibleSplittings
end AdmissibleSES

end DGModule

namespace DGModule
open AdmissibleSES AdmissibleSES.CompatibleSplittings

/-- For an admissible short exact sequence `0 → K → L → M → 0` of DG `A`-modules and any two
pairs of compatible splittings `(s, π)` and `(s', π')`, the two connecting maps
`δ = π ∘ d_L ∘ s` and `δ' = π' ∘ d_L ∘ s'`, viewed as homomorphisms of DG `A`-modules
`M ⟶ K[1]`, are **homotopic**. -/
theorem connectingMap_homotopic
    {K L M : DGModule A} (E : AdmissibleSES K L M)
    (P P' : E.CompatibleSplittings) :
    Homotopic P.connectingMap P'.connectingMap := by
  set happ : ∀ n, M.obj n →ₗ[R] K.obj n :=
    fun n => (P.π.app n).comp (P'.s.app n - P.s.app n) with hhapp
  have hα : ∀ (n : ℤ) (x : M.obj n),
      E.α.app n (happ n x) = P'.s.app n x - P.s.app n x := by
    intro n x
    have hβ : E.β.app n (P'.s.app n x - P.s.app n x) = 0 := by
      rw [map_sub, P'.βs n x, P.βs n x, sub_self]
    simp only [hhapp, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply]
    exact P.alpha_pi_of_beta_eq_zero hβ
  have hsmul : ∀ (i n : ℤ) (a : A.obj i) (x : M.obj n),
      happ (i + n) (M.smul i n a x) = K.smul i n a (happ n x) := by
    intro i n a x
    simp only [hhapp, LinearMap.coe_comp, Function.comp_apply, LinearMap.sub_apply]
    rw [GradedHom.app_smul P'.s i n a x, GradedHom.app_smul P.s i n a x]
    rw [← LinearMap.map_sub (L.smul i n a)]
    rw [GradedHom.app_smul P.π i n a (P'.s.app n x - P.s.app n x)]
  have hsx : ∀ (n : ℤ) (x : M.obj n),
      P'.s.app n x = P.s.app n x + E.α.app n (happ n x) := by
    intro n x
    rw [hα n x]; abel
  have hg : ∀ (m : ℤ) (x : M.obj m),
      P'.π.app m (P.s.app m x) = - happ m x := by
    intro m x
    have h0 := P'.πs m x
    rw [hsx, map_add, P'.πα m (happ m x)] at h0
    rw [eq_neg_iff_add_eq_zero]; exact h0
  have hπdiff : ∀ (m : ℤ) (y : L.obj m),
      P'.π.app m y = P.π.app m y + P'.π.app m (P.s.app m (E.β.app m y)) := by
    intro m y
    have hdec := P.decomp m y
    have h2 : P'.π.app m y = P'.π.app m (P.s.app m (E.β.app m y))
        + P'.π.app m (E.α.app m (P.π.app m y)) := by
      conv_lhs => rw [← hdec]
      rw [map_add]
    rw [h2, P'.πα m (P.π.app m y)]; abel
  set Htf : ∀ n, M.obj n →ₗ[R] (K.shift).obj (n + -1) :=
    fun n => (gcast (R := R) (obj := K.obj) (show n = (n + -1) + 1 by ring)).comp (happ n)
    with hHtf
  have hchain : ∀ (n : ℤ) (x : M.obj n),
      P.connectingMap.app n x - P'.connectingMap.app n x
        = happ (n + 1) (M.d n x) - K.d n (happ n x) := by
    intro n x
    rw [connectingMap_app, connectingMap_app]
    rw [deltaFun_apply, deltaFun_apply]
    rw [hsx, map_add]
    rw [← Hom.app_d E.α n (happ n x)]
    rw [map_add, P'.πα (n + 1) (K.d n (happ n x))]
    rw [hπdiff (n + 1) (L.d n (P.s.app n x))]
    rw [Hom.app_d E.β n (P.s.app n x), P.βs n x]
    rw [hg (n + 1) (M.d n x)]
    abel
  have hHval : ∀ (n : ℤ) (x : M.obj n),
      Htf n x = gcast (R := R) (obj := K.obj) (show n = (n + -1) + 1 by ring) (happ n x) := by
    intro n x; rw [hHtf]; rfl
  have hHsmul : ∀ (i n : ℤ) (a : A.obj i) (x : M.obj n),
      Htf (i + n) (M.smul i n a x)
        = (Int.negOnePow (i * (-1))) •
            gcast (R := R) (obj := (K.shift).obj) (show i + (n + -1) = (i + n) + -1 by ring)
              ((K.shift).smul i (n + -1) a (Htf n x)) := by
    intro i n a x
    rw [hHval (i + n) (M.smul i n a x), hHval n x]
    rw [hsmul i n a x]
    rw [shift_smul_apply]
    rw [gcast_smul_negOnePow]
    rw [smul_smul]
    have hsign : Int.negOnePow (i * (-1)) * Int.negOnePow i = 1 := by
      rw [← Int.negOnePow_add]; rw [show i * (-1) + i = 0 by ring]; rfl
    rw [hsign, _root_.one_smul]
    apply eq_of_heq
    refine (gcast_heq _ _).trans ?_
    refine HEq.symm ?_
    refine (gcast_heq _ _).trans ?_
    rw [← gcast_smul_cod K (show n = n + -1 + 1 by ring) i a (happ n x)]
    exact (gcast_heq _ _).trans (gcast_heq _ _)
  refine ⟨{ H := { toFun := Htf, map_smul := hHsmul }, rel := ?_ }⟩
  intro n x
  show P.connectingMap.app n x - P'.connectingMap.app n x
      = (gcast (R := R) (obj := (K.shift).obj) (show (n + -1) + 1 = n by ring))
          ((K.shift).d (n + -1) (Htf n x))
        + (gcast (R := R) (obj := (K.shift).obj) (show (n + 1) + -1 = n by ring))
          (Htf (n + 1) (M.d n x))
  rw [hchain n x]
  rw [hHval n x, hHval (n + 1) (M.d n x)]
  rw [shift_d_apply]
  rw [map_neg]
  rw [← gcast_d_cod K (show n = (n + -1) + 1 by ring) (happ n x)]
  have hcol : ∀ (p : ℤ) (h₁ : p = n) (h₂ : n + 1 = p + 1) (y : K.obj (n + 1)),
      gcast (R := R) (obj := (K.shift).obj) h₁ (gcast (R := R) (obj := K.obj) h₂ y) = y :=
    fun _ _ _ _ => eq_of_heq ((gcast_heq _ _).trans (gcast_heq _ _))
  rw [hcol, hcol]
  abel

/-- Equal morphisms are homotopic (via the zero homotopy). -/
theorem Homotopic.of_eq {M N : DGModule A} {f g : Hom M N} (h : f = g) :
    Homotopic f g := by
  subst h
  exact ⟨{ H := { toFun := fun n => 0, map_smul := by intro i n a x; simp }
           rel := by intro n x; simp }⟩

/-- The triangle associated to an admissible short exact sequence is, up to canonical
isomorphism in the homotopy category `K(Mod_{(A,d)})`, independent of the choice of
compatible splittings: for any two pairs of compatible splittings `(s, π)` and `(s', π')`,
the identity morphisms on `K`, `L`, `M` form an isomorphism of the associated triangles
`T : K → L → M → K[1]` and `T' : K → L → M → K[1]` in `K(Mod_{(A,d)})`. -/
@[stacks 09K6]
theorem associatedTriangle_iso_of_compatibleSplittings
    {K L M : DGModule A} (E : AdmissibleSES K L M)
    (P P' : E.CompatibleSplittings) :
    Nonempty (TriangleHtpyIso P.associatedTriangle P'.associatedTriangle) := by
  refine ⟨{ u₁ := HtpyEquiv.id K, u₂ := HtpyEquiv.id L, u₃ := HtpyEquiv.id M,
            comm₁ := ?_, comm₂ := ?_, comm₃ := ?_ }⟩
  iterate 2
    apply Homotopic.of_eq
    apply Hom.ext; intro n
    simp [associatedTriangle, HtpyEquiv.id]
  · have hL : (Hom.shiftMap (HtpyEquiv.id K).hom).comp P.connectingMap
        = P.connectingMap := by
      apply Hom.ext; intro n
      simp only [Hom.comp_app, HtpyEquiv.id, Hom.shiftMap, Hom.ofApp_app, Hom.id_app]
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    have hR : P'.connectingMap.comp (HtpyEquiv.id M).hom = P'.connectingMap := by
      apply Hom.ext; intro n
      simp only [Hom.comp_app, HtpyEquiv.id, Hom.id_app]
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    show Homotopic ((Hom.shiftMap (HtpyEquiv.id K).hom).comp
      (P.associatedTriangle.mor₃)) ((P'.associatedTriangle.mor₃).comp (HtpyEquiv.id M).hom)
    rw [show P.associatedTriangle.mor₃ = P.connectingMap from rfl,
        show P'.associatedTriangle.mor₃ = P'.connectingMap from rfl]
    rw [hL, hR]
    exact connectingMap_homotopic (E := E) (P := P) (P' := P')

end DGModule

end DifferentialGradedModule.AdmissibleTriangle
