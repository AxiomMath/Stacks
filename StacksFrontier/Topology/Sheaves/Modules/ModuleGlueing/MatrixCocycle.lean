module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTrivialisationSections
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# Glueing a finite locally free sheaf of modules from transition matrices

Let `O` be a sheaf of rings on a topological space `X` and let `V : K → Opens X` be a family of
opens. A *matrix cocycle* on that family is, for every pair `k`, `l` of indices and every open
`W` contained in both `V k` and `V l`, a matrix of sections of `O` over `W`, compatible with
restriction, equal to the identity matrix when `k = l`, and multiplicative along triples of
indices. This is the transition data of a finite locally free sheaf of modules trivialised over
the family, written out in coordinates.

This file glues such a datum, as a `Stacks.SheafOfModules.OModuleGlueData`, into a sheaf of
`O`-modules together with its basis sections over each member of the family, and shows that the
glued sheaf is finite locally free as soon as the family covers `X`.

## Main definitions

* `Stacks.SheafOfModules.rowMul`: the product of a row vector with a matrix, and
  `Stacks.SheafOfModules.rowMulEquiv`: an invertible matrix as a linear equivalence of row
  vectors. Both are stated over an arbitrary ring, the matrix acting on the right.
* `Stacks.SheafOfModules.freeCoordEquiv`: the coordinates of a section of a finite free sheaf of
  modules, as a linear equivalence.
* `Stacks.SheafOfModules.MatrixCocycle`: the transition data described above.
* `Stacks.SheafOfModules.MatrixCocycle.glued`: the sheaf of `O`-modules it glues to, and
  `Stacks.SheafOfModules.MatrixCocycle.basis`: its basis sections over each member of the family.

## Main results

* `Stacks.SheafOfModules.MatrixCocycle.bijective_combSections_basis`: **the basis sections
  trivialise the glued sheaf** over every open contained in a member of the family.
* `Stacks.SheafOfModules.MatrixCocycle.res_basis`: **the basis sections are related by the
  transition matrices.**
* `Stacks.SheafOfModules.MatrixCocycle.isFiniteLocallyFree_glued`: **the glued sheaf is finite
  locally free** when the family covers the space.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules

universe u v u'

namespace Stacks.SheafOfModules

/-! ### Row vectors times a matrix -/

section Row

variable {Rr : Type*} [Ring Rr]

/-- The product of a row vector with a matrix: the matrix acts on the right. -/
def rowMul {ι κ : Type*} [Fintype ι] (A : ι → κ → Rr) (c : ι → Rr) (b : κ) : Rr :=
  ∑ a : ι, c a * A a b

/-- Multiplication of row vectors by a matrix is additive. -/
lemma rowMul_add {ι κ : Type*} [Fintype ι] (A : ι → κ → Rr) (c d : ι → Rr) :
    rowMul A (c + d) = rowMul A c + rowMul A d := by
  funext b
  simp only [rowMul, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => add_mul _ _ _

/-- Multiplication of row vectors by a matrix commutes with left scalar multiplication. -/
lemma rowMul_smul {ι κ : Type*} [Fintype ι] (A : ι → κ → Rr) (r : Rr) (c : ι → Rr) :
    rowMul A (r • c) = r • rowMul A c := by
  funext b
  simp only [rowMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

/-- Multiplying a row vector by `A` and then by `B` is multiplying it by the product `A B`. -/
lemma rowMul_rowMul {ι κ ν : Type*} [Fintype ι] [Fintype κ] (A : ι → κ → Rr) (B : κ → ν → Rr)
    (c : ι → Rr) :
    rowMul B (rowMul A c) = rowMul (fun a n => ∑ b : κ, A a b * B b n) c := by
  funext n
  simp only [rowMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_assoc _ _ _

/-- The identity matrix fixes every row vector. -/
lemma rowMul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → Rr) :
    rowMul (fun a b : ι => if a = b then (1 : Rr) else 0) c = c := by
  funext b
  simp [rowMul]

/-- The `a`-th standard row vector times a matrix is the `a`-th row of the matrix. -/
lemma rowMul_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] (A : ι → κ → Rr) (a : ι) (b : κ) :
    rowMul A (fun a' => if a = a' then (1 : Rr) else 0) b = A a b := by
  simp [rowMul]

/-- A matrix with a two-sided inverse, read as a linear equivalence of row vectors. -/
noncomputable def rowMulEquiv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (A : ι → κ → Rr) (B : κ → ι → Rr)
    (hAB : ∀ a a' : ι, ∑ b : κ, A a b * B b a' = if a = a' then 1 else 0)
    (hBA : ∀ b b' : κ, ∑ a : ι, B b a * A a b' = if b = b' then 1 else 0) :
    (ι → Rr) ≃ₗ[Rr] (κ → Rr) where
  toFun := rowMul A
  map_add' := rowMul_add A
  map_smul' := rowMul_smul A
  invFun := rowMul B
  left_inv c := by
    rw [rowMul_rowMul, show (fun a a' : ι => ∑ b : κ, A a b * B b a')
      = (fun a a' : ι => if a = a' then (1 : Rr) else 0) from
        funext fun a => funext fun a' => hAB a a', rowMul_one]
  right_inv c := by
    rw [rowMul_rowMul, show (fun b b' : κ => ∑ a : ι, B b a * A a b')
      = (fun b b' : κ => if b = b' then (1 : Rr) else 0) from
        funext fun b => funext fun b' => hBA b b', rowMul_one]

/-- The linear equivalence `rowMulEquiv A B` is multiplication by `A`. -/
@[simp] lemma rowMulEquiv_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (A : ι → κ → Rr) (B : κ → ι → Rr) (hAB) (hBA) (c : ι → Rr) :
    rowMulEquiv A B hAB hBA c = rowMul A c := rfl

end Row

/-! ### Coordinates on a finite free sheaf of modules, as a linear equivalence -/

section FreeCoordEquiv

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Each coordinate of a sum of sections of a free sheaf of modules is the sum of the
coordinates. -/
lemma freeCoord_add {ι : Type u} [DecidableEq ι] (V : Cᵒᵖ)
    (e e' : ToType ((free (R := S) ι).val.obj V)) (i : ι) :
    freeCoord (S := S) V (e + e') i = freeCoord (S := S) V e i + freeCoord (S := S) V e' i :=
  ((freeProj (S := S) i).val.app V).hom.map_add e e'

/-- Each coordinate of `a • e` is `a` times the corresponding coordinate of `e`. -/
lemma freeCoord_smul {ι : Type u} [DecidableEq ι] (V : Cᵒᵖ) (a : ToType (S.obj.obj V))
    (e : ToType ((free (R := S) ι).val.obj V)) (i : ι) :
    freeCoord (S := S) V (a • e) i = a * freeCoord (S := S) V e i :=
  ((freeProj (S := S) i).val.app V).hom.map_smul a e

/-- **Coordinates identify the sections of a finite free sheaf of modules with tuples of
sections of the structure sheaf**, linearly. -/
noncomputable def freeCoordEquiv {ι : Type u} [Fintype ι] [DecidableEq ι] (V : Cᵒᵖ) :
    (free (R := S) ι).val.obj V ≃ₗ[ToType (S.obj.obj V)] (ι → ToType (S.obj.obj V)) where
  toFun := freeCoord V
  map_add' e e' := funext fun i => freeCoord_add V e e' i
  map_smul' a e := funext fun i => freeCoord_smul V a e i
  invFun := freeMk V
  left_inv := freeMk_freeCoord V
  right_inv := freeCoord_freeMk V

/-- The linear equivalence `freeCoordEquiv V` sends a section to its coordinates. -/
@[simp] lemma freeCoordEquiv_apply {ι : Type u} [Fintype ι] [DecidableEq ι] (V : Cᵒᵖ)
    (e : ToType ((free (R := S) ι).val.obj V)) :
    freeCoordEquiv (S := S) (ι := ι) V e = freeCoord V e := rfl

/-- The inverse of `freeCoordEquiv V` sends a tuple to the section with those coordinates. -/
@[simp] lemma freeCoordEquiv_symm_apply {ι : Type u} [Fintype ι] [DecidableEq ι] (V : Cᵒᵖ)
    (c : ι → ToType (S.obj.obj V)) :
    (freeCoordEquiv (S := S) (ι := ι) V).symm c = freeMk V c := rfl

/-- Coordinates are compatible with restriction. -/
lemma freeCoord_res {ι : Type u} [DecidableEq ι] {U W : C} (f : W ⟶ U)
    (e : ToType ((free (R := S) ι).val.obj (op U))) (i : ι) :
    freeCoord (S := S) (op W) (res (free (R := S) ι) f e) i
      = resR S f (freeCoord (S := S) (op U) e i) :=
  freeCoord_map f.op e i

/-- Restricting a section with prescribed coordinates restricts its coordinates. -/
lemma res_freeMk {ι : Type u} [Fintype ι] {U W : C} (f : W ⟶ U)
    (c : ι → ToType (S.obj.obj (op U))) :
    res (free (R := S) ι) f (freeMk (op U) c) = freeMk (op W) fun i => resR S f (c i) := by
  classical
  refine (freeCoordEquiv (op W)).injective (funext fun i => ?_)
  simp only [freeCoordEquiv_apply, freeCoord_res, freeCoord_freeMk]

/-- The `a`-th tautological section restricts to the `a`-th tautological section. -/
lemma res_freeMk_single {ι : Type u} [Fintype ι] [DecidableEq ι] {U W : C} (f : W ⟶ U) (a : ι) :
    res (free (R := S) ι) f
        (freeMk (op U) fun b => if a = b then (1 : ToType (S.obj.obj (op U))) else 0)
      = freeMk (op W) fun b => if a = b then 1 else 0 := by
  rw [res_freeMk]
  refine congrArg (freeMk (op W)) (funext fun b => ?_)
  by_cases hb : a = b
  · rw [ite_eq_left hb, ite_eq_left hb, resR_one]
  · rw [ite_eq_right hb, ite_eq_right hb, resR_zero]

/-- The section with prescribed coordinates is the combination of the tautological sections. -/
lemma freeMk_eq_sum_smul_single {ι : Type u} [Fintype ι] [DecidableEq ι] (V : Cᵒᵖ)
    (c : ι → ToType (S.obj.obj V)) :
    ∑ a : ι, c a • freeMk (S := S) V (fun b => if a = b then 1 else 0) = freeMk V c := by
  rw [show (fun a : ι => c a • freeMk (S := S) V (fun b => if a = b then 1 else 0))
      = fun a : ι => freeMk (S := S) V (fun b => c a * if a = b then 1 else 0) from
    funext fun a => freeMk_smul V _ _, freeMk_sum]
  refine congrArg (freeMk V) (funext fun b => ?_)
  simp

end FreeCoordEquiv

/-! ### Matrix cocycles and the module they glue to -/

section Glue

variable {X : TopCat.{u}}

/-- Two morphisms of opens with the same source and target give the same combination map. -/
lemma combSections_hom_eq {R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}
    (M : _root_.SheafOfModules.{u} R) {U : Opens X} {ι : Type u} [Fintype ι]
    (s : ι → ToType (M.val.obj (op U))) {W : Opens X} (f g : W ⟶ U) :
    combSections M s f = combSections M s g := by
  rw [Subsingleton.elim f g]

/-- **Transition data for a sheaf of modules trivialised over a family of opens**, written in
coordinates: a matrix of sections of `O` over every open contained in two members of the family,
compatible with restriction, the identity matrix on the diagonal, and multiplicative along
triples. -/
structure MatrixCocycle (O : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u})
    {K : Type u} (V : K → Opens X) (m : K → ℕ) where
  /-- The transition matrix from the `k`-th to the `l`-th trivialisation, over an open contained
  in both members. -/
  entry : ∀ (k l : K) ⦃W : Opens X⦄, W ≤ V k → W ≤ V l →
    ULift.{u} (Fin (m k)) → ULift.{u} (Fin (m l)) → ToType (O.obj.obj (op W))
  /-- The matrices are compatible with restriction. -/
  entry_res : ∀ (k l : K) ⦃W W' : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hW : W' ≤ W) a b,
    resR O (homOfLE hW) (entry k l hk hl a b) = entry k l (hW.trans hk) (hW.trans hl) a b
  /-- The matrix relating a trivialisation to itself is the identity. -/
  entry_self : ∀ (k : K) ⦃W : Opens X⦄ (hk : W ≤ V k) a b,
    entry k k hk hk a b = if a = b then 1 else 0
  /-- The cocycle condition. -/
  entry_mul : ∀ (k l j : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hj : W ≤ V j) a c,
    ∑ b, entry k l hk hl a b * entry l j hl hj b c = entry k j hk hj a c

namespace MatrixCocycle

variable {O : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}} {K : Type u}
  {V : K → Opens X} {m : K → ℕ} (D : MatrixCocycle O V m)

/-- The free sheaf of `O`-modules on the index set of the `k`-th trivialisation. -/
noncomputable abbrev chart (k : K) : _root_.SheafOfModules.{u} O :=
  _root_.SheafOfModules.free.{u} (ULift.{u} (Fin (m k)))

/-- The transition isomorphism of the glueing datum: multiplication by the transition matrix,
read in coordinates. -/
noncomputable def transEquiv (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l) :
    (chart (O := O) (m := m) k).val.obj (op W)
      ≃ₗ[ToType (O.obj.obj (op W))] (chart (O := O) (m := m) l).val.obj (op W) :=
  (freeCoordEquiv (op W)).trans
    ((rowMulEquiv (D.entry k l hk hl) (D.entry l k hl hk)
        (fun a a' => (D.entry_mul k l k hk hl hk a a').trans (D.entry_self k hk a a'))
        (fun b b' => (D.entry_mul l k l hl hk hl b b').trans (D.entry_self l hl b b'))).trans
      (freeCoordEquiv (op W)).symm)

/-- In coordinates, the transition isomorphism is multiplication by the transition matrix. -/
lemma freeCoordEquiv_transEquiv (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (e : ToType ((chart (O := O) (m := m) k).val.obj (op W))) :
    freeCoordEquiv (op W) (D.transEquiv k l hk hl e)
      = rowMul (D.entry k l hk hl) (freeCoordEquiv (op W) e) :=
  freeCoord_freeMk (op W) _

/-- The transition isomorphisms commute with restriction. -/
lemma transEquiv_res (k l : K) {W W' : Opens X} (hk : W ≤ V k) (hl : W ≤ V l) (hW : W' ≤ W)
    (e : ToType ((chart (O := O) (m := m) k).val.obj (op W))) :
    D.transEquiv k l (hW.trans hk) (hW.trans hl)
        (res (chart (O := O) (m := m) k) (homOfLE hW) e)
      = res (chart (O := O) (m := m) l) (homOfLE hW) (D.transEquiv k l hk hl e) := by
  refine (freeCoordEquiv (op W')).injective (funext fun b => ?_)
  rw [D.freeCoordEquiv_transEquiv, freeCoordEquiv_apply, freeCoordEquiv_apply, freeCoord_res,
    ← freeCoordEquiv_apply (e := D.transEquiv k l hk hl e), D.freeCoordEquiv_transEquiv]
  simp only [rowMul, freeCoordEquiv_apply, resR_sum, freeCoord_res, resR_mul, D.entry_res]

/-- The transition isomorphisms satisfy the cocycle condition. -/
lemma transEquiv_transEquiv (k l j : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (hj : W ≤ V j) (e : ToType ((chart (O := O) (m := m) k).val.obj (op W))) :
    D.transEquiv l j hl hj (D.transEquiv k l hk hl e) = D.transEquiv k j hk hj e := by
  refine (freeCoordEquiv (op W)).injective ?_
  rw [D.freeCoordEquiv_transEquiv l j hl hj, D.freeCoordEquiv_transEquiv k l hk hl,
    D.freeCoordEquiv_transEquiv k j hk hj, rowMul_rowMul,
    show (fun a c => ∑ b, D.entry k l hk hl a b * D.entry l j hl hj b c)
      = D.entry k j hk hj from
    funext fun a => funext fun c => D.entry_mul k l j hk hl hj a c]

/-- The glueing datum assembled from a matrix cocycle: free sheaves of modules on the members of
the family, compared by multiplication by the transition matrices. -/
noncomputable def glueData : OModuleGlueData O V :=
  OModuleGlueData.ofModules (fun k => chart (O := O) (m := m) k)
    (fun k l {_W} hk hl => D.transEquiv k l hk hl)
    (fun k l {_W _W'} hk hl hW e => D.transEquiv_res k l hk hl hW e)
    (fun k l j {_W} hk hl hj e => D.transEquiv_transEquiv k l j hk hl hj e)

/-- **The sheaf of `O`-modules glued from a matrix cocycle.** -/
noncomputable def glued : _root_.SheafOfModules.{u} O := D.glueData.glued

/-- The comparison of the glued sheaf with the `k`-th free chart, on sections over an open
contained in the `k`-th member of the family. -/
noncomputable def chartIso (k : K) {W : Opens X} (h : W ≤ V k) :
    D.glued.val.obj (op W) ≅ (chart (O := O) (m := m) k).val.obj (op W) :=
  D.glueData.chartIso k h

/-- The comparison with the `k`-th chart commutes with restriction. -/
lemma chartIso_hom_res (k : K) {W W' : Opens X} (h : W ≤ V k) (hW : W' ≤ W)
    (s : ToType (D.glued.val.obj (op W))) :
    (D.chartIso k (hW.trans h)).hom (res D.glued (homOfLE hW) s)
      = res (chart (O := O) (m := m) k) (homOfLE hW) ((D.chartIso k h).hom s) :=
  D.glueData.chartIso_hom_restrictₛₗ k h hW s

/-- The transition isomorphism carries the comparison with the `k`-th chart to the comparison
with the `l`-th chart. -/
lemma trans_chartIso_hom (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (s : ToType (D.glued.val.obj (op W))) :
    D.transEquiv k l hk hl ((D.chartIso k hk).hom s) = (D.chartIso l hl).hom s :=
  D.glueData.trans_chartIso_hom k l hk hl s

/-- The `a`-th basis section of the glued sheaf over the `k`-th member of the family. -/
noncomputable def basis (k : K) (a : ULift.{u} (Fin (m k))) :
    ToType (D.glued.val.obj (op (V k))) :=
  (D.chartIso k le_rfl).inv (freeMk (op (V k)) fun b => if a = b then 1 else 0)

/-- In the `k`-th chart, the `a`-th basis section is the `a`-th tautological section. -/
lemma chartIso_hom_basis (k : K) (a : ULift.{u} (Fin (m k))) :
    (D.chartIso k le_rfl).hom (D.basis k a)
      = freeMk (op (V k)) fun b => if a = b then 1 else 0 :=
  (D.chartIso k le_rfl).inv_hom_id_apply _

/-- In the `k`-th chart, the restriction of the `a`-th basis section to an open `W ≤ V k` is the
`a`-th tautological section over `W`. -/
lemma chartIso_hom_res_basis (k : K) {W : Opens X} (h : W ≤ V k) (a : ULift.{u} (Fin (m k))) :
    (D.chartIso k h).hom (res D.glued (homOfLE h) (D.basis k a))
      = freeMk (op W) fun b => if a = b then 1 else 0 := by
  refine Eq.trans (D.chartIso_hom_res k le_rfl h (D.basis k a)) ?_
  rw [chartIso_hom_basis, res_freeMk_single]

/-- In the `k`-th chart, the combination of the restricted basis sections with coefficients `c`
is the section with coordinates `c`. -/
lemma chartIso_hom_combSections (k : K) {W : Opens X} (h : W ≤ V k)
    (c : ULift.{u} (Fin (m k)) → ToType (O.obj.obj (op W))) :
    (D.chartIso k h).hom (combSections D.glued (D.basis k) (homOfLE h) c)
      = freeMk (op W) c := by
  rw [combSections, map_sum, ← freeMk_eq_sum_smul_single]
  exact Finset.sum_congr rfl fun a _ => by rw [map_smul, chartIso_hom_res_basis]

/-- **The basis sections trivialise the glued sheaf** over every open contained in a member of
the family: every section is uniquely a combination of them. -/
theorem bijective_combSections_basis (k : K) {W : Opens X} (h : W ≤ V k) :
    Function.Bijective (combSections D.glued (D.basis k) (homOfLE h)) := by
  refine (Function.Bijective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso (D.chartIso k h).hom) _).mp ?_
  rw [show _ ∘ _ = freeMk (S := O) (op W) from funext (D.chartIso_hom_combSections k h)]
  exact (freeCoordEquiv (op W)).symm.bijective

/-- **The basis sections of two members of the family are related by the transition matrix.** -/
theorem res_basis (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (a : ULift.{u} (Fin (m k))) :
    res D.glued (homOfLE hk) (D.basis k a)
      = combSections D.glued (D.basis l) (homOfLE hl) (D.entry k l hk hl a) := by
  refine (ConcreteCategory.bijective_of_isIso (D.chartIso l hl).hom).1 ?_
  rw [D.chartIso_hom_combSections l hl, ← D.trans_chartIso_hom k l hk hl,
    D.chartIso_hom_res_basis k hk]
  refine (freeCoordEquiv (op W)).injective ?_
  rw [D.freeCoordEquiv_transEquiv k l hk hl]
  simp only [freeCoordEquiv_apply, freeCoord_freeMk]
  funext b
  exact rowMul_single (D.entry k l hk hl) a b

/-- **The sheaf of modules glued from a matrix cocycle over a cover is finite locally free.** -/
theorem isFiniteLocallyFree_glued (hV : ⨆ k, V k = ⊤) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} D.glued :=
  isFiniteLocallyFree_of_combSections_bijective D.glued V hV m D.basis fun k W f => by
    rw [combSections_hom_eq D.glued (D.basis k) f (homOfLE (leOfHom f))]
    exact D.bijective_combSections_basis k (leOfHom f)

end MatrixCocycle

/-! ### The matrix cocycle of a trivialised sheaf of modules -/

section OfTrivialisation

variable {O : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}
  (M : _root_.SheafOfModules.{u} O) {K : Type u} (V : K → Opens X) (m : K → ℕ)
  (t : ∀ k, ULift.{u} (Fin (m k)) → ToType (M.val.obj (op (V k))))
  (hbij : ∀ (k : K) ⦃W : Opens X⦄ (h : W ≤ V k),
    Function.Bijective (combSections M (t k) (homOfLE h)))

/-- **The transition matrix between two trivialisations**: the coordinates, in the `l`-th
trivialisation, of the restricted sections of the `k`-th. -/
noncomputable def transMat (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (a : ULift.{u} (Fin (m k))) : ULift.{u} (Fin (m l)) → ToType (O.obj.obj (op W)) :=
  (Equiv.ofBijective _ (hbij l hl)).symm (res M (homOfLE hk) (t k a))

/-- The defining property of the transition matrix. -/
lemma combSections_transMat (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (a : ULift.{u} (Fin (m k))) :
    combSections M (t l) (homOfLE hl) (transMat M V m t hbij k l hk hl a)
      = res M (homOfLE hk) (t k a) :=
  (Equiv.ofBijective _ (hbij l hl)).apply_symm_apply _

/-- The transition matrix is the unique tuple with that property. -/
lemma eq_transMat (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (a : ULift.{u} (Fin (m k))) (c : ULift.{u} (Fin (m l)) → ToType (O.obj.obj (op W)))
    (hc : combSections M (t l) (homOfLE hl) c = res M (homOfLE hk) (t k a)) :
    c = transMat M V m t hbij k l hk hl a :=
  (hbij l hl).1 (hc.trans (combSections_transMat M V m t hbij k l hk hl a).symm)

/-- The transition matrices are compatible with restriction. -/
lemma transMat_res (k l : K) {W W' : Opens X} (hk : W ≤ V k) (hl : W ≤ V l) (hW : W' ≤ W)
    (a : ULift.{u} (Fin (m k))) (b : ULift.{u} (Fin (m l))) :
    resR O (homOfLE hW) (transMat M V m t hbij k l hk hl a b)
      = transMat M V m t hbij k l (hW.trans hk) (hW.trans hl) a b := by
  refine congrFun (eq_transMat M V m t hbij k l (hW.trans hk) (hW.trans hl) a
    (fun b => resR O (homOfLE hW) (transMat M V m t hbij k l hk hl a b)) ?_) b
  rw [combSections_hom_eq M (t l) (homOfLE (hW.trans hl)) (homOfLE hW ≫ homOfLE hl),
    ← res_combSections, combSections_transMat, res_res]
  exact congrFun (congrArg (res M) (Subsingleton.elim (homOfLE hW ≫ homOfLE hk)
    (homOfLE (hW.trans hk)))) (t k a)

/-- The transition matrix of a trivialisation with itself is the identity. -/
lemma transMat_self (k : K) {W : Opens X} (hk : W ≤ V k) (a b : ULift.{u} (Fin (m k))) :
    transMat M V m t hbij k k hk hk a b = if a = b then 1 else 0 := by
  refine (congrFun (eq_transMat M V m t hbij k k hk hk a
    (fun b => if a = b then 1 else 0) ?_) b).symm
  rw [combSections]
  simp

/-- The transition matrices satisfy the cocycle condition. -/
lemma transMat_mul (k l j : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l) (hj : W ≤ V j)
    (a : ULift.{u} (Fin (m k))) (c : ULift.{u} (Fin (m j))) :
    ∑ b, transMat M V m t hbij k l hk hl a b * transMat M V m t hbij l j hl hj b c
      = transMat M V m t hbij k j hk hj a c := by
  refine congrFun (eq_transMat M V m t hbij k j hk hj a
    (fun c => ∑ b, transMat M V m t hbij k l hk hl a b *
      transMat M V m t hbij l j hl hj b c) ?_) c
  calc combSections M (t j) (homOfLE hj)
        (fun c => ∑ b, transMat M V m t hbij k l hk hl a b *
          transMat M V m t hbij l j hl hj b c)
      = ∑ b, combSections M (t j) (homOfLE hj)
          (fun c => transMat M V m t hbij k l hk hl a b *
            transMat M V m t hbij l j hl hj b c) :=
        (combSections_sum M (t j) (homOfLE hj) Finset.univ
          (fun b c => transMat M V m t hbij k l hk hl a b *
            transMat M V m t hbij l j hl hj b c)).symm
    _ = ∑ b, transMat M V m t hbij k l hk hl a b •
          combSections M (t j) (homOfLE hj) (transMat M V m t hbij l j hl hj b) :=
        Finset.sum_congr rfl fun b _ => combSections_smul M (t j) (homOfLE hj)
          (transMat M V m t hbij k l hk hl a b) (transMat M V m t hbij l j hl hj b)
    _ = ∑ b, transMat M V m t hbij k l hk hl a b • res M (homOfLE hl) (t l b) :=
        Finset.sum_congr rfl fun b _ => congrArg
          (fun y => transMat M V m t hbij k l hk hl a b • y)
          (combSections_transMat M V m t hbij l j hl hj b)
    _ = res M (homOfLE hk) (t k a) := combSections_transMat M V m t hbij k l hk hl a

/-- **A sheaf of modules trivialised over a family of opens gives a matrix cocycle** on that
family: its transition matrices. -/
noncomputable def ofTrivialisation : MatrixCocycle O V m where
  entry k l _ hk hl := transMat M V m t hbij k l hk hl
  entry_res k l _ _ hk hl hW := transMat_res M V m t hbij k l hk hl hW
  entry_self k _ hk := transMat_self M V m t hbij k hk
  entry_mul k l j _ hk hl hj := transMat_mul M V m t hbij k l j hk hl hj

/-- The entries of the matrix cocycle of a trivialisation are its transition matrices. -/
@[simp] lemma ofTrivialisation_entry (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l) :
    (ofTrivialisation M V m t hbij).entry k l hk hl = transMat M V m t hbij k l hk hl := rfl

end OfTrivialisation

end Glue

end Stacks.SheafOfModules

end
