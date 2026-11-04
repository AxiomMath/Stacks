module

public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.MatrixCocycle

/-!
# Comparing two sheaves of modules trivialised by the same transition matrices

Let `α : O ⟶ O'` be a morphism of sheaves of rings on a topological space `X`, let `E` be a
sheaf of `O`-modules and `G` a sheaf of `O'`-modules, and suppose both are trivialised over one
and the same cover `V : K → Opens X` — by sections `e k` of `E` and `t k` of `G` whose linear
combinations exhaust the sections over every smaller open — in such a way that `α` carries the
transition matrices of `E` to those of `G`.

Then `G` is the extension of scalars of `E` along `α`, in the sense that the canonical `O`-linear
comparison

`θ : E ⟶ α_* G`

is *universal*: composing with `θ` is a bijection from `Hom_{O'}(G, T)` onto `Hom_O(E, α_* T)`
for every sheaf of `O'`-modules `T`. Through the adjunction between extension and restriction of
scalars that says exactly that the adjunct of `θ` is an isomorphism `α^* E ≅ G`, and it needs no
knowledge of how `α^* E` is built.

## Main definitions

* `Stacks.SheafOfModules.coordOf`: the coordinates of a section in a trivialisation.
* `Stacks.SheafOfModules.CompatTrivialisation`: the data above.
* `Stacks.SheafOfModules.CompatTrivialisation.compHom`: the comparison `θ : E ⟶ α_* G`, glued
  from the maps which push the coordinates of a section of `E` along `α`.

## Main results

* `Stacks.SheafOfModules.CompatTrivialisation.compHom_val_app`: the comparison reads off
  coordinates and pushes them along `α`.
* `Stacks.SheafOfModules.CompatTrivialisation.bijective_comp_restrictScalars_map`: **composing
  with the comparison is a bijection** from `Hom_{O'}(G, T)` onto `Hom_O(E, α_* T)`, for every
  sheaf of `O'`-modules `T`.

## Implementation notes

Everything is elementary: no sheafification, no tensor product and no pullback functor appears.
The two halves of the bijection are the two halves of the sheaf axiom applied to the cover `V`.
Injectivity holds because the image of `θ` over an open contained in `V k` contains the
restricted sections `t k a`, and those generate; surjectivity is a gluing of the local maps
`y ↦ ∑ a, (coordinates of y in the k-th trivialisation) • g (e k a)`.

Morphisms out of a glued local datum are produced by
`TopCat.Sheaf.existsUnique_hom_of_localModuleHom` and compared by
`TopCat.Sheaf.eq_hom_of_restrict`, both stated for presheaves of modules over a presheaf of
rings on a space, so the sheaf of rings enters only through its underlying presheaf.

Restriction of a section is always written `Stacks.SheafOfModules.res`, never `M.val.map f.op`,
and a morphism `g : E ⟶ α_* T` is applied through `Stacks.SheafOfModules.pushApp`, whose value
is *ascribed* to the sections of `T`.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules

universe u v u'

namespace Stacks.SheafOfModules

/-- The `b`-th entry of the row vector `c` times the matrix `A` is `∑ a, c a * A a b`. -/
lemma rowMul_apply {Rr : Type*} [Ring Rr] {ι κ : Type*} [Fintype ι] (A : ι → κ → Rr)
    (c : ι → Rr) (b : κ) : rowMul A c b = ∑ a : ι, c a * A a b := rfl

/-- The combination of the sections `s` with coefficients `c` is `∑ i, c i • s i|_W`. -/
lemma combSections_eq_sum {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : _root_.SheafOfModules.{u} R) {U : C} {ι : Type u} [Fintype ι]
    (s : ι → ToType (M.val.obj (op U))) {W : C} (f : W ⟶ U)
    (c : ι → ToType (R.obj.obj (op W))) :
    combSections M s f c = ∑ i : ι, c i • res M f (s i) := rfl

/-! ### Coordinates in a trivialisation -/

section Coord

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}
  (M : _root_.SheafOfModules.{u} O) {K : Type u} (V : K → Opens X) (m : K → ℕ)
  (s : ∀ k, ULift.{u} (Fin (m k)) → ToType (M.val.obj (op (V k))))
  (hbij : ∀ (k : K) ⦃W : Opens X⦄ (h : W ≤ V k),
    Function.Bijective (combSections M (s k) (homOfLE h)))

/-- The coordinates of a section in a trivialisation. -/
noncomputable def coordOf (k : K) {W : Opens X} (h : W ≤ V k)
    (x : ToType (M.val.obj (op W))) : ULift.{u} (Fin (m k)) → ToType (O.obj.obj (op W)) :=
  (Equiv.ofBijective _ (hbij k h)).symm x

/-- A section is the combination of the trivialising sections with its coordinates. -/
lemma combSections_coordOf (k : K) {W : Opens X} (h : W ≤ V k)
    (x : ToType (M.val.obj (op W))) :
    combSections M (s k) (homOfLE h) (coordOf M V m s hbij k h x) = x :=
  (Equiv.ofBijective _ (hbij k h)).apply_symm_apply x

/-- The coordinates of a combination of the trivialising sections are its coefficients. -/
lemma coordOf_combSections (k : K) {W : Opens X} (h : W ≤ V k)
    (c : ULift.{u} (Fin (m k)) → ToType (O.obj.obj (op W))) :
    coordOf M V m s hbij k h (combSections M (s k) (homOfLE h) c) = c :=
  (Equiv.ofBijective _ (hbij k h)).symm_apply_apply c

/-- Coefficients whose combination is `x` are the coordinates of `x`. -/
lemma eq_coordOf (k : K) {W : Opens X} (h : W ≤ V k)
    (c : ULift.{u} (Fin (m k)) → ToType (O.obj.obj (op W))) (x : ToType (M.val.obj (op W)))
    (hc : combSections M (s k) (homOfLE h) c = x) : c = coordOf M V m s hbij k h x := by
  rw [← hc, coordOf_combSections]

/-- Coefficients whose combination is `x` give the coordinates of `x`, entrywise. -/
private lemma coordOf_apply_of_combSections (k : K) {W : Opens X} (h : W ≤ V k)
    (c : ULift.{u} (Fin (m k)) → ToType (O.obj.obj (op W))) (x : ToType (M.val.obj (op W)))
    (hc : combSections M (s k) (homOfLE h) c = x) (b : ULift.{u} (Fin (m k))) :
    coordOf M V m s hbij k h x b = c b :=
  (congrFun (eq_coordOf M V m s hbij k h c x hc) b).symm

/-- Restricting a combination of the sections `s k` restricts its coefficients. -/
private lemma combSections_res_homOfLE (k : K) {W W' : Opens X} (h : W ≤ V k) (h' : W' ≤ W)
    (c : ULift.{u} (Fin (m k)) → ToType (O.obj.obj (op W))) :
    combSections M (s k) (homOfLE (h'.trans h)) (fun a => resR O (homOfLE h') (c a))
      = res M (homOfLE h') (combSections M (s k) (homOfLE h) c) := by
  rw [combSections_hom_eq M (s k) (homOfLE (h'.trans h)) (homOfLE h' ≫ homOfLE h),
    ← res_combSections]

/-- The coordinates of a sum are the sums of the coordinates. -/
lemma coordOf_add (k : K) {W : Opens X} (h : W ≤ V k) (x y : ToType (M.val.obj (op W)))
    (b : ULift.{u} (Fin (m k))) :
    coordOf M V m s hbij k h (x + y) b
      = coordOf M V m s hbij k h x b + coordOf M V m s hbij k h y b := by
  refine coordOf_apply_of_combSections M V m s hbij k h
    (fun b => coordOf M V m s hbij k h x b + coordOf M V m s hbij k h y b) (x + y) ?_ b
  rw [combSections_add, combSections_coordOf, combSections_coordOf]

/-- The coordinates of `r • x` are `r` times the coordinates of `x`. -/
lemma coordOf_smul (k : K) {W : Opens X} (h : W ≤ V k) (r : ToType (O.obj.obj (op W)))
    (x : ToType (M.val.obj (op W))) (b : ULift.{u} (Fin (m k))) :
    coordOf M V m s hbij k h (r • x) b = r * coordOf M V m s hbij k h x b := by
  refine coordOf_apply_of_combSections M V m s hbij k h
    (fun b => r * coordOf M V m s hbij k h x b) (r • x) ?_ b
  rw [combSections_smul, combSections_coordOf]

/-- The coordinates of a restricted section are the restrictions of its coordinates. -/
lemma coordOf_res (k : K) {W W' : Opens X} (h : W ≤ V k) (h' : W' ≤ W)
    (x : ToType (M.val.obj (op W))) (b : ULift.{u} (Fin (m k))) :
    coordOf M V m s hbij k (h'.trans h) (res M (homOfLE h') x) b
      = resR O (homOfLE h') (coordOf M V m s hbij k h x b) := by
  refine coordOf_apply_of_combSections M V m s hbij k (h'.trans h)
    (fun b => resR O (homOfLE h') (coordOf M V m s hbij k h x b))
    (res M (homOfLE h') x) ?_ b
  rw [combSections_res_homOfLE M V m s k h h', combSections_coordOf]

/-- The combination with the `a`-th tautological coefficients is the `a`-th section. -/
lemma combSections_single (k : K) {W : Opens X} (h : W ≤ V k) (a : ULift.{u} (Fin (m k))) :
    combSections M (s k) (homOfLE h) (fun b => if a = b then 1 else 0)
      = res M (homOfLE h) (s k a) := by
  rw [combSections_eq_sum]
  simp

/-- The coordinates of the restriction of the `a`-th trivialising section are the `a`-th
standard basis vector. -/
lemma coordOf_res_self (k : K) {W : Opens X} (h : W ≤ V k) (a b : ULift.{u} (Fin (m k))) :
    coordOf M V m s hbij k h (res M (homOfLE h) (s k a)) b = if a = b then 1 else 0 :=
  coordOf_apply_of_combSections M V m s hbij k h _ _ (combSections_single M V m s k h a) b

/-- **The combination of a matrix-transformed tuple.** If the sections `w k` are related by the
matrices `B`, then the `l`-th combination of `d` transformed by `B k l` is the `k`-th
combination of `d`. -/
lemma combSections_rowMul
    (w : ∀ k, ULift.{u} (Fin (m k)) → ToType (M.val.obj (op (V k))))
    (B : ∀ (k l : K) ⦃W : Opens X⦄, W ≤ V k → W ≤ V l →
      ULift.{u} (Fin (m k)) → ULift.{u} (Fin (m l)) → ToType (O.obj.obj (op W)))
    (hB : ∀ (k l : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) a,
      res M (homOfLE hk) (w k a) = combSections M (w l) (homOfLE hl) (B k l hk hl a))
    (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (d : ULift.{u} (Fin (m k)) → ToType (O.obj.obj (op W))) :
    combSections M (w l) (homOfLE hl) (rowMul (B k l hk hl) d)
      = combSections M (w k) (homOfLE hk) d :=
  calc combSections M (w l) (homOfLE hl) (rowMul (B k l hk hl) d)
      = ∑ a, combSections M (w l) (homOfLE hl) (fun b => d a * B k l hk hl a b) :=
        (combSections_sum M (w l) (homOfLE hl) Finset.univ
          (fun a b => d a * B k l hk hl a b)).symm
    _ = ∑ a, d a • combSections M (w l) (homOfLE hl) (B k l hk hl a) :=
        Finset.sum_congr rfl fun a _ =>
          combSections_smul M (w l) (homOfLE hl) (d a) (B k l hk hl a)
    _ = ∑ a, d a • res M (homOfLE hk) (w k a) :=
        Finset.sum_congr rfl fun a _ => congrArg (fun y => d a • y) (hB k l hk hl a).symm
    _ = combSections M (w k) (homOfLE hk) d := rfl

/-- The coordinates in one trivialisation are the matrix transform of those in another. -/
lemma coordOf_eq_rowMul (k l : K) {W : Opens X} (hk : W ≤ V k) (hl : W ≤ V l)
    (x : ToType (M.val.obj (op W))) :
    coordOf M V m s hbij l hl x
      = rowMul (transMat M V m s hbij k l hk hl) (coordOf M V m s hbij k hk x) :=
  (eq_coordOf M V m s hbij l hl _ x
    ((combSections_rowMul M V m s (fun k l _ hk hl => transMat M V m s hbij k l hk hl)
        (fun k l _ hk hl a => (combSections_transMat M V m s hbij k l hk hl a).symm)
        k l hk hl (coordOf M V m s hbij k hk x)).trans
      (combSections_coordOf M V m s hbij k hk x))).symm

end Coord


/-! ### Applying a morphism into a restriction of scalars -/

section Push

variable {X : TopCat.{u}} {O O' : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}
  {α : O ⟶ O'} {E : _root_.SheafOfModules.{u} O} {T : _root_.SheafOfModules.{u} O'}
  (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T)

/-- An `O`-linear morphism `E ⟶ α_* T` applied to a section of `E`, with the value ascribed to
the sections of `T`. The sections of `α_* T` are the same type carrying the `O`-action, so a
term spelled there finds the `O`-module instance and no `O'`-scalar can be multiplied into it. -/
noncomputable def pushApp {W : Opens X} (x : ToType (E.val.obj (op W))) :
    ToType (T.val.obj (op W)) :=
  g.val.app (op W) x

/-- `pushApp g` is semilinear along `α`: `pushApp g (r • x) = α r • pushApp g x`. -/
lemma pushApp_smul {W : Opens X} (r : ToType (O.obj.obj (op W)))
    (x : ToType (E.val.obj (op W))) :
    pushApp g (r • x) = α.hom.app (op W) r • pushApp g x :=
  (map_smul (g.val.app (op W)).hom r x).trans
    (ModuleCat.restrictScalars.smul_def (α.hom.app (op W)).hom r (g.val.app (op W) x))

/-- `pushApp g` commutes with finite sums. -/
lemma pushApp_sum {W : Opens X} {ι : Type*} (fs : Finset ι)
    (x : ι → ToType (E.val.obj (op W))) :
    pushApp g (∑ i ∈ fs, x i) = ∑ i ∈ fs, pushApp g (x i) :=
  map_sum _ x fs

/-- `pushApp g` commutes with restriction. -/
lemma pushApp_res {W W' : Opens X} (h' : W' ≤ W) (x : ToType (E.val.obj (op W))) :
    pushApp g (res E (homOfLE h') x) = res T (homOfLE h') (pushApp g x) :=
  PresheafOfModules.naturality_apply g.val (homOfLE h').op x

end Push

/-! ### Compatible trivialisations -/

/-- **Trivialisations of a sheaf of `O`-modules and of a sheaf of `O'`-modules over one and the
same cover of the space, whose transition matrices correspond under a morphism `α : O ⟶ O'` of
sheaves of rings.** -/
structure CompatTrivialisation {X : TopCat.{u}}
    {O O' : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}} (α : O ⟶ O')
    (E : _root_.SheafOfModules.{u} O) (G : _root_.SheafOfModules.{u} O') where
  /-- The index type of the cover. -/
  K : Type u
  /-- The cover. -/
  V : K → Opens X
  /-- The family covers the space. -/
  cover : ⨆ k, V k = ⊤
  /-- The ranks. -/
  m : K → ℕ
  /-- The trivialising sections of `E`. -/
  e : ∀ k, ULift.{u} (Fin (m k)) → ToType (E.val.obj (op (V k)))
  /-- The trivialising sections of `G`. -/
  t : ∀ k, ULift.{u} (Fin (m k)) → ToType (G.val.obj (op (V k)))
  /-- The sections of `E` trivialise it. -/
  bijE : ∀ (k : K) ⦃W : Opens X⦄ (h : W ≤ V k),
    Function.Bijective (combSections E (e k) (homOfLE h))
  /-- The sections of `G` trivialise it. -/
  bijG : ∀ (k : K) ⦃W : Opens X⦄ (h : W ≤ V k),
    Function.Bijective (combSections G (t k) (homOfLE h))
  /-- The transition matrices correspond under `α`. -/
  compat : ∀ (k l : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) a b,
    α.hom.app (op W) (transMat E V m e bijE k l hk hl a b)
      = transMat G V m t bijG k l hk hl a b

namespace CompatTrivialisation

variable {X : TopCat.{u}} {O O' : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}
  {α : O ⟶ O'} {E : _root_.SheafOfModules.{u} O} {G : _root_.SheafOfModules.{u} O'}
  (C : CompatTrivialisation α E G)

/-! #### Coordinates and transition matrices -/

/-- The coordinates of a section of `E` in the `k`-th trivialisation. -/
noncomputable def coordE (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (x : ToType (E.val.obj (op W))) : ULift.{u} (Fin (C.m k)) → ToType (O.obj.obj (op W)) :=
  coordOf E C.V C.m C.e C.bijE k h x

/-- The coordinates of a section of `G` in the `k`-th trivialisation. -/
noncomputable def coordG (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (y : ToType (G.val.obj (op W))) : ULift.{u} (Fin (C.m k)) → ToType (O'.obj.obj (op W)) :=
  coordOf G C.V C.m C.t C.bijG k h y

/-- The transition matrix of the trivialisation of `E`. -/
noncomputable def matE (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l) :
    ULift.{u} (Fin (C.m k)) → ULift.{u} (Fin (C.m l)) → ToType (O.obj.obj (op W)) :=
  transMat E C.V C.m C.e C.bijE k l hk hl

/-- The transition matrix of the trivialisation of `G`. -/
noncomputable def matG (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l) :
    ULift.{u} (Fin (C.m k)) → ULift.{u} (Fin (C.m l)) → ToType (O'.obj.obj (op W)) :=
  transMat G C.V C.m C.t C.bijG k l hk hl

/-- The morphism `α` carries the transition matrix `matE` to `matG`. -/
lemma compat' (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l)
    (a : ULift.{u} (Fin (C.m k))) (b : ULift.{u} (Fin (C.m l))) :
    α.hom.app (op W) (C.matE k l hk hl a b) = C.matG k l hk hl a b :=
  C.compat k l hk hl a b

/-- A section of `E` is the combination of the sections `e k` with its coordinates. -/
lemma combSections_coordE (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (x : ToType (E.val.obj (op W))) :
    combSections E (C.e k) (homOfLE h) (C.coordE k h x) = x :=
  combSections_coordOf E C.V C.m C.e C.bijE k h x

/-- A section of `G` is the combination of the sections `t k` with its coordinates. -/
lemma combSections_coordG (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (y : ToType (G.val.obj (op W))) :
    combSections G (C.t k) (homOfLE h) (C.coordG k h y) = y :=
  combSections_coordOf G C.V C.m C.t C.bijG k h y

/-- Coefficients whose combination of the sections `t k` is `y` are the coordinates of `y`. -/
lemma eq_coordG (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (c : ULift.{u} (Fin (C.m k)) → ToType (O'.obj.obj (op W)))
    (y : ToType (G.val.obj (op W))) (hc : combSections G (C.t k) (homOfLE h) c = y) :
    c = C.coordG k h y :=
  eq_coordOf G C.V C.m C.t C.bijG k h c y hc

/-- The coordinates in `E` of a sum are the sums of the coordinates. -/
lemma coordE_add (k : C.K) {W : Opens X} (h : W ≤ C.V k) (x y : ToType (E.val.obj (op W)))
    (b : ULift.{u} (Fin (C.m k))) :
    C.coordE k h (x + y) b = C.coordE k h x b + C.coordE k h y b :=
  coordOf_add E C.V C.m C.e C.bijE k h x y b

/-- The coordinates in `E` of `r • x` are `r` times the coordinates of `x`. -/
lemma coordE_smul (k : C.K) {W : Opens X} (h : W ≤ C.V k) (r : ToType (O.obj.obj (op W)))
    (x : ToType (E.val.obj (op W))) (b : ULift.{u} (Fin (C.m k))) :
    C.coordE k h (r • x) b = r * C.coordE k h x b :=
  coordOf_smul E C.V C.m C.e C.bijE k h r x b

/-- The coordinates in `E` of a restricted section are the restrictions of its coordinates. -/
lemma coordE_res (k : C.K) {W W' : Opens X} (h : W ≤ C.V k) (h' : W' ≤ W)
    (x : ToType (E.val.obj (op W))) (b : ULift.{u} (Fin (C.m k))) :
    C.coordE k (h'.trans h) (res E (homOfLE h') x) b
      = resR O (homOfLE h') (C.coordE k h x b) :=
  coordOf_res E C.V C.m C.e C.bijE k h h' x b

/-- The coordinates of the restriction of `e k a` are the `a`-th standard basis vector. -/
lemma coordE_res_self (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (a b : ULift.{u} (Fin (C.m k))) :
    C.coordE k h (res E (homOfLE h) (C.e k a)) b = if a = b then 1 else 0 :=
  coordOf_res_self E C.V C.m C.e C.bijE k h a b

/-- The `l`-th coordinates in `E` are the `k`-th coordinates transformed by `matE k l`. -/
lemma coordE_eq_rowMul (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l)
    (x : ToType (E.val.obj (op W))) :
    C.coordE l hl x = rowMul (C.matE k l hk hl) (C.coordE k hk x) :=
  coordOf_eq_rowMul E C.V C.m C.e C.bijE k l hk hl x

/-- The coordinates in `G` of a sum are the sums of the coordinates. -/
lemma coordG_add (k : C.K) {W : Opens X} (h : W ≤ C.V k) (y z : ToType (G.val.obj (op W)))
    (b : ULift.{u} (Fin (C.m k))) :
    C.coordG k h (y + z) b = C.coordG k h y b + C.coordG k h z b :=
  coordOf_add G C.V C.m C.t C.bijG k h y z b

/-- The coordinates in `G` of `r • y` are `r` times the coordinates of `y`. -/
lemma coordG_smul (k : C.K) {W : Opens X} (h : W ≤ C.V k) (r : ToType (O'.obj.obj (op W)))
    (y : ToType (G.val.obj (op W))) (b : ULift.{u} (Fin (C.m k))) :
    C.coordG k h (r • y) b = r * C.coordG k h y b :=
  coordOf_smul G C.V C.m C.t C.bijG k h r y b

/-- The coordinates in `G` of a restricted section are the restrictions of its coordinates. -/
lemma coordG_res (k : C.K) {W W' : Opens X} (h : W ≤ C.V k) (h' : W' ≤ W)
    (y : ToType (G.val.obj (op W))) (b : ULift.{u} (Fin (C.m k))) :
    C.coordG k (h'.trans h) (res G (homOfLE h') y) b
      = resR O' (homOfLE h') (C.coordG k h y b) :=
  coordOf_res G C.V C.m C.t C.bijG k h h' y b

/-- The `l`-th coordinates in `G` are the `k`-th coordinates transformed by `matG k l`. -/
lemma coordG_eq_rowMul (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l)
    (y : ToType (G.val.obj (op W))) :
    C.coordG l hl y = rowMul (C.matG k l hk hl) (C.coordG k hk y) :=
  coordOf_eq_rowMul G C.V C.m C.t C.bijG k l hk hl y

/-- The transition matrices of `E` relate its trivialising sections. -/
lemma res_e_eq (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l)
    (a : ULift.{u} (Fin (C.m k))) :
    res E (homOfLE hk) (C.e k a)
      = combSections E (C.e l) (homOfLE hl) (C.matE k l hk hl a) :=
  (combSections_transMat E C.V C.m C.e C.bijE k l hk hl a).symm

/-- The transition matrices of `G` relate its trivialising sections. -/
lemma res_t_eq (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l)
    (a : ULift.{u} (Fin (C.m k))) :
    res G (homOfLE hk) (C.t k a)
      = combSections G (C.t l) (homOfLE hl) (C.matG k l hk hl a) :=
  (combSections_transMat G C.V C.m C.t C.bijG k l hk hl a).symm

/-- The `l`-th combination in `G` of `d` transformed by `matG k l` is the `k`-th combination
of `d`. -/
lemma combSections_rowMul_matG (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l)
    (d : ULift.{u} (Fin (C.m k)) → ToType (O'.obj.obj (op W))) :
    combSections G (C.t l) (homOfLE hl) (rowMul (C.matG k l hk hl) d)
      = combSections G (C.t k) (homOfLE hk) d :=
  combSections_rowMul G C.V C.m C.t (fun k l _ hk hl => C.matG k l hk hl)
    (fun k l _ hk hl a => C.res_t_eq k l hk hl a) k l hk hl d

/-! #### The comparison morphism -/

/-- The comparison on sections over an open contained in the `k`-th member of the cover: read
the coordinates of a section of `E` and push them along `α`. -/
noncomputable def compMap (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (x : ToType (E.val.obj (op W))) : ToType (G.val.obj (op W)) :=
  combSections G (C.t k) (homOfLE h) fun a => α.hom.app (op W) (C.coordE k h x a)

/-- `compMap k h x` is the combination of the sections `t k` with the coordinates of `x`
pushed along `α`. -/
lemma compMap_def (k : C.K) {W : Opens X} (h : W ≤ C.V k) (x : ToType (E.val.obj (op W))) :
    C.compMap k h x
      = combSections G (C.t k) (homOfLE h) fun a => α.hom.app (op W) (C.coordE k h x a) := rfl

/-- The local comparison is additive. -/
lemma compMap_add (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (x y : ToType (E.val.obj (op W))) :
    C.compMap k h (x + y) = C.compMap k h x + C.compMap k h y := by
  rw [compMap_def, compMap_def, compMap_def, ← combSections_add]
  exact congrArg _ (funext fun a => by rw [C.coordE_add k h x y a, map_add])

/-- The local comparison is semilinear along `α`. -/
lemma compMap_smul (k : C.K) {W : Opens X} (h : W ≤ C.V k) (r : ToType (O.obj.obj (op W)))
    (x : ToType (E.val.obj (op W))) :
    C.compMap k h (r • x) = α.hom.app (op W) r • C.compMap k h x := by
  rw [compMap_def, compMap_def, ← combSections_smul]
  exact congrArg _ (funext fun a => by rw [C.coordE_smul k h r x a, map_mul])

/-- The local comparison commutes with restriction. -/
lemma compMap_res (k : C.K) {W W' : Opens X} (h : W ≤ C.V k) (h' : W' ≤ W)
    (x : ToType (E.val.obj (op W))) :
    C.compMap k (h'.trans h) (res E (homOfLE h') x)
      = res G (homOfLE h') (C.compMap k h x) := by
  rw [compMap_def, compMap_def,
    show (fun a => α.hom.app (op W') (C.coordE k (h'.trans h) (res E (homOfLE h') x) a))
      = (fun a => resR O' (homOfLE h') (α.hom.app (op W) (C.coordE k h x a))) from
      funext fun a => by
        rw [C.coordE_res k h h' x a]
        exact NatTrans.naturality_apply α.hom (homOfLE h').op (C.coordE k h x a),
    combSections_res_homOfLE]

/-- The coordinates in `G` of `compMap k h x` are the coordinates of `x` pushed along `α`. -/
lemma coordG_compMap (k : C.K) {W : Opens X} (h : W ≤ C.V k) (x : ToType (E.val.obj (op W)))
    (a : ULift.{u} (Fin (C.m k))) :
    C.coordG k h (C.compMap k h x) a = α.hom.app (op W) (C.coordE k h x a) :=
  coordOf_apply_of_combSections G C.V C.m C.t C.bijG k h _ _ rfl a

/-- The local comparison sends the restriction of `e k a` to the restriction of `t k a`. -/
lemma compMap_res_self (k : C.K) {W : Opens X} (h : W ≤ C.V k) (a : ULift.{u} (Fin (C.m k))) :
    C.compMap k h (res E (homOfLE h) (C.e k a)) = res G (homOfLE h) (C.t k a) := by
  rw [compMap_def]
  refine Eq.trans (congrArg _ (funext fun b => ?_)) (combSections_single G C.V C.m C.t k h a)
  rw [C.coordE_res_self k h a b]
  by_cases hb : a = b
  · rw [ite_eq_left hb, ite_eq_left hb, map_one]
  · rw [ite_eq_right hb, ite_eq_right hb, map_zero]

/-- On an open contained in two members of the cover the two comparisons agree. -/
lemma compMap_eq (k l : C.K) {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l)
    (x : ToType (E.val.obj (op W))) : C.compMap k hk x = C.compMap l hl x := by
  rw [compMap_def, compMap_def]
  refine Eq.trans (C.combSections_rowMul_matG k l hk hl
    (fun a => α.hom.app (op W) (C.coordE k hk x a))).symm ?_
  refine congrArg _ (funext fun b => ?_)
  rw [C.coordE_eq_rowMul k l hk hl x, rowMul_apply, rowMul_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [map_mul, C.compat' k l hk hl a b]

/-- The comparison over the `k`-th member of the cover, as a semilinear map. -/
noncomputable def compSemilinear (k : C.K) {W : Opens X} (h : W ≤ C.V k) :
    E.val.obj (op W) →ₛₗ[(α.hom.app (op W)).hom] G.val.obj (op W) where
  toFun := C.compMap k h
  map_add' := C.compMap_add k h
  map_smul' := C.compMap_smul k h

/-- The comparison over the `k`-th member of the cover, as local morphism data. -/
noncomputable def localCompHom (k : C.K) :
    TopCat.Sheaf.LocalModuleHom E.val
      ((_root_.SheafOfModules.restrictScalars α).obj G).val (C.V k) where
  app _ h := ModuleCat.semilinearMapAddEquiv _ _ _ (C.compSemilinear k h)
  naturality h h' x := C.compMap_res k h h' x

/-- On an open contained in two members of the cover the two local comparisons agree. -/
lemma localCompHom_app_eq (k l : C.K) (W : Opens X) (hk : W ≤ C.V k) (hl : W ≤ C.V l) :
    (C.localCompHom k).app W hk = (C.localCompHom l).app W hl :=
  ModuleCat.hom_ext (LinearMap.ext fun x => C.compMap_eq k l hk hl x)

/-- **The comparison morphism `θ : E ⟶ α_* G`.** -/
noncomputable def compHom : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj G :=
  ⟨TopCat.Sheaf.LocalModuleHom.gluedHom C.cover
    ((_root_.SheafOfModules.restrictScalars α).obj G).isSheaf C.localCompHom
    C.localCompHom_app_eq⟩

/-- The comparison morphism reads off coordinates and pushes them along `α`. -/
lemma compHom_val_app (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (x : ToType (E.val.obj (op W))) :
    C.compHom.val.app (op W) x = C.compMap k h x :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.LocalModuleHom.gluedHom_app C.cover
    ((_root_.SheafOfModules.restrictScalars α).obj G).isSheaf C.localCompHom
    C.localCompHom_app_eq k W h) x

/-! #### The comparison is universal -/

variable (T : _root_.SheafOfModules.{u} O')

/-- Applying a morphism out of `G` to a combination of the trivialising sections. -/
lemma app_combSections (f : G ⟶ T) (k : C.K) {W : Opens X} (h : W ≤ C.V k)
    (d : ULift.{u} (Fin (C.m k)) → ToType (O'.obj.obj (op W))) :
    f.val.app (op W) (combSections G (C.t k) (homOfLE h) d)
      = ∑ a, d a • f.val.app (op W) (res G (homOfLE h) (C.t k a)) := by
  rw [combSections_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- **Composing with the comparison is injective.** -/
theorem injective_comp_restrictScalars_map :
    Function.Injective fun f : G ⟶ T =>
      C.compHom ≫ (_root_.SheafOfModules.restrictScalars α).map f := by
  intro f f' hff
  have key : ∀ (k : C.K) ⦃W : Opens X⦄ (h : W ≤ C.V k) (a : ULift.{u} (Fin (C.m k))),
      f.val.app (op W) (res G (homOfLE h) (C.t k a))
        = f'.val.app (op W) (res G (homOfLE h) (C.t k a)) := by
    intro k W h a
    have h2 : f.val.app (op W) (C.compHom.val.app (op W) (res E (homOfLE h) (C.e k a)))
        = f'.val.app (op W) (C.compHom.val.app (op W) (res E (homOfLE h) (C.e k a))) :=
      ConcreteCategory.congr_hom
        (congrArg (fun z : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T =>
          z.val.app (op W)) hff) _
    rwa [C.compHom_val_app k h, C.compMap_res_self k h a] at h2
  refine _root_.SheafOfModules.Hom.ext ?_
  refine TopCat.Sheaf.eq_hom_of_restrict C.cover T.isSheaf
    (fun _ W _ => f.val.app (op W)) (fun _ _ _ => rfl) fun k W h => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  rw [← C.combSections_coordG k h y, C.app_combSections T f' k h, C.app_combSections T f k h]
  exact Finset.sum_congr rfl fun a _ => congrArg _ (key k h a).symm

/-- The sections of `T` obtained by applying an `O`-linear morphism to the trivialising sections
of `E`. -/
noncomputable def pushSections
    (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k : C.K)
    (a : ULift.{u} (Fin (C.m k))) : ToType (T.val.obj (op (C.V k))) :=
  pushApp g (C.e k a)

/-- The restriction of `pushSections T g k a` is `g` applied to the restriction of `e k a`. -/
lemma res_pushSections (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k : C.K)
    {W : Opens X} (h : W ≤ C.V k) (a : ULift.{u} (Fin (C.m k))) :
    res T (homOfLE h) (C.pushSections T g k a) = pushApp g (res E (homOfLE h) (C.e k a)) :=
  (pushApp_res g h (C.e k a)).symm

/-- The sections `pushSections T g` are related by the transition matrices of `G`. -/
lemma res_pushSections_eq (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k l : C.K)
    {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l) (a : ULift.{u} (Fin (C.m k))) :
    res T (homOfLE hk) (C.pushSections T g k a)
      = combSections T (C.pushSections T g l) (homOfLE hl) (C.matG k l hk hl a) := by
  rw [C.res_pushSections T g k hk a, C.res_e_eq k l hk hl a, combSections_eq_sum,
    pushApp_sum, combSections_eq_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pushApp_smul, C.compat' k l hk hl a b, C.res_pushSections T g l hl b]

/-- The local morphism `G ⟶ T` over the `k`-th member of the cover determined by an `O`-linear
morphism `E ⟶ α_* T`. -/
noncomputable def invMap (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k : C.K)
    {W : Opens X} (h : W ≤ C.V k) (y : ToType (G.val.obj (op W))) :
    ToType (T.val.obj (op W)) :=
  combSections T (C.pushSections T g k) (homOfLE h) (C.coordG k h y)

/-- `invMap T g k h y` is the combination of the sections `pushSections T g k` with the
coordinates of `y`. -/
lemma invMap_def (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k : C.K)
    {W : Opens X} (h : W ≤ C.V k) (y : ToType (G.val.obj (op W))) :
    C.invMap T g k h y
      = combSections T (C.pushSections T g k) (homOfLE h) (C.coordG k h y) := rfl

/-- The local morphism `invMap T g k h` is additive. -/
lemma invMap_add (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k : C.K)
    {W : Opens X} (h : W ≤ C.V k) (y z : ToType (G.val.obj (op W))) :
    C.invMap T g k h (y + z) = C.invMap T g k h y + C.invMap T g k h z := by
  rw [C.invMap_def T g k h, C.invMap_def T g k h, C.invMap_def T g k h, ← combSections_add]
  exact congrArg _ (funext fun a => C.coordG_add k h y z a)

/-- The local morphism `invMap T g k h` is `O'`-linear. -/
lemma invMap_smul (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k : C.K)
    {W : Opens X} (h : W ≤ C.V k) (r : ToType (O'.obj.obj (op W)))
    (y : ToType (G.val.obj (op W))) :
    C.invMap T g k h (r • y) = r • C.invMap T g k h y := by
  rw [C.invMap_def T g k h, C.invMap_def T g k h, ← combSections_smul]
  exact congrArg _ (funext fun a => C.coordG_smul k h r y a)

/-- The local morphism `invMap T g k` commutes with restriction. -/
lemma invMap_res (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k : C.K)
    {W W' : Opens X} (h : W ≤ C.V k) (h' : W' ≤ W) (y : ToType (G.val.obj (op W))) :
    C.invMap T g k (h'.trans h) (res G (homOfLE h') y)
      = res T (homOfLE h') (C.invMap T g k h y) := by
  rw [C.invMap_def T g k (h'.trans h), C.invMap_def T g k h,
    show C.coordG k (h'.trans h) (res G (homOfLE h') y)
      = (fun a => resR O' (homOfLE h') (C.coordG k h y a)) from
      funext fun a => C.coordG_res k h h' y a,
    combSections_res_homOfLE]

/-- On an open contained in two members of the cover the two local morphisms agree. -/
lemma invMap_eq (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k l : C.K)
    {W : Opens X} (hk : W ≤ C.V k) (hl : W ≤ C.V l) (y : ToType (G.val.obj (op W))) :
    C.invMap T g k hk y = C.invMap T g l hl y := by
  rw [C.invMap_def T g k hk, C.invMap_def T g l hl, C.coordG_eq_rowMul k l hk hl y]
  exact (combSections_rowMul T C.V C.m (C.pushSections T g)
    (fun k l _ hk hl => C.matG k l hk hl)
    (fun k l _ hk hl a => C.res_pushSections_eq T g k l hk hl a) k l hk hl
    (C.coordG k hk y)).symm

/-- The local morphism data out of `G` determined by an `O`-linear morphism `E ⟶ α_* T`. -/
noncomputable def localInvHom (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T)
    (k : C.K) : TopCat.Sheaf.LocalModuleHom G.val T.val (C.V k) where
  app _ h := ModuleCat.ofHom
    { toFun := C.invMap T g k h
      map_add' := C.invMap_add T g k h
      map_smul' := C.invMap_smul T g k h }
  naturality h h' y := C.invMap_res T g k h h' y

/-- On an open contained in two members of the cover the two local morphism data agree. -/
lemma localInvHom_app_eq (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) (k l : C.K)
    (W : Opens X) (hk : W ≤ C.V k) (hl : W ≤ C.V l) :
    (C.localInvHom T g k).app W hk = (C.localInvHom T g l).app W hl :=
  ModuleCat.hom_ext (LinearMap.ext fun y => C.invMap_eq T g k l hk hl y)

/-- **Composing with the comparison is surjective.** -/
theorem exists_comp_restrictScalars_map_eq
    (g : E ⟶ (_root_.SheafOfModules.restrictScalars α).obj T) :
    ∃ f : G ⟶ T, C.compHom ≫ (_root_.SheafOfModules.restrictScalars α).map f = g := by
  have hgl : ∀ (k : C.K) (W : Opens X) (h : W ≤ C.V k) (y : ToType (G.val.obj (op W))),
      (TopCat.Sheaf.LocalModuleHom.gluedHom C.cover T.isSheaf (C.localInvHom T g)
          (C.localInvHom_app_eq T g)).app (op W) y = C.invMap T g k h y := fun k W h y =>
    ConcreteCategory.congr_hom (TopCat.Sheaf.LocalModuleHom.gluedHom_app C.cover T.isSheaf
      (C.localInvHom T g) (C.localInvHom_app_eq T g) k W h) y
  refine ⟨⟨TopCat.Sheaf.LocalModuleHom.gluedHom C.cover T.isSheaf (C.localInvHom T g)
    (C.localInvHom_app_eq T g)⟩, ?_⟩
  refine _root_.SheafOfModules.Hom.ext ?_
  refine TopCat.Sheaf.eq_hom_of_restrict C.cover
    ((_root_.SheafOfModules.restrictScalars α).obj T).isSheaf
    (fun _ W _ => g.val.app (op W)) (fun k W h => ?_) fun _ _ _ => rfl
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Eq.trans (hgl k W h (C.compHom.val.app (op W) x)) ?_
  rw [C.compHom_val_app k h, C.invMap_def T g k h]
  refine Eq.trans (congrArg _ (funext fun a => C.coordG_compMap k h x a)) ?_
  calc combSections T (C.pushSections T g k) (homOfLE h)
          (fun a => α.hom.app (op W) (C.coordE k h x a))
      = ∑ a, α.hom.app (op W) (C.coordE k h x a) •
          res T (homOfLE h) (C.pushSections T g k a) := rfl
    _ = ∑ a, pushApp g (C.coordE k h x a • res E (homOfLE h) (C.e k a)) :=
        Finset.sum_congr rfl fun a _ => by
          rw [pushApp_smul, C.res_pushSections T g k h a]
    _ = pushApp g (combSections E (C.e k) (homOfLE h) (C.coordE k h x)) :=
        (pushApp_sum g Finset.univ
          (fun a => C.coordE k h x a • res E (homOfLE h) (C.e k a))).symm
    _ = pushApp g x := congrArg (pushApp g) (C.combSections_coordE k h x)

/-- **Composing with the comparison `θ : E ⟶ α_* G` is a bijection from the morphisms `G ⟶ T`
onto the morphisms `E ⟶ α_* T`.** This is the universal property saying that `G` is the
extension of scalars of `E` along `α`. -/
theorem bijective_comp_restrictScalars_map :
    Function.Bijective fun f : G ⟶ T =>
      C.compHom ≫ (_root_.SheafOfModules.restrictScalars α).map f :=
  ⟨C.injective_comp_restrictScalars_map T,
    fun g => C.exists_comp_restrictScalars_map_eq T g⟩

end CompatTrivialisation

end Stacks.SheafOfModules

end
