module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DirectSum
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Shift

/-!
# The cone of a closed degree-zero morphism of right differential graded modules

Let `C` be a differential graded category over a commutative ring `R` and let `f : M ⟶ N` be a
closed degree-zero morphism of right differential graded `C`-modules. The *cone* `c(f)` of `f`
is the direct sum `N ⊕ M⟦1⟧` with its differential twisted by `f`: on a pair `(n, m)` with
`m` of degree `i + 1` in `M`, the differential is `(d n + f m, -d m)`, the sign on the second
component being the one already carried by the differential of `M⟦1⟧`.

The twist squares to zero exactly because `f` is closed: the cross term of `d²` is
`d (f m) - f (d m)`, which is the value of the differential of `f` in `Mod^dg(C)`. The twist
is compatible with the right action of `C` because `f` commutes with it, so the Leibniz rule of
the direct sum survives the twist unchanged.

## Main definitions

* `DGCategory.RightModule.coneTwist`: the twist `(n, m) ↦ (f m, 0)` of the differential.
* `DGCategory.RightModule.coneD`: the differential of the cone.
* `DGCategory.RightModule.coneOf`: the cone of a closed degree-zero morphism.

## Main results

* `DGCategory.RightModule.d_app_eq_app_d`: a closed degree-zero morphism commutes with the two
  differentials — the single consequence of closedness that the cone uses.
* `DGCategory.RightModule.coneD_fst` and `DGCategory.RightModule.coneD_snd`: the two components
  of the differential of the cone.
* `DGCategory.RightModule.coneOf_obj`, `DGCategory.RightModule.coneOf_act` and
  `DGCategory.RightModule.coneOf_d`: the underlying graded module, the action and the
  differential of the cone.

## Implementation notes

The cone is built as a structure update of `DGCategory.RightModule.prod N
(DGCategory.RightModule.shift M 1)`, overriding only the differential. This is not merely
economical: it makes the underlying graded
module, hence the type of homogeneous morphisms into or out of the cone and the value of their
composition, *definitionally* those of the direct sum, so the four structure morphisms of the
direct sum and the five direct-sum identities of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DirectSum` can be reused verbatim for
the cone sequence. Only closedness, which is the one thing that refers to the differential, has
to be proved afresh.

The differential is kept in the shape `d_{N ⊕ M⟦1⟧} + coneTwist`, a sum rather than an explicit
pair, so that the direct sum's own additivity, linearity and Leibniz rule can be rewritten with
directly and only the twist has to be handled by hand.
-/

@[expose] public section

namespace DGCategory

namespace RightModule

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R} {M N : RightModule.{w} C}

/-! ### Closedness as commutation with the differentials -/

/-- A closed degree-zero morphism commutes with the two differentials. This is the only
consequence of closedness that the cone construction uses. -/
theorem d_app_eq_app_d {f : HomogeneousMap M N 0} (hf : homD f = 0) {x : C.Obj} {i j : ℤ}
    (h₁ : i + 0 + 1 = j) (h₂ : i + 1 + 0 = j) (a : M.obj x i) :
    N.d h₁ (app f rfl a) = app f h₂ (M.d rfl a) := by
  have h : app (homD f) (show i + (0 + 1) = j by omega) a = 0 := by rw [hf, zero_app]
  rw [app_homD, Int.natAbs_zero, pow_zero, one_smul] at h
  exact eq_of_sub_eq_zero h

/-! ### The differential of the cone -/

/-- The twist of the differential of `N ⊕ M⟦1⟧` by a degree-zero morphism `f : M ⟶ N`: the
map `(n, m) ↦ (f m, 0)`. -/
def coneTwist (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : (prod N (shift M 1)).obj x i) : (prod N (shift M 1)).obj x j :=
  (app f (show i + 1 + 0 = j by omega) a.2, 0)

/-- The first component of the twist is the value of `f`. -/
@[simp] theorem coneTwist_fst (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : (prod N (shift M 1)).obj x i) :
    (coneTwist f h a).1 = app f (show i + 1 + 0 = j by omega) a.2 := rfl

/-- The second component of the twist vanishes. -/
@[simp] theorem coneTwist_snd (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : (prod N (shift M 1)).obj x i) : (coneTwist f h a).2 = 0 := rfl

/-- The differential of the cone of `f : M ⟶ N`: the differential of `N ⊕ M⟦1⟧`, twisted
by `f`. -/
def coneD (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : (prod N (shift M 1)).obj x i) : (prod N (shift M 1)).obj x j :=
  (prod N (shift M 1)).d h a + coneTwist f h a

/-- The first component of the differential of the cone. -/
@[simp] theorem coneD_fst (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : (prod N (shift M 1)).obj x i) :
    (coneD f h a).1 = N.d h a.1 + app f (show i + 1 + 0 = j by omega) a.2 := rfl

/-- The second component of the differential of the cone is that of `M⟦1⟧`. -/
@[simp] theorem coneD_snd (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : (prod N (shift M 1)).obj x i) :
    (coneD f h a).2 = (shift M 1).d h a.2 := add_zero _

/-- The differential of the cone on an explicit pair. -/
@[simp] theorem coneD_mk (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (n : N.obj x i) (m : M.obj x (i + 1)) :
    coneD f h (n, m) =
      (N.d h n + app f (show i + 1 + 0 = j by omega) m, (shift M 1).d h m) :=
  Prod.ext rfl (add_zero _)

/-- The twist is additive. -/
theorem coneTwist_add (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a b : (prod N (shift M 1)).obj x i) :
    coneTwist f h (a + b) = coneTwist f h a + coneTwist f h b :=
  Prod.ext (app_add f _ a.2 b.2) (add_zero (0 : (shift M 1).obj x j)).symm

/-- The twist is `R`-linear. -/
theorem coneTwist_smul (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (c : R) (a : (prod N (shift M 1)).obj x i) :
    coneTwist f h (c • a) = c • coneTwist f h a :=
  Prod.ext (app_smul f _ c a.2)
    (show (0 : (shift M 1).obj x j) = c • (0 : (shift M 1).obj x j) by rw [smul_zero])

/-- The differential of the cone is additive. -/
theorem coneD_add (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a b : (prod N (shift M 1)).obj x i) :
    coneD f h (a + b) = coneD f h a + coneD f h b := by
  simp only [coneD, (prod N (shift M 1)).d_add, coneTwist_add]
  abel

/-- The differential of the cone is `R`-linear. -/
theorem coneD_smul (f : HomogeneousMap M N 0) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (c : R) (a : (prod N (shift M 1)).obj x i) :
    coneD f h (c • a) = c • coneD f h a := by
  simp only [coneD, (prod N (shift M 1)).d_smul, coneTwist_smul, smul_add]

/-- The differential of the cone squares to zero; this is where the closedness of `f` is
used, and it is the only place. -/
theorem coneD_coneD {f : HomogeneousMap M N 0} (hf : homD f = 0) {x : C.Obj} {i j k : ℤ}
    (h₁ : i + 1 = j) (h₂ : j + 1 = k) (a : (prod N (shift M 1)).obj x i) :
    coneD f h₂ (coneD f h₁ a) = 0 := by
  have hsign : ((-1 : R) ^ (1 : ℤ).natAbs) = -1 := by norm_num
  refine Prod.ext ?_ ?_
  · show _ = (0 : N.obj x k)
    rw [coneD_fst, coneD_fst, coneD_snd, N.d_add, N.d_d h₁ h₂ a.1,
      d_app f (show i + 1 + 0 = j by omega) h₂ (show i + 1 + 0 + 1 = k by omega),
      d_app_eq_app_d hf (show i + 1 + 0 + 1 = k by omega)
        (show i + 1 + 1 + 0 = k by omega) a.2,
      shift_d, app_smul,
      app_d f (show i + 1 + 1 = j + 1 by omega) (show j + 1 + 0 = k by omega)
        (show i + 1 + 1 + 0 = k by omega) a.2,
      hsign]
    module
  · show _ = (0 : (shift M 1).obj x k)
    rw [coneD_snd, coneD_snd, (shift M 1).d_d h₁ h₂ a.2]

/-- The twist commutes with the right action of `C`, which is what lets the Leibniz rule of the
direct sum survive the twist. -/
theorem coneTwist_act (f : HomogeneousMap M N 0) {x y : C.Obj} {m q k l : ℤ}
    (h : m + q = k) (hl : k + 1 = l) (a : (prod N (shift M 1)).obj y m) (g : C.Hom x y q) :
    coneTwist f hl ((prod N (shift M 1)).act h a g) =
      (prod N (shift M 1)).act (show m + 1 + q = l by omega)
        (coneTwist f (rfl : m + 1 = m + 1) a) g :=
  Prod.ext
    (app_act f (show m + 1 + 0 = m + 1 by omega) (show m + 1 + q = k + 1 by omega)
      (show m + 1 + q = l by omega) (show k + 1 + 0 = l by omega) a.2 g)
    (M.act_zero_left (show m + 1 + 1 + q = l + 1 by omega) g).symm

/-- The graded Leibniz rule for the differential of the cone. -/
theorem coneD_act (f : HomogeneousMap M N 0) {x y : C.Obj} {m q k l : ℤ}
    (h : m + q = k) (hl : k + 1 = l) (a : (prod N (shift M 1)).obj y m) (g : C.Hom x y q) :
    coneD f hl ((prod N (shift M 1)).act h a g) =
      (prod N (shift M 1)).act (show m + 1 + q = l by omega) (coneD f rfl a) g +
        (-1 : R) ^ m.natAbs •
          (prod N (shift M 1)).act (show m + (q + 1) = l by omega) a (C.d g) := by
  simp only [coneD]
  rw [(prod N (shift M 1)).leibniz h hl a g, coneTwist_act f h hl a g,
    (prod N (shift M 1)).act_add_left]
  abel

/-! ### The cone -/

/-- The cone `c(f)` of a closed degree-zero morphism `f : M ⟶ N` of right differential graded
`C`-modules: the direct sum `N ⊕ M⟦1⟧`, with the same right action and with its differential
twisted by `f`. -/
@[implicit_reducible]
def coneOf (f : HomogeneousMap M N 0) (hf : homD f = 0) : RightModule.{w} C :=
  { prod N (shift M 1) with
    d := coneD f
    d_add := by intro x i j h a b; exact coneD_add f h a b
    d_smul := by intro x i j h c a; exact coneD_smul f h c a
    d_d := by intro x i j k h₁ h₂ a; exact coneD_coneD hf h₁ h₂ a
    leibniz := by intro x y m q k l h hl a g; exact coneD_act f h hl a g }

variable (f : HomogeneousMap M N 0) (hf : homD f = 0)

/-- The underlying graded module of the cone is the direct sum `N ⊕ M⟦1⟧`. -/
@[simp] theorem coneOf_obj (x : C.Obj) (i : ℤ) :
    (coneOf f hf).obj x i = (N.obj x i × M.obj x (i + 1)) := rfl

/-- The right action on the cone is that of the direct sum `N ⊕ M⟦1⟧`. -/
@[simp] theorem coneOf_act {x y : C.Obj} {m q k : ℤ} (h : m + q = k)
    (a : (prod N (shift M 1)).obj y m) (g : C.Hom x y q) :
    (coneOf f hf).act h a g = (prod N (shift M 1)).act h a g := rfl

/-- The differential of the cone. -/
@[simp] theorem coneOf_d {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : (prod N (shift M 1)).obj x i) : (coneOf f hf).d h a = coneD f h a := rfl

end RightModule

end DGCategory
