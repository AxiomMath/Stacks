module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Cone
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# The admissible short exact sequence of a cone of right differential graded modules

Let `C` be a differential graded category over a commutative ring `R` and let `f : M ⟶ N` be a
closed degree-zero morphism of right differential graded `C`-modules. The cone `c(f)` sits in
an admissible short exact sequence `N ⟶ c(f) ⟶ M⟦1⟧`, split in the underlying graded category
by the two remaining structure morphisms of the direct sum `N ⊕ M⟦1⟧`.

## Main definitions

* `DGCategory.RightModule.coneInl`, `DGCategory.RightModule.coneSnd`,
  `DGCategory.RightModule.coneFst` and `DGCategory.RightModule.coneInr`: the four structure
  morphisms of the cone, homogeneous of degree zero.
* `DGCategory.RightModule.coneSequenceOf`: the sequence `N ⟶ c(f) ⟶ M⟦1⟧` with its graded
  splitting.

## Main results

* `DGCategory.RightModule.coneInl_closed` and `DGCategory.RightModule.coneSnd_closed`: the
  inclusion of `N` and the projection to `M⟦1⟧` are closed for the twisted differential.

## Implementation notes

Because the cone is a structure update of `DGCategory.RightModule.prod N
(DGCategory.RightModule.shift M 1)` which touches only the differential, its underlying graded
module and right action, hence the type of homogeneous morphisms into and out of it and the
value of their composites, are definitionally those of the direct sum. The four morphisms of
the sequence are therefore the four structure morphisms of the direct sum, read at the cone,
and the five direct-sum identities of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DirectSum` discharge the five
identities of a graded splitting unchanged. They are given their own names because the target
of a morphism is an implicit argument, inferred from the term and not from an ascription, so a
statement about the cone has to name the cone in the term itself.

Only closedness refers to the differential, and only two of the four morphisms are closed: the
inclusion of `N` and the projection to `M⟦1⟧`. The other two — the projection to `N` and the
inclusion of `M⟦1⟧` — are not, and the failure of the latter to be closed is exactly the
connecting morphism of the sequence.
-/

@[expose] public section

namespace DGCategory

namespace RightModule

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R} {M N : RightModule.{w} C}
variable (f : HomogeneousMap M N 0) (hf : homD f = 0)

/-! ### The four structure morphisms of the cone -/

/-- The inclusion `N ⟶ c(f)` of the target of `f` into its cone. -/
def coneInl : HomogeneousMap N (coneOf f hf) 0 := prodInl N (shift M 1)

/-- The value of the inclusion of the target. -/
@[simp] theorem app_coneInl {x : C.Obj} {i j : ℤ} (e : i + 0 = j) (a : N.obj x i) :
    app (coneInl f hf) e a = (N.objCast x (show i = j by omega) a, 0) := rfl

/-- The projection `c(f) ⟶ M⟦1⟧` of the cone onto the shifted source. -/
def coneSnd : HomogeneousMap (coneOf f hf) (shift M 1) 0 := prodSnd N (shift M 1)

/-- The value of the projection onto the shifted source. -/
@[simp] theorem app_coneSnd {x : C.Obj} {i j : ℤ} (e : i + 0 = j) (a : N.obj x i)
    (b : M.obj x (i + 1)) :
    app (coneSnd f hf) e (a, b) = (shift M 1).objCast x (show i = j by omega) b := rfl

/-- The projection `c(f) ⟶ N` of the cone onto the target of `f`; it is not closed. -/
def coneFst : HomogeneousMap (coneOf f hf) N 0 := prodFst N (shift M 1)

/-- The value of the projection onto the target. -/
@[simp] theorem app_coneFst {x : C.Obj} {i j : ℤ} (e : i + 0 = j) (a : N.obj x i)
    (b : M.obj x (i + 1)) :
    app (coneFst f hf) e (a, b) = N.objCast x (show i = j by omega) a := rfl

/-- The inclusion `M⟦1⟧ ⟶ c(f)` of the shifted source into the cone; it is not closed, and
its failure to be closed is the connecting morphism of the cone sequence. -/
def coneInr : HomogeneousMap (shift M 1) (coneOf f hf) 0 := prodInr N (shift M 1)

/-- The value of the inclusion of the shifted source. -/
@[simp] theorem app_coneInr {x : C.Obj} {i j : ℤ} (e : i + 0 = j)
    (b : (shift M 1).obj x i) :
    app (coneInr f hf) e b = (0, (shift M 1).objCast x (show i = j by omega) b) := rfl

/-! ### Closedness -/

/-- The differential commutes with the degree-zero transports of the cone's morphisms. -/
private theorem d_objCast_add_zero (P : RightModule C) {x : C.Obj} {i j : ℤ} (h₁ : i + 0 + 1 = j)
    (a : P.obj x i) :
    P.d h₁ (P.objCast x (show i = i + 0 by omega) a) =
      P.objCast x (show i + 1 = j by omega) (P.d (show i + 1 = i + 1 from rfl) a) := by
  rw [P.d_objCast (show i = i + 0 by omega) h₁ (show i + 1 = j by omega),
    P.objCast_d (show i + 1 = j by omega)]

/-- The inclusion of `N` into the cone is closed: the twist of the differential vanishes on the
first summand. -/
theorem coneInl_closed : homD (coneInl f hf) = 0 := by
  refine homD_eq_zero_of_comm_d _ fun x i j h₁ h₂ a => ?_
  refine Prod.ext ?_ ?_
  · simp only [app_coneInl, coneOf_d, coneD_mk, app_zero, add_zero]
    exact d_objCast_add_zero N h₁ a
  · simp only [app_coneInl, coneOf_d, coneD_mk, d_zero]

/-- The projection of the cone onto `M⟦1⟧` is closed: the twist of the differential lands in
the first summand. -/
theorem coneSnd_closed : homD (coneSnd f hf) = 0 := by
  refine homD_eq_zero_of_comm_d _ fun x i j h₁ h₂ a => ?_
  obtain ⟨a₁, a₂⟩ := a
  simp only [app_coneSnd, coneOf_d, coneD_mk]
  exact d_objCast_add_zero (shift M 1) h₁ a₂

/-! ### The cone sequence -/

/-- The admissible short exact sequence `N ⟶ c(f) ⟶ M⟦1⟧` of the cone of a closed degree-zero
morphism `f : M ⟶ N`, with its splitting in the underlying graded category: the four
morphisms are the four structure morphisms of the direct sum `N ⊕ M⟦1⟧`. -/
def coneSequenceOf :
    GradedSplitShortExact (A := rightModuleCategory.{w} C) N (coneOf f hf) (shift M 1) where
  a := ⟨coneInl f hf, coneInl_closed f hf⟩
  b := ⟨coneSnd f hf, coneSnd_closed f hf⟩
  π := coneFst f hf
  s := coneInr f hf
  π_a := prodFst_prodInl N (shift M 1)
  b_s := prodSnd_prodInr N (shift M 1)
  π_s := prodFst_prodInr N (shift M 1)
  a_π_add_s_b := prodInl_prodFst_add_prodInr_prodSnd N (shift M 1)

/-- The inclusion of the cone sequence. -/
@[simp] theorem coneSequenceOf_a : (coneSequenceOf f hf).a.1 = coneInl f hf := rfl

/-- The projection of the cone sequence. -/
@[simp] theorem coneSequenceOf_b : (coneSequenceOf f hf).b.1 = coneSnd f hf := rfl

/-- The splitting of the projection of the cone sequence. -/
@[simp] theorem coneSequenceOf_π : (coneSequenceOf f hf).π = coneFst f hf := rfl

/-- The splitting of the inclusion of the cone sequence. -/
@[simp] theorem coneSequenceOf_s : (coneSequenceOf f hf).s = coneInr f hf := rfl

end RightModule

end DGCategory
