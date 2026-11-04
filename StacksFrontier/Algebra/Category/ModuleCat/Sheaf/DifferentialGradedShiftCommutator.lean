module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackGradedShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor

/-!
# The commutator of a homogeneous family with the differentials

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded `R`-algebras.
A right-linear family of degree `-1` between two right differential graded `A`-modules — a
homomorphism of graded modules `X ⟶ Y[-1]` in the sense of
`SheafOfModules.GradedModule.shift` — has a commutator `d ∘ h + h ∘ d` with the differentials,
and that commutator is again right-linear, the two signs produced by the Leibniz rules being
opposite. This file records the commutator as a homomorphism of the underlying graded modules,
and the reading of a right-linear family of any degree as a local homomorphism in the sense of
`SheafOfModules.LocalHom`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.toLocalHom` reads a right-linear family of degree `k`
  as a degree-`k` local homomorphism over an object of the site.
* `SheafOfModules.DifferentialGradedModule.shiftDiffCommutator` is the commutator
  `d ∘ h + h ∘ d` of a right-linear family of degree `-1` with the differentials, as a
  homomorphism of the underlying graded modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.shiftDiffCommutator_apply`: the commutator acts on a
  local section by `x ↦ d (h x) + h (d x)`.

## References

* [Stacks Project, Tag 0FS0](https://stacks.math.columbia.edu/tag/0FS0)
* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {X Y : DifferentialGradedModule.{t, a, m} A}

/-- A right-linear family of degree `k`, read as a degree-`k` map of the underlying graded
modules over an object of the site. -/
noncomputable def toLocalGradedHom (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C) :
    LocalGradedHom X Y k U where
  app i _ hij V := (castHom Y.complex.X hij (Opposite.op V.left)).comp
    (homSections (g.app i) (Opposite.op V.left))
  map_smul i _ hij V r x :=
    (congrArg (castHom Y.complex.X hij (Opposite.op V.left))
        (homSections_smul (g.app i) (Opposite.op V.left) r x)).trans
      (castHom_smul Y.complex.X hij (Opposite.op V.left) r _)
  naturality i _ hij {_ W} q x :=
    (castHom_naturality Y.complex.X hij q.left.op _).trans
      (congrArg (castHom Y.complex.X hij (Opposite.op W.left))
        (homSections_naturality (g.app i) q.left.op x))

/-- The value of `toLocalGradedHom k g U` in degree `i` is the value of `g`, transported from
`i + k` to `j`. -/
@[simp] theorem toLocalGradedHom_app (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C)
    (i j : ℤ) (hij : i + k = j) (V : Over U)
    (x : (X.complex.X i).val.obj (Opposite.op V.left)) :
    (toLocalGradedHom k g U).app i j hij V x =
      castHom Y.complex.X hij (Opposite.op V.left)
        (homSections (g.app i) (Opposite.op V.left) x) :=
  rfl

/-- **A right-linear family of degree `k`, read as a degree-`k` local homomorphism** over an
object of the site: its value in degree `p` is the value of the family, transported from `p + k`
to the degree prescribed by the local homomorphism. -/
noncomputable def toLocalHom (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C) :
    LocalHom X Y k U :=
  { toLocalGradedHom := toLocalGradedHom k g U
    isLinear := by
      intro i j hij p V x b
      refine Eq.trans (toLocalGradedHom_app k g U (i + p) (j + p) (by omega) V _) ?_
      refine Eq.trans (congrArg (castHom Y.complex.X (show i + p + k = j + p by omega)
          (Opposite.op V.left))
        ((g.map_smul i p (Opposite.op V.left) x b).trans
          (GradedModule.shift_smul ((forgetToGradedModule A).obj Y) k i p (Opposite.op V.left)
            (homSections (g.app i) (Opposite.op V.left) x) b))) ?_
      refine Eq.trans (Cofree.castHom_castHom Y.complex.X _ _ (Opposite.op V.left) _) ?_
      refine Eq.trans ?_ (congrArg (fun z => (Y.mul j p).app (Opposite.op V.left) z b)
        (toLocalGradedHom_app k g U i j hij V x).symm)
      refine Eq.trans ?_ (mul_app_castHom Y hij p (Opposite.op V.left)
        (homSections (g.app i) (Opposite.op V.left) x) b).symm
      exact Cofree.castHom_eq_castHom _ _ (Opposite.op V.left) (HEq.refl _) }

/-- The value of `toLocalHom k g U` in degree `i` is the value of `g`, transported from `i + k`
to `j`. -/
@[simp] theorem toLocalHom_app (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C)
    (i j : ℤ) (hij : i + k = j) (V : Over U)
    (x : (X.complex.X i).val.obj (Opposite.op V.left)) :
    (toLocalHom k g U).app i j hij V x =
      castHom Y.complex.X hij (Opposite.op V.left)
        (homSections (g.app i) (Opposite.op V.left) x) :=
  rfl

section Commutator

variable (h : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift (-1))

/-- The first half of the commutator of a right-linear family of degree `-1` with the
differentials: the family followed by the differential of the target. -/
noncomputable def shiftDiffFst (n : ℤ) :
    ((forgetToGradedModule A).obj X).piece n ⟶ ((forgetToGradedModule A).obj Y).piece n :=
  h.app n ≫ Y.complex.d (n + -1) n

/-- The second half of the commutator of a right-linear family of degree `-1` with the
differentials: the differential of the source followed by the family. -/
noncomputable def shiftDiffSnd (n : ℤ) :
    ((forgetToGradedModule A).obj X).piece n ⟶ ((forgetToGradedModule A).obj Y).piece n :=
  X.complex.d n (n + 1) ≫ h.app (n + 1) ≫
    degCastHom Y.complex.X (show n + 1 + -1 = n by omega)

/-- The first half of the commutator acts on a local section by `x ↦ d (h x)`. -/
theorem shiftDiffFst_apply (n : ℤ) (U : Cᵒᵖ)
    (x : (((forgetToGradedModule A).obj X).piece n).val.obj U) :
    homSections (shiftDiffFst h n) U x =
      homSections (Y.complex.d (n + -1) n) U (homSections (h.app n) U x) :=
  homSections_comp _ _ U x

/-- The second half of the commutator acts on a local section by `x ↦ h (d x)`. -/
theorem shiftDiffSnd_apply (n : ℤ) (U : Cᵒᵖ)
    (x : (((forgetToGradedModule A).obj X).piece n).val.obj U) :
    homSections (shiftDiffSnd h n) U x =
      castHom Y.complex.X (show n + 1 + -1 = n by omega) U
        (homSections (h.app (n + 1)) U (homSections (X.complex.d n (n + 1)) U x)) :=
  (homSections_comp _ _ U x).trans
    ((homSections_comp _ _ U _).trans
      (degCastHom_val_app Y.complex.X (show n + 1 + -1 = n by omega) U _))

/-- The commutator of a right-linear family of degree `-1` with the differentials is, over each
object of the site, the commutator of the attached local homomorphism. -/
theorem shiftDiff_apply (n : ℤ) (U : Cᵒᵖ)
    (x : (((forgetToGradedModule A).obj X).piece n).val.obj U) :
    homSections (shiftDiffFst h n + shiftDiffSnd h n) U x =
      (toLocalHom (-1) h U.unop).diffCommutator.app n n (add_zero n)
        (Over.mk (𝟙 U.unop)) x :=
  (homSections_add _ _ U x).trans
    (congrArg₂ (· + ·) (shiftDiffFst_apply h n U x) (shiftDiffSnd_apply h n U x))

/-- **The commutator `d ∘ h + h ∘ d` of a right-linear family of degree `-1` with the
differentials**, as a homomorphism of the underlying graded modules. -/
noncomputable def shiftDiffCommutator :
    (forgetToGradedModule A).obj X ⟶ (forgetToGradedModule A).obj Y where
  app n := shiftDiffFst h n + shiftDiffSnd h n
  map_smul n i U x y :=
    ((shiftDiff_apply h (n + i) U _).trans
        ((toLocalHom (-1) h U.unop).diffCommutator.isLinear n n (add_zero n) i
          (Over.mk (𝟙 U.unop)) x y)).trans
      (congrArg (fun z => (Y.mul n i).app U z y) (shiftDiff_apply h n U x).symm)

/-- In degree `n`, the commutator is the sum of `shiftDiffFst h n` and `shiftDiffSnd h n`. -/
@[simp] theorem shiftDiffCommutator_app (n : ℤ) :
    (shiftDiffCommutator h).app n = shiftDiffFst h n + shiftDiffSnd h n :=
  rfl

/-- **The commutator of a right-linear family of degree `-1` with the differentials acts on a
local section by `x ↦ d (h x) + h (d x)`.** -/
theorem shiftDiffCommutator_apply (n : ℤ) (U : Cᵒᵖ)
    (x : (((forgetToGradedModule A).obj X).piece n).val.obj U) :
    homSections ((shiftDiffCommutator h).app n) U x =
      homSections (Y.complex.d (n + -1) n) U (homSections (h.app n) U x) +
        castHom Y.complex.X (show n + 1 + -1 = n by omega) U
          (homSections (h.app (n + 1)) U (homSections (X.complex.d n (n + 1)) U x)) :=
  shiftDiff_apply h n U x

end Commutator

section Homotopy

/-- Transport along an equality of degrees, read as `CategoryTheory.eqToHom`. -/
theorem degCastHom_eq_eqToHom (Z : ℤ → SheafOfModules.{m} R) {i j : ℤ} (hij : i = j) :
    degCastHom Z hij = eqToHom (congrArg Z hij) := by
  subst hij; simp

/-- **A right-linear family of degree `-1` whose commutator with the differentials is a
morphism of right differential graded modules is a homotopy from that morphism to zero.** -/
noncomputable def homotopyOfShiftDiffCommutator {f : X ⟶ Y}
    (h : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift (-1))
    (hf : shiftDiffCommutator h = (forgetToGradedModule A).map f) :
    Homotopy f (0 : X ⟶ Y) where
  app n := h.app n
  map_mul n q U x a := by
    refine HEq.trans (heq_of_eq ((h.map_smul n q U x a).trans
      (GradedModule.shift_smul ((forgetToGradedModule A).obj Y) (-1) n q U
        (homSections (h.app n) U x) a))) ?_
    exact heq_castHom Y.complex.X (show n + -1 + q = n + q + -1 by omega) U _
  comm n := by
    have hn := congrArg (fun α : (forgetToGradedModule A).obj X ⟶
      (forgetToGradedModule A).obj Y => α.app n) hf
    refine Eq.trans (sub_zero _) (Eq.trans hn.symm ?_)
    change shiftDiffFst h n + shiftDiffSnd h n = _
    refine congrArg₂ (· + ·) rfl ?_
    change X.complex.d n (n + 1) ≫ h.app (n + 1) ≫
        degCastHom Y.complex.X (show n + 1 + -1 = n by omega) = _
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun z => (X.complex.d n (n + 1) ≫ h.app (n + 1)) ≫ z)
      (degCastHom_eq_eqToHom Y.complex.X (show n + 1 + -1 = n by omega))

end Homotopy

section Pullback

universe a' m' v' u'

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  {R' : Sheaf J' RingCat.{t}} {w : C ⥤ C'} {σ : R.obj ⟶ w.op ⋙ R'.obj}
  {A₁ : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom w σ A A₁}

/-- A semilinear map of right differential graded modules commutes with a differential between
two degrees related by a step of one, in whichever spelling that step is written. -/
theorem SemilinearHom.app_d {Z : DifferentialGradedModule.{t, a, m} A}
    {W : DifferentialGradedModule.{t, a', m'} A₁} (θ : SemilinearHom φ Z W) {i j : ℤ}
    (hij : i + 1 = j) (V : Cᵒᵖ) (x : (Z.complex.X i).val.obj V) :
    θ.app j V (homSections (Z.complex.d i j) V x) =
      homSections (W.complex.d i j) (w.op.obj V) (θ.app i V x) := by
  subst hij; exact θ.comm_d i V x

/-- **The pullback of the commutator of a right-linear family of degree `-1` with the
differentials is the commutator of the pullback of the family**, as homomorphisms of the
graded modules underlying the pullback of `X`. -/
theorem PullbackData.gradedShiftMap_shiftDiffCommutator
    (PD : PullbackData.{t, a', m', v', u', a, m, v, u} φ)
    (h : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift (-1)) :
    shiftDiffCommutator (PD.gradedShiftMap (-1) h) =
      PD.gradedMap (shiftDiffCommutator h) := by
  refine PD.graded_hom_ext fun n V x => ?_
  have hdn : n + -1 + 1 = n := by omega
  have hup : n + 1 + -1 = n := by omega
  refine Eq.trans (shiftDiffCommutator_apply (PD.gradedShiftMap (-1) h) n (w.op.obj V) _) ?_
  refine Eq.trans ?_ (PD.gradedMap_unit (shiftDiffCommutator h) n V x).symm
  refine Eq.trans ?_ (congrArg ((PD.unit Y).app n V)
    (shiftDiffCommutator_apply h n V x)).symm
  refine Eq.trans ?_ (map_add ((PD.unit Y).app n V) _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans (congrArg (homSections ((PD.obj Y).complex.d (n + -1) n) (w.op.obj V))
      (PD.gradedShiftMap_unit (-1) h n V x)) ?_
    exact (SemilinearHom.app_d (PD.unit Y) hdn V (homSections (h.app n) V x)).symm
  · refine Eq.trans (congrArg (castHom (PD.obj Y).complex.X hup (w.op.obj V))
      (Eq.trans (congrArg (homSections ((PD.gradedShiftMap (-1) h).app (n + 1)) (w.op.obj V))
          (SemilinearHom.app_d (PD.unit X) rfl V x).symm)
        (PD.gradedShiftMap_unit (-1) h (n + 1) V
          (homSections (X.complex.d n (n + 1)) V x)))) ?_
    exact (SemilinearHom.app_castHom (PD.unit Y) hup V _).symm

end Pullback

end DifferentialGradedModule

end SheafOfModules

end
