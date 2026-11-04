module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackGraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedGrothendieck

/-!
# The pullback of a homogeneous family of right graded modules

Let `f` be a morphism of ringed sites and let `φ : A' ⟶ f_*A` be a semilinear homomorphism of
sheaves of differential graded algebras. A pullback `f^*` of right differential graded
`A'`-modules is given by a universal property which tests only *morphisms of differential graded
modules* out of `f^*M`, that is right-linear families of degree zero commuting with the
differentials. `SheafOfModules.DifferentialGradedModule.PullbackData.gradedMap` removes the
second restriction: a homomorphism of the underlying *graded* modules has a unique transport
along the pullback. This file removes the first one: a right-linear family of *any* degree `k`,

`W^p ⟶ Z^{p + k}`,

has a unique transport `(f^*W)^p ⟶ (f^*Z)^{p + k}` compatible with the units of the two
pullbacks, and the transport preserves identities, composites, sums and zero.

## Main definitions

* `SheafOfModules.GradedModule.shiftComp`: the composite of a degree-`k` family with a
  degree-`l` family. A degree-`k` family out of `M` into `N` is a homomorphism of graded modules
  `M ⟶ N.shift k`.
* `SheafOfModules.GradedModule.shiftOfHom`: a homomorphism of graded modules, read as a family of
  degree zero.
* `SheafOfModules.DifferentialGradedModule.PullbackData.gradedShiftMap`: the transport of a
  degree-`k` right-linear family along a pullback.

## Main results

* `SheafOfModules.DifferentialGradedModule.PullbackData.gradedShiftMap_unit`: the transport is
  compatible with the units of the two pullbacks.
* `SheafOfModules.DifferentialGradedModule.PullbackData.gradedShiftMap_shiftComp`,
  `gradedShiftMap_shiftOfHom`, `gradedShiftMap_zero` and `gradedShiftMap_add`: the transport
  preserves composites, carries the degree-zero family of a morphism of differential graded
  modules to the degree-zero family of its pullback, and is additive.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory

universe t a a' m m' v u v' u'

namespace SheafOfModules

namespace GradedModule

section ShiftHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R} {M N Q : GradedModule.{t, a, m} A}

/-- The action of a shift on a transported section is the transport of the action. -/
theorem shift_smul_castHom (k : ℤ) {p r i : ℤ} (h : r = p + k) (U : Cᵒᵖ)
    (x : (N.piece r).val.obj U) (y : (A.piece i).val.obj U) :
    (N.shift k).smul p i U (castHom N.piece h U x) y =
      castHom N.piece (show r + i = p + i + k by omega) U (N.smul r i U x y) := by
  subst h
  exact shift_smul N k p i U x y

/-- The composite of a degree-`k` right-linear family with a degree-`l` one, as a family of
degree `j` for any `j` with `k + l = j`. -/
noncomputable def shiftComp {k l j : ℤ} (hj : k + l = j) (g : M ⟶ N.shift k)
    (g' : N ⟶ Q.shift l) : M ⟶ Q.shift j where
  app p := g.app p ≫ g'.app (p + k) ≫ degCastHom Q.piece (by omega : p + k + l = p + j)
  map_smul p i U x y := by
    change ((degCastHom Q.piece (show p + i + k + l = p + i + j by omega)).val.app U)
        ((g'.app (p + i + k)).val.app U ((g.app (p + i)).val.app U (M.smul p i U x y))) =
      (Q.shift j).smul p i U
        (((degCastHom Q.piece (show p + k + l = p + j by omega)).val.app U)
          ((g'.app (p + k)).val.app U ((g.app p).val.app U x))) y
    rw [degCastHom_val_app, degCastHom_val_app,
      (g.map_smul p i U x y).trans (shift_smul N k p i U _ y),
      app_castHom g' (show p + k + i = p + i + k by omega) U,
      (g'.map_smul (p + k) i U ((g.app p).val.app U x) y).trans
        (shift_smul Q l (p + k) i U _ y),
      castHom_shift_piece Q l (show p + k + i = p + i + k by omega) U,
      shift_smul_castHom (N := Q) j (show p + k + l = p + j by omega) U,
      Cofree.castHom_castHom, Cofree.castHom_castHom]

/-- The degree-`p` component of `shiftComp hj g g'` is the composite of the components of `g`
and `g'` followed by the transport from degree `p + k + l` to degree `p + j`. -/
theorem shiftComp_app {k l j : ℤ} (hj : k + l = j) (g : M ⟶ N.shift k)
    (g' : N ⟶ Q.shift l) (p : ℤ) :
    (shiftComp hj g g').app p =
      g.app p ≫ g'.app (p + k) ≫ degCastHom Q.piece (by omega : p + k + l = p + j) :=
  rfl

/-- A homomorphism of right graded modules, read as a right-linear family of degree zero. -/
noncomputable def shiftOfHom (f : M ⟶ N) : M ⟶ N.shift 0 where
  app p := f.app p ≫ degCastHom N.piece (by omega : p = p + 0)
  map_smul p i U x y := by
    change ((degCastHom N.piece (show p + i = p + i + 0 by omega)).val.app U)
        ((f.app (p + i)).val.app U (M.smul p i U x y)) =
      (N.shift 0).smul p i U
        (((degCastHom N.piece (show p = p + 0 by omega)).val.app U)
          ((f.app p).val.app U x)) y
    rw [degCastHom_val_app, degCastHom_val_app, f.map_smul p i U x y,
      shift_smul_castHom (N := N) 0 (show p = p + 0 by omega) U]

/-- The degree-`p` component of `shiftOfHom f` is the component of `f` followed by the
transport from degree `p` to degree `p + 0`. -/
theorem shiftOfHom_app (f : M ⟶ N) (p : ℤ) :
    (shiftOfHom f).app p = f.app p ≫ degCastHom N.piece (by omega : p = p + 0) :=
  rfl

/-- A right-linear family of degree zero, read as a homomorphism of right graded modules; the
inverse of `SheafOfModules.GradedModule.shiftOfHom`. -/
noncomputable def ofShiftZero (g : M ⟶ N.shift 0) : M ⟶ N where
  app p := g.app p ≫ degCastHom N.piece (show p + 0 = p by omega)
  map_smul p i U x y := by
    change ((degCastHom N.piece (show p + i + 0 = p + i by omega)).val.app U)
        ((g.app (p + i)).val.app U (M.smul p i U x y)) =
      N.smul p i U
        (((degCastHom N.piece (show p + 0 = p by omega)).val.app U)
          ((g.app p).val.app U x)) y
    rw [degCastHom_val_app, degCastHom_val_app,
      (g.map_smul p i U x y).trans (shift_smul N 0 p i U _ y),
      Cofree.smul_castHom_left, Cofree.castHom_castHom]

/-- The degree-`p` component of `ofShiftZero g` is the component of `g` followed by the
transport from degree `p + 0` to degree `p`. -/
theorem ofShiftZero_app (g : M ⟶ N.shift 0) (p : ℤ) :
    (ofShiftZero g).app p = g.app p ≫ degCastHom N.piece (show p + 0 = p by omega) :=
  rfl

/-- Reading a homomorphism of right graded modules as a family of degree zero and back returns
the homomorphism. -/
theorem ofShiftZero_shiftOfHom (f : M ⟶ N) : ofShiftZero (shiftOfHom f) = f := by
  refine Hom.ext fun p => ?_
  rw [ofShiftZero_app, shiftOfHom_app, Category.assoc, degCastHom_comp_degCastHom,
    degCastHom_rfl, Category.comp_id]

/-- If a composite of two right-linear families is a given family `α`, then its components are
those of `α` followed by the inverse transport. -/
private theorem shiftComp_app_comp_degCastHom {k l j : ℤ} (g : M ⟶ N.shift k)
    (g' : N ⟶ Q.shift l) (hj : k + l = j) (α : M ⟶ Q.shift j) (hrel : shiftComp hj g g' = α)
    (p : ℤ) :
    g.app p ≫ g'.app (p + k) = α.app p ≫ degCastHom Q.piece (show p + j = p + k + l by omega) := by
  rw [← hrel, shiftComp_app]
  simp [degCastHom_comp_degCastHom]

/-- The component of a composite of two right-linear families which is the degree-zero reading
of a homomorphism of graded modules, with the trailing transport cancelled. -/
theorem shiftComp_app_of_eq_shiftOfHom {k l : ℤ} (g : M ⟶ N.shift k) (g' : N ⟶ Q.shift l)
    (hj : k + l = 0) (ρ : M ⟶ Q) (hrel : shiftComp hj g g' = shiftOfHom ρ) (p : ℤ) :
    g.app p ≫ g'.app (p + k) =
      ρ.app p ≫ degCastHom Q.piece (show p = p + k + l by omega) := by
  simpa [shiftOfHom_app, degCastHom_comp_degCastHom] using
    shiftComp_app_comp_degCastHom g g' hj _ hrel p

/-- The component of a composite of two right-linear families which vanishes, with the trailing
transport cancelled. -/
theorem shiftComp_app_of_eq_zero {k l j : ℤ} (g : M ⟶ N.shift k) (g' : N ⟶ Q.shift l)
    (hj : k + l = j) (hrel : shiftComp hj g g' = 0) (p : ℤ) :
    g.app p ≫ g'.app (p + k) = 0 := by
  simpa using shiftComp_app_comp_degCastHom g g' hj _ hrel p

/-- Transport between the pieces of a shift is the transport between the pieces it shifts. -/
theorem degCastHom_shift_piece (Z : GradedModule.{t, a, m} A) (k : ℤ) {i j : ℤ} (hij : i = j) :
    degCastHom (Z.shift k).piece hij =
      degCastHom Z.piece (show i + k = j + k by omega) := by
  subst hij; rfl

/-- A morphism of cochain complexes commutes with transport along an equality of degrees. -/
theorem degCastHom_comp_hom_f {K L : CochainComplex (SheafOfModules.{m} R) ℤ} (f : K ⟶ L)
    {i j : ℤ} (hij : i = j) :
    degCastHom K.X hij ≫ f.f j = f.f i ≫ degCastHom L.X hij := by
  subst hij
  rw [degCastHom_rfl, degCastHom_rfl, Category.id_comp, Category.comp_id]

/-- Transport along an equality of degrees is an isomorphism. -/
instance isIso_degCastHom (Z : ℤ → SheafOfModules.{m} R) {i j : ℤ} (hij : i = j) :
    IsIso (degCastHom Z hij) :=
  ⟨degCastHom Z hij.symm, by
    rw [degCastHom_comp_degCastHom, degCastHom_rfl], by
    rw [degCastHom_comp_degCastHom, degCastHom_rfl]⟩

/-- A homomorphism of right graded modules is determined by the degree-zero family it defines. -/
theorem shiftOfHom_injective : Function.Injective (shiftOfHom (M := M) (N := N)) :=
  fun f g hfg ↦ Hom.ext fun p ↦ (cancel_mono (degCastHom N.piece (show p = p + 0 by omega))).1 <| by
    simpa only [shiftOfHom_app] using congrArg (fun α : M ⟶ N.shift 0 => α.app p) hfg

end ShiftHom

end GradedModule

namespace DifferentialGradedModule

section PullbackShift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}

namespace PullbackData

variable (PD : PullbackData.{t, a, m, v, u, a', m', v', u'} φ)
  {W Z Y : DifferentialGradedModule.{t, a', m'} A'}

/-- The semilinear map of cofree modules which carries the unit of a pullback across a degree
shift: the unit of the pullback of `Z`, read in the degrees of the shift. -/
noncomputable def shiftUnitCofree (k : ℤ) :
    SemilinearHom φ
      (Cofree.cofree (((forgetToGradedModule A').obj Z).shift k))
      (Cofree.cofree (((forgetToGradedModule A).obj (PD.obj Z)).shift k)) :=
  Cofree.gradedSemilinearMap (fun n V => (PD.unit Z).gradedApp (n + k) V)
    (fun n V => (PD.unit Z).gradedApp_smul (n + k) V)
    (fun n _ _ q => (PD.unit Z).gradedApp_restrict (n + k) q)
    (fun n i V x b => by
      rw [GradedModule.shift_smul, GradedModule.shift_smul,
        SemilinearHom.gradedApp_castHom (PD.unit Z) (show n + k + i = n + i + k by omega),
        SemilinearHom.gradedApp_smul_algebra])

/-- The transport of a degree-`k` right-linear family along a pullback: the unique degree-`k`
right-linear family of the two pullbacks which is compatible with the units. -/
noncomputable def gradedShiftMap (k : ℤ)
    (g : (forgetToGradedModule A').obj W ⟶ ((forgetToGradedModule A').obj Z).shift k) :
    (forgetToGradedModule A).obj (PD.obj W) ⟶
      ((forgetToGradedModule A).obj (PD.obj Z)).shift k :=
  Cofree.lowerHom _ ((PD.isPullback W).desc
    ((PD.shiftUnitCofree k).precomp (Cofree.liftDgHom _ g)))

/-- The transport of a degree-`k` family is compatible with the units of the two pullbacks. -/
theorem gradedShiftMap_unit (k : ℤ)
    (g : (forgetToGradedModule A').obj W ⟶ ((forgetToGradedModule A').obj Z).shift k) (i : ℤ)
    (V : C'ᵒᵖ) (x : (((forgetToGradedModule A').obj W).piece i).val.obj V) :
    homSections ((PD.gradedShiftMap k g).app i) (u.op.obj V) ((PD.unit W).app i V x) =
      (PD.unit Z).app (i + k) V (homSections (g.app i) V x) := by
  have hfac : homSections (((PD.isPullback W).desc
          ((PD.shiftUnitCofree k).precomp
            (Cofree.liftDgHom (((forgetToGradedModule A').obj Z).shift k) g))
            ).toHomologicalComplex.f i)
        (u.op.obj V) ((PD.unit W).app i V x) =
      ((PD.shiftUnitCofree k).precomp
        (Cofree.liftDgHom (((forgetToGradedModule A').obj Z).shift k) g)).app i V x :=
    congrArg (fun ϑ : SemilinearHom φ W
        (Cofree.cofree (((forgetToGradedModule A).obj (PD.obj Z)).shift k)) => ϑ.app i V x)
      ((PD.isPullback W).fac ((PD.shiftUnitCofree k).precomp
        (Cofree.liftDgHom (((forgetToGradedModule A').obj Z).shift k) g)))
  change Cofree.coordFst (((forgetToGradedModule A).obj (PD.obj Z)).shift k) i (u.op.obj V)
      (homSections (((PD.isPullback W).desc
          ((PD.shiftUnitCofree k).precomp
            (Cofree.liftDgHom (((forgetToGradedModule A').obj Z).shift k) g))
            ).toHomologicalComplex.f i)
        (u.op.obj V) ((PD.unit W).app i V x)) = _
  rw [hfac]
  change Cofree.coordFst (((forgetToGradedModule A).obj (PD.obj Z)).shift k) i (u.op.obj V)
      (Cofree.gradedSemilinearApp (fun n V => (PD.unit Z).gradedApp (n + k) V) i V
        (homSections (Cofree.liftHom (((forgetToGradedModule A').obj Z).shift k) g i) V x)) = _
  rw [Cofree.coordFst_gradedSemilinearApp, Cofree.coordFst_liftHom]
  rfl

/-- The transport of a composite of two right-linear families is the composite of the
transports. -/
theorem gradedShiftMap_shiftComp {k l j : ℤ} (hj : k + l = j)
    (g : (forgetToGradedModule A').obj W ⟶ ((forgetToGradedModule A').obj Z).shift k)
    (g' : (forgetToGradedModule A').obj Z ⟶ ((forgetToGradedModule A').obj Y).shift l) :
    PD.gradedShiftMap j (GradedModule.shiftComp hj g g') =
      GradedModule.shiftComp hj (PD.gradedShiftMap k g) (PD.gradedShiftMap l g') := by
  refine PD.graded_hom_ext fun i V x => ?_
  have hd : i + k + l = i + j := by omega
  refine Eq.trans (PD.gradedShiftMap_unit j (GradedModule.shiftComp hj g g') i V x) ?_
  refine Eq.trans (congrArg ((PD.unit Y).app (i + j) V)
    (degCastHom_val_app ((forgetToGradedModule A').obj Y).piece hd V
      (homSections (g'.app (i + k)) V (homSections (g.app i) V x)))) ?_
  refine Eq.trans (SemilinearHom.app_castHom (PD.unit Y) hd V _) ?_
  refine Eq.trans ?_ (degCastHom_val_app ((forgetToGradedModule A).obj (PD.obj Y)).piece hd
    (u.op.obj V) (homSections ((PD.gradedShiftMap l g').app (i + k)) (u.op.obj V)
      (homSections ((PD.gradedShiftMap k g).app i) (u.op.obj V)
        ((PD.unit W).app i V x)))).symm
  refine congrArg (castHom ((forgetToGradedModule A).obj (PD.obj Y)).piece hd (u.op.obj V)) ?_
  refine Eq.trans ?_
    (congrArg (homSections ((PD.gradedShiftMap l g').app (i + k)) (u.op.obj V))
      (PD.gradedShiftMap_unit k g i V x).symm)
  exact (PD.gradedShiftMap_unit l g' (i + k) V (homSections (g.app i) V x)).symm

/-- The transport of the degree-zero family of a morphism of right differential graded modules
is the degree-zero family of its pullback. -/
theorem gradedShiftMap_shiftOfHom (h : W ⟶ Z) :
    PD.gradedShiftMap 0
        (GradedModule.shiftOfHom ((forgetToGradedModule A').map h)) =
      GradedModule.shiftOfHom ((forgetToGradedModule A).map (PD.map h)) := by
  refine PD.graded_hom_ext fun i V x => ?_
  have hd : i = i + 0 := by omega
  refine Eq.trans (PD.gradedShiftMap_unit 0
    (GradedModule.shiftOfHom ((forgetToGradedModule A').map h)) i V x) ?_
  refine Eq.trans (congrArg ((PD.unit Z).app (i + 0) V)
    (degCastHom_val_app ((forgetToGradedModule A').obj Z).piece hd V
      (homSections (h.toHomologicalComplex.f i) V x))) ?_
  refine Eq.trans (SemilinearHom.app_castHom (PD.unit Z) hd V _) ?_
  refine Eq.trans (congrArg (castHom (PD.obj Z).complex.X hd (u.op.obj V))
    (congrArg (fun ϑ : SemilinearHom φ W (PD.obj Z) => ϑ.app i V x)
      (PD.unit_postcomp_map h)).symm) ?_
  exact (degCastHom_val_app ((forgetToGradedModule A).obj (PD.obj Z)).piece hd (u.op.obj V)
    (homSections ((PD.map h).toHomologicalComplex.f i) (u.op.obj V)
      ((PD.unit W).app i V x))).symm

/-- The transport of the zero family is zero. -/
theorem gradedShiftMap_zero (k : ℤ) :
    PD.gradedShiftMap k
        (0 : (forgetToGradedModule A').obj W ⟶
          ((forgetToGradedModule A').obj Z).shift k) = 0 := by
  refine PD.graded_hom_ext fun i V x => ?_
  refine Eq.trans (PD.gradedShiftMap_unit k 0 i V x) ?_
  refine Eq.trans (congrArg ((PD.unit Z).app (i + k) V) (homSections_zero V x)) ?_
  exact (map_zero _).trans (homSections_zero (u.op.obj V) ((PD.unit W).app i V x)).symm

/-- The transport of a sum of two right-linear families is the sum of the transports. -/
theorem gradedShiftMap_add (k : ℤ)
    (g g' : (forgetToGradedModule A').obj W ⟶ ((forgetToGradedModule A').obj Z).shift k) :
    PD.gradedShiftMap k (g + g') = PD.gradedShiftMap k g + PD.gradedShiftMap k g' := by
  refine PD.graded_hom_ext fun i V x => ?_
  refine Eq.trans (PD.gradedShiftMap_unit k (g + g') i V x) ?_
  refine Eq.trans (congrArg ((PD.unit Z).app (i + k) V)
    (homSections_add (g.app i) (g'.app i) V x)) ?_
  refine Eq.trans (map_add ((PD.unit Z).app (i + k) V) _ _) ?_
  refine Eq.trans (congrArg₂ (· + ·) (PD.gradedShiftMap_unit k g i V x).symm
    (PD.gradedShiftMap_unit k g' i V x).symm) ?_
  exact (homSections_add ((PD.gradedShiftMap k g).app i) ((PD.gradedShiftMap k g').app i)
    (u.op.obj V) ((PD.unit W).app i V x)).symm

end PullbackData

end PullbackShift

end DifferentialGradedModule

end SheafOfModules

end
