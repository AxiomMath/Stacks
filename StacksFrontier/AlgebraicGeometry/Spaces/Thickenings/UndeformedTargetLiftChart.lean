module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleChartKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftDerivationActionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageRingSectionsChart
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealPowerCompatible
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# Twisting a lift into an undeformed target on an étale chart

Let `Z ⊂ X'` be a first order thickening of algebraic spaces over a scheme `S`, with inclusion
`i`, let `q : Y ⟶ Bs`, `p : X' ⟶ Bs` and `a : Z ⟶ Y`, and let `θ` be a local section, over the
part of `Z` above an étale chart `U'` of `X'`, of `SheafHom_{𝒪_Z}(a^*Ω_{Y/Bs}, 𝒞_{Z/X'})`. This
file moves a lift `α : U' ⟶ Y` of `a` by `θ` **on a chart**: on a chart `T ⟶ U'` of `X'` on which
`α` factors through an affine chart `ε : T ⟶ Q` of `Y` carrying an affine chart diagram over `Bs`,
the moved lift is the morphism `T ⟶ Q` whose map of regular functions is

`x ↦ ε^♯ x + ι_T (θ (d_{Y/Bs} x))`,

the source's `(a')^♯ + D` with `D = d_{Y/Bs} ∘ θ` (Equation (0619) and the proof of
[Stacks Project, Tag 04D0]).

## Main definitions

* `AlgebraicGeometry.Space.conormalChartDiagram` and `AlgebraicGeometry.Space.conormalChartIncl`:
  the base-changed chart `T_Z = Z ×_{X'} T` and the inclusion
  `ι_T : 𝒞_{Z/X'}(T_Z) ⟶ Γ(T, 𝒪_T)`, the inverse of the chart projection
  `(i_*𝒞_{Z/X'})(T) ≅ 𝒞_{Z/X'}(T_Z)` followed by
  `AlgebraicGeometry.Space.firstOrderConormalModuleι`.
* `AlgebraicGeometry.Space.liftActionSheafApp`: a local section of the acting sheaf evaluated on
  the sections over a chart above its chart.
* `AlgebraicGeometry.Space.LiftChart`: a chart of a lift, and `LiftChart.derivation`,
  `LiftChart.twist`, `LiftChart.twistScheme`, `LiftChart.twistHom`, `LiftChart.twistSection`: the
  derivation `θ ∘ d` on the chart, the twisted map of regular functions, the twisted morphism of
  schemes, the twisted morphism of the site over `S`, and the twisted section of `Y`.
* `AlgebraicGeometry.Space.liftChartSieve`: the sieve of the charts of a lift.

## Main results

* `AlgebraicGeometry.Space.conormalChartIncl_smul`, `conormalChartIncl_mem_definingIdealAt`,
  `conormalChartIncl_naturality`: `ι_T` is semilinear, lands in the defining ideal, and is natural.
* `AlgebraicGeometry.Space.LiftChart.derivation_mul`: the Leibniz rule for `θ ∘ d` on the chart.
* `AlgebraicGeometry.Space.LiftChart.twistScheme_comp_structure`: the twisted morphism lies over
  `S`, because `θ ∘ d` kills the functions read from `Bs`
  (`LiftChart.derivation_chartDiagramPullback`).
* `AlgebraicGeometry.Space.LiftChart.isChartLift_twistSection`: the twisted section is a lift.
* `AlgebraicGeometry.Space.LiftChart.map_comp_twistSection` and
  `AlgebraicGeometry.Space.twistSection_eq_of_liftChart`: the twisted section is natural in the
  chart of `X'` and does not depend on the chart of `Y`.
* `AlgebraicGeometry.Space.liftChartSieve_mem`: the charts of a lift cover.

## Implementation notes

Nothing here is a morphism into a non-affine target, so Properties of Spaces, Theorem 04KL is
never used: the twisted morphism is `Stacks.Thickenings.homOfAppTop` into the affine chart `Q`.
The conormal module is never formed for a chart of `X'`: the section `θ` is evaluated on the
base-changed chart `T_Z` of `Z` itself, and its value is included into `Γ(T, 𝒪_T)` through the
conormal module of `Z ⊂ X'`.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {X' : AlgebraicSpaces C S hS} (Z : ClosedSubspaces C S hS X'.1)

/-- **The chart diagram of the base change of an étale chart of `X'` to the closed subspace
`Z`**: the base-changed chart `T_Z = Z ×_{X'} T` of `Z`, the chart `T` of `X'` and the cartesian
projection `T_Z ⟶ T`, over the inclusion of `Z`. -/
noncomputable def conormalChartDiagram (T : SmallEtale C S hS X'.1) :
    ChartDiagram C S hS Z.1.toFunctor X'.1 (subspaceInclusion C S hS X' Z).hom where
  U := (smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj T
  V := T
  g := Z.2.2.rep.snd T.1.hom
  comm := Z.2.2.rep.w T.1.hom

/-- The cartesian form of `AlgebraicGeometry.Space.conormalChartDiagram` is the comparison of
the two base changes of `T`: both are the morphism to `Z ×_{X'} T` lifting the cartesian
projection. -/
theorem chartLift_conormalChartDiagram (T : SmallEtale C S hS X'.1) :
    chartLift C S hS (subspaceInclusion C S hS X' Z) (conormalChartDiagram C S hS Z T) =
      (smallBaseChangeComparisonIso C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep T).hom :=
  (chartLift_unique C S hS (subspaceInclusion C S hS X' Z) (conormalChartDiagram C S hS Z T)
    _ (congrArg (fun m ↦ m.hom) (smallBaseChangeComparisonIso_hom_projection C S hS
      (subspaceInclusion C S hS X' Z) Z.2.2.rep T))).symm

/-- **The chart projection of a direct image along the inclusion of `Z` at the base-changed
chart `T_Z` is bijective**: `T_Z` is the base change of `T`, so the index is initial. -/
theorem bijective_modulePushforwardCounitApp_conormalChartDiagram
    (F : Modules.{u, u} C S hS Z.1.toFunctor Z.2.1) (T : SmallEtale C S hS X'.1) :
    Function.Bijective (modulePushforwardCounitApp C S hS (subspaceInclusion C S hS X' Z) F
      (conormalChartDiagram C S hS Z T)) := by
  have hiso : IsIso (indexOfChartDiagram C S hS (subspaceInclusion C S hS X' Z)
      (conormalChartDiagram C S hS Z T)).hom.unop := by
    change IsIso
      (chartLift C S hS (subspaceInclusion C S hS X' Z) (conormalChartDiagram C S hS Z T))
    rw [chartLift_conormalChartDiagram]
    exact Iso.isIso_hom _
  exact bijective_directImageChartProjection_of_isIso_hom C S hS
    (subspaceInclusion C S hS X' Z) T _ hiso
    (moduleSetSheaf C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) F)

/-- The bijection `(i_*F)(T) ≅ F(T_Z)` of
`AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_conormalChartDiagram`. -/
noncomputable def modulePushforwardChartSectionsEquiv
    (F : Modules.{u, u} C S hS Z.1.toFunctor Z.2.1) (T : SmallEtale C S hS X'.1) :
    ((modulePushforward C S hS (subspaceInclusion C S hS X' Z)).obj F).val.obj (op T) ≃
      F.val.obj (op (conormalChartDiagram C S hS Z T).U) :=
  Equiv.ofBijective _ (bijective_modulePushforwardCounitApp_conormalChartDiagram C S hS Z F T)

variable (hZ : IsFirstOrderThickening C S hS X' Z.1)

/-- **The inclusion `ι_T : 𝒞_{Z/X'}(T_Z) ⟶ Γ(T, 𝒪_T)` of the conormal module of a first order
thickening, read on an étale chart `T` of the ambient space**: the inverse of the chart projection
`(i_*𝒞_{Z/X'})(T) ≅ 𝒞_{Z/X'}(T_Z)` followed by
`AlgebraicGeometry.Space.firstOrderConormalModuleι`. -/
noncomputable def conormalChartIncl (T : SmallEtale C S hS X'.1)
    (m : (conormalModule C S hS X' Z).val.obj (op (conormalChartDiagram C S hS Z T).U)) :
    (structureRingSheaf C S hS X').obj.obj (op T) :=
  (firstOrderConormalModuleι C S hS Z hZ).val.app (op T)
    ((modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).symm m)

/-- `ι_T` is additive. -/
theorem conormalChartIncl_add (T : SmallEtale C S hS X'.1)
    (m m' : (conormalModule C S hS X' Z).val.obj (op (conormalChartDiagram C S hS Z T).U)) :
    conormalChartIncl C S hS Z hZ T (m + m') =
      conormalChartIncl C S hS Z hZ T m + conormalChartIncl C S hS Z hZ T m' := by
  have h :
      (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).symm (m + m') =
      (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).symm m +
        (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).symm m' := by
    refine
      (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).injective ?_
    rw [Equiv.apply_symm_apply]
    refine ((modulePushforwardCounitApp_add C S hS (subspaceInclusion C S hS X' Z) _
      (conormalChartDiagram C S hS Z T) _ _).trans ?_).symm
    exact congrArg₂ (fun a b ↦ a + b)
      (Equiv.apply_symm_apply
        (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T) m)
      (Equiv.apply_symm_apply
        (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T) m')
  rw [conormalChartIncl, h]
  exact ((firstOrderConormalModuleι C S hS Z hZ).val.app (op T)).hom.map_add _ _

/-- **`ι_T` takes its values in the defining ideal of `T_Z ⊂ T`**, the kernel of pullback of
regular functions along `T_Z ⟶ T`. -/
theorem conormalChartIncl_mem_definingIdealAt (T : SmallEtale C S hS X'.1)
    (m : (conormalModule C S hS X' Z).val.obj (op (conormalChartDiagram C S hS Z T).U)) :
    (Scheme.Γ.map ((BigFppfOver.toScheme C S hS).map
        (Z.2.2.rep.snd T.1.hom)).op).hom (conormalChartIncl C S hS Z hZ T m) = 0 :=
  (mem_range_firstOrderConormalModuleι_app_iff_appTop_eq_zero C S hS Z hZ T _).1 ⟨_, rfl⟩

/-- **The values of `ι_T` have square zero.** -/
theorem conormalChartIncl_mul_conormalChartIncl (T : SmallEtale C S hS X'.1)
    (m m' : (conormalModule C S hS X' Z).val.obj (op (conormalChartDiagram C S hS Z T).U)) :
    conormalChartIncl C S hS Z hZ T m * conormalChartIncl C S hS Z hZ T m' = 0 :=
  mul_eq_zero_of_mem_definingIdealAt C S hS Z hZ
    ((mem_range_firstOrderConormalModuleι_app_iff C S hS Z hZ (op T) _).1 ⟨_, rfl⟩)
    ((mem_range_firstOrderConormalModuleι_app_iff C S hS Z hZ (op T) _).1 ⟨_, rfl⟩)

/-- **`ι_T` is semilinear**: for a regular function `f` on `T` with restriction `f|_{T_Z}`,
`ι_T (f|_{T_Z} • m) = f * ι_T m`. -/
theorem conormalChartIncl_smul (T : SmallEtale C S hS X'.1)
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite C S hS X'.1 X'.2).O)).obj.obj (op T))
    (m : (conormalModule C S hS X' Z).val.obj (op (conormalChartDiagram C S hS Z T).U)) :
    conormalChartIncl C S hS Z hZ T
        (chartDiagramPullback C S hS (subspaceInclusion C S hS X' Z)
          (conormalChartDiagram C S hS Z T) f • m) =
      (show (structureRingSheaf C S hS X').obj.obj (op T) from f) *
        conormalChartIncl C S hS Z hZ T m := by
  have h : (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).symm
      (chartDiagramPullback C S hS (subspaceInclusion C S hS X' Z)
        (conormalChartDiagram C S hS Z T) f • m) =
      f • (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).symm m := by
    refine
      (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).injective ?_
    rw [Equiv.apply_symm_apply]
    refine (Eq.trans ?_ (modulePushforwardCounitApp_smul C S hS (subspaceInclusion C S hS X' Z)
      _ (conormalChartDiagram C S hS Z T) f _).symm)
    exact congrArg _
      (Equiv.apply_symm_apply
        (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T) m).symm
  unfold conormalChartIncl
  rw [h]
  exact ((firstOrderConormalModuleι C S hS Z hZ).val.app (op T)).hom.map_smul f _

/-- **`ι_T` is natural in the chart `T`**: restricting along a morphism of charts `T' ⟶ T` before
or after the inclusion gives the same regular function on `T'`. -/
theorem conormalChartIncl_naturality {T T' : SmallEtale C S hS X'.1} (k : T' ⟶ T)
    (m : (conormalModule C S hS X' Z).val.obj (op (conormalChartDiagram C S hS Z T).U)) :
    conormalChartIncl C S hS Z hZ T'
        ((conormalModule C S hS X' Z).val.map
          ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map k).op m) =
      (structureRingSheaf C S hS X').obj.map k.op (conormalChartIncl C S hS Z hZ T m) := by
  have h : (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T').symm
      ((conormalModule C S hS X' Z).val.map
        ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map k).op m) =
      ((modulePushforward C S hS (subspaceInclusion C S hS X' Z)).obj
          (conormalModule C S hS X' Z)).val.map k.op
        ((modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T).symm m) := by
    refine
      (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T').injective ?_
    refine Eq.trans (Equiv.apply_symm_apply _ _) ?_
    refine ((modulePushforwardCounitApp_naturality C S hS (subspaceInclusion C S hS X' Z) _
      (conormalChartDiagram C S hS Z T) (conormalChartDiagram C S hS Z T')
      ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map k) k
      (smallBaseChange_map_snd C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep k) _).trans
      ?_).symm
    exact congrArg ((conormalModule C S hS X' Z).val.map
      ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map k).op)
      (Equiv.apply_symm_apply
        (modulePushforwardChartSectionsEquiv C S hS Z (conormalModule C S hS X' Z) T) m)
  unfold conormalChartIncl
  rw [h]
  exact PresheafOfModules.naturality_apply (firstOrderConormalModuleι C S hS Z hZ).val k.op _

/-! ### The derivation `θ ∘ d` attached to a local section of the acting sheaf -/

variable {Y Bs : AlgebraicSpaces C S hS} (q : Y ⟶ Bs)
  (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)

/-- A local section of `SheafHom_{𝒪_Z}(a^*Ω_{Y/Bs}, 𝒞_{Z/X'})` over a chart `W₀` of `Z`, evaluated
on the sections over a chart `n : K ⟶ W₀` above `W₀`. -/
noncomputable def liftActionSheafApp {W₀ : (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).C}
    (θ : (liftActionSheaf C S hS Z q a).val.obj (op W₀)) (n : Over W₀)
    (x : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.obj (op n.left)) :
    (conormalModule C S hS X' Z).val.obj (op n.left) :=
  ((show (restrFun (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj
        ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val ⟶
      (restrFun (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj
        (conormalModule C S hS X' Z).val from θ).app (op n)).hom x

variable {q a} in
/-- `liftActionSheafApp` is additive in the section. -/
theorem liftActionSheafApp_add {W₀ : (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).C}
    (θ : (liftActionSheaf C S hS Z q a).val.obj (op W₀)) (n : Over W₀)
    (x y : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.obj (op n.left)) :
    liftActionSheafApp C S hS Z q a θ n (x + y) =
      liftActionSheafApp C S hS Z q a θ n x + liftActionSheafApp C S hS Z q a θ n y :=
  map_add _ x y

variable {q a} in
/-- `liftActionSheafApp` is linear over the regular functions on the chart. -/
theorem liftActionSheafApp_smul {W₀ : (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).C}
    (θ : (liftActionSheaf C S hS Z q a).val.obj (op W₀)) (n : Over W₀)
    (f : (ORestr (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj (op n))
    (x : ((restrFun (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj
      ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val).obj (op n)) :
    liftActionSheafApp C S hS Z q a θ n (f • x) =
      f • (show ((restrFun (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj
        (conormalModule C S hS X' Z).val).obj (op n) from
          liftActionSheafApp C S hS Z q a θ n x) :=
  ((show (restrFun (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj
        ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val ⟶
      (restrFun (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj
        (conormalModule C S hS X' Z).val from θ).app (op n)).hom.map_smul f x

variable {q a} in
/-- `liftActionSheafApp` at two equal morphisms into `W₀`. -/
theorem liftActionSheafApp_mk_congr {W₀ W : (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).C}
    (θ : (liftActionSheaf C S hS Z q a).val.obj (op W₀)) {n₁ n₂ : W ⟶ W₀} (h : n₁ = n₂)
    (x : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.obj (op W)) :
    liftActionSheafApp C S hS Z q a θ (Over.mk n₁) x =
      liftActionSheafApp C S hS Z q a θ (Over.mk n₂) x := by
  subst h
  rfl

variable {q a} in
/-- `liftActionSheafApp` is additive in the local section of the acting sheaf. -/
theorem liftActionSheafApp_add_left {W₀ : (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).C}
    (θ θ' : (liftActionSheaf C S hS Z q a).val.obj (op W₀)) (n : Over W₀)
    (x : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.obj (op n.left)) :
    liftActionSheafApp C S hS Z q a (θ + θ') n x =
      liftActionSheafApp C S hS Z q a θ n x + liftActionSheafApp C S hS Z q a θ' n x :=
  rfl

variable {q a} in
/-- `liftActionSheafApp` of the zero section vanishes. -/
theorem liftActionSheafApp_zero_left {W₀ : (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).C}
    (n : Over W₀)
    (x : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.obj (op n.left)) :
    liftActionSheafApp C S hS Z q a (0 : (liftActionSheaf C S hS Z q a).val.obj (op W₀)) n x =
      0 :=
  rfl

variable {q a} in
/-- `liftActionSheafApp` of a restricted section is the original section on the composite
chart. -/
theorem liftActionSheafApp_map {W₀ W₁ : (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).C}
    (k : W₁ ⟶ W₀) (θ : (liftActionSheaf C S hS Z q a).val.obj (op W₀)) (n : Over W₁)
    (x : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.obj (op n.left)) :
    liftActionSheafApp C S hS Z q a ((liftActionSheaf C S hS Z q a).val.map k.op θ) n x =
      liftActionSheafApp C S hS Z q a θ (Over.mk (n.hom ≫ k)) x :=
  rfl

variable {q a} in
/-- `liftActionSheafApp` is natural along the morphisms of charts above `W₀`. -/
theorem liftActionSheafApp_naturality
    {W₀ : (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).C}
    (θ : (liftActionSheaf C S hS Z q a).val.obj (op W₀)) {n n' : Over W₀} (h : n' ⟶ n)
    (x : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.obj (op n.left)) :
    liftActionSheafApp C S hS Z q a θ n'
        (((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.map h.left.op x) =
      (conormalModule C S hS X' Z).val.map h.left.op (liftActionSheafApp C S hS Z q a θ n x) :=
  PresheafOfModules.naturality_apply
    (show (restrFun (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj
        ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val ⟶
      (restrFun (smallEtaleRingedSite C S hS Z.1.toFunctor Z.2.1).O.obj W₀).obj
        (conormalModule C S hS X' Z).val from θ) h.op x

/-! ### Charts of a lift, and the twisted map of regular functions -/

/-- **A chart of a section `α : U' ⟶ Y` over an étale chart `U'` of `X'`**: an étale chart `T` of
`X'` over `U'` and an étale chart `Q` of `Y` together with a morphism `ε : T ⟶ Q` through which
`α|_T` factors. -/
structure LiftChart (U' : SmallEtale C S hS X'.1)
    (α : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1) where
  /-- The chart of `X'`. -/
  T : SmallEtale C S hS X'.1
  /-- Its morphism to `U'`. -/
  m : T ⟶ U'
  /-- The chart of `Y`. -/
  Q : SmallEtale C S hS Y.1
  /-- The morphism of charts through which `α|_T` factors. -/
  ε : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q
  /-- `α|_T` factors through `ε`. -/
  w : yoneda.map ε ≫ Q.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ α

variable {C S hS Z q a}

variable {p : X' ⟶ Bs} {U' : SmallEtale C S hS X'.1}
  {α : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1}

/-- **The chart diagram over `a` of a chart of a lift**: the base-changed chart `T_Z` of `Z`, the
chart `Q` of `Y`, and the morphism `T_Z ⟶ T --ε--> Q`. It commutes over `a` because `α` restricts
to `a` on `Z`. -/
noncomputable abbrev LiftChart.diagram (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α) :
    ChartDiagram C S hS Z.1.toFunctor Y.1 a.hom where
  U := (conormalChartDiagram C S hS Z c.T).U
  V := c.Q
  g := Z.2.2.rep.snd c.T.1.hom ≫ c.ε
  comm := by
    have hw : yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ U'.1.hom = c.T.1.hom :=
      CostructuredArrow.w c.m.hom
    have hk : yoneda.map (Z.2.2.rep.snd c.T.1.hom ≫ (SmallEtale.toOver C S hS X'.1).map c.m) ≫
        U'.1.hom = (conormalChartDiagram C S hS Z c.T).U.1.hom ≫ Z.1.ι := by
      rw [Functor.map_comp, Category.assoc, hw]
      exact (Z.2.2.rep.w c.T.1.hom).symm
    have h := hα.2 _ _ _ hk
    refine h.symm.trans ?_
    calc yoneda.map (Z.2.2.rep.snd c.T.1.hom ≫ (SmallEtale.toOver C S hS X'.1).map c.m) ≫ α
        = yoneda.map (Z.2.2.rep.snd c.T.1.hom) ≫
            (yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ α) :=
          (congrArg (· ≫ α) (yoneda.map_comp _ _)).trans (Category.assoc _ _ _)
      _ = yoneda.map (Z.2.2.rep.snd c.T.1.hom) ≫ (yoneda.map c.ε ≫ c.Q.1.hom) :=
          congrArg (yoneda.map (Z.2.2.rep.snd c.T.1.hom) ≫ ·) c.w.symm
      _ = yoneda.map (Z.2.2.rep.snd c.T.1.hom ≫ c.ε) ≫ c.Q.1.hom :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c.Q.1.hom) (yoneda.map_comp _ _).symm)

/-- The vertical morphism of `LiftChart.diagram` is `T_Z ⟶ T --ε--> Q`. -/
theorem LiftChart.diagram_g (c : LiftChart C S hS U' α) (hα : IsChartLift C S hS p q a.hom U' α) :
    (c.diagram hα).g = Z.2.2.rep.snd c.T.1.hom ≫ c.ε :=
  rfl

/-- The pullback of regular functions along the vertical morphism of `LiftChart.diagram` is
pullback along `ε` followed by restriction to `T_Z`. -/
theorem LiftChart.chartDiagramPullback_diagram (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (x : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite C S hS Y.1 Y.2).O)).obj.obj (op c.Q)) :
    chartDiagramPullback C S hS a (c.diagram hα) x =
      chartDiagramPullback C S hS (subspaceInclusion C S hS X' Z)
        (conormalChartDiagram C S hS Z c.T)
        ((Scheme.Γ.map ((BigFppfOver.toScheme C S hS).map c.ε).op).hom x) := by
  change ((Scheme.Γ.map ((BigFppfOver.toScheme C S hS).map
      (Z.2.2.rep.snd c.T.1.hom ≫ c.ε)).op).hom x) = _
  rw [Functor.map_comp, op_comp, Functor.map_comp]
  rfl

/-- **The derivation `D = θ ∘ d_{Y/Bs}` read on a chart of a lift**: a regular function `x` on
`Q` goes to the value of the local section `θ` of `SheafHom_{𝒪_Z}(a^*Ω_{Y/Bs}, 𝒞_{Z/X'})` on the
unit section of `d x` over `T_Z`, a section of the conormal module over `T_Z`. -/
noncomputable def LiftChart.derivation (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (x : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    (conormalModule C S hS X' Z).val.obj (op (conormalChartDiagram C S hS Z c.T).U) :=
  liftActionSheafApp C S hS Z q a θ
    (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m))
    (modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q) (c.diagram hα)
      ((universalDerivation C S hS q).d x))

/-- The unit section of a module pullback is additive. -/
theorem modulePullbackUnitSection_add {X₁ X₂ : AlgebraicSpaces C S hS} (g : X₁ ⟶ X₂)
    (M : Modules.{u, u} C S hS X₂.1 X₂.2) (d : ChartDiagram C S hS X₁.1 X₂.1 g.hom)
    (s t : M.val.obj (op d.V)) :
    modulePullbackUnitSection C S hS g M d (s + t) =
      modulePullbackUnitSection C S hS g M d s + modulePullbackUnitSection C S hS g M d t := by
  have h := (modulePullbackHomFMap C S hS g M _ (𝟙 _)).map_add d s t
  rw [modulePullbackHomFMap_app, modulePullbackHomFMap_app, modulePullbackHomFMap_app] at h
  exact h

/-- **The Leibniz rule for the derivation read on a chart of a lift.** -/
theorem LiftChart.derivation_mul (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (x y : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    c.derivation hα θ (x * y) =
      chartDiagramPullback C S hS a (c.diagram hα) x • c.derivation hα θ y +
        chartDiagramPullback C S hS a (c.diagram hα) y • c.derivation hα θ x := by
  refine (congrArg (fun t ↦ liftActionSheafApp C S hS Z q a θ
    (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m))
    (modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q) (c.diagram hα) t))
    ((universalDerivation C S hS q).d_mul x y)).trans ?_
  refine (congrArg (liftActionSheafApp C S hS Z q a θ
    (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m)))
    (modulePullbackUnitSection_add a _ (c.diagram hα) _ _)).trans ?_
  refine (liftActionSheafApp_add C S hS Z θ _ _ _).trans ?_
  refine congrArg₂ (· + ·) ?_ ?_ <;>
  exact (congrArg (liftActionSheafApp C S hS Z q a θ
      (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m)))
      (modulePullbackUnitSection_smul C S hS a _ (c.diagram hα) _ _)).trans
      (liftActionSheafApp_smul C S hS Z θ _ _ _)

/-- A map out of the sections of a sheaf of abelian groups which is additive kills `0`. -/
theorem liftChart_map_zero_of_add {M N : Type*} [AddGroup M] [AddGroup N] (f : M → N)
    (hf : ∀ x y, f (x + y) = f x + f y) : f 0 = 0 := by
  have h := hf 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

/-- **The derivation read on a chart of a lift is additive.** -/
theorem LiftChart.derivation_add (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (x y : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    c.derivation hα θ (x + y) = c.derivation hα θ x + c.derivation hα θ y := by
  unfold LiftChart.derivation
  refine (congrArg (fun t ↦ liftActionSheafApp C S hS Z q a θ
    (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m))
    (modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q) (c.diagram hα) t))
    (map_add ((universalDerivation C S hS q).d (X := op c.Q)) x y)).trans ?_
  refine (congrArg (liftActionSheafApp C S hS Z q a θ
    (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m)))
    (modulePullbackUnitSection_add a _ (c.diagram hα) _ _)).trans ?_
  exact liftActionSheafApp_add C S hS Z θ _ _ _

/-- The derivation read on a chart of a lift kills the functions killed by `d_{Y/Bs}`. -/
private theorem LiftChart.derivation_eq_zero_of_d_eq_zero (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    {x : (structureRingSheaf C S hS Y).obj.obj (op c.Q)}
    (h : (universalDerivation C S hS q).d (X := op c.Q) x = 0) : c.derivation hα θ x = 0 := by
  unfold LiftChart.derivation
  rw [h]
  refine (congrArg (liftActionSheafApp C S hS Z q a θ
    (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m)))
    (liftChart_map_zero_of_add _ (modulePullbackUnitSection_add a _ (c.diagram hα)))).trans ?_
  exact liftChart_map_zero_of_add _ (liftActionSheafApp_add C S hS Z θ _)

/-- **The derivation read on a chart of a lift kills `1`.** -/
theorem LiftChart.derivation_one (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U'))) :
    c.derivation hα θ 1 = 0 :=
  c.derivation_eq_zero_of_d_eq_zero hα θ ((universalDerivation C S hS q).d_one (op c.Q))

/-- The pullback of regular functions along the morphism `ε : T ⟶ Q` of a chart of a lift. -/
noncomputable abbrev LiftChart.pullback (c : LiftChart C S hS U' α) :
    (structureRingSheaf C S hS Y).obj.obj (op c.Q) →+*
      (structureRingSheaf C S hS X').obj.obj (op c.T) :=
  ((forget₂ CommRingCat RingCat).map
    (Scheme.Γ.map ((BigFppfOver.toScheme C S hS).map c.ε).op)).hom

/-- **`ι_T ∘ D` satisfies the Leibniz rule along the pullback by `ε`.** -/
theorem LiftChart.conormalChartIncl_derivation_mul (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (x y : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    conormalChartIncl C S hS Z hZ c.T (c.derivation hα θ (x * y)) =
      c.pullback x * conormalChartIncl C S hS Z hZ c.T (c.derivation hα θ y) +
        c.pullback y * conormalChartIncl C S hS Z hZ c.T (c.derivation hα θ x) := by
  refine (congrArg (conormalChartIncl C S hS Z hZ c.T) (c.derivation_mul hα θ x y)).trans ?_
  refine (conormalChartIncl_add C S hS Z hZ c.T _ _).trans ?_
  refine congrArg₂ (· + ·) ?_ ?_ <;>
  exact (congrArg (conormalChartIncl C S hS Z hZ c.T ∘ (· • _))
      (c.chartDiagramPullback_diagram hα _)).trans
      (conormalChartIncl_smul C S hS Z hZ c.T _ _)

/-- The algebra behind the multiplicativity of the twisted map: in a commutative ring, a
perturbation by a square-zero term satisfying the Leibniz rule is multiplicative. -/
theorem liftChart_add_mul_add_of_leibniz {R : Type*} [CommRing R] (px py pxy ix iy ixy : R)
    (hp : pxy = px * py) (hi : ixy = px * iy + py * ix) (h0 : ix * iy = 0) :
    pxy + ixy = (px + ix) * (py + iy) := by
  rw [hp, hi, add_mul, mul_add, mul_add, h0, add_zero]
  ring

/-- The algebra behind the additivity of the twisted map. -/
theorem liftChart_add_add_add {R : Type*} [AddCommGroup R] (px py pxy ix iy ixy : R)
    (hp : pxy = px + py) (hi : ixy = ix + iy) :
    pxy + ixy = (px + ix) + (py + iy) := by
  rw [hp, hi]
  abel

/-- **The twisted map of regular functions on a chart of a lift**:
`x ↦ ε^♯ x + ι_T (θ (d x))`, the comorphism of `α` on the chart moved by the derivation
`θ ∘ d_{Y/Bs}`. This is the source's `(a')^♯ + D` of [Stacks Project, Tag 04D0], read on a
chart. -/
noncomputable def LiftChart.twist (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U'))) :
    (structureRingSheaf C S hS Y).obj.obj (op c.Q) →+*
      (structureRingSheaf C S hS X').obj.obj (op c.T) where
  toFun x := c.pullback x + conormalChartIncl C S hS Z hZ c.T (c.derivation hα θ x)
  map_one' :=
    (congrArg₂ (· + ·) (map_one c.pullback)
      ((congrArg (conormalChartIncl C S hS Z hZ c.T) (c.derivation_one hα θ)).trans
        (liftChart_map_zero_of_add _ (conormalChartIncl_add C S hS Z hZ c.T)))).trans (add_zero _)
  map_mul' x y :=
    liftChart_add_mul_add_of_leibniz
      (R := ToType ((smallEtaleRingedSite C S hS X'.1 X'.2).O.obj.obj (op c.T))) _ _ _ _ _ _
      (map_mul c.pullback x y) (c.conormalChartIncl_derivation_mul hZ hα θ x y)
      (conormalChartIncl_mul_conormalChartIncl C S hS Z hZ c.T _ _)
  map_zero' :=
    (congrArg₂ (· + ·) (map_zero c.pullback)
      ((congrArg (conormalChartIncl C S hS Z hZ c.T)
        (liftChart_map_zero_of_add _ (c.derivation_add hα θ))).trans
        (liftChart_map_zero_of_add _ (conormalChartIncl_add C S hS Z hZ c.T)))).trans (add_zero _)
  map_add' x y :=
    liftChart_add_add_add
      (R := ToType ((smallEtaleRingedSite C S hS X'.1 X'.2).O.obj.obj (op c.T))) _ _ _ _ _ _
      (map_add c.pullback x y)
      ((congrArg (conormalChartIncl C S hS Z hZ c.T) (c.derivation_add hα θ x y)).trans
        (conormalChartIncl_add C S hS Z hZ c.T _ _))

/-- The value of the twisted map. -/
theorem LiftChart.twist_apply (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (x : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    c.twist hZ hα θ x = c.pullback x + conormalChartIncl C S hS Z hZ c.T (c.derivation hα θ x) :=
  rfl

/-! ### The twisted morphism of charts -/

/-- **The derivation kills the functions read from the base**: a regular function on a chart
`V_B` of `Bs` pulled back to `Q` along a chart diagram over `q` is a value of `q^♯`, which the
universal derivation `d_{Y/Bs}` kills. -/
theorem LiftChart.derivation_chartDiagramPullback (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (VB : SmallEtale C S hS Bs.1)
    (qq : (SmallEtale.toOver C S hS Y.1).obj c.Q ⟶ (SmallEtale.toOver C S hS Bs.1).obj VB)
    (hqq : c.Q.1.hom ≫ q.hom = yoneda.map qq ≫ VB.1.hom)
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite C S hS Bs.1 Bs.2).O)).obj.obj (op VB)) :
    c.derivation hα θ (chartDiagramPullback C S hS q ⟨c.Q, VB, qq, hqq⟩ f) = 0 := by
  obtain ⟨t, ht⟩ := exists_app_structureSharpRingInverseImage_eq_chartPullbackRingHom C S hS q VB
    (indexOfChartDiagram C S hS q ⟨c.Q, VB, qq, hqq⟩) f
  have hpb : chartDiagramPullback C S hS q ⟨c.Q, VB, qq, hqq⟩ f =
      chartPullbackRingHom C S hS q VB (indexOfChartDiagram C S hS q ⟨c.Q, VB, qq, hqq⟩) f :=
    (chartPullback_indexOfChartDiagram C S hS q ⟨c.Q, VB, qq, hqq⟩ f).symm
  have hd : (universalDerivation C S hS q).d
      (chartDiagramPullback C S hS q ⟨c.Q, VB, qq, hqq⟩ f) = 0 := by
    rw [hpb, ← ht, structureSharpRingInverseImage_eq_forget₂]
    exact (universalDerivation C S hS q).d_app t
  exact c.derivation_eq_zero_of_d_eq_zero hα θ hd

/-- **The twisted map agrees with the pullback by `ε` on the functions read from the base.** -/
theorem LiftChart.twist_chartDiagramPullback (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (VB : SmallEtale C S hS Bs.1)
    (qq : (SmallEtale.toOver C S hS Y.1).obj c.Q ⟶ (SmallEtale.toOver C S hS Bs.1).obj VB)
    (hqq : c.Q.1.hom ≫ q.hom = yoneda.map qq ≫ VB.1.hom)
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite C S hS Bs.1 Bs.2).O)).obj.obj (op VB)) :
    c.twist hZ hα θ (chartDiagramPullback C S hS q ⟨c.Q, VB, qq, hqq⟩ f) =
      c.pullback (chartDiagramPullback C S hS q ⟨c.Q, VB, qq, hqq⟩ f) := by
  refine (c.twist_apply hZ hα θ _).trans ?_
  refine (congrArg (fun z ↦ c.pullback (chartDiagramPullback C S hS q ⟨c.Q, VB, qq, hqq⟩ f) + z)
    ((congrArg (conormalChartIncl C S hS Z hZ c.T)
      (c.derivation_chartDiagramPullback hα θ VB qq hqq f)).trans
      (liftChart_map_zero_of_add _ (conormalChartIncl_add C S hS Z hZ c.T)))).trans ?_
  exact add_zero _

/-- **The twisted morphism of schemes `T ⟶ Q`** of a chart of a lift with affine `Q`: the
morphism into the affine scheme `Q` whose map of regular functions is the twisted map. -/
noncomputable def LiftChart.twistScheme (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    [IsAffine ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS Y.1).obj c.Q))] :
    (BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj c.T) ⟶
      (BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS Y.1).obj c.Q) :=
  Stacks.Thickenings.homOfAppTop
    (show Γ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS Y.1).obj c.Q),
        (⊤ : ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS Y.1).obj c.Q)).Opens))
      ⟶ Γ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj c.T),
        (⊤ : ((BigFppfOver.toScheme C S hS).obj
          ((SmallEtale.toOver C S hS X'.1).obj c.T)).Opens)) from
      CommRingCat.ofHom (c.twist hZ hα θ))

/-- The twisted morphism acts on regular functions by the twisted map. -/
theorem LiftChart.twistScheme_appTop (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    [IsAffine ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS Y.1).obj c.Q))]
    (x : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    (c.twistScheme hZ hα θ).appTop.hom x = c.twist hZ hα θ x := by
  unfold LiftChart.twistScheme
  rw [Stacks.Thickenings.homOfAppTop_appTop]
  rfl

/-- **The twisted morphism agrees with `ε` after any affine chart `V_B` of the base**: their
maps of regular functions agree on the functions read from `V_B`. -/
theorem LiftChart.twistScheme_comp_eq (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    [IsAffine ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS Y.1).obj c.Q))]
    (VB : SmallEtale C S hS Bs.1)
    [IsAffine ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS Bs.1).obj VB))]
    (qq : (SmallEtale.toOver C S hS Y.1).obj c.Q ⟶ (SmallEtale.toOver C S hS Bs.1).obj VB)
    (hqq : c.Q.1.hom ≫ q.hom = yoneda.map qq ≫ VB.1.hom) :
    c.twistScheme hZ hα θ ≫ (BigFppfOver.toScheme C S hS).map qq =
      (BigFppfOver.toScheme C S hS).map c.ε ≫ (BigFppfOver.toScheme C S hS).map qq := by
  refine ext_of_isAffine ?_
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  refine CommRingCat.hom_ext (RingHom.ext fun f ↦ ?_)
  exact (c.twistScheme_appTop hZ hα θ _).trans (c.twist_chartDiagramPullback hZ hα θ VB qq hqq f)

/-- **The twisted morphism lies over `S`.** -/
theorem LiftChart.twistScheme_comp_structure (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    [IsAffine ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS Y.1).obj c.Q))]
    (hQ : HasAffineChartDiagram C S hS q c.Q) :
    c.twistScheme hZ hα θ ≫ C.inclusion.map ((SmallEtale.toOver C S hS Y.1).obj c.Q).hom =
      C.inclusion.map ((SmallEtale.toOver C S hS X'.1).obj c.T).hom := by
  obtain ⟨-, VB, qq, hqq, hVB⟩ := hQ
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Bs.1).obj VB)) := hVB
  have hQS : (BigFppfOver.toScheme C S hS).map qq ≫
      C.inclusion.map ((SmallEtale.toOver C S hS Bs.1).obj VB).hom =
      C.inclusion.map ((SmallEtale.toOver C S hS Y.1).obj c.Q).hom :=
    BigFppfOver.toScheme_map_comp_inclusion_map_structureHom C S hS qq
  rw [← hQS, ← Category.assoc, c.twistScheme_comp_eq hZ hα θ VB qq hqq.symm, Category.assoc, hQS,
    BigFppfOver.toScheme_map_comp_inclusion_map_structureHom C S hS c.ε]

/-- **The twisted morphism of charts**, as a morphism of the big fppf category over `S`. -/
noncomputable def LiftChart.twistHom (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q) :
    (SmallEtale.toOver C S hS X'.1).obj c.T ⟶ (SmallEtale.toOver C S hS Y.1).obj c.Q :=
  haveI : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
  (BigFppfOver.exists_hom_of_comp_eq C S hS _
    (c.twistScheme_comp_structure hZ hα θ hQ)).choose

/-- The twisted morphism of charts has the twisted morphism of schemes as underlying morphism. -/
theorem LiftChart.toScheme_map_twistHom (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q) :
    haveI : IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
    (BigFppfOver.toScheme C S hS).map (c.twistHom hZ hα θ hQ) = c.twistScheme hZ hα θ :=
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
  (BigFppfOver.exists_hom_of_comp_eq C S hS _
    (c.twistScheme_comp_structure hZ hα θ hQ)).choose_spec

/-- Morphisms of the big fppf category into an affine scheme agree when they agree on regular
functions. -/
private theorem hom_eq_of_appTop_eq {A B : BigFppfOver C S hS}
    [IsAffine ((BigFppfOver.toScheme C S hS).obj B)] {f g : A ⟶ B}
    (h : ∀ x, ((BigFppfOver.toScheme C S hS).map f).appTop.hom x =
      ((BigFppfOver.toScheme C S hS).map g).appTop.hom x) : f = g :=
  (BigFppfOver.toScheme C S hS).map_injective
    (ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext h)))

/-- **The twisted morphism of charts agrees with `ε` on the thickening `T_Z ⊂ T`**: the twisted
map differs from the pullback by `ε` by values of `ι_T`, which restrict to zero on `T_Z`. -/
theorem LiftChart.snd_comp_twistHom (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q) :
    Z.2.2.rep.snd c.T.1.hom ≫ c.twistHom hZ hα θ hQ = Z.2.2.rep.snd c.T.1.hom ≫ c.ε := by
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
  refine hom_eq_of_appTop_eq fun x ↦ ?_
  rw [Functor.map_comp, Functor.map_comp, c.toScheme_map_twistHom hZ hα θ hQ,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  change ((BigFppfOver.toScheme C S hS).map (Z.2.2.rep.snd c.T.1.hom)).appTop.hom
      ((c.twistScheme hZ hα θ).appTop.hom x) =
    ((BigFppfOver.toScheme C S hS).map (Z.2.2.rep.snd c.T.1.hom)).appTop.hom (c.pullback x)
  rw [c.twistScheme_appTop hZ hα θ x, c.twist_apply hZ hα θ x]
  have h0 := conormalChartIncl_mem_definingIdealAt C S hS Z hZ c.T (c.derivation hα θ x)
  exact ((((BigFppfOver.toScheme C S hS).map (Z.2.2.rep.snd c.T.1.hom)).appTop.hom.map_add
    _ _).trans (congrArg (fun z ↦ _ + z) h0)).trans (add_zero _)

/-- **The twisted section** of `Y` over the chart `T` of a lift: the twisted morphism of charts
followed by the chart `Q ⟶ Y`. -/
noncomputable def LiftChart.twistSection (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q) :
    yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj c.T) ⟶ Y.1 :=
  yoneda.map (c.twistHom hZ hα θ hQ) ≫ c.Q.1.hom

/-- **The twisted section is a lift**: it lies over `Bs`, and it restricts to `a` on `T_Z`. -/
theorem LiftChart.isChartLift_twistSection (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q) :
    IsChartLift C S hS p q a.hom c.T (c.twistSection hZ hα θ hQ) := by
  have hw : yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ U'.1.hom = c.T.1.hom :=
    CostructuredArrow.w c.m.hom
  refine ⟨?_, fun W k t hkt ↦ ?_⟩
  · obtain ⟨-, VB, qq, hqq, hVB⟩ := id hQ
    have : IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((SmallEtale.toOver C S hS Bs.1).obj VB)) := hVB
    have : IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
    have hcomp : c.twistHom hZ hα θ hQ ≫ qq = c.ε ≫ qq := by
      refine (BigFppfOver.toScheme C S hS).map_injective ?_
      rw [Functor.map_comp, Functor.map_comp, c.toScheme_map_twistHom hZ hα θ hQ]
      exact c.twistScheme_comp_eq hZ hα θ VB qq hqq.symm
    calc c.twistSection hZ hα θ hQ ≫ q.hom
        = yoneda.map (c.twistHom hZ hα θ hQ) ≫ c.Q.1.hom ≫ q.hom := Category.assoc _ _ _
      _ = yoneda.map (c.twistHom hZ hα θ hQ ≫ qq) ≫ VB.1.hom := by
          rw [← hqq, Functor.map_comp, Category.assoc]
      _ = yoneda.map c.ε ≫ c.Q.1.hom ≫ q.hom := by
          rw [hcomp, Functor.map_comp, Category.assoc, hqq]
      _ = yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ α ≫ q.hom := by
          rw [← Category.assoc, c.w, Category.assoc]
      _ = c.T.1.hom ≫ p.hom := by rw [hα.1, ← Category.assoc, hw]
  · have hk : t ≫ Z.1.ι = yoneda.map k ≫ c.T.1.hom := hkt.symm
    let k' := Z.2.2.rep.lift t k hk
    have hk'₁ : yoneda.map k' ≫ Z.2.2.rep.fst c.T.1.hom = t := Z.2.2.rep.lift_fst t k hk
    have hk'₂ : k' ≫ Z.2.2.rep.snd c.T.1.hom = k := Z.2.2.rep.lift_snd t k hk
    have hdiag : Z.2.2.rep.fst c.T.1.hom ≫ a.hom =
        yoneda.map (Z.2.2.rep.snd c.T.1.hom ≫ c.ε) ≫ c.Q.1.hom := (c.diagram hα).comm
    calc yoneda.map k ≫ c.twistSection hZ hα θ hQ
        = yoneda.map k' ≫ yoneda.map (Z.2.2.rep.snd c.T.1.hom ≫ c.twistHom hZ hα θ hQ) ≫
            c.Q.1.hom := by
          rw [← hk'₂, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
          rfl
      _ = yoneda.map k' ≫ yoneda.map (Z.2.2.rep.snd c.T.1.hom ≫ c.ε) ≫ c.Q.1.hom := by
          rw [c.snd_comp_twistHom hZ hα θ hQ]
      _ = yoneda.map k' ≫ Z.2.2.rep.fst c.T.1.hom ≫ a.hom := by
          rw [← hdiag]
      _ = t ≫ a.hom := by rw [← Category.assoc, hk'₁]

/-! ### Naturality of the twisted section -/

/-- **The restriction of a chart of a lift** along a morphism of charts `T' ⟶ T`. -/
def LiftChart.restrict (c : LiftChart C S hS U' α) {T' : SmallEtale C S hS X'.1}
    (g : T' ⟶ c.T) : LiftChart C S hS U' α where
  T := T'
  m := g ≫ c.m
  Q := c.Q
  ε := (SmallEtale.toOver C S hS X'.1).map g ≫ c.ε
  w := by
    rw [Functor.map_comp, Category.assoc, c.w, Functor.map_comp, Functor.map_comp,
      Category.assoc]

/-- The derivation of a restricted chart is the restriction of the derivation. -/
theorem LiftChart.derivation_restrict (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    {T' : SmallEtale C S hS X'.1} (g : T' ⟶ c.T)
    (x : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    (c.restrict g).derivation hα θ x =
      (conormalModule C S hS X' Z).val.map
        ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map g).op
        (c.derivation hα θ x) := by
  have hsnd : (SmallEtale.toOver C S hS Z.1.toFunctor).map
        ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map g) ≫
        (c.diagram hα).g = ((c.restrict g).diagram hα).g :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c.ε)
      (smallBaseChange_map_snd C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep g)).trans
      (Category.assoc _ _ _))
  have hcond : (SmallEtale.toOver C S hS Z.1.toFunctor).map
        ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map g) ≫
        (c.diagram hα).g =
      ((c.restrict g).diagram hα).g ≫ (SmallEtale.toOver C S hS Y.1).map (𝟙 c.Q) :=
    hsnd.trans ((Category.comp_id _).symm.trans
      (congrArg (((c.restrict g).diagram hα).g ≫ ·)
        ((SmallEtale.toOver C S hS Y.1).map_id c.Q).symm))
  have hunit0 := modulePullbackUnitSection_naturality a (sheafOfDifferentials C S hS q)
    (c.diagram hα) ((c.restrict g).diagram hα)
    ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map g) (𝟙 c.Q) hcond
    ((universalDerivation C S hS q).d x)
  have hid : (sheafOfDifferentials C S hS q).val.map (𝟙 c.Q).op
      ((universalDerivation C S hS q).d x) = (universalDerivation C S hS q).d x :=
    PresheafOfModules.map_id_apply _ _ _
  have hunit := (congrArg (modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q)
    ((c.restrict g).diagram hα)) hid).symm.trans hunit0
  have hm : (smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map
      (c.restrict g).m =
      (smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map g ≫
        (smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m :=
    Functor.map_comp _ _ _
  unfold LiftChart.derivation
  refine (liftActionSheafApp_mk_congr C S hS Z θ hm _).trans ?_
  refine (congrArg (liftActionSheafApp C S hS Z q a θ
    (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map g ≫
      (smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m))) hunit).trans ?_
  exact liftActionSheafApp_naturality C S hS Z θ
    (Over.homMk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map g) rfl :
      Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map g ≫
        (smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m) ⟶
      Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m)) _

/-- **The twisted map is natural in the chart of `X'`.** -/
theorem LiftChart.twist_restrict (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    {T' : SmallEtale C S hS X'.1} (g : T' ⟶ c.T)
    (x : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    (c.restrict g).twist hZ hα θ x =
      (structureRingSheaf C S hS X').obj.map g.op (c.twist hZ hα θ x) := by
  refine ((c.restrict g).twist_apply hZ hα θ x).trans ?_
  refine Eq.trans ?_ (((structureRingSheaf C S hS X').obj.map g.op).hom.map_add _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · change ((forget₂ CommRingCat RingCat).map (Scheme.Γ.map ((BigFppfOver.toScheme C S hS).map
      ((SmallEtale.toOver C S hS X'.1).map g ≫ c.ε)).op)).hom x = _
    rw [Functor.map_comp, op_comp, Functor.map_comp, Functor.map_comp]
    rfl
  · exact (congrArg (conormalChartIncl C S hS Z hZ T') (c.derivation_restrict hα θ g x)).trans
      (conormalChartIncl_naturality C S hS Z hZ g (c.derivation hα θ x))

/-- **The twisted morphism of charts is natural in the chart of `X'`.** -/
theorem LiftChart.map_comp_twistHom (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q) {T' : SmallEtale C S hS X'.1} (g : T' ⟶ c.T) :
    (SmallEtale.toOver C S hS X'.1).map g ≫ c.twistHom hZ hα θ hQ =
      (c.restrict g).twistHom hZ hα θ hQ := by
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj (c.restrict g).Q)) := hQ.1
  refine hom_eq_of_appTop_eq fun x ↦ ?_
  refine Eq.trans ?_ (congrArg (fun f ↦ f.appTop.hom x)
    ((c.restrict g).toScheme_map_twistHom hZ hα θ hQ)).symm
  rw [Functor.map_comp, c.toScheme_map_twistHom hZ hα θ hQ, Scheme.Hom.comp_appTop]
  change ((BigFppfOver.toScheme C S hS).map ((SmallEtale.toOver C S hS X'.1).map g)).appTop.hom
      ((c.twistScheme hZ hα θ).appTop.hom x) = ((c.restrict g).twistScheme hZ hα θ).appTop.hom x
  rw [c.twistScheme_appTop hZ hα θ x, (c.restrict g).twistScheme_appTop hZ hα θ x,
    c.twist_restrict hZ hα θ g x]
  rfl

/-- **The twisted section is natural in the chart of `X'`.** -/
theorem LiftChart.map_comp_twistSection (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q) {T' : SmallEtale C S hS X'.1} (g : T' ⟶ c.T) :
    yoneda.map ((SmallEtale.toOver C S hS X'.1).map g) ≫ c.twistSection hZ hα θ hQ =
      (c.restrict g).twistSection hZ hα θ hQ := by
  unfold LiftChart.twistSection
  rw [← Category.assoc, ← Functor.map_comp, c.map_comp_twistHom hZ hα θ hQ g]
  rfl

/-- **A chart of a lift rerouted through a chart `Q₃ ⟶ Q` of `Y`.** -/
def LiftChart.reroute (c : LiftChart C S hS U' α) {Q₃ : SmallEtale C S hS Y.1} (r : Q₃ ⟶ c.Q)
    (ε₃ : (SmallEtale.toOver C S hS X'.1).obj c.T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q₃)
    (hε₃ : ε₃ ≫ (SmallEtale.toOver C S hS Y.1).map r = c.ε) : LiftChart C S hS U' α where
  T := c.T
  m := c.m
  Q := Q₃
  ε := ε₃
  w := by
    rw [← c.w, ← hε₃, Functor.map_comp, Category.assoc]
    exact congrArg (yoneda.map ε₃ ≫ ·) (CostructuredArrow.w r.hom).symm

/-- **The twisted map is natural in the chart of `Y`.** -/
theorem LiftChart.twist_reroute (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    {Q₃ : SmallEtale C S hS Y.1} (r : Q₃ ⟶ c.Q)
    (ε₃ : (SmallEtale.toOver C S hS X'.1).obj c.T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q₃)
    (hε₃ : ε₃ ≫ (SmallEtale.toOver C S hS Y.1).map r = c.ε)
    (x : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    (c.reroute r ε₃ hε₃).twist hZ hα θ ((structureRingSheaf C S hS Y).obj.map r.op x) =
      c.twist hZ hα θ x := by
  refine ((c.reroute r ε₃ hε₃).twist_apply hZ hα θ _).trans ?_
  refine Eq.trans ?_ (c.twist_apply hZ hα θ x).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · have h := congrArg (fun e ↦ ((forget₂ CommRingCat RingCat).map
      (Scheme.Γ.map ((BigFppfOver.toScheme C S hS).map e).op)).hom x) hε₃
    refine Eq.trans ?_ h
    change _ = ((forget₂ CommRingCat RingCat).map (Scheme.Γ.map
      ((BigFppfOver.toScheme C S hS).map (ε₃ ≫ (SmallEtale.toOver C S hS Y.1).map r)).op)).hom x
    rw [Functor.map_comp, op_comp, Functor.map_comp, Functor.map_comp]
    rfl
  · refine congrArg (conormalChartIncl C S hS Z hZ c.T) ?_
    have hcond : (SmallEtale.toOver C S hS Z.1.toFunctor).map
          (𝟙 (conormalChartDiagram C S hS Z c.T).U) ≫ (c.diagram hα).g =
        ((c.reroute r ε₃ hε₃).diagram hα).g ≫ (SmallEtale.toOver C S hS Y.1).map r := by
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact (congrArg (Z.2.2.rep.snd c.T.1.hom ≫ ·) hε₃.symm).trans (Category.assoc _ _ _).symm
    have hunit := modulePullbackUnitSection_naturality a (sheafOfDifferentials C S hS q)
      (c.diagram hα) ((c.reroute r ε₃ hε₃).diagram hα)
      (𝟙 (conormalChartDiagram C S hS Z c.T).U) r hcond ((universalDerivation C S hS q).d x)
    have hid : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.map
        (𝟙 (conormalChartDiagram C S hS Z c.T).U).op
          (modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q) (c.diagram hα)
            ((universalDerivation C S hS q).d x)) =
        modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q) (c.diagram hα)
          ((universalDerivation C S hS q).d x) :=
      PresheafOfModules.map_id_apply _ _ _
    unfold LiftChart.derivation
    refine (congrArg (fun t ↦ liftActionSheafApp C S hS Z q a θ
      (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m))
      (modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q)
        ((c.reroute r ε₃ hε₃).diagram hα) t))
      ((universalDerivation C S hS q).d_map r.op x)).trans ?_
    exact congrArg (liftActionSheafApp C S hS Z q a θ
      (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m)))
      (hunit.trans hid)

/-- **The twisted section does not depend on rerouting through a chart of `Y`.** -/
theorem LiftChart.twistSection_reroute (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q)
    {Q₃ : SmallEtale C S hS Y.1} (r : Q₃ ⟶ c.Q)
    (ε₃ : (SmallEtale.toOver C S hS X'.1).obj c.T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q₃)
    (hε₃ : ε₃ ≫ (SmallEtale.toOver C S hS Y.1).map r = c.ε)
    (hQ₃ : HasAffineChartDiagram C S hS q (c.reroute r ε₃ hε₃).Q) :
    (c.reroute r ε₃ hε₃).twistSection hZ hα θ hQ₃ = c.twistSection hZ hα θ hQ := by
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj (c.reroute r ε₃ hε₃).Q)) := hQ₃.1
  have hhom : (c.reroute r ε₃ hε₃).twistHom hZ hα θ hQ₃ ≫ (SmallEtale.toOver C S hS Y.1).map r =
      c.twistHom hZ hα θ hQ := by
    refine hom_eq_of_appTop_eq fun x ↦ ?_
    refine Eq.trans ?_ (congrArg (fun f ↦ f.appTop.hom x) (c.toScheme_map_twistHom hZ hα θ hQ)).symm
    rw [Functor.map_comp, (c.reroute r ε₃ hε₃).toScheme_map_twistHom hZ hα θ hQ₃,
      Scheme.Hom.comp_appTop]
    change ((c.reroute r ε₃ hε₃).twistScheme hZ hα θ).appTop.hom
        (((BigFppfOver.toScheme C S hS).map ((SmallEtale.toOver C S hS Y.1).map r)).appTop.hom
          x) = (c.twistScheme hZ hα θ).appTop.hom x
    exact (((c.reroute r ε₃ hε₃).twistScheme_appTop hZ hα θ _).trans
      (c.twist_reroute hZ hα θ r ε₃ hε₃ x)).trans (c.twistScheme_appTop hZ hα θ x).symm
  unfold LiftChart.twistSection
  rw [← hhom]
  refine Eq.trans ?_ (congrArg (· ≫ c.Q.1.hom) (yoneda.map_comp _ _)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (yoneda.map ((c.reroute r ε₃ hε₃).twistHom hZ hα θ hQ₃) ≫ ·)
    (CostructuredArrow.w r.hom).symm

/-! ### Independence of the chart of `Y` -/

/-- The étale chart of the representable `U'` named by a chart `m : T ⟶ U'` of `X'` over `U'`. -/
def liftChartSpaceChart (T : SmallEtale C S hS X'.1) (m : T ⟶ U') :
    SmallEtale C S hS (yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U')) :=
  ⟨CostructuredArrow.mk (yoneda.map ((SmallEtale.toOver C S hS X'.1).map m)),
    presheaf_etale_toOver_map C S hS X'.1 m⟩

/-- An étale chart of the representable `U'`, read as an étale chart of `X'`. -/
def liftChartOfSpaceChart
    (K : SmallEtale C S hS (yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U'))) :
    SmallEtale C S hS X'.1 :=
  ⟨CostructuredArrow.mk (K.1.hom ≫ U'.1.hom),
    haveI := isMultiplicative_presheaf_etale C S hS
    MorphismProperty.comp_mem _ _ _ K.2 U'.2⟩

/-- The morphism of charts of `X'` attached to a morphism of charts of `U'` into the chart named
by `m : T ⟶ U'`. -/
def liftChartOfSpaceChartHom {T : SmallEtale C S hS X'.1} (m : T ⟶ U')
    {K : SmallEtale C S hS (yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U'))}
    (n : K ⟶ liftChartSpaceChart T m) : liftChartOfSpaceChart K ⟶ T :=
  ObjectProperty.homMk (CostructuredArrow.homMk n.hom.left (by
    have hn : yoneda.map n.hom.left ≫ yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) =
        K.1.hom := CostructuredArrow.w n.hom
    change yoneda.map n.hom.left ≫ T.1.hom = K.1.hom ≫ U'.1.hom
    rw [← hn, Category.assoc]
    exact congrArg (yoneda.map n.hom.left ≫ ·) (CostructuredArrow.w m.hom).symm))

/-- **The twisted section does not depend on the chart of `Y`**: two charts of a lift on the same
chart `T ⟶ U'` of `X'` give the same twisted section. The two charts of `Y` are refined, locally on
`T`, to a common affine chart, through which both twisted sections are computed. -/
theorem twistSection_eq_of_liftChart (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (T : SmallEtale C S hS X'.1) (m : T ⟶ U')
    (Q₁ : SmallEtale C S hS Y.1)
    (ε₁ : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q₁)
    (w₁ : yoneda.map ε₁ ≫ Q₁.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ α)
    (hQ₁ : HasAffineChartDiagram C S hS q Q₁)
    (Q₂ : SmallEtale C S hS Y.1)
    (ε₂ : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q₂)
    (w₂ : yoneda.map ε₂ ≫ Q₂.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ α)
    (hQ₂ : HasAffineChartDiagram C S hS q Q₂) :
    (⟨T, m, Q₁, ε₁, w₁⟩ : LiftChart C S hS U' α).twistSection hZ hα θ hQ₁ =
      (⟨T, m, Q₂, ε₂, w₂⟩ : LiftChart C S hS U' α).twistSection hZ hα θ hQ₂ := by
  refine eq_of_pointwise_agreement C S hS T _ _ fun z ↦ ?_
  obtain ⟨K₃, n, V₃, p₁, p₂, q₃, hV₃, hq₃, hc₁, hc₂, z', hz'⟩ :=
    exists_affineChartDiagram_common_chartHom C S hS
      (X := ⟨yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U'),
        isAlgebraicSpace_yoneda C S hS _⟩)
      (ObjectProperty.homMk α) q (liftChartSpaceChart T m) Q₁ Q₂ ε₁ ε₂ w₁ w₂ z
  let g := liftChartOfSpaceChartHom m n
  have hw₃ : yoneda.map q₃ ≫ V₃.1.hom =
      yoneda.map ((SmallEtale.toOver C S hS X'.1).map (g ≫ m)) ≫ α := by
    refine hq₃.trans ?_
    have hn : yoneda.map n.hom.left ≫ yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) =
        K₃.1.hom := CostructuredArrow.w n.hom
    rw [Functor.map_comp, Functor.map_comp, ← hn]
    rfl
  let c₃ : LiftChart C S hS U' α := ⟨liftChartOfSpaceChart K₃, g ≫ m, V₃, q₃, hw₃⟩
  have key : ∀ (Q : SmallEtale C S hS Y.1)
      (ε : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q)
      (w : yoneda.map ε ≫ Q.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ α)
      (hQ : HasAffineChartDiagram C S hS q Q) (pr : V₃ ⟶ Q)
      (hpr : q₃ ≫ (SmallEtale.toOver C S hS Y.1).map pr = n.hom.left ≫ ε),
      yoneda.map ((SmallEtale.toOver C S hS X'.1).map g) ≫
          (⟨T, m, Q, ε, w⟩ : LiftChart C S hS U' α).twistSection hZ hα θ hQ =
        c₃.twistSection hZ hα θ hV₃ := fun Q ε w hQ pr hpr ↦
    ((⟨T, m, Q, ε, w⟩ : LiftChart C S hS U' α).map_comp_twistSection hZ hα θ hQ g).trans
      (((⟨T, m, Q, ε, w⟩ : LiftChart C S hS U' α).restrict g).twistSection_reroute hZ hα θ hQ
        pr q₃ hpr hV₃).symm
  exact ⟨liftChartOfSpaceChart K₃, g,
    (key Q₁ ε₁ w₁ hQ₁ p₁ hc₁).trans (key Q₂ ε₂ w₂ hQ₂ p₂ hc₂).symm, z', hz'⟩

/-! ### The charts of a lift cover -/

variable (q) in
/-- **The sieve of the charts of `α` with an affine chart of `Y` carrying an affine chart diagram
over `q`**: the morphisms `m : T ⟶ U'` through which `α|_T` factors through such a chart. -/
def liftChartSieve (α : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1) :
    Sieve U' where
  arrows T m := ∃ (Q : SmallEtale C S hS Y.1)
    (ε : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q),
    yoneda.map ε ≫ Q.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ α ∧
      HasAffineChartDiagram C S hS q Q
  downward_closed := fun {T _} {m} hm g ↦
    ⟨hm.choose, _, ((⟨T, m, hm.choose, hm.choose_spec.choose,
      hm.choose_spec.choose_spec.1⟩ : LiftChart C S hS U' α).restrict g).w,
      hm.choose_spec.choose_spec.2⟩

variable (q) in
/-- **The charts of a lift cover**: `liftChartSieve` is a covering sieve. Above every point of
`U'` the morphism `α`, read on the representable `U'`, factors locally through an affine chart of
`Y` carrying an affine chart diagram over `q`. -/
theorem liftChartSieve_mem (α : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1) :
    liftChartSieve (q := q) α ∈ SmallEtale.topology C S hS X'.1 U' := by
  refine (SmallEtale.mem_topology_iff_exists_mem_range C S hS X'.1 _).2 fun z ↦ ?_
  obtain ⟨K₃, n, ⟨V, q', hq', hV⟩, z', hz'⟩ := exists_hasChartHomToAffineChartDiagram C S hS
    (X := ⟨yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U'), isAlgebraicSpace_yoneda C S hS _⟩)
    (ObjectProperty.homMk α) q (liftChartSpaceChart U' (𝟙 U')) z
  let g := liftChartOfSpaceChartHom (𝟙 U') n
  have h1 : yoneda.map ((SmallEtale.toOver C S hS X'.1).map (𝟙 U')) = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hK : K₃.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map g) :=
    (CostructuredArrow.w n.hom).symm.trans
      ((congrArg (yoneda.map n.hom.left ≫ ·) h1).trans (Category.comp_id _))
  exact ⟨liftChartOfSpaceChart K₃, g, ⟨V, q', hq'.trans (congrArg (· ≫ α) hK), hV⟩, z', hz'⟩

/-! ### Comparing twisted sections -/

/-- **Two charts on the same `T` and `Q` with the same morphism `ε` up to their twisted maps give
the same twisted section**: a morphism into the affine scheme `Q` is determined by its map of
regular functions. -/
theorem LiftChart.twistSection_eq_of_twist_eq (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (hQ : HasAffineChartDiagram C S hS q c.Q)
    {U'' : SmallEtale C S hS X'.1}
    {α' : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U'') ⟶ Y.1}
    (m' : c.T ⟶ U'')
    (ε' : (SmallEtale.toOver C S hS X'.1).obj c.T ⟶ (SmallEtale.toOver C S hS Y.1).obj c.Q)
    (w' : yoneda.map ε' ≫ c.Q.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m') ≫ α')
    (hα' : IsChartLift C S hS p q a.hom U'' α')
    (θ' : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U'')))
    (hQ' : HasAffineChartDiagram C S hS q
      (⟨c.T, m', c.Q, ε', w'⟩ : LiftChart C S hS U'' α').Q)
    (h : ∀ x, (⟨c.T, m', c.Q, ε', w'⟩ : LiftChart C S hS U'' α').twist hZ hα' θ' x =
      c.twist hZ hα θ x) :
    (⟨c.T, m', c.Q, ε', w'⟩ : LiftChart C S hS U'' α').twistSection hZ hα' θ' hQ' =
      c.twistSection hZ hα θ hQ := by
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
  have hhom : (⟨c.T, m', c.Q, ε', w'⟩ : LiftChart C S hS U'' α').twistHom hZ hα' θ' hQ' =
      c.twistHom hZ hα θ hQ := by
    refine hom_eq_of_appTop_eq fun x ↦ ?_
    rw [(⟨c.T, m', c.Q, ε', w'⟩ : LiftChart C S hS U'' α').toScheme_map_twistHom hZ hα' θ' hQ',
      c.toScheme_map_twistHom hZ hα θ hQ]
    exact (((⟨c.T, m', c.Q, ε', w'⟩ : LiftChart C S hS U'' α').twistScheme_appTop hZ hα' θ'
      x).trans (h x)).trans (c.twistScheme_appTop hZ hα θ x).symm
  unfold LiftChart.twistSection
  rw [hhom]

/-- **The twisted section of the zero section is the original lift.** -/
theorem LiftChart.twistSection_zero (c : LiftChart C S hS U' α)
    (hα : IsChartLift C S hS p q a.hom U' α) (hQ : HasAffineChartDiagram C S hS q c.Q) :
    c.twistSection hZ hα 0 hQ = yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ α := by
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
  have hhom : c.twistHom hZ hα 0 hQ = c.ε := by
    refine hom_eq_of_appTop_eq fun x ↦ ?_
    rw [c.toScheme_map_twistHom hZ hα 0 hQ]
    refine ((c.twistScheme_appTop hZ hα 0 x).trans (c.twist_apply hZ hα 0 x)).trans ?_
    refine Eq.trans (congrArg (fun z ↦ c.pullback x + z) ?_) (add_zero _)
    exact liftChart_map_zero_of_add _ (conormalChartIncl_add C S hS Z hZ c.T)
  unfold LiftChart.twistSection
  rw [hhom]
  exact c.w

end AlgebraicGeometry.Space

end
