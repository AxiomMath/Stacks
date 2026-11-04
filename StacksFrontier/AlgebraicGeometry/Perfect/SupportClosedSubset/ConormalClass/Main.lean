module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ChartExists

/-!
# The canonical map `⋀^c(𝒞_{Z/X})^∨ ⊗_{𝒪_Z} i^*ℱ ⟶ ℋ^c_Z(ℱ)` (Stacks 0G7T)

Let `X` be a scheme and `i : Z ⟶ X` a closed immersion of finite presentation whose conormal
sheaf `𝒞_{Z/X}` is finite locally free of rank `c`.  For every `𝒪_X`-module `ℱ` there is a
canonical map

`c : ⋀^c(𝒞_{Z/X})^∨ ⊗_{𝒪_Z} i^*ℱ ⟶ ℋ^c_Z(ℱ)`,

functorial in `ℱ`, read on `X` (through the direct image along `i`, which is fully faithful).
Over an open `W ⊆ X` on which `f₁, …, f_c` generate the ideal of `Z`, it sends `λ ⊗ s` to the
class `c_{f₁, …, f_c}(λ(f₁ ∧ ⋯ ∧ f_c) s)` of Stacks 0G7Q, where `f₁ ∧ ⋯ ∧ f_c` is the wedge of
the conormal classes; by Stacks 0G7S these local maps do not depend on the generators, and they
glue.

## Main definitions

* `Stacks.Perfect.ConormalClass.conormalTwistClass`: the canonical map, as a natural
  transformation of functors of `ℱ`.

## Main results

* `Stacks.Perfect.ConormalClass.conormalTwistClass_app_tmul`: its value on `λ ⊗ s` over a chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.SheafOfModules.OnSpace (dualSheaf dualValue dualEval tensorObjTmul)
open Stacks.Perfect.SupportedFraction (supportCohomologySheaf supportCohomologySheafMap
  supportCohomologySheafFunctor)

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] modulesMonoidal

/-- The value of a local functional at the part of its open inside `V` is its value on the whole
open, read on the part inside `V`. -/
theorem map_dualValue_interOver {Y : Scheme.{u}} (L : Y.Modules) {V P : Y.Opens} (hP : P ≤ V)
    (ω : Γ(L, V)) (lam : (dualSheaf Y.toRingedSpace L).val.obj (op P)) :
    Y.presheaf.map (homOfLE (le_image_preimage hP)).op
        (dualValue Y.toRingedSpace L lam (op (interOver V P))
          (L.presheaf.map (homOfLE (V.ι_image_le _)).op ω)) =
      dualEval Y.toRingedSpace L lam (L.presheaf.map (homOfLE hP).op ω) := by
  let φ : Over.mk (𝟙 P) ⟶ interOver V P :=
    Over.homMk (homOfLE (le_image_preimage hP)) (Subsingleton.elim _ _)
  have hval := congrArg (fun q => q.hom (L.presheaf.map (homOfLE (V.ι_image_le _)).op ω))
    (lam.naturality φ.op)
  refine hval.symm.trans ?_
  exact congrArg (lam.app (op (Over.mk (𝟙 P)))).hom (modules_map_map_eq L _ _ _ (𝟙 _) ω |>.trans
    (by rw [op_id, L.presheaf.map_id]; rfl))

section Main

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] {c : ℕ} (F : X.Modules)

/-- The evaluation of a chart on a local pure tensor `λ ⊗ g` is `λ(ω_f) g`. -/
theorem chartEvalSec_tmul {W : X.Opens} {f : Fin c → Γ(X, W)}
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f) (U : X.Opens) (hU : U ≤ W)
    (lam : (dualSheaf Z.toRingedSpace (line i c)).val.obj (op (i ⁻¹ᵁ U)))
    (g : Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ U)) :
    chartEvalSec F hgen U hU (tensorObjTmul Z.toRingedSpace (dualModule (line i c))
        ((Scheme.Modules.pullback i).obj F) (op (i ⁻¹ᵁ U)) lam g) =
      (dualEval Z.toRingedSpace (line i c) lam
        ((line i c).presheaf.map (homOfLE (i.preimage_mono hU)).op (chartWedge hgen)) • g :
          Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ U)) := by
  have e := evalAt_tmul (line i c) ((Scheme.Modules.pullback i).obj F) (i ⁻¹ᵁ W) (chartWedge hgen)
    (i ⁻¹ᵁ U) lam g
  refine (congrArg (((Scheme.Modules.pullback i).obj F).presheaf.map
    (homOfLE (le_image_preimage (i.preimage_mono hU))).op).hom e).trans ?_
  refine (Scheme.Modules.map_smul ((Scheme.Modules.pullback i).obj F) _ _ _).trans ?_
  exact congrArg₂ (fun (a : Γ(Z, i ⁻¹ᵁ U)) (b : Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ U)) =>
      a • b)
    (map_dualValue_interOver (line i c) (i.preimage_mono hU) (chartWedge hgen) lam)
    (modules_map_map_self ((Scheme.Modules.pullback i).obj F) _ _ g)

variable [LocallyOfFinitePresentation i] (c)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormal i) c]

/-- Every point of the closed subset `zeroLocus i` lies in the open of some chart. -/
theorem charts_cover : ∀ x ∈ zeroLocus i, ∃ a : ChartIndex i c, x ∈ a.1.1 := by
  rintro _ ⟨z, rfl⟩
  exact exists_chart i c z

/-- The canonical map `⋀^c(𝒞_{Z/X})^∨ ⊗_{𝒪_Z} i^*ℱ ⟶ ℋ^c_Z(ℱ)`, functorial in `ℱ`, for a closed
immersion `i : Z ⟶ X` of finite presentation whose conormal sheaf `𝒞_{Z/X}` is finite locally
free of rank `c`.  The source is `i_*` of the tensor product over `𝒪_Z` (Stacks 01CA) of the dual
`SheafHom(⋀^c 𝒞_{Z/X}, 𝒪_Z)` of the `c`-th exterior power of the conormal sheaf with `i^*ℱ`, and
the target is `ℋ^c_Z(ℱ)` read on `X`; the direct image along `i` is fully faithful, so this is the
map of `𝒪_X|_Z`-modules of the statement.  On a chart it is the map of
`conormalTwistClass_app_tmul`. -/
@[stacks 0G7T "the canonical map, as a natural transformation of functors of the module F; \
its value on a chart is conormalTwistClass_app_tmul"]
def conormalTwistClass :
    twistFunctor i c ⟶ supportCohomologySheafFunctor (isClosed_zeroLocus i) (c : ℤ) where
  app F := twistMap i c F (charts_cover i c)
  naturality _ _ φ := twistMap_natural i c (charts_cover i c) φ

/-- The value of `conormalTwistClass` on a chart.  Let `W ⊆ X` be an open on which
`f₁, …, f_c` generate the ideal sheaf of `Z`, let `U ⊆ W` be open, `λ` a local section of
`(⋀^c 𝒞_{Z/X})^∨` over `Z ∩ U`, `s` a local section of `ℱ` over `U` and `r` a function on `U`
restricting on `Z ∩ U` to `λ(f₁ ∧ ⋯ ∧ f_c)`.  Then `c(λ ⊗ s)`, read in `ℋ^c_{T}(ℱ)` for the
closed subset `T ⊇ Z` of the chart (over `W` the change of support `ℋ^c_Z ⟶ ℋ^c_T` is an
isomorphism), is the class `c_{f₁, …, f_c}(r s)` of the fraction `r s / (f₁ ⋯ f_c)` of
Stacks 0G7Q.  In particular the map does not depend on the chart. -/
@[stacks 0G7T "canonicity: on every chart the map is the twisted fraction class of Stacks 0G7Q, \
λ ⊗ s ↦ c_{f₁, …, f_c}(λ(f₁ ∧ ⋯ ∧ f_c) s)"]
theorem conormalTwistClass_app_tmul {W : X.Opens} {f : Fin c → Γ(X, W)}
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f) (U : X.Opens) (hU : U ≤ W)
    (lam : (dualSheaf Z.toRingedSpace (line i c)).val.obj (op (i ⁻¹ᵁ U))) (s : Γ(F, U))
    (r : Γ(X, U))
    (hr : (i.app U).hom r = dualEval Z.toRingedSpace (line i c) lam
      ((line i c).presheaf.map (homOfLE (i.preimage_mono hU)).op
        (wedge i f (app_chart_eq_zero W f hgen)))) :
    (supportChangeH (isClosed_zeroLocus i) (isClosed_chartSupport W (chartEq W f))
        (zeroLocus_subset_chartSupport W f hgen) F (c : ℤ)).app U
        (((conormalTwistClass i c).app F).app U
          (tensorObjTmul Z.toRingedSpace (dualModule (line i c)) ((Scheme.Modules.pullback i).obj F)
            (op (i ⁻¹ᵁ U)) lam
            (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app U s))) =
      (topClass W F (isClosed_chartSupport W (chartEq W f)) (chartEq W f) subset_rfl).app U
        (r • s) := by
  refine (congrArg ((chartTheta F hgen).app U)
    (twistMap_app_chart i c F (charts_cover i c) hgen U hU _)).trans ?_
  refine (chartTheta_chartSec F hgen U hU _).trans ?_
  refine (congrArg (chartDescSec F hgen U hU) (chartEvalSec_tmul i F hgen U hU lam _)).trans ?_
  refine Eq.trans ?_ (chartDescSec_unit F hgen U hU (r • s))
  refine congrArg (chartDescSec F hgen U hU) ?_
  refine (congrArg (fun a : Γ(Z, i ⁻¹ᵁ U) => a •
    (show Γ((Scheme.Modules.pullback i).obj F, i ⁻¹ᵁ U) from
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app U s)) hr.symm).trans ?_
  exact (Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F)
    r s).symm

end Main

end Stacks.Perfect.ConormalClass
