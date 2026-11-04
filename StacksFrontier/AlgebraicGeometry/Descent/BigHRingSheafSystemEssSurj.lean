module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemDescentIsoMk
public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemGlue
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.ChartHom

/-!
# Effective descent along a family of opens, for a system of sheaves of rings
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {𝓡 : RingSheafSystem B S hS}
  {U : BigHOver B S hS} {ι : Type u} {W : ι → ((toScheme B S hS).obj U).Opens}
  {D : 𝓡.modulePseudofunctor.DescentData (fun i => opensι B S hS (W i))}
  (h𝓡 : 𝓡.UnitBijective)

/-- **The comparison of the glued module with the `i`-th pushed-forward member**, as a morphism
of sheaves of modules on the ambient object. -/
def chartHom (i : ι) : (glueData D h𝓡).glued ⟶ member D i :=
  Stacks.SheafOfModules.OModuleGlueData.chartHom (fun i => member D i)
    (fun i j _ hi hj => glueTrans D h𝓡 i j hi hj)
    (fun i j _ _ hi hj hV' s => glueTrans_map h𝓡 i j hi hj hV' s)
    (fun i j k _ hi hj hk s => glueTrans_trans h𝓡 i j k hi hj hk s)
    (fun i T => 𝓡.bijective_push_map_inf (dobj D i) T) i

/-- On an open `T` contained in the `i`-th member, the chart comparison `chartHom h𝓡 i` acts as
the `i`-th chart isomorphism of the glued module. -/
lemma chartHom_app_of_le (i : ι) {T : ((toScheme B S hS).obj U).Opens} (hT : T ≤ W i)
    (s : ToType ((glueData D h𝓡).glued.val.obj (op T))) :
    (chartHom h𝓡 i).val.app (op T) s = ((glueData D h𝓡).chartIso i hT).hom s :=
  Stacks.SheafOfModules.OModuleGlueData.chartHom_app_of_le _ _ _ _ _ i hT s

/-- On an open `T` contained in the `i`-th member, the component of the chart comparison
`chartHom h𝓡 i` at `T` is bijective. -/
lemma bijective_chartHom_app (i : ι) {T : ((toScheme B S hS).obj U).Opens} (hT : T ≤ W i) :
    Function.Bijective ((chartHom h𝓡 (D := D) i).val.app (op T)) := by
  have e : ⇑(ConcreteCategory.hom ((chartHom h𝓡 (D := D) i).val.app (op T))) =
      ⇑(ConcreteCategory.hom ((glueData D h𝓡).chartIso i hT).hom) :=
    funext (chartHom_app_of_le h𝓡 i hT)
  rw [e]
  exact ConcreteCategory.bijective_of_isIso _

/-- **The chart comparisons of the glued module are compatible with the gluing morphisms** over
the intersection of two members. -/
lemma chartHom_comp_glueMap (i j : ι) :
    chartHom h𝓡 i ≫ glueMap D i j (inf_le_left : W i ⊓ W j ≤ W i) inf_le_right =
      chartHom h𝓡 j ≫ glueMap D j j (inf_le_right : W i ⊓ W j ≤ W j) inf_le_right := by
  refine 𝓡.hom_ext_push _ _ fun T hT => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have hi : T ≤ W i := hT.trans inf_le_left
  have hj : T ≤ W j := hT.trans inf_le_right
  have key : (glueMap D i j (inf_le_left : W i ⊓ W j ≤ W i) inf_le_right).val.app (op T)
        ((chartHom h𝓡 i).val.app (op T) x) =
      (glueMap D j j (inf_le_right : W i ⊓ W j ≤ W j) inf_le_right).val.app (op T)
        ((chartHom h𝓡 j).val.app (op T) x) := by
    rw [chartHom_app_of_le h𝓡 i hi, chartHom_app_of_le h𝓡 j hj,
      ← (glueData D h𝓡).trans_chartIso_hom i j hi hj x]
    exact (glueMap_transP h𝓡 i j inf_le_left inf_le_right T hT _).symm
  exact (congrFun (coe_app_comp _ _ (op T)) x).trans
    (key.trans (congrFun (coe_app_comp _ _ (op T)) x).symm)

/-- The comparison of the restriction of the glued module to the `i`-th member with the `i`-th
component of the descent datum: the transpose of
`AlgebraicGeometry.BigHOver.RingSheafSystem.chartHom`. -/
def chartFlat (i : ι) :
    (𝓡.pull (opensι B S hS (W i)).op).obj (glueData D h𝓡).glued ⟶ dobj D i :=
  ((𝓡.adj (opensι B S hS (W i))).homEquiv _ _).symm (chartHom h𝓡 i)

/-- The adjunction transpose of `chartFlat h𝓡 i` is `chartHom h𝓡 i`. -/
lemma homEquiv_chartFlat (i : ι) :
    (𝓡.adj (opensι B S hS (W i))).homEquiv _ _ (chartFlat h𝓡 (D := D) i) = chartHom h𝓡 i :=
  Equiv.apply_symm_apply _ _

/-- The transposed chart comparison `chartFlat h𝓡 i` is an isomorphism. -/
instance isIso_chartFlat (i : ι) : IsIso (chartFlat h𝓡 (D := D) i) := by
  refine 𝓡.isIso_of_bijective_push_app _ fun T hT => ?_
  have e := coe_app_congr (homEquiv_chartFlat h𝓡 (D := D) i) (op T)
  rw [Adjunction.homEquiv_unit, coe_app_comp] at e
  have hb := bijective_chartHom_app h𝓡 (D := D) i hT
  rw [← e] at hb
  exact (Function.Bijective.of_comp_iff _ (h𝓡 U (W i) _ T hT)).mp hb

/-- **The transposes of the chart comparisons are compatible with the gluing morphisms** over the
intersection of two members. -/
lemma chartFlat_compatible (i j : ι) :
    (𝓡.adj (opensι B S hS (W i))).homEquiv _ _ (chartFlat h𝓡 (D := D) i) ≫
        𝓡.etaG (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i)) (opensι B S hS (W i))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) (dobj D i) ≫
        (𝓡.push (opensι B S hS (W i ⊓ W j))).map (dhom D i j inf_le_left inf_le_right) =
      (𝓡.adj (opensι B S hS (W j))).homEquiv _ _ (chartFlat h𝓡 (D := D) j) ≫
        𝓡.etaG (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j)) (opensι B S hS (W j))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) (dobj D j) := by
  have h := chartHom_comp_glueMap h𝓡 (D := D) i j
  rw [glueMap_self, glueMap] at h
  rwa [homEquiv_chartFlat, homEquiv_chartFlat]

variable (D) in
/-- **The canonical descent datum of the glued module is the given descent datum.** -/
def gluedDescentDataIso :
    (𝓡.modulePseudofunctor.toDescentData (fun i => opensι B S hS (W i))).obj
      (glueData D h𝓡).glued ≅ D :=
  𝓡.toDescentDataIsoOfHomEquiv D (fun i j => opensChosenPullback B S hS (W i) (W j))
    (glueData D h𝓡).glued (fun i => @asIso _ _ _ _ (chartFlat h𝓡 (D := D) i)
      (isIso_chartFlat h𝓡 i))
    (fun i j => chartFlat_compatible h𝓡 i j)

variable (W) in
include h𝓡 in
/-- **Descent of modules of a system of sheaves of rings with the restriction property along a
family of opens is effective.** -/
theorem essSurj_toDescentData_opens :
    (𝓡.modulePseudofunctor.toDescentData (fun i => opensι B S hS (W i))).EssSurj where
  mem_essImage D := ⟨(glueData D h𝓡).glued, ⟨gluedDescentDataIso D h𝓡⟩⟩

end AlgebraicGeometry.BigHOver.RingSheafSystem
