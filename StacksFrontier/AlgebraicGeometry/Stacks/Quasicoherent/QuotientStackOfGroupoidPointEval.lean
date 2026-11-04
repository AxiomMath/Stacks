module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackOfGroupoidModuleIso

/-!
# Sections of the module on `[U/R]` attached to `(𝒢, α)` at affine points

Let `ℱ` be the quasi-coherent module on `[U/R]` built from a quasi-coherent module `(𝒢, α)` on a
groupoid `(U, R, s, t, c)` in algebraic spaces. At an affine point `(T, a)` of `[U/_pR]` the
sections of `ℱ` are `Γ(T, a^*𝒢)` by construction; this file records that identification and its
naturality along arrows of `[U/_pR]`, the restriction maps of `Γ(T, a^*𝒢)` being those of the
proof of Stacks 06WT.

## Main definitions

* `AlgebraicGeometry.Stack.pointEval`: `ℱ(x(T, a)) ≅ Γ(T, a^*𝒢)` at an affine point.

## Main results

* `AlgebraicGeometry.Stack.pointEval_map`: naturality along arrows between affine points.
* `AlgebraicGeometry.Stack.pointEval_map_quotientStackModuleOfGroupoidHom`: the composite with
  `𝒢 ⟶ x^*ℱ|_{U_étale}` over an affine chart `W` is restriction of the chart section along
  `u_W`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- **The sections of `ℱ` at an affine point `(T, a)` are `Γ(T, a^*𝒢)`.** -/
def pointEval (X : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
    (z : (quotientStackModuleOfGroupoid G M).val.obj
      (op ((pointwiseToQuotientStack G).obj X.obj))) :
    pointSections G M X.obj :=
  (pointwiseModuleAffineIso G M).hom.val.app (op X)
    (((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).hom.val.app (op X.obj) z)

/-- The map `ℱ(x(T, a)) → Γ(T, a^*𝒢)` at an affine point is injective. -/
theorem injective_pointEval (X : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p) :
    Function.Injective (pointEval G M X) := by
  refine Function.Injective.comp ?_ ?_
  · exact (Stacks.SheafOfModules.bijective_inv_val_app _
      (pointwiseModuleAffineIso G M).symm _).1
  · exact (Stacks.SheafOfModules.bijective_inv_val_app _
      ((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).symm _).1

/-- **Naturality of `ℱ(x(T, a)) ≅ Γ(T, a^*𝒢)`** along an arrow between affine points. -/
theorem pointEval_map {X Y : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p} (m : X ⟶ Y)
    (z : (quotientStackModuleOfGroupoid G M).val.obj
      (op ((pointwiseToQuotientStack G).obj Y.obj))) :
    pointEval G M X ((quotientStackModuleOfGroupoid G M).val.map
        ((pointwiseToQuotientStack G).map m.hom).op z) =
      pointSectionRestrict G M m.hom (pointEval G M Y z) := by
  have h1 := PresheafOfModules.naturality_apply
    ((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).hom.val m.hom.op z
  have h2 := PresheafOfModules.naturality_apply (pointwiseModuleAffineIso G M).hom.val m.op
    (((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).hom.val.app (op Y.obj) z)
  have hp : (pointPresheaf G M).map m.op (pointEval G M Y z) =
      pointSectionRestrict G M m.hom (pointEval G M Y z) :=
    (Stacks.PresheafOfModules.mkOfSemilinear_map_apply (fun x => pointModule G M x.unop)
      (fun f => affinePointSemilinear G M f) (affinePointSemilinear_id G M)
      (fun f g s => affinePointSemilinear_comp G M f g s) m.op (pointEval G M Y z)).trans
    (affinePointSemilinear_apply G M m.op (pointEval G M Y z))
  unfold pointEval
  refine (congrArg ((pointwiseModuleAffineIso G M).hom.val.app (op X)) h1).trans ?_
  exact h2.trans hp

/-- At the point of an affine chart `W`, the identification `ℱ(x(W)) ≅ Γ(W, 𝒢)` sends the image
of a section of `𝒢` over `W` to the corresponding chart section. -/
theorem pointEval_chartModuleMap (A : Space.AffineEtale C S hS G.objects.obj)
    (x : M.F.obj.val.obj (op A.obj)) :
    pointEval G M (affineChartPoint G A) (chartModuleMap G M A x) =
      chartPointSection G M A.obj x := by
  have e1 := congrArg (fun φ => φ.val.app (op (chartPoint G A.obj))
      ((pointwiseModuleAffineIso G M).inv.val.app (op (affineChartPoint G A))
        (chartPointSection G M A.obj x)))
    ((pointwiseRestriction G).objObjPreimageIso (pointwiseModule G M)).inv_hom_id
  have e2 := congrArg (fun φ => φ.val.app (op (affineChartPoint G A))
      (chartPointSection G M A.obj x)) (pointwiseModuleAffineIso G M).inv_hom_id
  exact (congrArg ((pointwiseModuleAffineIso G M).hom.val.app (op (affineChartPoint G A)))
    e1).trans e2

/-- **The composite of `𝒢 ⟶ x^*ℱ|_{U_étale}` with restriction along an arrow** from an affine
point `(T, a)` to the point of an affine chart `W`, read in `Γ(T, a^*𝒢)`: the restriction of the
chart section along `u_W`. -/
theorem pointEval_map_quotientStackModuleOfGroupoidHom
    (X : AffineCategory C S hS (presheafOfGroupoids
      (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p)
    (A : Space.AffineEtale C S hS G.objects.obj) (m : X.obj ⟶ chartPoint G A.obj)
    (x : M.F.obj.val.obj (op A.obj)) :
    pointEval G M X ((quotientStackModuleOfGroupoid G M).val.map
        ((pointwiseToQuotientStack G).map m).op
        ((quotientStackModuleOfGroupoidHom G M).val.app (op A.obj) x)) =
      pointSectionRestrict G M m (chartPointSection G M A.obj x) := by
  have h := quotientStackModuleOfGroupoidHom_app G M A x
  have e := pointEval_map G M (X := X) (Y := affineChartPoint G A) (ObjectProperty.homMk m)
    (chartModuleMap G M A x)
  rw [pointEval_chartModuleMap] at e
  refine Eq.trans ?_ e
  exact congrArg (fun z => pointEval G M X ((quotientStackModuleOfGroupoid G M).val.map
    ((pointwiseToQuotientStack G).map m).op z)) h

end AlgebraicGeometry.Stack

end
