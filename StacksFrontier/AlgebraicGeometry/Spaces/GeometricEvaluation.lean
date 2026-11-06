module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleNeighborhoodBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence

/-!
# Evaluation of germs at a geometric point of an algebraic space

A geometric point `x̄` of a presheaf `F` on the big fppf site of `S` is a section of `F` over the
spectrum of an algebraically closed field `Ω`.  A regular function on a small étale
neighbourhood of `x̄` can be pulled back along the chosen lift of `x̄` to that neighbourhood and
so has a *value* in `Ω`; the values of a function and of its restriction to a refinement agree,
so this assignment factors through the étale local ring `𝒪_{F, x̄}`.

This is `AlgebraicGeometry.Space.geometricEval`, the evaluation at `x̄`. It is compatible with
the homomorphisms of étale local rings induced by a morphism `f : F ⟶ H`: evaluating a germ over
`H` at `f(x̄)` is the same as evaluating its image over `F` at `x̄`.

## Main definitions

* `AlgebraicGeometry.Space.geometricEval`: the evaluation of germs at a geometric point.

## Main results

* `AlgebraicGeometry.Space.geometricEval_etaleLocalRingGerm`: its value on the germ of a regular
  function on a small étale neighbourhood.
* `AlgebraicGeometry.Space.geometricEval_isEtaleLocalRingMap_germ`: the triangle of evaluations
  over a morphism of algebraic spaces commutes on the germ of a regular function over any
  commuting square of pointed charts.

## References

* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The value in the field of a geometric point of a global regular function on the chart of a
small étale neighbourhood: pull the function back along the chosen lift and read it in the
field through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
@[sga "3 I 4.3.3.1" "special case"]
def geometricEvalApp {x : GeometricPoint B S hS F} (N : SmallEtaleNeighborhood x) :
    ((structurePresheaf B S hS F).obj (op N.chart)) →+* x.val.carrier :=
  (Scheme.ΓSpecIso (CommRingCat.of x.val.carrier)).hom.hom.comp
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map N.point).op).hom

/-- Taking global sections of the schemes underlying a composite of morphisms of the big fppf site
over `S` gives the composite of the maps on global sections, in the opposite order. -/
private theorem Γ_map_toScheme_comp {X Y Z : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ Z) (h : a ≫ b = c) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map b).op) ≫
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map a).op) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map c).op := by
  rw [← Scheme.Γ.map_comp, ← op_comp, ← (BigFppfOver.toScheme B S hS).map_comp, h]

/-- Values at a geometric point are unchanged by restriction to a refinement of the
neighbourhood. -/
theorem geometricEvalApp_comp {x : GeometricPoint B S hS F} {N M : SmallEtaleNeighborhood x}
    (k : M ⟶ N) :
    (geometricEvalApp B S hS F M).comp
        ((structurePresheaf B S hS F).map k.hom.op).hom =
      geometricEvalApp B S hS F N := by
  have hG := Γ_map_toScheme_comp B S hS _ _ _ k.point_comp
  ext a
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of x.val.carrier)).hom.hom
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hG) a)

/-- The cocone on the diagram of sections over the small étale neighbourhoods of a geometric
point whose component at a neighbourhood is evaluation of a global function at the point. -/
def geometricEvalCocone (x : GeometricPoint B S hS F) :
    Cocone (SmallEtaleNeighborhood.sections (x := x) (liftedStructurePresheaf B S hS F)) where
  pt := CommRingCat.of (ULift.{u + 1} x.val.carrier)
  ι :=
    { app := fun N => CommRingCat.ofHom (geometricEvalApp B S hS F N.unop).ulift
      naturality := fun N M k => by
        apply CommRingCat.hom_ext
        refine RingHom.ext fun a => ?_
        refine ULift.ext ?_
        exact DFunLike.congr_fun (geometricEvalApp_comp B S hS F k.unop) a.down }

/-- **Evaluation of germs at a geometric point.**  The homomorphism from the étale local ring of
`F` at `x̄` to the field of `x̄` sending the germ of a regular function on a small étale
neighbourhood to its value at the chosen lift of `x̄`. -/
@[stacks 04HX "the geometric evaluation map, for an algebraic space"]
def geometricEval (x : GeometricPoint B S hS F) :
    ↥(etaleLocalRing B S hS F x) →+* x.val.carrier :=
  ULift.ringEquiv.toRingHom.comp
    (colimit.desc _ (geometricEvalCocone B S hS F x)).hom

/-- Evaluation at a geometric point sends the germ of a regular function on a small étale
neighbourhood to its value at the chosen lift of the point. -/
theorem geometricEval_etaleLocalRingGerm (x : GeometricPoint B S hS F)
    (N : SmallEtaleNeighborhood x)
    (a : (structurePresheaf B S hS F).obj (op N.chart)) :
    geometricEval B S hS F x (etaleLocalRingGerm B S hS F x (op N) a) =
      geometricEvalApp B S hS F N a := by
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (colimit.ι_desc (geometricEvalCocone B S hS F x) (op N))) (ULift.up a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  show ULift.ringEquiv ((colimit.desc _ (geometricEvalCocone B S hS F x)).hom
    ((colimit.ι (SmallEtaleNeighborhood.sections
      (liftedStructurePresheaf B S hS F)) (op N)).hom (ULift.up a))) = _
  rw [h]
  rfl

/-- **The triangle of geometric evaluations commutes on a germ.** Let `φ` be a homomorphism of
étale local rings induced by `f : F ⟶ H` at `x̄`, in the sense of
`AlgebraicGeometry.Space.IsEtaleLocalRingMap`, and let a commuting square of pointed étale charts
over `f` be given. Then evaluating the germ at `f(x̄)` of a regular function on the chart of `H`
is the same as evaluating its image under `φ` at `x̄`. -/
theorem geometricEval_isEtaleLocalRingMap_germ {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (x : GeometricPoint B S hS F)
    {φ : ↥(etaleLocalRing B S hS H (geometricPointMap f x)) →+* ↥(etaleLocalRing B S hS F x)}
    (hφ : IsEtaleLocalRingMap f x φ)
    (U : SmallEtaleNeighborhood x) (V : SmallEtaleNeighborhood (geometricPointMap f x))
    (g : U.chart.obj.left ⟶ V.chart.obj.left)
    (hover : U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom)
    (hpoint : U.point ≫ g = V.point)
    (a : (structurePresheaf B S hS H).obj (op V.chart)) :
    geometricEval B S hS F x
        (φ (etaleLocalRingGerm B S hS H (geometricPointMap f x) (op V) a)) =
      geometricEval B S hS H (geometricPointMap f x)
        (etaleLocalRingGerm B S hS H (geometricPointMap f x) (op V) a) := by
  have h : φ (etaleLocalRingGerm B S hS H (geometricPointMap f x) (op V) a) =
      etaleLocalRingGerm B S hS F x (op U)
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom a) :=
    (DFunLike.congr_fun (hφ U V g hover hpoint) a).symm
  have hG := Γ_map_toScheme_comp B S hS _ _ _ hpoint
  rw [h, geometricEval_etaleLocalRingGerm]
  exact (geometricEval_etaleLocalRingGerm B S hS F x U _).trans
    (congrArg (Scheme.ΓSpecIso (CommRingCat.of x.val.carrier)).hom.hom
      (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hG) a))

end AlgebraicGeometry.Space

end
