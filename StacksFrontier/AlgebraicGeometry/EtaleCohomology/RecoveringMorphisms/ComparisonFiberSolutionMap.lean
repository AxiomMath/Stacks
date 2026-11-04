module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ComparisonCoordAdjunct
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ComparisonFiberCoordinates
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.EtaleCoefficientCompatibility

/-!
# The fibre of the comparison sheaf map is the solution-set map

Let `g` be a morphism of the small étale ringed topoi of `X` and `Y`, `e` an isomorphism between
the fibre functor at a geometric point `ȳ` of `Y` and `g⁻¹` followed by the fibre functor at a
geometric point `x̄` of `X`, and `φ` the induced map of étale local rings
(`AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso`). For an affine étale chart `V` of `Y` with
a standard presentation by polynomials `P`, the fibre at `x̄` of the comparison
`g⁻¹h_V ⟶ h_{X ×_Y V}` (`AlgebraicGeometry.comparisonSheafHom`) is, on the solutions of `P` in the
étale local rings, postcomposition with `φ`.

## Main results

* `AlgebraicGeometry.sheafFiber_map_yonedaEquiv_symm`: the germ of a global function on a chart is
  the fibre of its Yoneda morphism at the germ of the identity.
* `AlgebraicGeometry.yonedaIso_symm_eq_toPresheafFiber_id`: the lift of a geometric point named by
  a fibre element of a representable sheaf is the one whose germ of the identity it is.
* `AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso_toPresheafFiber_of_type`: `φ` on a germ,
  given the computation on sheaves of sets.
* `AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions_comparisonSheafHom` and
  `AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions_comparisonSheafHom_apply`: the
  solution named by the lift of `x̄` which the comparison assigns to a lift `u` of `ȳ` is `φ`
  applied coordinatewise to the solution named by `u`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.StalkInverseImage
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.StalkTransport

universe u

namespace AlgebraicGeometry

/-- **The germ of a global function on a chart is the fibre functor applied to its Yoneda
morphism, at the germ of the identity.**  For a global function `t` on an étale chart `W`, viewed
as a morphism `h_W ⟶ 𝒪_S` of sheaves by Yoneda, the germ of `t` at a lift `w` of the geometric
point is the image of the germ of `𝟙_W` under the fibre of that morphism. -/
theorem sheafFiber_map_yonedaEquiv_symm (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (s : GeometricPoint S) (W : SmallEtale B S hS)
    (w : (geometricPointSitePoint B S hS s).fiber.obj W)
    (t : Γ((SmallEtale.toScheme B S hS).obj W, ⊤)) :
    ((geometricPointSitePoint B S hS s).sheafFiber (A := Type u)).map
        (((SmallEtale.topology B S hS).yonedaEquiv
          (F := Sheaf.ringSheaf (smallEtaleRingSheaf B hS))).symm t)
        (((geometricPointSitePoint B S hS s).toPresheafFiber W w
          ((SmallEtale.topology B S hS).yoneda.obj W).obj).hom (CategoryStruct.id W)) =
      (((geometricPointSitePoint B S hS s).toPresheafFiber W w
        (Sheaf.ringSheaf (smallEtaleRingSheaf B hS)).obj).hom t) := by
  refine ((geometricPointSitePoint B S hS s).toPresheafFiber_naturality_apply
    (((SmallEtale.topology B S hS).yonedaEquiv
      (F := Sheaf.ringSheaf (smallEtaleRingSheaf B hS))).symm t).hom W w
    (CategoryStruct.id W)).trans ?_
  refine congrArg ((geometricPointSitePoint B S hS s).toPresheafFiber W w
    (Sheaf.ringSheaf (smallEtaleRingSheaf B hS)).obj).hom ?_
  change (Sheaf.ringSheaf (smallEtaleRingSheaf B hS)).obj.map (CategoryStruct.id W).op t = t
  exact (Sheaf.ringSheaf (smallEtaleRingSheaf B hS)).obj.map_id_apply (op W) t

/-- The lift of a geometric point which a fibre element of a representable sheaf names is the one
whose germ of the identity morphism it is. -/
theorem yonedaIso_symm_eq_toPresheafFiber_id (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (s : GeometricPoint S) (W : SmallEtale B S hS)
    (w : (geometricPointSitePoint B S hS s).fiber.obj W) :
    ((yonedaCompEtaleStalkPresheafFunctorIso B S hS s).app W).toEquiv.symm w =
      (((geometricPointSitePoint B S hS s).toPresheafFiber W w
        ((SmallEtale.topology B S hS).yoneda.obj W).obj).hom (CategoryStruct.id W)) :=
  (Equiv.symm_apply_eq _).2
    ((smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm B S hS s W
      (Functor.elementsMk (geometricPointFiber B S hS s) W w) (CategoryStruct.id W)).trans
      ((geometricPointFiber B S hS s).map_id_apply W w)).symm

section StepTwo

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (x : GeometricPoint X.obj) (y : GeometricPoint Y.obj)
  (e : (geometricPointSitePoint B Y.obj Y.property y).sheafFiber (A := Type u) ≅
    g.toToposHom.inverseImage ⋙
      (geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))

/-- **`φ` on a germ, given the computation on sheaves of sets.**  Suppose the fibre at `x̄` of
the structure map `g⁻¹𝒪_Y ⟶ 𝒪_X`, applied to the image under `e` of the germ at `(W, u)` of a
global function `t` on `W`, is the germ at `(W', v)` of a global function `t'`. Then
`φ = AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso B g x y e` carries the germ of `t` in
`𝒪^{ét}_{Y,ȳ}` to the germ of `t'` in `𝒪^{ét}_{X,x̄}`. -/
theorem etaleLocalRingHomOfSheafFiberIso_toPresheafFiber_of_type
    (W : SmallEtale B Y.obj Y.property)
    (u : (geometricPointSitePoint B Y.obj Y.property y).fiber.obj W)
    (t : Γ((SmallEtale.toScheme B Y.obj Y.property).obj W, ⊤))
    (W' : SmallEtale B X.obj X.property)
    (v : (geometricPointSitePoint B X.obj X.property x).fiber.obj W')
    (t' : Γ((SmallEtale.toScheme B X.obj X.property).obj W', ⊤))
    (hA : (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
          ((RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).forgetRing.map g.fSharpInverseImage))
          (e.hom.app ((RingedSite.toRingedTopos
              (smallEtaleRingedSite B Y.obj Y.property)).forgetRing.obj
              (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O)
            (((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber W u
              ((RingedSite.toRingedTopos
                (smallEtaleRingedSite B Y.obj Y.property)).forgetRing.obj
                (RingedSite.toRingedTopos
                  (smallEtaleRingedSite B Y.obj Y.property)).O).obj).hom t)) =
        (((geometricPointSitePoint B X.obj X.property x).toPresheafFiber W' v
          (CategoryTheory.Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
            (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).O)).obj)).hom t') :
    etaleLocalRingHomOfSheafFiberIso B g x y e
        ((((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber W u
          (SmallEtale.structureSheaf B Y.obj Y.property).obj)).hom t) =
      (((geometricPointSitePoint B X.obj X.property x).toPresheafFiber W' v
        (SmallEtale.structureSheaf B X.obj X.property).obj)).hom t' := by
  change etaleCommRingFiberEquiv B X.obj X.property x
      ((((geometricPointSitePoint B X.obj X.property x).sheafFiber
        (A := CommRingCat.{u})).map g.fSharpInverseImage).hom
        (etaleLocalRingEquivInverseImageFiber B g x y e _)) = _
  rw [etaleLocalRingEquivInverseImageFiber_toPresheafFiber B g x y e W u t]
  refine Eq.trans (congrArg (etaleCommRingFiberEquiv B X.obj X.property x)
    (commRingFiber_map_ringStalkComparison (geometricPointSitePoint B X.obj X.property x)
      g.fSharpInverseImage _)) ?_
  refine Eq.trans (congrArg (fun z ↦ etaleCommRingFiberEquiv B X.obj X.property x
      ((Stacks.commRingPresheafFiberIso (geometricPointSitePoint B X.obj X.property x)
          (RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).O.obj).ringCatIsoToRingEquiv
        (ringStalkComparison (geometricPointSitePoint B X.obj X.property x)
          (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).O) z))) hA) ?_
  refine Eq.trans (congrArg (fun z ↦ etaleCommRingFiberEquiv B X.obj X.property x
      ((Stacks.commRingPresheafFiberIso (geometricPointSitePoint B X.obj X.property x)
          (RingedSite.toRingedTopos
            (smallEtaleRingedSite B X.obj X.property)).O.obj).ringCatIsoToRingEquiv z))
    (ringStalkComparison_ringGerm (geometricPointSitePoint B X.obj X.property x)
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.toRingedTopos
        (smallEtaleRingedSite B X.obj X.property)).O) W' v t')) ?_
  refine Eq.trans (congrArg (etaleCommRingFiberEquiv B X.obj X.property x)
    (ConcreteCategory.congr_hom
      ((geometricPointSitePoint B X.obj X.property x).toPresheafFiber_presheafFiberCompIso_hom_app
        (F := forget₂ CommRingCat.{u} RingCat.{u}) W' v
        (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).O.obj) t')) ?_
  exact etaleCommRingFiberEquiv_toPresheafFiber B X.obj X.property x W' v t'

variable (f : X ⟶ Y)
  (hf : (B.inclusion.map f).appTop =
    g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property))
  [IsAffine Y.obj] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y.obj, ⊤)}
  (V : SmallEtale B Y.obj Y.property)
  [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)]
  (pres : StandardPresentationOver ((SmallEtale.toScheme B Y.obj Y.property).obj V)
    (schemeStructureHom B Y.obj Y.property V) P)

include hf in
/-- **The fibre at `x̄` of the comparison is the solution-set map.**  Let `u` be a lift of the
geometric point `ȳ` to the affine étale chart `V`, and let `v` be the lift of `x̄` to `X ×_Y V`
which the fibre at `x̄` of `AlgebraicGeometry.comparisonSheafHom` assigns to it (the hypothesis
`hv`). Then the solution of `P` in `𝒪^{ét}_{X,x̄}` which `v` names is
`φ = AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso B g x y e` applied coordinatewise to the
solution in `𝒪^{ét}_{Y,ȳ}` which `u` names. -/
theorem baseChangeGeometricPointFiberEquivSolutions_comparisonSheafHom
    (u : (geometricPointSitePoint B Y.obj Y.property y).fiber.obj V)
    (v : (geometricPointSitePoint B X.obj X.property x).fiber.obj
      ((smallEtaleBaseChange B f).obj V))
    (hv : ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
        (comparisonSheafHom B g f hf V)
        (e.hom.app ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)
          (((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber V u
            ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V).obj).hom
            (CategoryStruct.id V))) =
      (((geometricPointSitePoint B X.obj X.property x).toPresheafFiber
        ((smallEtaleBaseChange B f).obj V) v
        ((SmallEtale.topology B X.obj X.property).yoneda.obj
          ((smallEtaleBaseChange B f).obj V)).obj).hom
        (CategoryStruct.id ((smallEtaleBaseChange B f).obj V))))
    (i : Fin n) :
    (baseChangeGeometricPointFiberEquivSolutions B f V pres x v).1 i =
      etaleLocalRingHomOfSheafFiberIso B g x y e
        ((geometricPointFiberEquivEtaleLocalSolutions B Y.obj Y.property y V pres u).1 i) := by
  rw [baseChangeGeometricPointFiberEquivSolutions_coe B f V pres x v i,
    geometricPointFiberEquivEtaleLocalSolutions_coe B Y.obj Y.property y V pres u i]
  refine (etaleLocalRingHomOfSheafFiberIso_toPresheafFiber_of_type B g x y e V u
    (presCoord B Y.property V pres i) ((smallEtaleBaseChange B f).obj V) v
    ((SmallEtale.baseChangeProj B f V).appTop.hom (presCoord B Y.property V pres i)) ?_).symm
  refine Eq.trans (congrArg (fun z ↦
      (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))).map
        ((RingedSite.toRingedTopos
          (smallEtaleRingedSite B X.obj X.property)).forgetRing.map g.fSharpInverseImage)
      (e.hom.app ((RingedSite.toRingedTopos
        (smallEtaleRingedSite B Y.obj Y.property)).forgetRing.obj
        (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).O) z))
    (sheafFiber_map_yonedaEquiv_symm B Y.obj Y.property y V u
      (presCoord B Y.property V pres i)).symm) ?_
  refine Eq.trans (congrArg (fun z ↦
      (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))).map
        ((RingedSite.toRingedTopos
          (smallEtaleRingedSite B X.obj X.property)).forgetRing.map g.fSharpInverseImage) z)
    (NatTrans.naturality_apply e.hom (((SmallEtale.topology B Y.obj Y.property).yonedaEquiv
      (F := Sheaf.ringSheaf (smallEtaleRingSheaf B Y.property))).symm
        (presCoord B Y.property V pres i))
      ((((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber V u
      ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V).obj).hom
      (CategoryStruct.id V))))) ?_
  refine Eq.trans
    ((((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))).map_comp_apply
    (g.toToposHom.inverseImage.map (((SmallEtale.topology B Y.obj Y.property).yonedaEquiv
      (F := Sheaf.ringSheaf (smallEtaleRingSheaf B Y.property))).symm
        (presCoord B Y.property V pres i)))
    ((RingedSite.toRingedTopos
      (smallEtaleRingedSite B X.obj X.property)).forgetRing.map g.fSharpInverseImage)
    (e.hom.app ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)
      ((((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber V u
      ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V).obj).hom
      (CategoryStruct.id V))))).symm ?_
  refine Eq.trans (congrArg (fun m ↦
      (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))).map m
        (e.hom.app ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)
          ((((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber V u
          ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V).obj).hom
          (CategoryStruct.id V)))))
    (comparisonCoord_eq_inverseImage_yoneda B X.property Y.property g V pres i).symm) ?_
  refine Eq.trans (congrArg (fun m ↦
      (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))).map m
        (e.hom.app ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)
          ((((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber V u
          ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V).obj).hom
          (CategoryStruct.id V)))))
    (comparisonSheafHom_comp_yoneda B g f hf V pres i).symm) ?_
  refine Eq.trans
    ((((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))).map_comp_apply
    (comparisonSheafHom B g f hf V) (((SmallEtale.topology B X.obj X.property).yonedaEquiv
      (F := Sheaf.ringSheaf (smallEtaleRingSheaf B X.property))).symm
      ((SmallEtale.baseChangeProj B f V).appTop.hom (presCoord B Y.property V pres i)))
    (e.hom.app ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)
      ((((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber V u
      ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V).obj).hom
      (CategoryStruct.id V))))) ?_
  refine Eq.trans (congrArg (fun z ↦
      (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))).map
        (((SmallEtale.topology B X.obj X.property).yonedaEquiv
      (F := Sheaf.ringSheaf (smallEtaleRingSheaf B X.property))).symm
      ((SmallEtale.baseChangeProj B f V).appTop.hom (presCoord B Y.property V pres i))) z) hv) ?_
  exact sheafFiber_map_yonedaEquiv_symm B X.obj X.property x
    ((smallEtaleBaseChange B f).obj V) v
    ((SmallEtale.baseChangeProj B f V).appTop.hom (presCoord B Y.property V pres i))

include hf in
/-- **The fibre at `x̄` of the comparison is the solution-set map, at the lift it assigns.**  For
a lift `u` of `ȳ` to `V`, the solution of `P` named by the lift of `x̄` to `X ×_Y V` which the
fibre at `x̄` of `AlgebraicGeometry.comparisonSheafHom` assigns to `u`, through the identification
of the fibre of a representable sheaf with the set of lifts, is
`φ = AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso B g x y e` applied coordinatewise to the
solution named by `u`. -/
theorem baseChangeGeometricPointFiberEquivSolutions_comparisonSheafHom_apply
    (u : (geometricPointSitePoint B Y.obj Y.property y).fiber.obj V) (i : Fin n) :
    (baseChangeGeometricPointFiberEquivSolutions B f V pres x
        (((yonedaCompEtaleStalkPresheafFunctorIso B X.obj X.property x).app
            ((smallEtaleBaseChange B f).obj V)).hom
          (((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
            (comparisonSheafHom B g f hf V)
            (e.hom.app ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)
              (((geometricPointSitePoint B Y.obj Y.property y).toPresheafFiber V u
                ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V).obj).hom
                (CategoryStruct.id V)))))).1 i =
      etaleLocalRingHomOfSheafFiberIso B g x y e
        ((geometricPointFiberEquivEtaleLocalSolutions B Y.obj Y.property y V pres u).1 i) :=
  baseChangeGeometricPointFiberEquivSolutions_comparisonSheafHom B g x y e f hf V pres u _
    ((((yonedaCompEtaleStalkPresheafFunctorIso B X.obj X.property x).app
        ((smallEtaleBaseChange B f).obj V)).toEquiv.symm_apply_apply _).symm.trans
      (yonedaIso_symm_eq_toPresheafFiber_id B X.obj X.property x
        ((smallEtaleBaseChange B f).obj V) _)) i

end StepTwo

end AlgebraicGeometry

end
