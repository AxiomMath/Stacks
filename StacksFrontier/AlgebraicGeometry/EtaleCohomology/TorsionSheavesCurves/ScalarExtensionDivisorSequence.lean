module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupDivisorBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictionShortComplexMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionDivisorSquare

/-!
# The divisor sequences of a smooth curve and of its scalar extension

Let `X` be a smooth curve over an algebraically closed field `k`, `k'/k` an algebraically closed
extension, `X' = X_{k'}` and `p : X' ⟶ X` the projection. The divisor sequences
`0 → 𝐆_m → j_* 𝐆_{m,η} → ⨁_x i_{x,*} 𝐙 → 0` of `X` and of `X'` are compared by a morphism of
short complexes into the direct image of the second one.

## Main results

* `Stacks.EtaleCohomology.divisorSequenceSecondMap_comp_closedPointDivisorDirectImageMap`: the
  second commuting square.
* `Stacks.EtaleCohomology.divisorSequenceInverseImageHom`: the morphism
  `p⁻¹(divisor sequence of X) ⟶ divisor sequence of X_{k'}`.
* `Stacks.EtaleCohomology.sheafH_map_etaleCohomologyRestrictionMap_divisorBoundary`: the
  connecting maps `Γ(⨁ i_{x,*} 𝐙) → H¹(𝐆_m)` commute with restriction to `X_{k'}`.
* `Stacks.EtaleCohomology.curveClassGroupScalarExtensionMap` and
  `Stacks.EtaleCohomology.curveClassGroupScalarExtensionMap_single`: restriction on
  `H¹(𝐆_m) ≅ Cl` sends the class of a closed point to the class of the closed point over it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
  AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k']

section Square

variable [IsNormal X] [IsLocallyNoetherian X]

/-! ### The second commuting square -/

/-- **The second square on sections, pointwise**: over an étale `X`-scheme `U` with Noetherian
space, the divisor of an invertible function on the generic fibre of `U`, carried to `X'`, is the
divisor of its restriction to the generic fibre of `U ×_X X'`. -/
theorem closedPointDivisorDirectImageMap_divisorSequenceSecondMap_apply (U : X.Etale)
    [NoetherianSpace U.left]
    [NoetherianSpace ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U).left]
    (x : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) :
    ((closedPointDivisorDirectImageMap.{u, v} (scalarExtensionFst k k' g)
        (scalarExtensionClosedPoint g k')
          (scalarExtensionFst_scalarExtensionClosedPoint g k')).hom.app
          (op U)).hom (((divisorSequenceSecondMap.{u, v} X).hom.app (op U)).hom
            (Stacks.Kummer.ofUnit x)) =
      ((divisorSequenceSecondMap.{u, v} (scalarExtension k k' g)).hom.app
          (op ((smallEtaleBaseChange (scalarExtensionFst k k' g)).obj U))).hom
        (((multiplicativeDirectImageSquareMap.{u, v}
          (genericPointSquare_scalarExtension g k')).hom.app (op U)).hom
          (Stacks.Kummer.ofUnit x)) := by
  have : IsLocallyNoetherian U.left := isLocallyNoetherian_etale_left X U
  set p := scalarExtensionFst k k' g
  set U' := (smallEtaleBaseChange p).obj U
  have : IsLocallyNoetherian U'.left := isLocallyNoetherian_etale_left _ U'
  set y := Units.map (genericFibreScalarExtensionMap g k' U).appTop.hom.toMonoidHom x
  have h1 : ((divisorSequenceSecondMap.{u, v} X).hom.app (op U)).hom (Stacks.Kummer.ofUnit x) =
      closedPointDivisorSheafSection.{u, v} U (Additive.ofMul x) :=
    divisorSequenceSecondMap_app_of_noetherianSpace U _
  have h2 : closedPointDivisorSheafSection.{u, v} U (Additive.ofMul x) =
      closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} X U
        (closedPointDivisorSections.{u, v} U (Additive.ofMul x)) :=
    closedPointDivisorSheafSection_apply U _
  have h3 := closedPointDivisorDirectImageMap_app_sheafSectionOfDirectSum.{u, v} g k' U
    (closedPointDivisorSections.{u, v} U (Additive.ofMul x))
  have h4 := closedPointDivisorDirectImageDirectSum_closedPointDivisorSections.{u, v} g k' U x
  have h5 : ((multiplicativeDirectImageSquareMap.{u, v}
      (genericPointSquare_scalarExtension g k')).hom.app (op U)).hom (Stacks.Kummer.ofUnit x) =
      Stacks.Kummer.ofUnit
        (U := (smallEtaleBaseChange (genericPointInclusion (scalarExtension k k' g))).obj U') y :=
    multiplicativeDirectImageSquareMap_app_ofUnit _ U x
  have h6 : ((divisorSequenceSecondMap.{u, v} (scalarExtension k k' g)).hom.app (op U')).hom
      (Stacks.Kummer.ofUnit
        (U := (smallEtaleBaseChange (genericPointInclusion (scalarExtension k k' g))).obj U') y) =
      closedPointDivisorSheafSection.{u, v} U' (Additive.ofMul y) :=
    divisorSequenceSecondMap_app_of_noetherianSpace U' _
  have h7 : closedPointDivisorSheafSection.{u, v} U' (Additive.ofMul y) =
      closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, v} (scalarExtension k k' g) U'
        (closedPointDivisorSections.{u, v} U' (Additive.ofMul y)) :=
    closedPointDivisorSheafSection_apply U' _
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- **The second commuting square at an affine étale `X`-scheme.** -/
theorem divisorSequenceSecondMap_comp_closedPointDivisorDirectImageMap_app (W : X.AffineEtale) :
    (divisorSequenceSecondMap.{u, v} X ≫ closedPointDivisorDirectImageMap.{u, v}
        (scalarExtensionFst k k' g) (scalarExtensionClosedPoint g k')
          (scalarExtensionFst_scalarExtensionClosedPoint g k')).hom.app
        (op ((Scheme.AffineEtale.Spec X).obj W)) =
      (multiplicativeDirectImageSquareMap.{u, v} (genericPointSquare_scalarExtension g k') ≫
        (etaleAbelianDirectImage.{u, v} (scalarExtensionFst k k' g)).map
          (divisorSequenceSecondMap.{u, v} (scalarExtension k k' g))).hom.app
        (op ((Scheme.AffineEtale.Spec X).obj W)) := by
  have : NoetherianSpace ((Scheme.AffineEtale.Spec X).obj W).left :=
    noetherianSpace_affineEtale_left X W
  have : CompactSpace ((Scheme.AffineEtale.Spec X).obj W).left :=
    inferInstanceAs (CompactSpace (Scheme.Spec.obj W.left))
  have := noetherianSpace_smallEtaleBaseChange_scalarExtension g k'
    ((Scheme.AffineEtale.Spec X).obj W)
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ?_)
  obtain ⟨x, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{u, v} z
  exact closedPointDivisorDirectImageMap_divisorSequenceSecondMap_apply g k' _ x

/-- **The second commuting square of the divisor-sequence comparison**: the divisor map of `X`
followed by the third component equals the second component followed by the direct image of the
divisor map of `X_{k'}`. -/
theorem divisorSequenceSecondMap_comp_closedPointDivisorDirectImageMap :
    divisorSequenceSecondMap.{u, v} X ≫ closedPointDivisorDirectImageMap.{u, v}
        (scalarExtensionFst k k' g) (scalarExtensionClosedPoint g k')
          (scalarExtensionFst_scalarExtensionClosedPoint g k') =
      multiplicativeDirectImageSquareMap.{u, v} (genericPointSquare_scalarExtension g k') ≫
        (etaleAbelianDirectImage.{u, v} (scalarExtensionFst k k' g)).map
          (divisorSequenceSecondMap.{u, v} (scalarExtension k k' g)) :=
  Sheaf.hom_ext ((Functor.IsCoverDense.restrictHomEquivHom (G := Scheme.AffineEtale.Spec X)
    (K := X.smallEtaleTopology)).symm.injective
      (NatTrans.ext (funext fun W =>
        divisorSequenceSecondMap_comp_closedPointDivisorDirectImageMap_app g k' W.unop)))

end Square

/-! ### The morphism of divisor sequences -/

section Hom

/-- **The morphism from the divisor sequence of `X` to the direct image of that of `X_{k'}`**:
restriction of invertible functions to `U ×_X X'` and to its generic fibre, and the map of
divisors sending the closed point `x` to the closed point over it. -/
def divisorSequenceScalarExtensionHom :
    divisorSequence g ⟶ (divisorSequence (scalarExtensionSnd k k' g)).map
      (etaleAbelianDirectImage.{u, u + 1} (scalarExtensionFst k k' g)) :=
  haveI := isNormal_of_isCurve_of_smooth g
  haveI := isLocallyNoetherian_of_isCurve g
  { τ₁ := multiplicativeDirectImageComparison.{u, u + 1} (scalarExtensionFst k k' g)
    τ₂ := multiplicativeDirectImageSquareMap.{u, u + 1} (genericPointSquare_scalarExtension g k')
    τ₃ := closedPointDivisorDirectImageMap.{u, u + 1} (scalarExtensionFst k k' g)
      (scalarExtensionClosedPoint g k') (scalarExtensionFst_scalarExtensionClosedPoint g k')
    comm₁₂ := multiplicativeDirectImageComparison_comp_multiplicativeDirectImageSquareMap.{u, u + 1}
      (genericPointSquare_scalarExtension g k')
    comm₂₃ :=
      (divisorSequenceSecondMap_comp_closedPointDivisorDirectImageMap.{u, u + 1} g k').symm }

/-- **The morphism from the inverse image of the divisor sequence of `X` to the divisor sequence
of `X_{k'}`**, adjoint to `divisorSequenceScalarExtensionHom`. -/
def divisorSequenceInverseImageHom :
    (divisorSequence g).map (etaleAbelianInverseImage.{u, u + 1} (scalarExtensionFst k k' g)) ⟶
      divisorSequence (scalarExtensionSnd k k' g) :=
  inverseImageShortComplexHom.{u, u + 1} (scalarExtensionFst k k' g)
    (divisorSequenceScalarExtensionHom g k')

/-- The first component of `divisorSequenceInverseImageHom` is the comparison
`p⁻¹ 𝐆_{m,X} ⟶ 𝐆_{m,X'}`. -/
theorem divisorSequenceInverseImageHom_τ₁ :
    (divisorSequenceInverseImageHom g k').τ₁ =
      Stacks.Kummer.multiplicativeInverseImageComparison.{u, u + 1} (scalarExtensionFst k k' g) :=
  rfl

end Hom

/-! ### The connecting maps -/

section Boundary

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The third component on global sections**: a global divisor of `X` is carried to `X'` by
`closedPointDivisorDirectImageMap`, and read over `X'` itself. -/
def closedPointDivisorScalarExtensionTop :
    ToType ((closedPointDivisorSheaf.{u, u + 1} X).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) →+
      ToType ((closedPointDivisorSheaf.{u, u + 1} (scalarExtension k k' g)).obj.obj
        (op (Scheme.Etale.mk (𝟙 (scalarExtension k k' g))))) :=
  ((closedPointDivisorSheaf.{u, u + 1} (scalarExtension k k' g)).obj.map
      (((isTerminalEtaleMkId X).isTerminalObj
        (smallEtaleBaseChange (scalarExtensionFst k k' g))).from
          (Scheme.Etale.mk (𝟙 (scalarExtension k k' g)))).op).hom.comp
    ((divisorSequenceScalarExtensionHom g k').τ₃.hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom

/-- **Restriction in degree zero along the third component**: the restriction of the class of a
global divisor of `X`, moved along `p⁻¹(⨁ i_{x,*} 𝐙) ⟶ ⨁ i_{x',*} 𝐙`, is the class of the
carried global divisor. -/
theorem sheafH_map_etaleCohomologyRestrictionMap_closedPointDivisorSheaf
    (s : ToType ((closedPointDivisorSheaf.{u, u + 1} X).obj.obj (op (Scheme.Etale.mk (𝟙 X))))) :
    Sheaf.H.map (divisorSequenceInverseImageHom g k').τ₃ 0
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' g)
          (closedPointDivisorSheaf.{u, u + 1} X) 0
          ((Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} X)
            (isTerminalEtaleMkId X)).symm s)) =
      (Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} (scalarExtension k k' g))
        (isTerminalEtaleMkId (scalarExtension k k' g))).symm
          (closedPointDivisorScalarExtensionTop g k' s) := by
  have hψ : (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (scalarExtensionFst k k' g)).unit.app
      (closedPointDivisorSheaf.{u, u + 1} X) ≫
        (etaleAbelianDirectImage.{u, u + 1} (scalarExtensionFst k k' g)).map
          (divisorSequenceInverseImageHom g k').τ₃ = (divisorSequenceScalarExtensionHom g k').τ₃ :=
    ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (scalarExtensionFst k k' g)).homEquiv_unit
      _ _ _).symm.trans (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1}
        (scalarExtensionFst k k' g)).homEquiv _ _).apply_symm_apply _)
  have h0 := equiv₀_etaleCohomologyRestrictionMap_zero.{u, u + 1, u + 1} (scalarExtensionFst k k' g)
    (closedPointDivisorSheaf.{u, u + 1} X) (isTerminalEtaleMkId (scalarExtension k k' g))
    ((Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} X) (isTerminalEtaleMkId X)).symm s)
  rw [AddEquiv.apply_symm_apply] at h0
  refine ((Sheaf.H.equiv₀ _
    (isTerminalEtaleMkId (scalarExtension k k' g))).symm_apply_eq.mpr ?_).symm
  refine Eq.trans ?_ (Sheaf.H.equiv₀_naturality (isTerminalEtaleMkId (scalarExtension k k' g))
    (divisorSequenceInverseImageHom g k').τ₃ _)
  refine Eq.trans ?_ (congrArg (fun t => ((divisorSequenceInverseImageHom g k').τ₃.hom.app
    (op (Scheme.Etale.mk (𝟙 (scalarExtension k k' g))))).hom t) h0.symm)
  refine Eq.trans ?_ (ConcreteCategory.congr_hom
    ((divisorSequenceInverseImageHom g k').τ₃.hom.naturality
      (((isTerminalEtaleMkId X).isTerminalObj
        (smallEtaleBaseChange (scalarExtensionFst k k' g))).from
          (Scheme.Etale.mk (𝟙 (scalarExtension k k' g)))).op) _).symm
  exact (congrArg (fun t => ((closedPointDivisorSheaf.{u, u + 1} (scalarExtension k k' g)).obj.map
      (((isTerminalEtaleMkId X).isTerminalObj
        (smallEtaleBaseChange (scalarExtensionFst k k' g))).from
          (Scheme.Etale.mk (𝟙 (scalarExtension k k' g)))).op).hom t)
    (ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f => f.hom) hψ)
      (op (Scheme.Etale.mk (𝟙 X)))) s)).symm

/-- **The connecting map of the divisor sequence commutes with scalar extension**: restricting
the class in `H¹(X, 𝐆_m)` of a global divisor of `X` to `X'` (and moving it along
`p⁻¹ 𝐆_{m,X} ⟶ 𝐆_{m,X'}`) gives the class of the carried global divisor of `X'`. -/
theorem sheafH_map_etaleCohomologyRestrictionMap_divisorBoundary
    (s : ToType ((closedPointDivisorSheaf.{u, u + 1} X).obj.obj (op (Scheme.Etale.mk (𝟙 X))))) :
    Sheaf.H.map (Stacks.Kummer.multiplicativeInverseImageComparison.{u, u + 1}
        (scalarExtensionFst k k' g)) 1
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' g)
          (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 (divisorBoundary g s)) =
      divisorBoundary (scalarExtensionSnd k k' g)
        (closedPointDivisorScalarExtensionTop g k' s) := by
  have h := etaleCohomologyRestrictionMap_extClass_of_hom.{u, u + 1, u + 1}
    (scalarExtensionFst k k' g)
    (shortExact_divisorSequenceOfCurve g)
    (shortExact_divisorSequenceOfCurve (scalarExtensionSnd k k' g))
    (divisorSequenceInverseImageHom g k') 0 1 (zero_add 1)
    ((Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} X) (isTerminalEtaleMkId X)).symm s)
  rw [sheafH_map_etaleCohomologyRestrictionMap_closedPointDivisorSheaf] at h
  exact h

end Boundary

/-! ### Sections of the skyscrapers which are constant -/

section Constant

/-- Restriction of sections of `i_{y,*} 𝐙` carries constant functions on the fibre to constant
functions. -/
theorem integerSkyscraperSectionsIsoLocallyConstantMaps_map_of_eq_const {Y : Scheme.{u}} (y : Y)
    {V W : Y.Etale} (f : V ⟶ W) (w : ToType ((integerSkyscraper.{u, v} Y y).obj.obj (op W)))
    (c : ULift.{max (u + 1) v} ℤ)
    (hw : (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y W).hom w =
      LocallyConstant.const _ c) :
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y V).hom
        (((integerSkyscraper.{u, v} Y y).obj.map f.op).hom w) = LocallyConstant.const _ c := by
  have hnat := ConcreteCategory.congr_hom ((smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v}
    (Spec (Y.residueField y)) (ULift.{max (u + 1) v} ℤ)).hom.naturality
      ((smallEtaleBaseChange (Y.fromSpecResidueField y)).map f).op) w
  refine hnat.trans ?_
  show LocallyConstant.comap _
    ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y W).hom w) = _
  rw [hw]
  rfl

/-- `i_{p x',*} 𝐙 ⟶ p_* i_{x',*} 𝐙` carries constant functions on the fibre to constant
functions. -/
theorem integerSkyscraperDirectImageMap_app_of_eq_const {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) (y' : Y')
    (U : Y.Etale) (w : ToType ((integerSkyscraper.{u, v} Y (q.base y')).obj.obj (op U)))
    (c : ULift.{max (u + 1) v} ℤ)
    (hw : (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y (q.base y') U).hom w =
      LocallyConstant.const _ c) :
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y' y'
        ((smallEtaleBaseChange q).obj U)).hom
        ((integerSkyscraperDirectImageMap.{u, v} q y').hom.app (op U) w) =
      LocallyConstant.const _ c := by
  rw [integerSkyscraperDirectImageMap_app, hw]
  rfl

/-- Transport of sections of `i_{y,*} 𝐙` along an equality of points carries constant functions
to constant functions. -/
theorem integerSkyscraperSectionsIsoLocallyConstantMaps_eqToHom_of_eq_const {Y : Scheme.{u}}
    {y₁ y₂ : Y} (h : y₁ = y₂) (E : integerSkyscraper.{u, v} Y y₁ = integerSkyscraper.{u, v} Y y₂)
    (U : Y.Etale) (w : ToType ((integerSkyscraper.{u, v} Y y₁).obj.obj (op U)))
    (c : ULift.{max (u + 1) v} ℤ)
    (hw : (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y₁ U).hom w =
      LocallyConstant.const _ c) :
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y₂ U).hom
        ((eqToHom E).hom.app (op U) w) = LocallyConstant.const _ c := by
  subst h
  exact hw

/-- A global section of `i_{y,*} 𝐙` is the constant function with value its integer. -/
theorem integerSkyscraperSectionsIsoLocallyConstantMaps_eq_const (Y : Scheme.{u}) (y : Y)
    (w : ToType ((integerSkyscraper.{u, v} Y y).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))) :
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y (Scheme.Etale.mk (𝟙 Y))).hom w =
      LocallyConstant.const _ (ULift.up (integerSkyscraperTopAddEquiv.{u, v} Y y w)) := by
  have := subsingleton_residueFibre_etaleMkId Y y
  refine LocallyConstant.ext fun z => ?_
  rw [Subsingleton.elim z (residueFibreEtaleMkIdPoint Y y)]
  rfl

/-- The integer of a global section of `i_{y,*} 𝐙` which is the constant function `c`. -/
theorem integerSkyscraperTopAddEquiv_of_eq_const (Y : Scheme.{u}) (y : Y)
    (w : ToType ((integerSkyscraper.{u, v} Y y).obj.obj (op (Scheme.Etale.mk (𝟙 Y)))))
    (c : ULift.{max (u + 1) v} ℤ)
    (hw : (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y
      (Scheme.Etale.mk (𝟙 Y))).hom w = LocallyConstant.const _ c) :
    integerSkyscraperTopAddEquiv.{u, v} Y y w = c.down := by
  show ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} Y y
    (Scheme.Etale.mk (𝟙 Y))).hom w (residueFibreEtaleMkIdPoint Y y)).down = _
  rw [hw]
  rfl

end Constant

/-! ### The map of class groups -/

section ClassGroup

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- The global divisor of a single section of one summand, read as a finitely supported
function. -/
theorem closedPointDivisorSheafTopAddEquiv_ι (Y : Scheme.{u})
    [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] [NoetherianSpace Y]
    [QuasiSeparatedSpace Y] (y : closedPoints Y)
    (w : (closedPointSkyscraper.{u, u + 1} Y y).obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
    closedPointDivisorSheafTopAddEquiv.{u, u + 1} Y
        (((closedPointDivisorSheaf.ι.{u, u + 1} Y y).hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom w) =
      Finsupp.single y (integerSkyscraperTopAddEquiv.{u, u + 1} Y y.1 w) := by
  let : DecidableEq ↥(closedPoints Y) := Classical.decEq _
  have h : ((closedPointDivisorSheaf.ι.{u, u + 1} Y y).hom.app (op (Scheme.Etale.mk (𝟙 Y)))).hom w =
      closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, u + 1} Y (Scheme.Etale.mk (𝟙 Y))
        (DirectSum.of _ y w) := by
    rw [closedPointDivisorSheaf.sheafSectionOfDirectSum, DirectSum.toAddMonoid_of]
  rw [h]
  refine Finsupp.ext fun z => ?_
  rw [closedPointDivisorSheafTopAddEquiv_apply,
    closedPointDivisorSheaf.sectionsAddEquivDirectSum_symm_apply]
  by_cases hz : z = y
  · subst hz
    rw [DirectSum.of_eq_same, Finsupp.single_eq_same]
  · have h1 := DirectSum.of_eq_of_ne (β := fun x : closedPoints Y =>
      (closedPointSkyscraper.{u, u + 1} Y x).obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) y z w
      (fun h => hz h)
    refine (congrArg (fun r => integerSkyscraperTopAddEquiv.{u, u + 1} Y z.1 r) h1).trans ?_
    refine (map_zero (integerSkyscraperTopAddEquiv.{u, u + 1} Y z.1)).trans ?_
    exact (Finsupp.single_eq_of_ne (by exact fun h => hz (by exact h))).symm

/-- **The carried global divisor of a single section of the summand at `x`** is the restriction
of its image in the summand at the closed point over `x`. -/
theorem closedPointDivisorScalarExtensionTop_ι (x : closedPoints X)
    (t : (closedPointSkyscraper.{u, u + 1} X x).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    closedPointDivisorScalarExtensionTop g k'
        (((closedPointDivisorSheaf.ι.{u, u + 1} X x).hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom t) =
      ((closedPointDivisorSheaf.ι.{u, u + 1} (scalarExtension k k' g)
          (scalarExtensionClosedPoint g k' x)).hom.app
            (op (Scheme.Etale.mk (𝟙 (scalarExtension k k' g))))).hom
        (((closedPointSkyscraper.{u, u + 1} (scalarExtension k k' g)
            (scalarExtensionClosedPoint g k' x)).obj.map
              (((isTerminalEtaleMkId X).isTerminalObj
                (smallEtaleBaseChange (scalarExtensionFst k k' g))).from
                  (Scheme.Etale.mk (𝟙 (scalarExtension k k' g)))).op).hom
            (closedPointDivisorDirectImageSummandMap.{u, u + 1} g k' (Scheme.Etale.mk (𝟙 X))
              x t)) := by
  let : DecidableEq ↥(closedPoints X) := Classical.decEq _
  let : DecidableEq ↥(closedPoints (scalarExtension k k' g)) := Classical.decEq _
  have := isNormal_of_isCurve_of_smooth g
  have := isLocallyNoetherian_of_isCurve g
  have h0 :
    ((closedPointDivisorSheaf.ι.{u, u + 1} X x).hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom t =
      closedPointDivisorSheaf.sheafSectionOfDirectSum.{u, u + 1} X (Scheme.Etale.mk (𝟙 X))
        (DirectSum.of _ x t) := by
    rw [closedPointDivisorSheaf.sheafSectionOfDirectSum, DirectSum.toAddMonoid_of]
  have h1 := closedPointDivisorDirectImageMap_app_sheafSectionOfDirectSum.{u, u + 1} g k'
    (Scheme.Etale.mk (𝟙 X)) (DirectSum.of _ x t)
  have h2 : closedPointDivisorDirectImageDirectSum.{u, u + 1} g k' (Scheme.Etale.mk (𝟙 X))
      (DirectSum.of _ x t) = DirectSum.of _ (scalarExtensionClosedPoint g k' x)
        (closedPointDivisorDirectImageSummandMap.{u, u + 1} g k' (Scheme.Etale.mk (𝟙 X)) x t) := by
    rw [closedPointDivisorDirectImageDirectSum, DirectSum.toAddMonoid_of]
    rfl
  have h3 := DFunLike.congr_fun (closedPointDivisorSheaf.map_comp_sheafSectionOfDirectSum.{u, u + 1}
    (scalarExtension k k' g) (((isTerminalEtaleMkId X).isTerminalObj
      (smallEtaleBaseChange (scalarExtensionFst k k' g))).from
        (Scheme.Etale.mk (𝟙 (scalarExtension k k' g)))))
    (DirectSum.of _ (scalarExtensionClosedPoint g k' x)
        (closedPointDivisorDirectImageSummandMap.{u, u + 1} g k' (Scheme.Etale.mk (𝟙 X)) x t))
  rw [h0]
  refine (congrArg (fun z => ((closedPointDivisorSheaf.{u, u + 1} (scalarExtension k k' g)).obj.map
    (((isTerminalEtaleMkId X).isTerminalObj (smallEtaleBaseChange (scalarExtensionFst k k' g))).from
      (Scheme.Etale.mk (𝟙 (scalarExtension k k' g)))).op).hom z)
    (h1.trans (congrArg _ h2))).trans ?_
  refine h3.trans ?_
  rw [AddMonoidHom.comp_apply, DirectSum.map_of, closedPointDivisorSheaf.sheafSectionOfDirectSum,
    DirectSum.toAddMonoid_of]

omit [IsCurve k g] [IsAlgClosed k'] in
/-- **The integer of a summand section is unchanged under scalar extension.** -/
theorem integerSkyscraperTopAddEquiv_closedPointDivisorDirectImageSummandMap (x : closedPoints X)
    (t : (closedPointSkyscraper.{u, u + 1} X x).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) :
    integerSkyscraperTopAddEquiv.{u, u + 1} (scalarExtension k k' g)
        (scalarExtensionClosedPoint g k' x).1
        (((closedPointSkyscraper.{u, u + 1} (scalarExtension k k' g)
            (scalarExtensionClosedPoint g k' x)).obj.map
              (((isTerminalEtaleMkId X).isTerminalObj
                (smallEtaleBaseChange (scalarExtensionFst k k' g))).from
                  (Scheme.Etale.mk (𝟙 (scalarExtension k k' g)))).op).hom
            (closedPointDivisorDirectImageSummandMap.{u, u + 1} g k' (Scheme.Etale.mk (𝟙 X)) x t)) =
      integerSkyscraperTopAddEquiv.{u, u + 1} X x.1 t := by
  refine integerSkyscraperTopAddEquiv_of_eq_const _ _ _ _ ?_
  refine integerSkyscraperSectionsIsoLocallyConstantMaps_map_of_eq_const _ _ _ _ ?_
  refine integerSkyscraperDirectImageMap_app_of_eq_const _ _ _ _ _ ?_
  exact integerSkyscraperSectionsIsoLocallyConstantMaps_eqToHom_of_eq_const
    (scalarExtensionFst_scalarExtensionClosedPoint g k' x).symm _ _ _ _
    (integerSkyscraperSectionsIsoLocallyConstantMaps_eq_const X x.1 t)

/-- **The map of class groups induced by scalar extension**: `H¹(X, 𝐆_m) → H¹(X', 𝐆_m)`
(restriction followed by `p⁻¹ 𝐆_{m,X} ⟶ 𝐆_{m,X'}`), read through `H¹(𝐆_m) ≅ Cl`. -/
def curveClassGroupScalarExtensionMap :
    curveClassGroup g →+ curveClassGroup (scalarExtensionSnd k k' g) :=
  (sheafHOneMultiplicativeAddEquivClosedPointClassGroup
      (scalarExtensionSnd k k' g)).toAddMonoidHom.comp
    ((Sheaf.H.map (Stacks.Kummer.multiplicativeInverseImageComparison.{u, u + 1}
      (scalarExtensionFst k k' g)) 1).comp
      ((etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' g)
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1).comp
        (sheafHOneMultiplicativeAddEquivClosedPointClassGroup g).symm.toAddMonoidHom))

/-- **The class group map sends the class of a closed point to the class of the closed point
over it.** -/
theorem curveClassGroupScalarExtensionMap_single (x : closedPoints X) :
    curveClassGroupScalarExtensionMap g k'
        (QuotientAddGroup.mk (Finsupp.single x (1 : ℤ)) : curveClassGroup g) =
      (QuotientAddGroup.mk (Finsupp.single (scalarExtensionClosedPoint g k' x) (1 : ℤ)) :
        curveClassGroup (scalarExtensionSnd k k' g)) := by
  obtain ⟨_, _, _, _⟩ :=
    isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve g
  obtain ⟨_, _, _, _⟩ := isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve
    (scalarExtensionSnd k k' g)
  let t : (closedPointSkyscraper.{u, u + 1} X x).obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
    (integerSkyscraperTopAddEquiv.{u, u + 1} X x.1).symm 1
  let sx := ((closedPointDivisorSheaf.ι.{u, u + 1} X x).hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom t
  have hsx : closedPointDivisorSheafTopAddEquiv.{u, u + 1} X sx = Finsupp.single x 1 := by
    refine (closedPointDivisorSheafTopAddEquiv_ι X x t).trans ?_
    rw [AddEquiv.apply_symm_apply]
  have he := sheafHOneMultiplicativeAddEquivClosedPointClassGroup_divisorBoundary g sx
  rw [hsx] at he
  rw [← he]
  show sheafHOneMultiplicativeAddEquivClosedPointClassGroup (scalarExtensionSnd k k' g)
    (Sheaf.H.map (Stacks.Kummer.multiplicativeInverseImageComparison.{u, u + 1}
      (scalarExtensionFst k k' g)) 1
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (scalarExtensionFst k k' g)
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1
        ((sheafHOneMultiplicativeAddEquivClosedPointClassGroup g).symm
          (sheafHOneMultiplicativeAddEquivClosedPointClassGroup g (divisorBoundary g sx))))) = _
  rw [AddEquiv.symm_apply_apply, sheafH_map_etaleCohomologyRestrictionMap_divisorBoundary,
    sheafHOneMultiplicativeAddEquivClosedPointClassGroup_divisorBoundary]
  refine congrArg QuotientAddGroup.mk
    ((congrArg _ (closedPointDivisorScalarExtensionTop_ι g k' x t)).trans
      ((closedPointDivisorSheafTopAddEquiv_ι _ _ _).trans ?_))
  rw [integerSkyscraperTopAddEquiv_closedPointDivisorDirectImageSummandMap,
    AddEquiv.apply_symm_apply]

end ClassGroup

end Stacks.EtaleCohomology

end
