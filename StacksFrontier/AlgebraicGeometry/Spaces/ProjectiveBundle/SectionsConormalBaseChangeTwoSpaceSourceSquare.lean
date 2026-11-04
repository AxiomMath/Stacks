module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChangeTwoSpaceInverse

/-!
# The source square of the conormal isomorphism of Stacks 0B4I over two spaces, assembled

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `u : T ⟶ X` and `v : T' ⟶ X'` scheme points
and `h : T' ⟶ T` with `v ≫ g = u ∘ h`.  The source readings of the conormal isomorphism at `u ∘ h`
on `X` and at `v` on `X'` are compared at `T'` by pasting the tensor square
(`AlgebraicGeometry.Space.conormalSourceTensorReading_twoSpace`), the kernel square
(`AlgebraicGeometry.Space.kernelPointReadingHom_twoSpace`) and the inverse-line square
(`AlgebraicGeometry.Space.inversePointReadingHom_twoSpace`); together with the square along `h`
this gives the source square of `AlgebraicGeometry.Space.ConormalChartSourceCompat` over two
spaces.

## Main results

* `AlgebraicGeometry.Space.conormalSourceReading_twoSpace`: the comparison at `T'` of the source
  readings at `u ∘ h` on `X` and at `v` on `X'`.
* `AlgebraicGeometry.Space.conormalSource_twoSpace`: the source square over two spaces, given the
  monoidality of the base change of the Zariski reading along `h`.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  {T T' : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1) (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T)
  (hvh : v ≫ g.hom = yoneda.map h ≫ u) (Q : InvertibleQuotient X E)

/-- **The comparison at `T'` of the source readings at `u ∘ h` on `X` and at `v` on `X'`**: the
reading of `v^*g^* ≅ (u ∘ h)^*` at the conormal source, followed by the source reading at `u ∘ h`
on `X` and the comparison of the two base changes of the conormal source along `h`, is the reading
of the base change of the conormal source along `g` followed by the source reading at `v` on
`X'`. -/
theorem conormalSourceReading_twoSpace :
    (zariskiReadingFunctor T').map
        ((pointPullbackCompIso X g u v h hvh).hom.app (sectionConormalSource X E Q)) ≫
      (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          Q.L := Q.invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T').Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T').map (modulePullbackTensorIso B S hS (pointHom (yoneda.map h ≫ u))
          (kernel Q.q) (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (pointHom (yoneda.map h ≫ u))).obj
          (kernel Q.q)) ((modulePullback B S hS (pointHom (yoneda.map h ≫ u))).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom (yoneda.map h ≫ u)) (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom (yoneda.map h ≫ u)) (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom (yoneda.map h ≫ u))).obj
          (kernel Q.q))) ((zariskiReadingFunctor T').obj
          ((modulePullback B S hS (pointHom (yoneda.map h ≫ u))).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T' (yoneda.map h ≫ u))
          (inversePointReadingIso X T' (yoneda.map h ≫ u) Q.L).hom)) ≫
      (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X E T' (yoneda.map h ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u h) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u))
        (sectionPointQuotientBaseChangeL X E hE Q u h)
        (sectionPointQuotient_baseChange_q X E hE Q u h)).inv ≫
      (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).hom =
    (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
        (sectionConormalSourceBaseChangeHom X E Q g)) ≫
      (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L := (Q.baseChange g
          (Iso.refl _)).invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T').Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T').map (modulePullbackTensorIso B S hS (pointHom v)
          (kernel (Q.baseChange g (Iso.refl _)).q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (pointHom v)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q))
          ((modulePullback B S hS (pointHom v)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom v)
          (kernel (Q.baseChange g (Iso.refl _)).q)
          (isQuasicoherentOnSite_kernel_q X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _))))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom v)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
          (-1)))).hom ≫ (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q)))
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))))).hom))
      (kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T' v) (inversePointReadingIso X' T' v
          (Q.baseChange g (Iso.refl _)).L).hom)) := by
  refine CategoryTheory.Functor.compBifunctorMap_comp_eq_of_squares
    (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules) (iℬ := Scheme.Modules.instCategory)
    _ _ _ _ _ _ _ _ _ _ _
    ((Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X E T' (yoneda.map h ≫ u))
        (pointZariskiModuleBaseChangeIso X E hE u h) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u))
        (sectionPointQuotientBaseChangeL X E hE Q u h)
        (sectionPointQuotient_baseChange_q X E hE Q u h)).1.inv ≫
      (Stacks.Divisors.quotientKernelBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).1.hom)
    ((Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X E T' (yoneda.map h ≫ u))
        (sectionPointQuotient X E hE Q T u) (sectionPointQuotient X E hE Q T' (yoneda.map h ≫ u))
        (sectionPointQuotientBaseChangeL X E hE Q u h)).inv ≫
      (Stacks.Divisors.inverseQuotientBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)).hom)
    (have := preservesZeroMorphisms_modulePullback B S hS g
     (zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).inv.app (kernel Q.q) ≫
        (modulePullback B S hS (pointHom v)).map (kernelComparison Q.q (modulePullback B S hS g) ≫
          (kernelBaseChangeIso X E Q g).hom)))
    (have : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        Q.L := Q.invertible.toAlgebraicGeometry
     (zariskiReadingFunctor T').map ((pointPullbackCompIso X g u v h hvh).inv.app
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)) ≫
        (modulePullback B S hS (pointHom v)).map (modulePullbackTensorPowerIso g Q.L (-1)).hom))
    ?hc ?hT ?hK ?hΛ
  case hc => exact Stacks.Divisors.conormalSourceBaseChange_inv_comp_hom _ _ _ _ _ _ _ _ _ _ _ _ _
  case hT => exact conormalSourceTensorReading_twoSpace X E hE g u v h hvh Q
  case hK => exact kernelPointReadingHom_twoSpace X E hE g u v h hvh Q
  case hΛ => exact inversePointReadingHom_twoSpace X E hE g u v h hvh Q


/-- **The source square over two spaces**, given the monoidality `hc` of the base change of the
Zariski reading along `h`: the comparison of the source readings of
`AlgebraicGeometry.Space.ConormalChartSourceCompat` followed by the base change along `h` of the
source reading at `u` on `X` and the two-space base change of the conormal source is the reading of
the base change of the conormal source along `g` followed by the source reading at `v` on `X'`. -/
theorem conormalSource_twoSpace
    (hc : ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).obj (yonedaSpace B S hS T).property)
      (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
      CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
              ((zariskiReadingFunctor T).obj (N))).obj ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
          (isAlgebraicSpace_yoneda B S hS T')) ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
          (zariskiReadingFunctor T') (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj (N)) ((zariskiReadingFunctor T).obj (M))).hom)
          ((Stacks.RingedSpace.comparisonBifunctorIso
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
          ((zariskiReadingFunctor T).obj (N), (zariskiReadingFunctor T).obj (M)))
          ((zariskiReadingPullbackHom h).app (N)) ((zariskiReadingPullbackHom h).app (M))
          ((zariskiReadingPullbackHom h).app ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (N) hN)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (M) hM)).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N)))
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (M)))).hom))
    :
    (CategoryTheory.Functor.conormalGlueComparison
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
        (zariskiReadingFunctor T') (Ku := ((modulePullback B S hS (pointHom u)).obj
        (sectionConormalSource X E Q))) (Kx := ((modulePullback B S hS (pointHom v)).obj
        ((modulePullback B S hS g).obj (sectionConormalSource X E Q))))
        (N := ((modulePullback B S hS (yonedaSpaceMap h)).obj
        ((modulePullback B S hS (pointHom u)).obj (sectionConormalSource X E Q))))
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫ eqToIso
        (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫ g =
        yonedaSpaceMap h ≫ pointHom u).symm) ≪≫ (modulePullbackCompIso B S hS (pointHom v)
        g).symm).inv.app (sectionConormalSource X E Q))
        (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom u)).obj
        (sectionConormalSource X E Q))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u)
        (sectionConormalSource X E Q) (isQuasicoherentOnSite_sectionConormalSource X E hE Q))).inv)
        ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
            (haveI : IsInvertible (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L := Q.invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom u) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T ((modulePullback B S hS (pointHom u)).obj (kernel Q.q))
          ((modulePullback B S hS (pointHom u)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u)
          (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom u)).obj (kernel Q.q)))
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom u)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T u) (inversePointReadingIso X T u Q.L).hom)) ≫
        (Stacks.Divisors.conormalSourceBaseChange ((BigFppfOver.toScheme B S hS).map h)
        (pointZariskiModule X E T u) (pointZariskiModule X' ((modulePullback B S hS g).obj E) T' v)
        (pointZariskiModuleTwoSpaceIso X E hE g u v h hvh) (sectionPointQuotient X E hE Q T u)
        (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T' v)
        (sectionPointQuotientTwoSpaceL X E hE g u v h hvh Q)
        (sectionPointQuotient_twoSpace_q X E hE g u v h hvh Q)).hom =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
        (sectionConormalSourceBaseChangeHom X E Q g)) ≫
            (haveI : IsInvertible (structureCommRings B S hS X')
              (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L :=
              (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T').Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T').map (modulePullbackTensorIso B S hS (pointHom v)
          (kernel (Q.baseChange g (Iso.refl _)).q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (pointHom v)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q))
          ((modulePullback B S hS (pointHom v)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom v)
          (kernel (Q.baseChange g (Iso.refl _)).q)
          (isQuasicoherentOnSite_kernel_q X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _))))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom v)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
          (-1)))).hom ≫ (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q)))
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))))).hom))
      (kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T' v) (inversePointReadingIso X' T' v
          (Q.baseChange g (Iso.refl _)).L).hom)) :=
  conormalSource_twoSpace_of X E hE g u v h hvh Q
    (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) =>
      (have : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          Q.L := Q.invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T ((modulePullback B S hS (pointHom x)).obj (kernel Q.q))
          ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)))
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
      (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom)))
    (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1) =>
      (have : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L := (Q.baseChange g
          (Iso.refl _)).invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))).hom ≫
          ((zariskiReadingTensorObjIso T ((modulePullback B S hS (pointHom x)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q))
          ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q)
          (isQuasicoherentOnSite_kernel_q X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _))))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
          (-1)))).hom ≫ (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q)))
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))))).hom))
      (kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T x) (inversePointReadingIso X' T x
          (Q.baseChange g (Iso.refl _)).L).hom)))
    (conormalSourcePointReading_baseChange X E hE Q u h hc)
    (conormalSourceReading_twoSpace X E hE g u v h hvh Q)

end AlgebraicGeometry.Space

end
