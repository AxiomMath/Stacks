module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChangeTwoSpaceSourceSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalFibreTwoSpaceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorMonoidal

/-!
# The conormal isomorphism of Stacks 0B4I commutes with base change

Let `ℰ` be a quasi-coherent module on an algebraic space `X`, `σ` a section of `π : 𝐏(ℰ) ⟶ X`
corresponding to the invertible quotient `q : ℰ ⟶ ℒ`, and `g : X' ⟶ X` with `σ'` the section of
`𝐏(g^*ℰ) ⟶ X'` of the base-changed quotient.  This file proves that the isomorphisms
`Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_{σ(X)/𝐏(ℰ)}` of the conormal clause of Stacks 0B4I over `X` and over `X'`
are compatible with the base-change maps along `g`.

## Main results

* `AlgebraicGeometry.Space.sectionConormalIso_baseChange`: the base-change square of the conormal
  isomorphisms commutes.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
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
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)
  {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
  (σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
  (hσ' : σ' ≫ projectiveBundleπ X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' = 𝟙 X')
  (comm : σ' ≫ (projectiveBundleBaseChange X E hE hb g hb') = g ≫ σ)

/-- The compatibility of the source readings of the conormal clause of Stacks 0B4I along a
comparison `h` of scheme points `v ≫ g = u ∘ h`, for the explicit families of source readings. -/
theorem conormalChartSourceCompat_sectionConormal (Q : InvertibleQuotient X E)
    {T T' : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1) (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T)
    (hvh : v ≫ g.hom = yoneda.map h ≫ u)
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (hQ' : projectiveBundleSectionsEquiv X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟨σ', hσ'⟩ =
        Quotient.mk _ (Q.baseChange g (Iso.refl _))) :
    ConormalChartSourceCompat X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q)
      (sectionConormalSourceBaseChangeHom X E Q g) ((fun (T : BigFppfOver B S hS)
          (x : yoneda.obj T ⟶ X.1) =>
      (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
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
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)))
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
      (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom))) T u)
      (sectionPointConormalIso X E hE hb σ hσ Q hQ T u)
      (sectionPointConormalFibreIso X E hE hb σ hσ T u) ((fun (T : BigFppfOver B S hS)
          (x : yoneda.obj T ⟶ X'.1) =>
      (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1))).hom ≫ ((zariskiReadingTensorObjIso T
          ((modulePullback B S hS (pointHom x)).obj (kernel (Q.baseChange g (Iso.refl _)).q))
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q) (isQuasicoherentOnSite_kernel_q X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
          E hE g) (Q.baseChange g (Iso.refl _))))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
          (-1)))).hom ≫ (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q))) ((zariskiReadingFunctor T).obj
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1))))).hom))
      (kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T x) (inversePointReadingIso X' T x
          (Q.baseChange g (Iso.refl _)).L).hom))) T' v)
      (sectionPointConormalIso X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'
          (Q.baseChange g (Iso.refl _)) hQ' T' v)
      (sectionPointConormalFibreIso X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v) :=
  conormalChartSourceCompat_of_twoSpace X E hE g u v h hvh Q hb hb' σ hσ σ' hσ' comm hQ hQ'
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
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)))
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
          (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1))).hom ≫ ((zariskiReadingTensorObjIso T
          ((modulePullback B S hS (pointHom x)).obj (kernel (Q.baseChange g (Iso.refl _)).q))
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q) (isQuasicoherentOnSite_kernel_q X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
          E hE g) (Q.baseChange g (Iso.refl _))))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
          (-1)))).hom ≫ (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q))) ((zariskiReadingFunctor T).obj
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1))))).hom))
      (kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T x) (inversePointReadingIso X' T x
          (Q.baseChange g (Iso.refl _)).L).hom)))
    (pointFibreProjectiveBundleIso_hom_comp_projectiveBundleBaseChange_twoSpace X E u g v h hvh hE
        hb hb')
    (conormalSource_twoSpace X E hE g u v h hvh Q (zariskiReadingPullbackTensorSquare h))

/-- **The conormal isomorphism of Stacks 0B4I commutes with base change**: for `g : X' ⟶ X`, the
section `σ'` of `𝐏(g^*ℰ) ⟶ X'` with `σ' ≫ (𝐏(g^*ℰ) ⟶ 𝐏(ℰ)) = g ≫ σ`, and the isomorphisms
`φ : Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_σ`, `φ' : Ker(q') ⊗ ℒ'^{⊗ -1} ≅ 𝒞_{σ'}` of the conormal clause (for `q`
and its base change `q' = g^*q`), the square of `g^*φ`, `φ'` and the base-change maps
`g^*(Ker q ⊗ ℒ^{-1}) ⟶ Ker q' ⊗ ℒ'^{-1}`, `g^*𝒞_σ ⟶ 𝒞_{σ'}` commutes. -/
theorem sectionConormalIso_baseChange (Q : InvertibleQuotient X E)
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (hQ' : projectiveBundleSectionsEquiv X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟨σ', hσ'⟩ =
        Quotient.mk _ (Q.baseChange g (Iso.refl _)))
    (φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ)
    (hφ : ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
        (sectionConormalChartFamilyOf X E hE Q hb σ hσ
        (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) =>
      (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
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
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)))
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
        (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ U).hom)
    (φ' : sectionConormalSource X' ((modulePullback B S hS g).obj E) (Q.baseChange g (Iso.refl _)) ≅
        sectionConormalTarget X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')
    (hφ' : ∀ V : SmallEtale B S hS X'.1, (chartModuleRestriction B S hS X' V).map φ'.hom =
        (sectionConormalChartFamilyOf X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) hb' σ' hσ'
        (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1) =>
      (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1))).hom ≫ ((zariskiReadingTensorObjIso T
          ((modulePullback B S hS (pointHom x)).obj (kernel (Q.baseChange g (Iso.refl _)).q))
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q) (isQuasicoherentOnSite_kernel_q X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
          E hE g) (Q.baseChange g (Iso.refl _))))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
          (-1)))).hom ≫ (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q))) ((zariskiReadingFunctor T).obj
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1))))).hom))
      (kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T x) (inversePointReadingIso X' T x
          (Q.baseChange g (Iso.refl _)).L).hom)))
        (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X'
            ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle
            X E hE g) (Q.baseChange g (Iso.refl _)) T x hx) hQ' V).hom)
    :
    (@CategoryStruct.comp _ _ ((modulePullback B S hS g).obj
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
           Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
           (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
           (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
           (structureRingSheaf B S hS X).property Q.L (-1))))) ((modulePullback B S hS g).obj
           (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
              (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
              ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')))
              ((modulePullback B S hS g).map
              (X :=
              (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
                 X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
                 (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
                 (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                 (structureRingSheaf B S hS X).property Q.L (-1))))) (Y :=
                 (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2 X.2
                 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) φ.hom)
              (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm)) =
              (@CategoryStruct.comp _ _ ((modulePullback B S hS g).obj
              (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
                 X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
                 (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
                 (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
                 (structureRingSheaf B S hS X).property Q.L (-1)))))
                 (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
                    X').property (Q.baseChange g (Iso.refl _)).L := (Q.baseChange g
                    (Iso.refl _)).invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
                    (C := Modules.{u, u} B S hS X'.1 X'.2) (kernel (Q.baseChange g (Iso.refl _)).q)
                    (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
                    (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))))
                    (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
                    ((modulePullback B S hS g).obj E)
                    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2
                    σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')))
              (sectionConormalSourceBaseChangeHom X E Q g) (Iso.hom (X :=
              (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
                 X').property (Q.baseChange g (Iso.refl _)).L := (Q.baseChange g
                 (Iso.refl _)).invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
                 (C := Modules.{u, u} B S hS X'.1 X'.2) (kernel (Q.baseChange g (Iso.refl _)).q)
                 (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
                 (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1)))))
                 (Y := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
                 ((modulePullback B S hS g).obj E)
                 (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
              φ')) :=
  sectionConormalIso_baseChange_of X E hE hb g hb' σ hσ σ' hσ' comm Q
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
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)))
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
    (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ
    (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1) =>
      (have : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry
      (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
          (iC := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
      ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1))).hom ≫ ((zariskiReadingTensorObjIso T
          ((modulePullback B S hS (pointHom x)).obj (kernel (Q.baseChange g (Iso.refl _)).q))
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1)))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (kernel (Q.baseChange g (Iso.refl _)).q) (isQuasicoherentOnSite_kernel_q X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
          E hE g) (Q.baseChange g (Iso.refl _))))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
          (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
          (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
          (-1)))).hom ≫ (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
          (kernel (Q.baseChange g (Iso.refl _)).q))) ((zariskiReadingFunctor T).obj
          ((modulePullback B S hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1))))).hom))
      (kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) T x) (inversePointReadingIso X' T x
          (Q.baseChange g (Iso.refl _)).L).hom)))
    (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T x hx) hQ' φ hφ φ' hφ'
    fun V U h hvh => conormalChartSourceCompat_sectionConormal X E hE hb g hb' σ hσ σ' hσ' comm Q
      (T := (SmallEtale.toOver B S hS X.1).obj U) (T' := (SmallEtale.toOver B S hS X'.1).obj V)
      U.1.hom V.1.hom h hvh hQ hQ'

end AlgebraicGeometry.Space

end
