module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsClassification
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChangeSquare

/-!
# The conormal clause of Stacks 0B4I

Let `X` be an algebraic space, `ℰ` a quasi-coherent `𝒪_X`-module and `σ` a section of
`π : 𝐏(ℰ) ⟶ X` corresponding to the invertible quotient `q : ℰ ⟶ ℒ`.  This file states the
conormal clause of Stacks 0B4I: there is a canonical isomorphism
`Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_{σ(X)/𝐏(ℰ)}`, and it is compatible with base change along every
`g : X' ⟶ X`.  The bijection, the closed immersion and the base change of the bijection are
`AlgebraicGeometry.Space.projectiveBundle_sections_invertibleQuotients`.

## Main results

* `AlgebraicGeometry.Space.projectiveBundleSectionsEquiv_baseChange_mk`: a section `σ'` of
  `𝐏(g^*ℰ) ⟶ X'` over the section `σ` of `q` corresponds to `g^*q`.
* `AlgebraicGeometry.Space.projectiveBundle_sectionConormalIso`: Stacks 0B4I for the conormal
  isomorphism and its base change.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
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

/-- A section `σ'` of `𝐏(g^*ℰ) ⟶ X'` lying over the section `σ` of `𝐏(ℰ) ⟶ X` of the invertible
quotient `q` corresponds to the base change `g^*q`. -/
theorem projectiveBundleSectionsEquiv_baseChange_mk {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))
    (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
    (σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
    (hσ' : σ' ≫ projectiveBundleπ X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' = 𝟙 X')
    (comm : σ' ≫ (projectiveBundleBaseChange X E hE hb g hb') = g ≫ σ) (Q : InvertibleQuotient X E)
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q) :
    projectiveBundleSectionsEquiv X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟨σ', hσ'⟩ =
      Quotient.mk _ (Q.baseChange g (Iso.refl _)) :=
  (((projectiveBundle_sections_invertibleQuotients X E hE hb).2.2 X' g hb').2 ⟨σ, hσ⟩ ⟨σ', hσ'⟩
    comm).trans (congrArg (invertibleQuotientBaseChangeClass g (Iso.refl _)) hQ)

/-- **Stacks 0B4I, the conormal isomorphism and its base change.**  For a section `σ` of
`𝐏(ℰ) ⟶ X` corresponding to `q : ℰ ⟶ ℒ` there is a unique `Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_{σ(X)/𝐏(ℰ)}`
restricting on every étale chart to the chart isomorphism of Stacks 0B3V; along `g : X' ⟶ X` with
`σ'` over `σ`, these isomorphisms for `q` and `g^*q` commute with the base-change maps. -/
@[stacks 0B4I "the canonical isomorphism Ker(E -> L) tensor L^{-1} = conormal sheaf of sigma(X) in \
P(E), and its compatibility with base change"]
theorem projectiveBundle_sectionConormalIso :
    (∀ (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
        (Q : InvertibleQuotient X E)
        (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q),
      ∃! φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ,
        ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
          (sectionConormalChartFamilyOf X E hE Q hb σ hσ
            (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) =>
        haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
            Q.L := Q.invertible.toAlgebraicGeometry
        (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj
            T).Modules) (iC := Scheme.Modules.instCategory)
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
            (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
        ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x) (kernel Q.q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫ ((zariskiReadingTensorObjIso T
            ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)) ((modulePullback B S hS
            (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S
            hS X) (structureRingSheaf B S hS X).property Q.L (-1)))
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
        (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom))
            (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ U).hom) ∧
    (∀ (X' : AlgebraicSpaces B S hS) (g : X' ⟶ X)
        (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))
        (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙
            X)
        (σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
        (hσ' : σ' ≫ projectiveBundleπ X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' = 𝟙 X')
        (comm : σ' ≫ (projectiveBundleBaseChange X E hE hb g hb') = g ≫ σ)
        (Q : InvertibleQuotient X E)
        (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
        (φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ)
        (hφ : ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
            (sectionConormalChartFamilyOf X E hE Q hb σ hσ
            (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1) =>
          (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
              Q.L := Q.invertible.toAlgebraicGeometry
          (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj
              T).Modules) (iC := Scheme.Modules.instCategory)
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
              (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
          ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x) (kernel Q.q)
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1))).hom ≫ ((zariskiReadingTensorObjIso T
              ((modulePullback B S hS (pointHom x)).obj (kernel Q.q)) ((modulePullback B S hS
              (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B
              S hS X) (structureRingSheaf B S hS X).property Q.L (-1)))
              (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
              (kernel Q.q) (isQuasicoherentOnSite_kernel_q X E hE Q))
              (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x)
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1))
              (isQuasicoherentOnSite_invertibleTensorPower X Q.L (-1)))).hom ≫
              (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
              ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (kernel
              Q.q))) ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
              (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L (-1))))).hom))
          (kernelPointReadingHom X E hE Q T x) (inversePointReadingIso X T x Q.L).hom)))
            (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X E hE Q T x hx) hQ U).hom)
        (φ' : sectionConormalSource X' ((modulePullback B S hS g).obj E) (Q.baseChange g (Iso.refl
            _)) ≅ sectionConormalTarget X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')
        (hφ' : ∀ V : SmallEtale B S hS X'.1, (chartModuleRestriction B S hS X' V).map φ'.hom =
            (sectionConormalChartFamilyOf X' ((modulePullback B S hS g).obj E)
                (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) (Q.baseChange g
                (Iso.refl _)) hb' σ' hσ'
            (fun (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1) =>
          (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
              X').property (Q.baseChange g (Iso.refl _)).L := (Q.baseChange g (Iso.refl
              _)).invertible.toAlgebraicGeometry
          (CategoryTheory.Functor.compBifunctorMap (𝒞 := ((BigFppfOver.toScheme B S hS).obj
              T).Modules) (iC := Scheme.Modules.instCategory)
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
              (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)
          ((zariskiReadingFunctor T).map (modulePullbackTensorIso B S hS (pointHom x) (kernel
              (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
              (structureCommRings B S hS X') (structureRingSheaf B S hS X').property (Q.baseChange g
              (Iso.refl _)).L (-1))).hom ≫ ((zariskiReadingTensorObjIso T ((modulePullback B S hS
              (pointHom x)).obj (kernel (Q.baseChange g (Iso.refl _)).q)) ((modulePullback B S hS
              (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B
              S hS X') (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L
              (-1))) (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom
              x) (kernel (Q.baseChange g (Iso.refl _)).q) (isQuasicoherentOnSite_kernel_q X'
              ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) (Q.baseChange g
              (Iso.refl _)))) (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
              (pointHom x) (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS
              X') (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1))
              (isQuasicoherentOnSite_invertibleTensorPower X' (Q.baseChange g (Iso.refl _)).L
              (-1)))).hom ≫ (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
              ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (kernel
              (Q.baseChange g (Iso.refl _)).q))) ((zariskiReadingFunctor T).obj ((modulePullback B S
              hS (pointHom x)).obj (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings
              B S hS X') (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L
              (-1))))).hom))
          (kernelPointReadingHom X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) (Q.baseChange g
              (Iso.refl _)) T x) (inversePointReadingIso X' T x (Q.baseChange g (Iso.refl
              _)).L).hom)))
            (fun T x hx => isIso_conormalSourcePointReading_of_isEtale X' ((modulePullback B S hS
                g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
                (Q.baseChange g (Iso.refl _)) T x hx) (projectiveBundleSectionsEquiv_baseChange_mk X
                E hE hb g hb' σ hσ σ' hσ' comm Q hQ) V).hom),
      (@CategoryStruct.comp _ _ ((modulePullback B S hS g).obj
          (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
              Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj (C := Modules.{u,
              u} B S hS X.1 X.2) (kernel Q.q) (Stacks.SheafOfModules.Invertible.tensorPower
              (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L (-1)))))
              ((modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
              (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
          (isImmersion_of_isClosedImmersion B S hS
            (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
                (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X' ((modulePullback
                B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
                hb').2 X'.2 σ'.hom
          (isImmersion_of_isClosedImmersion B S hS
            (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
                (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')))
                ((modulePullback B S hS g).map (X :=
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
                    X').property (Q.baseChange g (Iso.refl _)).L := (Q.baseChange g (Iso.refl
                    _)).invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj (C :=
                    Modules.{u, u} B S hS X'.1 X'.2) (kernel (Q.baseChange g (Iso.refl _)).q)
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
                    X').property (Q.baseChange g (Iso.refl _)).L := (Q.baseChange g (Iso.refl
                    _)).invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj (C :=
                    Modules.{u, u} B S hS X'.1 X'.2) (kernel (Q.baseChange g (Iso.refl _)).q)
                    (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X')
                    (structureRingSheaf B S hS X').property (Q.baseChange g (Iso.refl _)).L (-1)))))
                    (Y := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
                    ((modulePullback B S hS g).obj E)
                    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2
                    σ'.hom
          (isImmersion_of_isClosedImmersion B S hS
            (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
                (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
                φ'))) :=
  ⟨fun σ hσ Q hQ => existsUnique_sectionConormalIso X E hE Q hb σ hσ
      (fun h => zariskiReadingPullbackTensorSquare h) hQ,
    fun _ g hb' σ hσ σ' hσ' comm Q hQ φ hφ φ' hφ' =>
      sectionConormalIso_baseChange X E hE hb g hb' σ hσ σ' hσ' comm Q hQ
        (projectiveBundleSectionsEquiv_baseChange_mk X E hE hb g hb' σ hσ σ' hσ' comm Q hQ)
        φ hφ φ' hφ'⟩

end AlgebraicGeometry.Space

end
