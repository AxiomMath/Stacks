module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsConormalBaseChangeIso

/-!
# Base change of the conormal isomorphism of Stacks 0B4I

Let `g : X' ⟶ X` be a morphism of algebraic spaces, `q : ℰ ⟶ ℒ` an invertible quotient with
section `σ` of `𝐏(ℰ) ⟶ X`, and `σ'` the section of `𝐏(g^*ℰ) ⟶ X'` of the base change
`g^*q`.  This file proves that the conormal isomorphism `Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_σ` of
Stacks 0B4I is compatible with base change along `g`, given the compatibility of the source
readings at the étale scheme points along the comparison maps of the points.

## Main results

* `AlgebraicGeometry.Space.ConormalChartSourceCompat`: the compatibility of the source readings
  at `u` and at `v` along `h`, for `v ≫ g = u ∘ h`.
* `AlgebraicGeometry.Space.zariskiReading_sectionConormal_baseChange_chart_of`: the base change
  of the conormal isomorphism read at a chart of the source.
* `AlgebraicGeometry.Space.sectionConormalIso_baseChange_of`: the base change of the conormal
  isomorphism, through families of source readings.

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
  {T T' : BigFppfOver B S hS} (u : yoneda.obj T ⟶ X.1) (v : yoneda.obj T' ⟶ X'.1) (h : T' ⟶ T)
  (hvh : v ≫ g.hom = yoneda.map h ≫ u)
  (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X)
  (σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
  (hσ' : σ' ≫ projectiveBundleπ X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' = 𝟙 X')
  (comm : σ' ≫ (projectiveBundleBaseChange X E hE hb g hb') = g ≫ σ)

/-- **The compatibility of the source readings along `h`** (for `v ≫ g = u ∘ h`): the readings
`s`, `θ`, `F` of a source `K` at `u` and `s'`, `θ'`, `F'` of a source `K'` at `v`, ending in the
conormal sheaves of the sections `k_u`, `k'_v` of the fibres, are compatible with `h^*`, the
comparison `h^*u^* ≅ v^*g^*`, the base-change map `sB : g^*K ⟶ K'` and the base-change map of
conormal sheaves along the square of sections. -/
structure ConormalChartSourceCompat {K : Modules.{u, u} B S hS X.1 X.2}
    (hK : K.IsQuasicoherentOnSite)
    {K' : Modules.{u, u} B S hS X'.1 X'.2} (sB : (modulePullback B S hS g).obj K ⟶ K')
    {a₁ a₂ : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    {b₁ b₂ : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (s : (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom u)).obj K) ⟶ a₁)
    (θ : a₁ ≅ a₂)
    (F : haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
      a₂ ≅ Stacks.Conormal.conormalSheaf (Z := (BigFppfOver.toScheme B S hS).obj T)
        (X := (BigFppfOver.toScheme B S hS).obj
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibre T u))
        ((BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T u)))
    (s' : (zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj K') ⟶ b₁)
    (θ' : b₁ ≅ b₂)
    (F' : haveI := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
           (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
      b₂ ≅ Stacks.Conormal.conormalSheaf (Z := (BigFppfOver.toScheme B S hS).obj T')
        (X := (BigFppfOver.toScheme B S hS).obj
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibre T' v))
        ((BigFppfOver.toScheme B S hS).map (sectionFibreLift X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v))) :
          Prop where
  /-- The compatibility of the source readings along `h`. -/
  eq : haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
    haveI := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
    (CategoryTheory.Functor.conormalGlueComparison
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
      (zariskiReadingFunctor T') (Ku := ((modulePullback B S hS (pointHom u)).obj K))
      (Kx := ((modulePullback B S hS (pointHom v)).obj ((modulePullback B S hS g).obj K)))
      (N := ((modulePullback B S hS (yonedaSpaceMap h)).obj
      ((modulePullback B S hS (pointHom u)).obj K)))
      ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom u) ≪≫ eqToIso
      (congrArg (modulePullback B S hS) (ObjectProperty.hom_ext _ hvh : pointHom v ≫
      g = yonedaSpaceMap h ≫ pointHom u).symm) ≪≫ (modulePullbackCompIso B S hS (pointHom v)
      g).symm).inv.app K) (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom u)).obj
      K) (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom u) K
      hK)).inv) ≫ (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map s ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map θ.hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map F.hom ≫
      (Stacks.Conormal.conormalBaseChangeMap
      (toScheme_map_sectionFibreLift_comp_sectionFibreBaseChangeComparison X E hE hb g hb' u v h
      hvh σ hσ σ' hσ' comm)) =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map sB) ≫ s' ≫
      θ'.hom ≫ F'.hom

/-- The base change of a glued conormal isomorphism at a chart of the source
(`zariskiReading_conormal_baseChange_chart`), with the compatibility of the source readings
stated as `ConormalChartSourceCompat`. -/
theorem zariskiReading_conormal_baseChange_chart_of_compat (hu : IsEtale B S hS u)
    (hv : IsEtale B S hS v)
    {K : Modules.{u, u} B S hS X.1 X.2} (hK : K.IsQuasicoherentOnSite)
    {K' : Modules.{u, u} B S hS X'.1 X'.2}
      (φ : K ⟶ (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2
      X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
            (φ' : K' ⟶ (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
            ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
    (sB : (modulePullback B S hS g).obj K ⟶ K')
    {a₁ a₂ : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    {b₁ b₂ : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (s : (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom u)).obj K) ⟶ a₁)
    (hs : IsIso s) (θ : a₁ ≅ a₂)
    (F : haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
      a₂ ≅ Stacks.Conormal.conormalSheaf (Z := (BigFppfOver.toScheme B S hS).obj T)
        (X := (BigFppfOver.toScheme B S hS).obj
          ((projectiveBundleSituation X E hE hb).relativeProjPoints.fibre T u))
        ((BigFppfOver.toScheme B S hS).map (sectionFibreLift X E hE hb σ hσ T u)))
    (s' : (zariskiReadingFunctor T').obj ((modulePullback B S hS (pointHom v)).obj K') ⟶ b₁)
    (hs' : IsIso s') (θ' : b₁ ≅ b₂)
    (F' : haveI := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
           (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
      b₂ ≅ Stacks.Conormal.conormalSheaf (Z := (BigFppfOver.toScheme B S hS).obj T')
        (X := (BigFppfOver.toScheme B S hS).obj
          ((projectiveBundleSituation X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          hb').relativeProjPoints.fibre T' v))
        ((BigFppfOver.toScheme B S hS).map (sectionFibreLift X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)))
    (hφu : haveI := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
      (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom u)).map φ) =
      (@asIso _ _ _ _ s hs ≪≫ θ ≪≫ F ≪≫ (zariskiReadingConormalIso (sectionFibreLift X E hE hb σ
        hσ T u)).symm ≪≫
        ((zariskiReadingFunctor T).mapIso (sectionConormalChartIso X E hE hb σ hσ T u
          hu)).symm).hom)
    (hφv : haveI := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map φ') =
      (@asIso _ _ _ _ s' hs' ≪≫ θ' ≪≫ F' ≪≫ (zariskiReadingConormalIso
        (sectionFibreLift X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v)).symm ≪≫
        ((zariskiReadingFunctor T').mapIso (sectionConormalChartIso X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle
          X E hE g) hb' σ' hσ' T' v hv)).symm).hom)
    (hpt : ConormalChartSourceCompat X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm hK sB s θ F s'
      θ' F') :
    (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
      ((modulePullback B S hS g).map φ)) ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
          (X := (modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
          (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
            (Y := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
            ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
            (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm)) =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map sB) ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map φ') :=
  zariskiReading_conormal_baseChange_chart X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm hu hv hK
    φ φ' sB s hs θ F s' hs' θ' F' hφu hφv hpt.eq

/-- **The base change of the conormal isomorphism of Stacks 0B4I at a chart of the source**
(through families `s`, `s'` of source readings): let `φ` read at the étale point `u` of `X` as
the chart isomorphism through `s`, and `φ'` at the étale point `v` of `X'` as the chart
isomorphism through `s'`, with `v ≫ g = u ∘ h`.  Given the compatibility `hpt` of the source
readings, Stacks 0B3V and the identifications of sections at `u` and at `v` along `h`, the
Zariski readings of `v^*(g^*φ ≫ (g^*𝒞_σ ⟶ 𝒞_{σ'}))` and of
`v^*((g^*(Ker q ⊗ ℒ^{-1}) ⟶ Ker q' ⊗ ℒ'^{-1}) ≫ φ')` agree. -/
theorem zariskiReading_sectionConormal_baseChange_chart_of (Q : InvertibleQuotient X E)
    (s : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
        X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))))) ⟶
      (letI := (sectionPointQuotient X E hE Q T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
            (kernel (sectionPointQuotient X E hE Q T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
            T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))) (hQ : projectiveBundleSectionsEquiv X
              E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (hu : IsEtale B S hS u) (hs : IsIso (s T u))
      (φ : (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
      X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
      (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
      (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property Q.L (-1)))) ⟶ (conormalModuleOfImmersion B S hS
      (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
    (hφ : (zariskiReadingFunctor T).map ((modulePullback B S hS (pointHom u)).map φ) =
      (sectionConormalReadingIsoOf X E hE Q hb σ hσ s hQ T u hu hs).hom)
    (s' : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
        X').property (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
          (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
        (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
        (Q.baseChange g (Iso.refl _)).L (-1))))) ⟶
      (letI := (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
            (kernel (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
            T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
              (Q.baseChange g (Iso.refl _)) T x).L (-1))))))
    (hQ' : projectiveBundleSectionsEquiv X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟨σ', hσ'⟩ = Quotient.mk
      _ (Q.baseChange g (Iso.refl _)))
    (hv : IsEtale B S hS v) (hs' : IsIso (s' T' v))
      (φ' : (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
      X').property (Q.baseChange g (Iso.refl _)).L :=
              (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
              (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
      (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
      (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
      (Q.baseChange g (Iso.refl _)).L (-1)))) ⟶ (conormalModuleOfImmersion B S hS
      (relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
    (hφ' : (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map φ') =
      (sectionConormalReadingIsoOf X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) hb' σ' hσ' s' hQ' T' v hv hs').hom)
    (hpt : ConormalChartSourceCompat X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q) (sectionConormalSourceBaseChangeHom X
      E Q g)
      (s T u) (sectionPointConormalIso X E hE hb σ hσ Q hQ T u) (sectionPointConormalFibreIso X E
        hE hb σ hσ T u) (s' T' v) (sectionPointConormalIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'
        (Q.baseChange g (Iso.refl _)) hQ' T' v) (sectionPointConormalFibreIso X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
        E hE g) hb' σ' hσ' T' v)) :
    (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
      ((modulePullback B S hS g).map φ)) ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
          (X := (modulePullback B S hS g).obj (conormalModuleOfImmersion B S hS
          (relativeProjSymmetricAlgebra X E hE hb).2 X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ))))
            (Y := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
            ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
            (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm)) =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map
        (X := (modulePullback B S hS g).obj (haveI : IsInvertible (structureCommRings B S hS X)
                                              (structureRingSheaf B S hS X).property
                                              Q.L := Q.invertible.toAlgebraicGeometry;
                                              (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1)))))
        (Y := (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
        X').property (Q.baseChange g (Iso.refl _)).L :=
                (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
                (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
        (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
        (Q.baseChange g (Iso.refl _)).L (-1))))) (sectionConormalSourceBaseChangeHom X E Q g)) ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS (pointHom v)).map φ') :=
  have := isClosedImmersion_sectionFibreLift X E hE hb σ hσ T u
  have := isClosedImmersion_sectionFibreLift X' ((modulePullback B S hS g).obj E)
    (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ' T' v
  zariskiReading_conormal_baseChange_chart_of_compat X E hE hb g hb' u v h hvh σ hσ σ' hσ' comm
    hu hv (isQuasicoherentOnSite_sectionConormalSource X E hE Q) φ φ'
      (sectionConormalSourceBaseChangeHom X E Q g) (s T u) hs (sectionPointConormalIso X E hE hb
      σ hσ Q hQ T u) (sectionPointConormalFibreIso X E hE hb σ hσ T u) (s' T' v) hs'
      (sectionPointConormalIso X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'
      (Q.baseChange g (Iso.refl _)) hQ' T' v) (sectionPointConormalFibreIso X'
      ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
      E hE g) hb' σ' hσ' T' v)
    (hφ.trans (congrArg Iso.hom (sectionConormalReadingIsoOf_eq X E hE Q hb σ hσ s hQ T u hu hs)))
    (hφ'.trans (congrArg Iso.hom
      (sectionConormalReadingIsoOf_eq X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) hb' σ' hσ' s' hQ' T' v hv hs'))) hpt

/-- The reading at a chart `U` of the inverse image of `f` along the point of `U`, when the
restriction of `f` to `U` has the reading `r`. -/
private theorem zariskiReading_map_modulePullback_map_of_chart_eq
    {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1)
    {M N : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N)
    {ψ : (chartModuleRestriction B S hS X U).obj M ⟶ (chartModuleRestriction B S hS X U).obj N}
    (hf : (chartModuleRestriction B S hS X U).map f = ψ)
    {r : (zariskiReadingFunctor ((SmallEtale.toOver B S hS X.1).obj U)).obj
      ((modulePullback B S hS (pointHom (T := (SmallEtale.toOver B S hS X.1).obj U) (X := X)
        U.1.hom)).obj M) ⟶ (zariskiReadingFunctor ((SmallEtale.toOver B S hS X.1).obj U)).obj
      ((modulePullback B S hS (pointHom (T := (SmallEtale.toOver B S hS X.1).obj U) (X := X)
        U.1.hom)).obj N)}
    (hψ : (zariskiReadingFunctor ((SmallEtale.toOver B S hS X.1).obj U)).map ψ = r) :
    (zariskiReadingFunctor ((SmallEtale.toOver B S hS X.1).obj U)).map
      ((modulePullback B S hS (pointHom (T := (SmallEtale.toOver B S hS X.1).obj U) (X := X)
        U.1.hom)).map f) = r :=
  (congrArg _ ((chartModuleRestriction_map_eq_modulePullback_map X U f).trans hf)).trans hψ

/-- **The base change of the conormal isomorphism of Stacks 0B4I on a chart of the source**
(through families `s`, `s'` of source readings): for isomorphisms `φ`, `φ'` restricting on every
étale chart to the chart isomorphisms through `s`, `s'`, and étale charts `V` of `X'`, `U` of `X`
with `V ≫ g = U ∘ h`, given the compatibility `hpt` of the source readings along `h`, the inverse
images along `V` of `g^*φ ≫ (g^*𝒞_σ ⟶ 𝒞_{σ'})` and of
`(g^*(Ker q ⊗ ℒ^{-1}) ⟶ Ker q' ⊗ ℒ'^{-1}) ≫ φ'` agree. -/
theorem modulePullback_map_sectionConormalIso_baseChange_chart_of (Q : InvertibleQuotient X E)
    (s : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
        X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))))) ⟶
      (letI := (sectionPointQuotient X E hE Q T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
            (kernel (sectionPointQuotient X E hE Q T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
            T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))) (hs : ∀ (T : BigFppfOver B S hS)
              (x : yoneda.obj T ⟶ X.1), IsEtale B S hS x → IsIso (s T x))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (s' : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
        X').property (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
          (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
        (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
        (Q.baseChange g (Iso.refl _)).L (-1))))) ⟶
      (letI := (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
            (kernel (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
            T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
              (Q.baseChange g (Iso.refl _)) T x).L (-1)))))) (hs' : ∀ (T : BigFppfOver B S hS)
              (x : yoneda.obj T ⟶ X'.1), IsEtale B S hS x → IsIso (s' T x))
    (hQ' : projectiveBundleSectionsEquiv X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟨σ', hσ'⟩ = Quotient.mk
      _ (Q.baseChange g (Iso.refl _)))
    (φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ)
    (hφ : ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
        (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ U).hom)
    (φ' : sectionConormalSource X' ((modulePullback B S hS g).obj E)
      (Q.baseChange g (Iso.refl _)) ≅ sectionConormalTarget X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')
    (hφ' : ∀ V : SmallEtale B S hS X'.1, (chartModuleRestriction B S hS X' V).map φ'.hom =
        (sectionConormalChartFamilyOf X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) hb' σ' hσ' s' hs' hQ' V).hom)
    (V : SmallEtale B S hS X'.1) (U : SmallEtale B S hS X.1)
    (h : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj U)
    (hvh : V.1.hom ≫ g.hom = yoneda.map h ≫ U.1.hom)
    (hpt : ConormalChartSourceCompat X E hE hb g hb' U.1.hom V.1.hom h hvh σ hσ σ' hσ' comm
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q)
      (sectionConormalSourceBaseChangeHom X E Q g) (s ((SmallEtale.toOver B S hS X.1).obj U)
        U.1.hom) (sectionPointConormalIso X E hE hb σ hσ Q hQ ((SmallEtale.toOver B S hS X.1).obj
        U) U.1.hom) (sectionPointConormalFibreIso X E hE hb σ hσ
        ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom)
        (s' ((SmallEtale.toOver B S hS X'.1).obj V) V.1.hom) (sectionPointConormalIso X'
        ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle X
        E hE g) hb' σ' hσ' (Q.baseChange g (Iso.refl _)) hQ' ((SmallEtale.toOver B S hS X'.1).obj
        V) V.1.hom) (sectionPointConormalFibreIso X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'
        ((SmallEtale.toOver B S hS X'.1).obj V) V.1.hom)) :
    (modulePullback B S hS (pointHom (T := (SmallEtale.toOver B S hS X'.1).obj V) (X := X')
      V.1.hom)).map
        (@CategoryStruct.comp _ _ ((modulePullback B S hS g).obj
          (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
          X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
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
            (X := (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
            X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
            (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))))
            (Y := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2
            X.2 σ.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ)))) φ.hom)
            (sectionConormalTargetBaseChangeHom X E hE hb σ hσ g hb' σ' hσ' comm)) =
      (modulePullback B S hS (pointHom (T := (SmallEtale.toOver B S hS X'.1).obj V)
        (X := X') V.1.hom)).map
        (@CategoryStruct.comp _ _ ((modulePullback B S hS g).obj
          (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
          X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L (-1)))))
          (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
          X').property (Q.baseChange g (Iso.refl _)).L :=
            (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
            (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
          (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
          (Q.baseChange g (Iso.refl _)).L (-1)))) (conormalModuleOfImmersion B S hS
          (relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')))
            (sectionConormalSourceBaseChangeHom X E Q g)
            (Iso.hom (X := (haveI : IsInvertible (structureCommRings B S hS X')
                             (structureRingSheaf B S hS X').property
                             (Q.baseChange g (Iso.refl _)).L :=
                             (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
                             (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
            (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
            (Q.baseChange g (Iso.refl _)).L (-1)))))
            (Y := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
            ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ'))))
            φ')) := by
  have e₁ := zariskiReading_map_modulePullback_map_of_chart_eq U φ.hom (hφ U)
    (zariskiReading_map_sectionConormalChartFamilyOf_hom X E hE Q hb σ hσ s hs hQ U)
  have e₂ := zariskiReading_map_modulePullback_map_of_chart_eq V φ'.hom (hφ' V)
    (zariskiReading_map_sectionConormalChartFamilyOf_hom X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
      (Q.baseChange g (Iso.refl _)) hb' σ' hσ' s' hs' hQ' V)
  have key := zariskiReading_sectionConormal_baseChange_chart_of X E hE hb g hb'
    (T := ((SmallEtale.toOver B S hS X.1).obj U))
    (T' := ((SmallEtale.toOver B S hS X'.1).obj V)) U.1.hom V.1.hom h hvh σ hσ σ' hσ' comm Q s hQ
      (isEtale_of_presheaf_etale B S hS U.2)
    (hs ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom (isEtale_of_presheaf_etale B S hS U.2))
      φ.hom e₁ s' hQ'
    (isEtale_of_presheaf_etale B S hS V.2) (hs' ((SmallEtale.toOver B S hS X'.1).obj V) V.1.hom
      (isEtale_of_presheaf_etale B S hS V.2))
    φ'.hom e₂ hpt
  have hN := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (pointHom (T := (SmallEtale.toOver B S hS X'.1).obj V) (X := X') V.1.hom) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g _
      (isQuasicoherentOnSite_sectionConormalSource X E hE Q))
  have key' := zariskiReading_map_injective (T := (SmallEtale.toOver B S hS X'.1).obj V) hN
    (((zariskiReadingFunctor _).map_comp _ _).trans
      (key.trans ((zariskiReadingFunctor _).map_comp _ _).symm))
  simp only [Functor.map_comp]
  exact key'

/-- **The base change of the conormal isomorphism of Stacks 0B4I** (through families `s`, `s'`
of source readings): for isomorphisms `φ : Ker(q) ⊗ ℒ^{⊗ -1} ≅ 𝒞_σ` and
`φ' : Ker(q') ⊗ ℒ'^{⊗ -1} ≅ 𝒞_{σ'}` restricting on every étale chart to the chart isomorphisms
through `s`, `s'`, given the compatibility `hpt` of the source readings along every comparison
`h` of étale charts `V ≫ g = U ∘ h`, the square of `g^*φ`, `φ'` and the base-change maps
`g^*(Ker q ⊗ ℒ^{-1}) ⟶ Ker q' ⊗ ℒ'^{-1}`, `g^*𝒞_σ ⟶ 𝒞_{σ'}` commutes. -/
theorem sectionConormalIso_baseChange_of (Q : InvertibleQuotient X E)
    (s : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
        X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property Q.L (-1))))) ⟶
      (letI := (sectionPointQuotient X E hE Q T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
            (kernel (sectionPointQuotient X E hE Q T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
            T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X E hE Q T x).L (-1)))))) (hs : ∀ (T : BigFppfOver B S hS)
              (x : yoneda.obj T ⟶ X.1), IsEtale B S hS x → IsIso (s T x))
    (hQ : projectiveBundleSectionsEquiv X E hE hb ⟨σ, hσ⟩ = Quotient.mk _ Q)
    (s' : (∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X'.1),
      (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj
        (haveI : IsInvertible (structureCommRings B S hS X') (structureRingSheaf B S hS
        X').property (Q.baseChange g (Iso.refl _)).L :=
          (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
          (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
        (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
        (Q.baseChange g (Iso.refl _)).L (-1))))) ⟶
      (letI := (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
        (Q.baseChange g (Iso.refl _)) T x).invertible;
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩).obj
            (kernel (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            (Q.baseChange g (Iso.refl _)) T x).q)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower ((BigFppfOver.toScheme B S hS).obj
            T).presheaf ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2
            (sectionPointQuotient X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
              (Q.baseChange g (Iso.refl _)) T x).L (-1)))))) (hs' : ∀ (T : BigFppfOver B S hS)
              (x : yoneda.obj T ⟶ X'.1), IsEtale B S hS x → IsIso (s' T x))
    (hQ' : projectiveBundleSectionsEquiv X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟨σ', hσ'⟩ = Quotient.mk
      _ (Q.baseChange g (Iso.refl _)))
    (φ : sectionConormalSource X E Q ≅ sectionConormalTarget X E hE hb σ hσ)
    (hφ : ∀ U : SmallEtale B S hS X.1, (chartModuleRestriction B S hS X U).map φ.hom =
        (sectionConormalChartFamilyOf X E hE Q hb σ hσ s hs hQ U).hom)
    (φ' : sectionConormalSource X' ((modulePullback B S hS g).obj E)
      (Q.baseChange g (Iso.refl _)) ≅ sectionConormalTarget X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')
    (hφ' : ∀ V : SmallEtale B S hS X'.1, (chartModuleRestriction B S hS X' V).map φ'.hom =
        (sectionConormalChartFamilyOf X' ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
          (Q.baseChange g (Iso.refl _)) hb' σ' hσ' s' hs' hQ' V).hom)
    (hpt : ∀ (V : SmallEtale B S hS X'.1) (U : SmallEtale B S hS X.1)
      (h : (SmallEtale.toOver B S hS X'.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj U)
      (hvh : V.1.hom ≫ g.hom = yoneda.map h ≫ U.1.hom),
      ConormalChartSourceCompat X E hE hb g hb' U.1.hom V.1.hom h hvh σ hσ σ' hσ' comm
        (isQuasicoherentOnSite_sectionConormalSource X E hE Q)
        (sectionConormalSourceBaseChangeHom X E Q g)
          (s ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom) (sectionPointConormalIso X E hE hb σ
          hσ Q hQ ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom) (sectionPointConormalFibreIso X
          E hE hb σ hσ ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom)
          (s' ((SmallEtale.toOver B S hS X'.1).obj V) V.1.hom) (sectionPointConormalIso X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle
          X E hE g) hb' σ' hσ' (Q.baseChange g (Iso.refl _)) hQ'
          ((SmallEtale.toOver B S hS X'.1).obj V) V.1.hom) (sectionPointConormalFibreIso X'
          ((modulePullback B S hS g).obj E) (isQuasicoherentOnSite_modulePullback_projectiveBundle
          X E hE g) hb' σ' hσ' ((SmallEtale.toOver B S hS X'.1).obj V) V.1.hom)) :
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
            (X := (haveI : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS
            X).property Q.L := Q.invertible.toAlgebraicGeometry; (MonoidalCategory.tensorObj
            (C := Modules.{u, u} B S hS X.1 X.2) (kernel Q.q)
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L (-1)))))
            (Y := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X E hE hb).2
            X.2 σ.hom
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
            X').property (Q.baseChange g (Iso.refl _)).L :=
              (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
              (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
            (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
            (Q.baseChange g (Iso.refl _)).L (-1)))) (conormalModuleOfImmersion B S hS
            (relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')))
            (sectionConormalSourceBaseChangeHom X E Q g)
            (Iso.hom (X := (haveI : IsInvertible (structureCommRings B S hS X')
                             (structureRingSheaf B S hS X').property
                             (Q.baseChange g (Iso.refl _)).L :=
                             (Q.baseChange g (Iso.refl _)).invertible.toAlgebraicGeometry;
                             (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS X'.1 X'.2)
            (kernel (Q.baseChange g (Iso.refl _)).q) (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X') (structureRingSheaf B S hS X').property
            (Q.baseChange g (Iso.refl _)).L (-1)))))
            (Y := (conormalModuleOfImmersion B S hS (relativeProjSymmetricAlgebra X'
            ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb').2 X'.2 σ'.hom
        (isImmersion_of_isClosedImmersion B S hS
          (isClosedImmersion_of_section_projectiveBundleπ X' ((modulePullback B S hS g).obj E)
            (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' σ' hσ')))) φ')) :=
  hom_ext_of_chart_factorization g fun V U h hvh =>
    modulePullback_map_sectionConormalIso_baseChange_chart_of X E hE hb g hb' σ hσ σ' hσ' comm Q s
      hs hQ s' hs' hQ' φ hφ φ' hφ' V U h hvh (hpt V U h hvh)

end AlgebraicGeometry.Space

end
