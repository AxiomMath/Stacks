module

public import
    StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackSquareCube
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingDerivedPullback

/-!
# Descending an object along a morphism of elementary distinguished squares

Let `p : W' ⟶ W` be a morphism of algebraic spaces and let `(U ⊆ W, V ⟶ W)` and
`(U' ⊆ W', V' ⟶ W')` be elementary distinguished squares, with intersections `P` and `P'`,
together with morphisms `pU : U' ⟶ U`, `pV : V' ⟶ V`, `pP : P' ⟶ P` making the resulting cube
commute.  Let `E` be an object of `D(𝒪_{W'})` whose restrictions to `U'` and `V'` are derived
pullbacks `LpU^* A` and `LpV^* B` of objects of `D(𝒪_U)` and `D(𝒪_V)`, and let
`c : A|_P ≅ B|_P` be an isomorphism whose derived pullback to `P'` is the identification of the
two restrictions of `E` to `P'`.  Then `A` and `B` are glued by an object `F` of `D(𝒪_W)` with
`Lp^* F ≅ E`.

This is the step of the source's proof of Stacks 0DKW at an elementary distinguished square
(the square of a stage of Situation 0DKU and its base change to the limit): the glued object
`F` is produced by the first assertion of Stacks 08HB at `W`
(`AlgebraicGeometry.Space.exists_glue_derivedPullback_eds`), and the comparison
`Lp^* F ⟶ E` by its second assertion at `W'`
(`AlgebraicGeometry.Space.exists_hom_derivedPullback_eds`), which is an isomorphism because it
is one on `U'` and on `V'`.  The source glues the adjoint map `F ⟶ Rp_* E` instead; glueing at
`W'` avoids the direct image.  The compatibility over the intersection is carried through the
cube by `AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_cube`.

## Main results

* `AlgebraicGeometry.Space.exists_glue_derivedPullback_iso_of_eds`.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Descending an object along a morphism of elementary distinguished squares.**  In the
situation of the module docstring, with `αU : LpU^* A ≅ E|_{U'}`, `αV : LpV^* B ≅ E|_{V'}` and
`c : A|_P ≅ B|_P` whose derived pullback to `P'` is `αV^{-1}|_{P'} ∘ αU|_{P'}` read through the
identifications of the faces of the cube (hypothesis `hc`), there is an object `F` of `D(𝒪_W)`
with `F|_U ≅ A`, `F|_V ≅ B` and `Lp^* F ≅ E`. -/
theorem exists_glue_derivedPullback_iso_of_eds
    {W W' : AlgebraicSpaces B S hS} {V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {Uo' : Subfunctor W'.1} {fV : V ⟶ W.1} {fV' : V' ⟶ W'.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hsq' : IsElementaryDistinguishedSquare B S hS W'.2 Uo' fV')
    (p : W' ⟶ W) (pU : edsOpen B S hS hsq' ⟶ edsOpen B S hS hsq)
    (pV : edsEtale B S hS hsq' ⟶ edsEtale B S hS hsq)
    (pP : edsInter B S hS hsq' ⟶ edsInter B S hS hsq)
    (hU : edsOpenHom B S hS hsq' ≫ p = pU ≫ edsOpenHom B S hS hsq)
    (hV : edsEtaleHom B S hS hsq' ≫ p = pV ≫ edsEtaleHom B S hS hsq)
    (hPU : edsFst B S hS hsq' ≫ pU = pP ≫ edsFst B S hS hsq)
    (hPV : edsSnd B S hS hsq' ≫ pV = pP ≫ edsSnd B S hS hsq)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))
    (A : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsOpen B S hS hsq))))
    (Bo : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (αU : (smallEtaleDerivedModulePullback B S hS pU).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq')).obj E)
    (αV : (smallEtaleDerivedModulePullback B S hS pV).obj Bo ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq')).obj E)
    (c : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).obj A ≅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq)).obj Bo)
    (hc : (smallEtaleDerivedModulePullback B S hS pP).map c.hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso (edsFst B S hS hsq') pU pP
          (edsFst B S hS hsq) hPU).hom.app A ≫
        (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq')).map αU.hom ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq')
          (edsEtaleHom B S hS hsq') (edsFst B S hS hsq') (edsOpenHom B S hS hsq')
          (isPullback_edsInter B S hS hsq').flip.w).hom.app E ≫
        (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq')).map αV.inv ≫
        ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq') pV pP
          (edsSnd B S hS hsq) hPV).inv.app Bo) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
      (_ : (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq)).obj F ≅ A)
      (_ : (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq)).obj F ≅ Bo),
      Nonempty ((smallEtaleDerivedModulePullback B S hS p).obj F ≅ E) := by
  obtain ⟨F, f, g, hfg⟩ := exists_glue_derivedPullback_eds hsq A Bo c
  refine ⟨F, f, g, ?_⟩
  let φU : (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS hsq')).obj
      ((smallEtaleDerivedModulePullback B S hS p).obj F) ⟶ (smallEtaleDerivedModulePullback B S hS
      (edsOpenHom B S hS hsq')).obj E :=
    ((DerivedPullbackComposition.canonical B S hS).squareIso (edsOpenHom B S hS hsq') p pU
        (edsOpenHom B S hS hsq) hU).inv.app F
        ≫ (smallEtaleDerivedModulePullback B S hS pU).map f.hom ≫ αU.hom
  let φV : (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq')).obj
      ((smallEtaleDerivedModulePullback B S hS p).obj F) ⟶
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq')).obj E :=
    ((DerivedPullbackComposition.canonical B S hS).squareIso (edsEtaleHom B S hS hsq') p pV
        (edsEtaleHom B S hS hsq) hV).inv.app F
        ≫ (smallEtaleDerivedModulePullback B S hS pV).map g.hom ≫ αV.hom
  -- the compatibility of `c` with `αU` and `αV`, solved for `αU`
  have hc' : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq')).map αU.hom
      ≫ ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq')
      (edsEtaleHom B S hS hsq') (edsFst B S hS hsq') (edsOpenHom B S hS hsq')
      (isPullback_edsInter B S hS hsq').flip.w).hom.app E =
      ((DerivedPullbackComposition.canonical B S hS).squareIso (edsFst B S hS hsq') pU pP
          (edsFst B S hS hsq) hPU).inv.app A
          ≫ (smallEtaleDerivedModulePullback B S hS pP).map c.hom
          ≫ ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq') pV pP
          (edsSnd B S hS hsq) hPV).hom.app Bo ≫
        (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq')).map αV.hom := by
    rw [hc]
    simp
  have hcube := (DerivedPullbackComposition.canonical B S hS).squareIso_cube (edsFst B S hS hsq')
      (edsSnd B S hS hsq')
    (edsOpenHom B S hS hsq') (edsEtaleHom B S hS hsq') (edsFst B S hS hsq) (edsSnd B S hS hsq)
    (edsOpenHom B S hS hsq) (edsEtaleHom B S hS hsq) p pU pV pP
    (isPullback_edsInter B S hS hsq').flip.w (isPullback_edsInter B S hS hsq).flip.w hU hV hPU hPV F
  have hagree : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq')).map φU
      ≫ ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq')
      (edsEtaleHom B S hS hsq') (edsFst B S hS hsq') (edsOpenHom B S hS hsq')
      (isPullback_edsInter B S hS hsq').flip.w).hom.app E =
      ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq')
          (edsEtaleHom B S hS hsq') (edsFst B S hS hsq') (edsOpenHom B S hS hsq')
          (isPullback_edsInter B S hS hsq').flip.w).hom.app
          ((smallEtaleDerivedModulePullback B S hS p).obj F)
          ≫ (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq')).map φV := by
    have e1 : (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq')).map φU
        ≫ ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq')
        (edsEtaleHom B S hS hsq') (edsFst B S hS hsq') (edsOpenHom B S hS hsq')
        (isPullback_edsInter B S hS hsq').flip.w).hom.app E =
        (smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq')).map
            (((DerivedPullbackComposition.canonical B S hS).squareIso
            (edsOpenHom B S hS hsq') p pU (edsOpenHom B S hS hsq) hU).inv.app F)
            ≫ ((DerivedPullbackComposition.canonical B S hS).squareIso (edsFst B S hS hsq') pU pP
            (edsFst B S hS hsq) hPU).inv.app ((smallEtaleDerivedModulePullback B S hS
            (edsOpenHom B S hS hsq)).obj F) ≫
          (smallEtaleDerivedModulePullback B S hS pP).map ((smallEtaleDerivedModulePullback B S hS
              (edsFst B S hS hsq)).map f.hom ≫ c.hom)
              ≫ ((DerivedPullbackComposition.canonical B S hS).squareIso
              (edsSnd B S hS hsq') pV pP (edsSnd B S hS hsq) hPV).hom.app Bo ≫
          (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq')).map αV.hom := by
      simp only [φU, Functor.map_comp, Category.assoc]
      rw [hc']
      have := ((DerivedPullbackComposition.canonical B S hS).squareIso (edsFst B S hS hsq') pU pP
        (edsFst B S hS hsq) hPU).inv.naturality f.hom
      simp only [Functor.comp_map] at this
      rw [reassoc_of% this]
    have e2 : (smallEtaleDerivedModulePullback B S hS pP).map
        ((smallEtaleDerivedModulePullback B S hS (edsFst B S hS hsq)).map f.hom ≫ c.hom)
        ≫ ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq') pV pP
        (edsSnd B S hS hsq) hPV).hom.app Bo =
        (smallEtaleDerivedModulePullback B S hS pP).map
            (((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq)
            (edsEtaleHom B S hS hsq) (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
            (isPullback_edsInter B S hS hsq).flip.w).hom.app F)
            ≫ ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq') pV pP
            (edsSnd B S hS hsq) hPV).hom.app ((smallEtaleDerivedModulePullback B S hS
            (edsEtaleHom B S hS hsq)).obj F) ≫
          (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS hsq')).map
              ((smallEtaleDerivedModulePullback B S hS pV).map g.hom) := by
      have := ((DerivedPullbackComposition.canonical B S hS).squareIso (edsSnd B S hS hsq') pV pP
        (edsSnd B S hS hsq) hPV).hom.naturality g.hom
      simp only [Functor.comp_map] at this
      rw [hfg, Functor.map_comp, Category.assoc, this]
    rw [e1, reassoc_of% e2, reassoc_of% hcube]
    simp only [φV, Functor.map_comp]
  obtain ⟨φ, hφU, hφV⟩ := exists_hom_derivedPullback_eds hsq' φU φV hagree
  have hφ : IsIso φ := isIso_of_isIso_derivedPullback_eds hsq' φ
    (by rw [hφU]; dsimp only [φU]; infer_instance) (by rw [hφV]; dsimp only [φV]; infer_instance)
  exact ⟨asIso φ⟩

end AlgebraicGeometry.Space

end
