module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCurveOverCompleteLocalProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeReflectsRepresentable
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# A family of curves over a complete local ring is a projective scheme

Let `A` be a complete Noetherian local ring and `F` a family of curves (Stacks 0D4Z) over
`Spec A`. Then the total space of `F` is the algebraic space of a scheme projective over `A`.

The family is an algebraic space over the big fppf site of `Spec(ℤ)` with a morphism to `Spec A`;
by Stacks 04SG it is the lower-shriek extension of an algebraic space `X` over the big fppf site
of `Spec A`. Properness of `X ⟶ Spec A` is that of the family (it does not depend on the base,
`AlgebraicGeometry.Space.isProper_relocalizeToYoneda_iff`), and the closed fibre of `X` is
representable with dimension at most one, because the closed fibre of the family is the family of
a proper curve over the residue field
(`AlgebraicGeometry.CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq`) and the lower-shriek
extension reflects representability
(`CategoryTheory.OverShriek.exists_left_eq_nonempty_iso_yoneda`). Stacks 0AE7 then makes `X`, hence
the family, a projective scheme.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_iso_schemeSpace_of_isAdicComplete`: the statement above.

## References

* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

section Relocalize

variable {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S} (h : B.obj hW ⟶ B.obj hS)

/-- The structure morphism of a lower-shriek extension is natural. -/
@[reassoc]
theorem relocalize_map_relocalizeToYoneda {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (φ : F ⟶ G) :
    (OverShriek.relocalizePresheafFunctor h).map φ ≫ OverShriek.relocalizeToYoneda h G =
      OverShriek.relocalizeToYoneda h F := by
  ext V x
  exact Over.OverMorphism.ext rfl

/-- The structure morphism of the lower-shriek extension of a representable presheaf, read through
`CategoryTheory.OverShriek.relocalizeYonedaIso`. -/
theorem relocalizeYonedaIso_hom_app_comp (V : BigFppfOver B W hW) :
    (OverShriek.relocalizeYonedaIso h).hom.app V ≫
        yoneda.map (Over.homMk V.hom : (Over.map h).obj V ⟶ Over.mk h) =
      OverShriek.relocalizeToYoneda h (yoneda.obj V) := by
  ext T p
  exact Over.OverMorphism.ext (Over.w p.1.2)

/-- Transporting `CategoryTheory.OverShriek.relocalizeYonedaIso` along an isomorphism `o` and a
morphism `t` with `o.hom ≫ t` the structure morphism gives the structure morphism of the
lower-shriek extension of a representable presheaf. -/
private theorem relocalizeYonedaIso_app_trans_comp {V : BigFppfOver B W hW}
    {U : BigFppfOver B S hS} (o : (Over.map h).obj V ≅ U) (t : U ⟶ Over.mk h)
    (ht : o.hom ≫ t = Over.homMk V.hom) :
    ((OverShriek.relocalizeYonedaIso h).app V ≪≫ yoneda.mapIso o).hom ≫ yoneda.map t =
      OverShriek.relocalizeToYoneda h (yoneda.obj V) := by
  rw [← relocalizeYonedaIso_hom_app_comp, ← ht]
  simp

end Relocalize

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (hA : B.Contains (Spec (.of A)))

/-- The structure morphism of `Spec A` to `Spec ℤ` in the site. -/
abbrev structureToIntegers : B.obj hA ⟶ B.obj hZ := (integerSiteObject B hZ hA).hom

/-- A family of curves over `Spec A`, read as an object of the category of Stacks 04SG: an
algebraic space over `Spec ℤ` with a morphism to `Spec A`. -/
def toSpacesOverSmallerBase (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hA) :
    SpacesOverSmallerBase B (Spec (.of A)) integerBase hA hZ (structureToIntegers A hA) :=
  ⟨Over.mk (F.toBaseYonedaOfEq hF), F.total.property⟩

omit [IsNoetherianRing A] in
/-- **The closed fibre of the algebraic space over `Spec A` underlying a family of curves has
dimension at most one.** Let `X` be an algebraic space over `Spec A` whose lower-shriek extension
is identified with the total space of a family of curves `F` over `Spec A`, compatibly with the
structure morphisms. Then the zeroth adic fibre of `X` is representable by a scheme of dimension
at most one: its extension is the total space of the closed fibre of `F`, which is the family of a
proper curve over the residue field. -/
theorem dimension_adicFibre_zero_le_one (F : CurveFamily B hZ)
    (hF : F.base = Over.mk (structureToIntegers (hZ := hZ) A hA))
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (e1 : (OverShriek.relocalizePresheafFunctor (structureToIntegers (hZ := hZ) A hA)).obj X.1 ≅
      F.total.obj)
    (he1 : e1.hom ≫ F.toBaseYonedaOfEq hF =
      OverShriek.relocalizeToYoneda (structureToIntegers (hZ := hZ) A hA) X.1) :
    Space.dimension B (Spec (.of A)) hA
      (Space.adicFibre A (maximalIdeal A) B hA (Space.contains_adicThickening A _ B hA)
        (Space.toYonedaId B (Spec (.of A)) hA X.1) 0)
      (Space.isAlgebraicSpace_adicFibre A _ B hA (Space.contains_adicThickening A _ B hA) X.2
        (Space.toYonedaId B (Spec (.of A)) hA X.1) 0) ≤ 1 := by
  -- `Λ` of the defining square of the adic fibre
  have sq := (IsPullback.of_hasPullback (Space.toYonedaId B (Spec (.of A)) hA X.1)
    (yoneda.map (Space.adicThickeningMap A (maximalIdeal A) B hA
      (Space.contains_adicThickening A _ B hA) 0))).map
    (OverShriek.relocalizePresheafFunctor (structureToIntegers (hZ := hZ) A hA))
  -- the closed fibre of `F`
  let t0' : integerSiteObject B hZ (Space.contains_adicThickening A (maximalIdeal A) B hA 0) ⟶
      Over.mk (structureToIntegers (hZ := hZ) A hA) :=
    Over.homMk (ObjectProperty.homMk (adicThickeningι A (maximalIdeal A) 0))
      (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  -- the three identifications of the cospan
  let e2 := asIso (OverShriek.relocalizeToYoneda (structureToIntegers (hZ := hZ) A hA)
    (yoneda.obj (Over.mk (𝟙 (B.obj hA)))))
  let overIso0 : (Over.map (structureToIntegers (hZ := hZ) A hA)).obj
      (Space.adicThickeningObject A (maximalIdeal A) B hA
        (Space.contains_adicThickening A _ B hA) 0) ≅
      integerSiteObject B hZ (Space.contains_adicThickening A (maximalIdeal A) B hA 0) :=
    Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  let e3 := (OverShriek.relocalizeYonedaIso (structureToIntegers (hZ := hZ) A hA)).app
      (Space.adicThickeningObject A (maximalIdeal A) B hA
        (Space.contains_adicThickening A _ B hA) 0) ≪≫ yoneda.mapIso overIso0
  have cf : (OverShriek.relocalizePresheafFunctor (structureToIntegers (hZ := hZ) A hA)).map
      (Space.toYonedaId B (Spec (.of A)) hA X.1) ≫ e2.hom = e1.hom ≫ F.toBaseYonedaOfEq hF := by
    rw [he1]
    exact relocalize_map_relocalizeToYoneda _ _
  let toG : (Over.map (structureToIntegers (hZ := hZ) A hA)).obj
      (Space.adicThickeningObject A (maximalIdeal A) B hA
        (Space.contains_adicThickening A _ B hA) 0) ⟶
      Over.mk (structureToIntegers (hZ := hZ) A hA) :=
    Over.homMk (Space.adicThickeningObject A (maximalIdeal A) B hA
        (Space.contains_adicThickening A _ B hA) 0).hom
  have hmap0 : overIso0.hom ≫ t0' = toG := Over.OverMorphism.ext (Category.id_comp _)
  have cg : (OverShriek.relocalizePresheafFunctor (structureToIntegers (hZ := hZ) A hA)).map
      (yoneda.map (Space.adicThickeningMap A (maximalIdeal A) B hA
        (Space.contains_adicThickening A _ B hA) 0)) ≫ e2.hom = e3.hom ≫ yoneda.map t0' := by
    exact (relocalize_map_relocalizeToYoneda _ _).trans
      (relocalizeYonedaIso_app_trans_comp _ overIso0 t0' hmap0).symm
  have sq' := sq.of_iso (Iso.refl _) e1 e3 e2 (Category.id_comp _).symm (Category.id_comp _).symm
    cf cg
  have sq0 := AlgebraicSpaces.isPullback_hom B integerBase hZ
    ((F.ofBaseEq hF).isPullback_pullbackHom t0')
  -- `Λ` of the adic fibre is the total space of the closed fibre of `F`
  have eΛ := sq'.isoIsPullback _ _ sq0
  -- the closed fibre of `F` is the family of a proper curve over the residue field
  have : (maximalIdeal A ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]
    infer_instance
  let : Field (A ⧸ maximalIdeal A ^ (0 + 1)) := Ideal.Quotient.field _
  obtain ⟨X0, hX0p, hdim0, ⟨φ⟩⟩ :=
    exists_iso_curveFamilyOfScheme_of_base_eq (K := A ⧸ maximalIdeal A ^ (0 + 1))
      (Space.contains_adicThickening A (maximalIdeal A) B hA 0) ((F.ofBaseEq hF).pullback t0') rfl
  have := hX0p
  let eTot : ((F.ofBaseEq hF).pullback t0').total ≅
      (curveFamilyOfScheme X0 B hZ (Space.contains_adicThickening A (maximalIdeal A) B hA 0)
        hdim0).total :=
    { hom := φ.hom.totalMap
      inv := φ.inv.totalMap
      hom_inv_id := by rw [← comp_totalMap, φ.hom_inv_id, id_totalMap]
      inv_hom_id := by rw [← comp_totalMap, φ.inv_hom_id, id_totalMap] }
  let eT : (OverShriek.relocalizePresheafFunctor (structureToIntegers (hZ := hZ) A hA)).obj
        (Space.adicFibre A (maximalIdeal A) B hA (Space.contains_adicThickening A _ B hA)
          (Space.toYonedaId B (Spec (.of A)) hA X.1) 0) ≅
      yoneda.obj (integerSiteObject B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
        X0.hom (Space.contains_adicThickening A (maximalIdeal A) B hA 0))) :=
    eΛ ≪≫ (ObjectProperty.ι _).mapIso eTot
  obtain ⟨T', hT', ⟨eZ⟩⟩ := OverShriek.exists_left_eq_nonempty_iso_yoneda _ eT
  have hX : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj T' = X0.left :=
    congrArg (fun t => t.obj) hT'
  rwa [Space.dimension_eq_of_iso B (Spec (.of A)) hA _ (isAlgebraicSpace_yoneda B _ hA T') eZ,
    Space.dimension_yoneda_eq_topologicalKrullDim, hX]

/-- **A family of curves over a complete Noetherian local ring is a projective scheme.** Let
`A` be a complete Noetherian local ring and `F` a family of curves over `Spec A`. Then the total
space of `F` is the algebraic space of a scheme `Y`, H-projective over `A`, compatibly with the
structure morphisms. -/
theorem exists_iso_schemeSpace_of_isAdicComplete [IsAdicComplete (maximalIdeal A) A]
    (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hA) :
    ∃ (Y : Scheme.{u}) (hY : B.Contains Y) (fY : Y ⟶ Spec (.of A)), IsProjectiveMorphism fY ∧
      ∃ e : F.total.obj ≅ yoneda.obj (integerSiteObject B hZ hY),
        e.hom ≫ yoneda.map (integerSiteMap B hZ hY hA fY) = F.toBaseYonedaOfEq hF := by
  set g := structureToIntegers (hZ := hZ) A hA
  set E := spacesOverSmallerBaseEquivalence B (Spec (.of A)) integerBase hA hZ g
  set Fy := toSpacesOverSmallerBase A hA F hF
  set X := E.inverse.obj Fy
  set ε := E.counitIso.app Fy
  set Λ := OverShriek.relocalizePresheafFunctor g
  -- the identification of `Λ X` with the total space of `F`
  let e1 : Λ.obj X.1 ≅ F.total.obj :=
    ((spacesOverSmallerBaseFunctorForgetIso B (Spec (.of A)) integerBase hA hZ g).app X).symm ≪≫
      ((ObjectProperty.ι _ ⋙ Over.forget _).mapIso ε)
  have hF' : F.base = Over.mk g := hF
  have he1 : e1.hom ≫ F.toBaseYonedaOfEq hF' = OverShriek.relocalizeToYoneda g X.1 := by
    rw [← Space.relocalizeToYoneda_eq B (Spec (.of A)) integerBase hA hZ g X]
    simp only [e1]
    exact congrArg (_ ≫ ·) (Over.w ε.hom.hom)
  -- properness of `X` over `Spec A`
  set fX := Space.toYonedaId B (Spec (.of A)) hA X.1
  have hP : Space.IsProper B (Spec (.of A)) hA fX := by
    refine (Space.isProper_relocalizeToYoneda_iff B (Spec (.of A)) integerBase hA hZ g X.1
      X.2).1 ?_
    rw [← he1, Space.isProper_isIso_comp_iff B integerBase hZ e1.hom]
    exact (F.ofBaseEq hF).proper
  -- the closed fibre of `X` has dimension at most one
  have hdim : Space.dimension B (Spec (.of A)) hA
      (Space.adicFibre A (maximalIdeal A) B hA (Space.contains_adicThickening A _ B hA) fX 0)
      (Space.isAlgebraicSpace_adicFibre A _ B hA (Space.contains_adicThickening A _ B hA) X.2
        fX 0) ≤ 1 :=
    dimension_adicFibre_zero_le_one A hA F hF' X e1 he1
  obtain ⟨Y, hY, fY, -, hproj, eX, heX⟩ :=
    Space.exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one A B hA
      (fun hX hY fX fY hpX hsY hfY g hg hgc =>
        Space.existsUnique_adicFibreMap_eq A (maximalIdeal A) B hA
          (Space.contains_adicThickening A _ B hA) hX hY fX fY hpX hsY hfY g hg hgc)
      X.2 fX hP hdim
  -- transport back along `Λ`
  let overIso : (Over.map g).obj (siteObject B (Spec (.of A)) hA hY fY) ≅
      integerSiteObject B hZ hY :=
    Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  refine ⟨Y, hY, fY, hproj, e1.symm ≪≫ Λ.mapIso eX ≪≫
    (OverShriek.relocalizeYonedaIso g).app _ ≪≫ yoneda.mapIso overIso, ?_⟩
  let t' : integerSiteObject B hZ hY ⟶ Over.mk g :=
    Over.homMk (ObjectProperty.homMk fY)
      (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  have hmap : overIso.hom ≫ t' =
      (Over.homMk (siteObject B (Spec (.of A)) hA hY fY).hom :
        (Over.map g).obj (siteObject B (Spec (.of A)) hA hY fY) ⟶ Over.mk g) :=
    Over.OverMorphism.ext (Category.id_comp _)
  calc _ = e1.inv ≫ Λ.map eX.hom ≫
        (((OverShriek.relocalizeYonedaIso g).app _ ≪≫ yoneda.mapIso overIso).hom ≫
          yoneda.map t') := by
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
        rfl
    _ = e1.inv ≫ OverShriek.relocalizeToYoneda g X.1 := by
        rw [relocalizeYonedaIso_app_trans_comp _ overIso t' hmap,
          relocalize_map_relocalizeToYoneda]
    _ = F.toBaseYonedaOfEq hF' := by
        rw [← he1, Iso.inv_hom_id_assoc]

end CurveFamily

end AlgebraicGeometry

end
