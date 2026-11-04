/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveMorFunctorsEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyOfIsPullback
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# `Isom_V(Y, X) ⟶ V` over a Noetherian affine base, from H-projective charts

Let `Y` and `X` be families of curves over a common Noetherian affine base `V`. Through every
point of `V` there is an affine étale chart `φ : U ⟶ V` along which both families are schemes,
H-projective over `U` (Stacks 0E6F, from the smooth local polarizations of Stacks 0DQ0:
`AlgebraicGeometry.C1590Private.exists_affine_etale_isPullback_isProjectiveMorphism` and
`AlgebraicGeometry.C1590Private.curvesSmoothLocallyPolarized`). Finitely many charts cover `V`;
the base change of `Isom_V(Y, X)` to each is `Isom_U(Y_U, X_U)` (Stacks 05Y4); if those are
quasi-compact, they jointly surject onto `Isom_V(Y, X)`, which is therefore a quasi-compact
algebraic space (Stacks 040W), and its morphism to the affine `V` is quasi-compact (Stacks 073B).

This is the step of the proof of Stacks 0DSQ that brings the quasi-compactness of the diagonal of
`Curves` down to families of curves which are H-projective schemes over a Noetherian affine base.

## Main results

* `AlgebraicGeometry.CurveFamily.isQuasiCompact_isomFunctorProjection_of_projectiveCharts`.

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **`Isom_V(Y, X) ⟶ V` over a Noetherian affine base, from the H-projective case.** Let `F` and
`G` be families of curves over a common Noetherian affine base `V`. Suppose that for all families
of curves `F'` and `G'` over a common Noetherian affine base whose total spaces are H-projective
schemes over it, `Isom(F', G')` is quasi-compact over the base (`hproj`). Then `Isom_V(F, G) ⟶ V`
is quasi-compact. -/
theorem isQuasiCompact_isomFunctorProjection_of_projectiveCharts
    (hproj : ∀ (F' G' : CurveFamily B hZ) (hb' : G'.base = F'.base),
      IsAffine ((𝒯).obj F'.base) → IsNoetherian ((𝒯).obj F'.base) →
      ∀ (Z₁ Z₂ : BigFppfOver B integerBase hZ) (q₁ : Z₁ ⟶ F'.base) (q₂ : Z₂ ⟶ F'.base),
        ∀ (e₁ : F'.total.obj ≅ yoneda.obj Z₁) (e₂ : G'.total.obj ≅ yoneda.obj Z₂),
        F'.toBase.hom = e₁.hom ≫ yoneda.map q₁ →
        G'.toBase.hom ≫ yoneda.map (eqToHom hb') = e₂.hom ≫ yoneda.map q₂ →
        IsProjectiveMorphism ((𝒯).map q₁) → IsProjectiveMorphism ((𝒯).map q₂) →
        Space.IsQuasiCompact B integerBase hZ
          (isomFunctorProjection F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb'))))
    (F G : CurveFamily B hZ) (hb : G.base = F.base)
    (haff : IsAffine ((𝒯).obj F.base)) (hnoeth : IsNoetherian ((𝒯).obj F.base)) :
    Space.IsQuasiCompact B integerBase hZ
      (isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))) := by
  classical
  set f := isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))
  have hV : IsAlgebraicSpace B integerBase hZ (yoneda.obj F.base) :=
    isAlgebraicSpace_yoneda B integerBase hZ F.base
  have halg : IsAlgebraicSpace B integerBase hZ
      (isomFunctor F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))).toFunctor :=
    C1590Private.curveIsomFunctorsAlgebraic_of_curveMorFunctorsAlgebraic B hZ
      (C1590Private.curveMorFunctorsAlgebraic_of_projectiveMorFunctorsBounded B hZ
        (C1590Private.projectiveMorFunctorsBounded_of_projectiveSpaceHilbertModelsBounded B hZ
          (C1590Private.projectiveSpaceHilbertModelsBounded B hZ))) F G hb
  let X : Bool → CurveFamily B hZ := fun b => Bool.rec G F b
  have hX : ∀ b, (X b).base = F.base := fun b => by cases b <;> simp [X, hb]
  choose U φ u hφ hU hu hch using fun s =>
    C1590Private.exists_affine_etale_isPullback_isProjectiveMorphism X hX
      (fun b => C1590Private.curvesSmoothLocallyPolarized B hZ (X b)) s
  have hopen : ∀ s, IsOpen (Set.range ((𝒯).map (φ s))) := fun s => by
    have := hφ s
    exact ((𝒯).map (φ s)).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s => Set.range ((𝒯).map (φ s)))
    hopen (fun s _ => Set.mem_iUnion.2 ⟨s, u s, hu s⟩)
  have hFiqc : ∀ s, Space.IsQuasiCompactSpace B integerBase hZ (pullback f (yoneda.map (φ s))) := by
    intro s
    have := hU s
    have := hφ s
    have : IsLocallyNoetherian ((𝒯).obj (U s)) :=
      LocallyOfFiniteType.isLocallyNoetherian ((𝒯).map (φ s))
    obtain ⟨Z₁, p₁, q₁, sq₁, hq₁⟩ := hch s true
    obtain ⟨Z₂, p₂, q₂, sq₂, hq₂⟩ := hch s false
    have hUn : IsNoetherian ((𝒯).obj (U s)) := { }
    have sq₁' : IsPullback p₁ (schemeSpaceMap q₁) F.toBase (schemeSpaceMap (φ s)) := by
      simpa [X, hX] using sq₁
    have sq₂' : IsPullback p₂ (schemeSpaceMap q₂) G.toBase
        (schemeSpaceMap (φ s ≫ eqToHom hb.symm)) := by
      simpa [X, hX] using sq₂
    let F' := C1590Private.curveFamilyOfIsPullback F (φ s) p₁ (schemeSpaceMap q₁) sq₁'
    let G' := C1590Private.curveFamilyOfIsPullback G (φ s ≫ eqToHom hb.symm) p₂
      (schemeSpaceMap q₂) sq₂'
    let φ' : F' ⟶ F := C1590Private.curveFamilyOfIsPullbackHom F (φ s) p₁ (schemeSpaceMap q₁) sq₁'
    let ψ' : G' ⟶ G := C1590Private.curveFamilyOfIsPullbackHom G (φ s ≫ eqToHom hb.symm) p₂
      (schemeSpaceMap q₂) sq₂'
    have hb' : G'.base = F'.base := rfl
    obtain ⟨g, hg⟩ := exists_isPullback_isomFunctorProjection_eqToHom φ' ψ' hb hb' (by
      show (φ s ≫ eqToHom hb.symm) ≫ eqToHom hb = 𝟙 _ ≫ φ s
      rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, Category.id_comp])
    have hqc' := hproj F' G' hb' (hU s) hUn Z₁ Z₂ q₁ q₂ (Iso.refl _) (Iso.refl _)
      (by simp [F']; rfl) (by simp [G']; rfl) hq₁ hq₂
    exact Space.isQuasiCompactSpace_of_iso B integerBase hZ hg.isoPullback
      (Space.isQuasiCompactSpace_source_of_isQuasiCompact B integerBase hZ
        (isAlgebraicSpace_yoneda B integerBase hZ (U s))
        (Space.isQuasiCompactSpace_yoneda_of_isAffine B integerBase hZ (U s) (hU s)) hqc')
  have hsurj : Space.IsJointlySurjective B integerBase hZ
      (fun j : t => pullback f (yoneda.map (φ j))) (fun j => pullback.fst f _) := by
    rw [Space.isJointlySurjective_iff]
    intro z
    obtain ⟨j, y, hy⟩ := Space.exists_pointsMap_yonedaMap_eq_of_jointly_surjective B integerBase
      hZ (fun j : t => φ j) (fun x => by
        obtain ⟨s, hs, y, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
        exact ⟨⟨s, hs⟩, y, hy⟩) (Space.pointsMap B integerBase hZ _ f z)
    obtain ⟨w, hw, -⟩ := Space.exists_points_of_isPullback B integerBase hZ
      (IsPullback.of_hasPullback f (yoneda.map (φ j))) z y hy.symm
    exact ⟨j, w, hw⟩
  exact Space.isQuasiCompact_of_isQuasiCompactSpace B integerBase hZ B.contains_terminal hV
    (Space.isAbsolutelyQuasiSeparated_yoneda_obj B integerBase hZ B.contains_terminal F.base
      inferInstance)
    (Space.isQuasiCompactSpace_of_finite_jointly_surjective B integerBase hZ
      (fun j : t => isAlgebraicSpace_pullback B integerBase hZ f (yoneda.map (φ j)) halg
        (isAlgebraicSpace_yoneda B integerBase hZ (U j)) hV)
      halg (fun j => pullback.fst f _) hsurj (fun j => hFiqc j)) f

end CurveFamily

end AlgebraicGeometry

end
