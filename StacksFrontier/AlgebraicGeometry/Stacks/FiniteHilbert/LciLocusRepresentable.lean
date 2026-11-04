module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLciLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusCoverProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusExists
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusIso
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusOpen

/-!
# The inclusion of the local complete intersection locus is an open immersion

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
which is representable by algebraic spaces, flat and locally of finite presentation, and let `d`
be a natural number. This file proves the representability clauses of **Stacks 06CL** at those
hypotheses: the inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` of the local complete intersection locus
of Stacks 06CJ is representable — every base change of it along a scheme-valued point of
`ℋ_d(𝒳/𝒴)` is represented by an open subscheme of the base — and an open immersion.

Flatness and local finite presentation of `F` are spelled in the written-out form of Stacks 03YK
at flatness and at local finite presentation of morphisms of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.hasOpenLciLocus`: every scheme-valued point of
  `ℋ_d(𝒳/𝒴)` cuts out an open subscheme of its base, over which its image lies in the local
  complete intersection locus.
* `AlgebraicGeometry.Stack.exists_isOpenImmersion_representing_lciFiniteHilbertInclusion_of_flat`:
  **Stacks 06CL**, the inclusion is representable, by an open subscheme of the base.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_lciFiniteHilbertInclusion_of_flat`:
  **Stacks 06CL**, the inclusion is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isOpenImmersion_lciFiniteHilbertInclusion_of_flat`: **Stacks 06CL**,
  the inclusion is an open immersion.

The stack-in-groupoids clause of Stacks 06CL is
`AlgebraicGeometry.Stack.isStackInGroupoids_lciFiniteHilbertCategory_of_flat` in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusStack`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 05X8](https://stacks.math.columbia.edu/tag/05X8)
* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

/-- Given data exhibiting the relative map of a quintuple `Ξ` of `ℋ_d(𝒳/𝒴)`, there is an open
subscheme `V` of its base such that, for every morphism `φ : Ξ' ⟶ Ξ` of quintuples, the base
object of `Ξ'` read over the base of `Ξ` through `φ` factors through `V` exactly when `Ξ'` lies in
the local complete intersection locus. -/
private theorem exists_isOpenImmersion_forall_lciLocus_hom
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (Q : Object B S hS 𝒳 𝒴 F d) (D : RelativeMapData Q) :
    ∃ V : BigFppfOver B Q.U.left.1 Q.U.left.2, IsOpenImmersion V.hom.hom ∧
      ∀ (P : Object B S hS 𝒳 𝒴 F d) (φ : P ⟶ Q),
        Nonempty ((Over.mk φ.f.left : BigFppfOver B Q.U.left.1 Q.U.left.2) ⟶ V) ↔
          lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P := by
  have hqflat : Space.IsFlat B Q.U.left.1 Q.U.left.2
      (Space.toYonedaId B Q.U.left.1 Q.U.left.2 D.Xy) :=
    (Space.holdsOnEveryEtaleChart_algebraicSpaceMap_iff B S hS
        (@_root_.AlgebraicGeometry.Flat.{u}) Q.U D.Xy D.isAlgebraicSpace).mp
      (hFflat Q.U D.y D.y_comp D.Xy D.isAlgebraicSpace ⟨D.e⟩)
  have hqlfp : Space.IsLocallyOfFinitePresentation B Q.U.left.1 Q.U.left.2
      (Space.toYonedaId B Q.U.left.1 Q.U.left.2 D.Xy) :=
    (Space.holdsOnEveryEtaleChart_algebraicSpaceMap_iff B S hS
        (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) Q.U D.Xy
        D.isAlgebraicSpace).mp
      (hFlfp Q.U D.y D.y_comp D.Xy D.isAlgebraicSpace ⟨D.e⟩)
  obtain ⟨V, s, hs, hsprop⟩ :=
    Space.exists_isOpenImmersion_comp_iff_isUnramified_and_isLocalCompleteIntersection_baseChange
      B Q.U.left.1 Q.U.left.2
      (isAlgebraicSpace_yoneda B Q.U.left.1 Q.U.left.2 Q.coverOver) D.isAlgebraicSpace
      Q.baseOver D.map.hom
      (Space.toYonedaId B Q.U.left.1 Q.U.left.2 (yoneda.obj Q.coverOver))
      (Space.toYonedaId B Q.U.left.1 Q.U.left.2 D.Xy)
      (eq_toYonedaId B Q.U.left.1 Q.U.left.2 _)
      Q.isFlat_toYonedaId_coverOver Q.isLocallyOfFinitePresentation_toYonedaId_coverOver
      Q.isClosedMorphism_toYonedaId_coverOver hqflat hqlfp
  have hw : s.left = V.hom := (Category.comp_id s.left).symm.trans (Over.w s)
  refine ⟨V, by rwa [← hw], fun P φ => ?_⟩
  have hiso := RelativeMapData.isIso_restrictYonedaHom_coverComparison φ
  have hR (R : MorphismProperty Scheme.{u}) :
      Space.HoldsOnEveryEtaleChart B P.U.left.1 P.U.left.2 R
          (RelativeMapData.ofHom φ D).map.hom ↔
        Space.HoldsOnEveryEtaleChart B Q.U.left.1 Q.U.left.2 R
          (Space.baseChangeOverBase B Q.U.left.1 Q.U.left.2 D.map.hom
            (Space.toYonedaId B Q.U.left.1 Q.U.left.2 (yoneda.obj Q.coverOver))
            (Space.toYonedaId B Q.U.left.1 Q.U.left.2 D.Xy)
            (eq_toYonedaId B Q.U.left.1 Q.U.left.2 _)
            (yoneda.map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 (Over.mk φ.f.left)))) := by
    rw [RelativeMapData.map_hom_ofHom φ D]
    exact (Space.holdsOnEveryEtaleChart_iso_comp_iff B P.U.left.1 P.U.left.2 _ _ _).trans
      (Space.holdsOnEveryEtaleChart_relocalizeRestrict_iff_baseChangeOverBase
        B Q.U.left.1 P.U.left.1 Q.U.left.2 P.U.left.2 φ.f.left R D.map.hom
        (fun Z => OverShriek.subsingleton_yoneda_obj_mkId Z) _ _
        (eq_toYonedaId B Q.U.left.1 Q.U.left.2 _)
        (yoneda.map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 (Over.mk φ.f.left))))
  refine Iff.trans ⟨fun ⟨t⟩ => ⟨t, (Over.mkIdTerminal (X := Q.U.left)).hom_ext _ _⟩,
    fun ⟨t, _⟩ => ⟨t⟩⟩ ((hsprop (Over.mk φ.f.left)
      (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 (Over.mk φ.f.left))).trans
    ((and_congr (hR _).symm (hR _).symm).trans (lciLocus_iff (RelativeMapData.ofHom φ D)).symm))

/-- For a 1-morphism `F` representable by algebraic spaces, flat and locally of finite
presentation, every scheme-valued point of `ℋ_d(𝒳/𝒴)` cuts out an open subscheme of its base
through which an object of the big fppf site of that base maps exactly when its image under the
point lies in the local complete intersection locus. -/
theorem hasOpenLciLocus (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom) :
    HasOpenLciLocus B S hS 𝒳 𝒴 F d := by
  intro U y hy
  obtain ⟨Q, hQ⟩ : ∃ Q : Object B S hS 𝒳 𝒴 F d, Q = y.obj (Over.mk (𝟙 U.left)) := ⟨_, rfl⟩
  have hbase : Q.U = U := by
    rw [hQ]
    exact (Functor.congr_obj hy (Over.mk (𝟙 U.left))).trans
      (PresheafOfCategories.over_mk_eq U (Category.id_comp U.hom))
  subst hbase
  obtain ⟨D⟩ := nonempty_relativeMapData Q hFrep
  obtain ⟨V, hV, hVprop⟩ := exists_isOpenImmersion_forall_lciLocus_hom hFflat hFlfp Q D
  refine ⟨V, hV, fun T => ?_⟩
  have hTl : (y.obj T).U.left = T.left := congrArg Over.left (Functor.congr_obj hy T)
  have hbaseMap : (y.map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T)).f =
      eqToHom (Functor.congr_obj hy T) ≫
        (Over.map Q.U.hom).map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T) ≫
        eqToHom (Functor.congr_obj hy (Over.mk (𝟙 Q.U.left))).symm :=
    Functor.congr_hom hy (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T)
  have hunitMap : (eqToHom hQ.symm : y.obj (Over.mk (𝟙 Q.U.left)) ⟶ Q).f =
      eqToHom (congrArg Object.U hQ.symm) :=
    eqToHom_map (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F) (d := d)) hQ.symm
  have hfull : (y.map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T) ≫ eqToHom hQ.symm).f =
      (eqToHom (Functor.congr_obj hy T) ≫
            (Over.map Q.U.hom).map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T) ≫
          eqToHom (Functor.congr_obj hy (Over.mk (𝟙 Q.U.left))).symm) ≫
        eqToHom (congrArg Object.U hQ.symm) := by
    show (y.map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T)).f ≫
      (eqToHom hQ.symm : y.obj (Over.mk (𝟙 Q.U.left)) ⟶ Q).f = _
    rw [hbaseMap, hunitMap]
    rfl
  have hm : eqToHom hTl ≫ T.hom =
      (y.map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T) ≫ eqToHom hQ.symm).f.left :=
    (((congrArg (fun ψ : (y.obj T).U ⟶ Q.U => ψ.left) hfull).trans
        (Over.left_eqToHom_conj (Functor.congr_obj hy T)
          ((Over.map Q.U.hom).map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T))
          (Functor.congr_obj hy (Over.mk (𝟙 Q.U.left))).symm
          (congrArg Object.U hQ.symm))).trans
      (congrArg (fun k : T.left ⟶ Q.U.left => eqToHom hTl ≫ k)
        (Category.comp_id T.hom))).symm
  refine Iff.trans ?_ (hVprop (y.obj T)
    (y.map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T) ≫ eqToHom hQ.symm))
  have e : (Over.mk (y.map (Space.toTerminalHom B Q.U.left.1 Q.U.left.2 T) ≫
        eqToHom hQ.symm).f.left : BigFppfOver B Q.U.left.1 Q.U.left.2) ≅ T :=
    Over.isoMk (eqToIso hTl) hm
  exact ⟨fun ⟨t⟩ => ⟨e.hom ≫ t⟩, fun ⟨t⟩ => ⟨e.inv ≫ t⟩⟩

end FiniteHilbert

/-- The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of the local complete intersection locus is
representable: every 2-fibre product of it with a scheme-valued point of `ℋ_d(𝒳/𝒴)` is
represented by an object of the big fppf site of the base which is an open subscheme of it, namely
the open subscheme cut out by the locus. This is "representable" in the sense of Stacks 04ST, by a
scheme. -/
@[stacks 06CL "the inclusion ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴) is representable, by an open subscheme \
of the base"]
theorem exists_isOpenImmersion_representing_lciFiniteHilbertInclusion_of_flat
    (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).obj),
      y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).p = Over.map U.hom →
      ∃ V : BigFppfOver B U.left.1 U.left.2, IsOpenImmersion V.hom.hom ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p y
            (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).toFunctor)
          (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p) :=
  exists_isOpenImmersion_representing_lciFiniteHilbertInclusion hFrep hFflat hFlfp
    FiniteHilbert.isClosedUnderIsomorphisms_lciLocus
    (FiniteHilbert.hasOpenLciLocus hFrep hFflat hFlfp)

/-- The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of the local complete intersection locus is
representable by algebraic spaces, the representing algebraic space of a base change being the
open subscheme of the base cut out by the locus. -/
@[stacks 06CL "the inclusion ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴) is representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_lciFiniteHilbertInclusion_of_flat
    (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom) :
    IsRepresentableByAlgebraicSpaces B S hS
      (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)) :=
  isRepresentableByAlgebraicSpaces_lciFiniteHilbertInclusion hFrep hFflat hFlfp
    FiniteHilbert.isClosedUnderIsomorphisms_lciLocus
    (FiniteHilbert.hasOpenLciLocus hFrep hFflat hFlfp)

/-- The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of the local complete intersection locus is an
open immersion: every algebraic space representing a base change of it along a scheme-valued
point of `ℋ_d(𝒳/𝒴)` has open immersion structural morphism, read as a morphism of algebraic
spaces over `S`. This is the condition of Stacks 04XB at `AlgebraicGeometry.Space.IsOpenImmersion`,
written out. -/
@[stacks 06CL "the inclusion ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴) is an open immersion"]
theorem isOpenImmersion_lciFiniteHilbertInclusion_of_flat
    (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFflat : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsFlat B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom)
    (hFlfp : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).obj),
      y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p y
            (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).toFunctor)
          (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsOpenImmersion B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom :=
  isOpenImmersion_lciFiniteHilbertInclusion hFrep hFflat hFlfp
    FiniteHilbert.isClosedUnderIsomorphisms_lciLocus
    (FiniteHilbert.hasOpenLciLocus hFrep hFflat hFlfp)

end AlgebraicGeometry.Stack

end
