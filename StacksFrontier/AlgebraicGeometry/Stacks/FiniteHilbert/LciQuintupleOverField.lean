module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiniteRegularSliceOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RegularImmersionFollowedByEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.NonemptyChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMapFromRepresentingSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusChoice
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointOfObject

/-!
# A positive-degree object of the local complete intersection locus over a field

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
which is representable by algebraic spaces, surjective and locally of finite presentation, let `U`
be an object of the site whose underlying scheme is the spectrum of a field, and let `y` be an
object of `𝒴` over `U`. This file produces a degree `d ≥ 1` and an object `(U, Z, y, x, α)` of the
relative finite Hilbert category `ℋ_d(𝒳/𝒴)` which lies in the local complete intersection locus
of Stacks 06CJ.

These are the **second through ninth steps of the proof of Stacks 06DA**, the first step being the
reduction to a field object, which is `AlgebraicGeometry.Stack.IsSurjectiveOnObjects`.

The construction runs as follows.

*The fibre.* The 2-Yoneda lemma turns `y` into a scheme-valued point `(Sch/U)_{fppf} ⟶ 𝒴`
together with a vertical comparison morphism
(`CategoryTheory.Functor.exists_slicePoint`), and representability of `F` supplies an algebraic
space `X_y` over `U` representing the 2-fibre product of `F` with that point.

*The chart.* Surjectivity and local finite presentation of `F` make `X_y` nonempty over `U` and
give it an étale chart `T` whose underlying scheme is nonempty and locally of finite presentation
over the field; this is
`AlgebraicGeometry.Space.exists_nonempty_etaleChart_locallyOfFinitePresentation`.

*The slice.* A nonempty scheme locally of finite presentation over a field carries a regular
immersion `i : Z ⟶ T` whose source is finite locally free of positive degree over the field
(`Stacks.AlgebraicGeometry.exists_isRegularImmersion_isFiniteLocallyFreeOfRank_of_field`, Stacks
045U, 0570 and 00PJ). Its source is contained in the site because a monomorphism cannot raise the
size past a strong prelimit cutoff
(`AlgebraicGeometry.BigFppfSite.contains_of_mono`, Stacks 000R (8)), so `Z` is an object of the
site over `U`.

*The quintuple.* The composite `Z ⟶ T ⟶ X_y` is unramified and a local complete intersection
morphism of algebraic spaces
(`AlgebraicGeometry.Space.isUnramified_yoneda_map_comp_of_isRegularImmersion` and its Koszul
counterpart), and the inverse of the construction of Stacks 06CK
(`AlgebraicGeometry.Stack.exists_relativeMap_eq`) names it by an object `x` of `𝒳` over `Z`
together with a comparison isomorphism. Those assemble into the quintuple, and the data just used
assembles into a `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData` for it whose relative map
is that composite; membership of the locus follows because it may be tested on a single datum,
which is `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_iff`.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.exists_lciLocus_object_of_isFieldObject`: the quintuple.

## Implementation notes

Surjectivity and local finite presentation of `F` are taken in the written-out form of
Stacks 03YK: a condition on the structural morphism, read as a morphism of algebraic spaces over
`S` by the forward functor of Stacks 04SG, of every algebraic space representing the base change
of `F` along a scheme-valued point of `𝒴`. Flatness of `F`, the remaining standing hypothesis of
the source's section, is **not** needed: the only place the source uses it is the Cohen-Macaulay
locus of the chart over the base, and a morphism to the spectrum of a field is flat anyway, which
is why
`Stacks.AlgebraicGeometry.exists_isRegularImmersion_isFiniteLocallyFreeOfRank_of_field` does not
ask for it.

The cover of the quintuple is the slice `Z` read as an object of the big fppf site of `S` through
`CategoryTheory.Over.map U.hom`; its structure morphism to `U` is
`CategoryTheory.Functor.structHom`, so that the cover read back over `U`
(`AlgebraicGeometry.Stack.FiniteHilbert.Object.coverOver`) is the object of the site of `U` the
construction started from, and the comparison isomorphism supplied by Stacks 06CK is an admissible
field of the data without transport.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 00PJ](https://stacks.math.columbia.edu/tag/00PJ)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
-/

@[expose] public section

open CategoryTheory

open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack.FiniteHilbert

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- **The second through ninth steps of the proof of Stacks 06DA.** For a 1-morphism `F` of stacks
in groupoids which is representable by algebraic spaces, surjective and locally of finite
presentation, every object `y` of `𝒴` over an object `U` of the big fppf site whose underlying
scheme is the spectrum of a field is the object of `𝒴` of an object of the local complete
intersection locus `ℋ_{d,lci}(𝒳/𝒴)` for some degree `d ≥ 1`, over that same `U`. -/
theorem exists_lciLocus_object_of_isFieldObject
    (hFrep : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFsurj : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj),
      y ⋙ 𝒴.toBasedCategory.p = Over.map U.hom →
      ∀ (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hP : IsAlgebraicSpace B U.left.1 U.left.2 P),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p y
            F.toFunctor) (presheafOfCategories (P ⋙ typeToCat)).p) →
        Space.IsSurjective B S hS (algebraicSpaceMap B S hS U
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
    (U : BigFppfOver B S hS) (hU : IsFieldObject B S hS U)
    (y : 𝒴.toBasedCategory.obj) (hy : 𝒴.toBasedCategory.p.obj y = U) :
    ∃ (d : ℕ) (_ : 0 < d) (P : Object B S hS 𝒳 𝒴 F d),
      lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P ∧ P.y = y := by
  obtain ⟨k, hk, ⟨ek⟩⟩ := hU
  let : Field k := hk
  have hfib : 𝒴.toBasedCategory.p.IsFibered :=
    𝒴.isStackInGroupoids.isFiberedInGroupoids.isFibered
  -- the scheme-valued point of `𝒴` extending `y`, by the 2-Yoneda lemma
  set yp : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.toBasedCategory.obj :=
    Functor.slicePointOfObject 𝒴.toBasedCategory.p U y hy with hypdef
  have hypcomp : yp ⋙ 𝒴.toBasedCategory.p = Over.map U.hom :=
    Functor.slicePointOfObject_comp 𝒴.toBasedCategory.p U y hy
  set yUnit : yp.obj (Over.mk (𝟙 U.left)) ⟶ y :=
    Functor.slicePointUnit 𝒴.toBasedCategory.p U y hy with hyunitdef
  have hyUnit : 𝒴.toBasedCategory.p.IsHomLift (𝟙 U) yUnit :=
    Functor.isHomLift_slicePointUnit 𝒴.toBasedCategory.p U y hy
  -- the fibre `X_y`, by representability of `F`
  obtain ⟨Xy, hXy, ⟨e⟩⟩ := hFrep U yp hypcomp
  -- `U` is nonempty, being the spectrum of a field
  have hUne : Nonempty ((BigFppfOver.toScheme B S hS).obj U) :=
    ⟨ek.inv.base (Classical.choice (inferInstance : Nonempty (Spec (.of k))))⟩
  -- a nonempty étale chart of `X_y`, locally of finite presentation over `U`
  obtain ⟨T, φ, hφet, hTne, hTlfp⟩ :=
    Space.exists_nonempty_etaleChart_locallyOfFinitePresentation B S hS U Xy hXy
      (hFsurj U yp hypcomp Xy hXy ⟨e⟩) (hFlfp U yp hypcomp Xy hXy ⟨e⟩) hUne
  have : LocallyOfFinitePresentation (B.inclusion.map T.hom) := hTlfp
  -- the regular slice of the chart, finite locally free of positive degree over the field
  obtain ⟨d, hd, Z, i, hiimm, hreg, hflf⟩ :=
    Stacks.AlgebraicGeometry.exists_isRegularImmersion_isFiniteLocallyFreeOfRank_of_field k
      (B.inclusion.map T.hom ≫ ek.hom) hTne
  have := hiimm
  -- the slice is an object of the site over `U`
  have hZcont : B.Contains Z := B.contains_of_mono i T.left.2
  set Zu : BigFppfOver B U.left.1 U.left.2 :=
    Over.mk (ObjectProperty.homMk (X := B.obj hZcont) (Y := U.left)
      (i ≫ B.inclusion.map T.hom)) with hZudef
  set iu : Zu ⟶ T := Over.homMk (ObjectProperty.homMk (X := B.obj hZcont) (Y := T.left) i)
    (by apply ObjectProperty.hom_ext; rfl) with hiudef
  have : AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B U.left.1 U.left.2).map iu) := hiimm
  -- the composite `Z ⟶ T ⟶ X_y` is unramified and a local complete intersection morphism
  have hunram : Space.IsUnramified B U.left.1 U.left.2 (yoneda.map iu ≫ φ) :=
    Space.isUnramified_yoneda_map_comp_of_isRegularImmersion B U.left.1 U.left.2 hXy iu φ hφet
  have hlci : Space.IsLocalCompleteIntersection B U.left.1 U.left.2 (yoneda.map iu ≫ φ) :=
    Space.isLocalCompleteIntersection_yoneda_map_comp_of_isRegularImmersion B U.left.1 U.left.2
      hXy iu hreg φ hφet
  -- the pair `(x, α)` naming that composite, by the inverse of Stacks 06CK
  obtain ⟨x, hx, α, hα, hmapeq⟩ :=
    exists_relativeMap_eq (F := F) (U := U) (y := yp) (e := e) hXy Zu
      (ObjectProperty.homMk (yoneda.map iu ≫ φ))
  -- the cover is finite locally free of degree `d` over `U`
  have hflf' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (i ≫ B.inclusion.map T.hom) d := by
    have h := Stacks.Morphisms.isFiniteLocallyFreeOfRank_postcomp ek.symm
      (i ≫ B.inclusion.map T.hom ≫ ek.hom) hflf
    simpa using h
  -- verticality of the identification of the quintuple
  have hαinv : 𝒴.toBasedCategory.p.IsHomLift
      (𝟙 ((Over.map U.hom).obj Zu)) α.inv :=
    IsHomLift.lift_id_inv 𝒴.toBasedCategory.p _ α
  have hmapToMkId := Functor.isHomLift_map_toMkId 𝒴.toBasedCategory.p U yp hypcomp Zu
  have hright : 𝒴.toBasedCategory.p.IsHomLift (Functor.structHom U Zu)
      (yp.map (Functor.toMkId U Zu) ≫ yUnit) :=
    IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p (Functor.structHom U Zu)
      (yp.map (Functor.toMkId U Zu)) U yUnit
  have hαover : 𝒴.toBasedCategory.p.IsHomLift (Functor.structHom U Zu)
      (α.inv ≫ yp.map (Functor.toMkId U Zu) ≫ yUnit) :=
    IsHomLift.comp_lift_id_left' 𝒴.toBasedCategory.p ((Over.map U.hom).obj Zu) α.inv
      (Functor.structHom U Zu) (yp.map (Functor.toMkId U Zu) ≫ yUnit)
  -- the quintuple
  refine ⟨d, hd,
    { U := U
      Z := (Over.map U.hom).obj Zu
      q := Functor.structHom U Zu
      finiteLocallyFree := hflf'
      y := y
      y_over := hy
      x := x
      x_over := hx
      α := α.inv ≫ yp.map (Functor.toMkId U Zu) ≫ yUnit
      α_over := hαover }, ?_, rfl⟩
  -- membership of the locus, tested on the datum just assembled
  refine (lciLocus_iff
    { y := yp
      y_comp := hypcomp
      yUnit := yUnit
      yUnit_over := hyUnit
      Xy := Xy
      isAlgebraicSpace := hXy
      e := e
      α := α
      α_over := hα
      α_comp := rfl }).mpr ?_
  have hDmap : (relativeMap F yp e hXy Zu x hx α hα).hom = yoneda.map iu ≫ φ :=
    congrArg (fun m => m.hom) hmapeq
  exact ⟨hDmap ▸ hunram, hDmap ▸ hlci⟩

end AlgebraicGeometry.Stack.FiniteHilbert

end
