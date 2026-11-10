module

public import Mathlib.CategoryTheory.Sigma.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLciPointOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.RelativeMapIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePoint
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Transport
public import StacksFrontier.CategoryTheory.TwoFibreProduct.ElementsSpan

/-!
# The local complete intersection loci cover the target stack

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
which is representable by algebraic spaces, flat, surjective and locally of finite presentation.
**Stacks 06DA** says that the 1-morphism `∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is surjective on
objects in the sense of Stacks 06D4.

## Main definitions

* `AlgebraicGeometry.Stack.lciFiniteHilbertCoproductProjection` and
  `AlgebraicGeometry.Stack.lciFiniteHilbertCoproductCategory`: the disjoint union
  `∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴)` as a category over the big fppf site of `S`.
* `AlgebraicGeometry.Stack.lciFiniteHilbertCoproductToTarget`: the 1-morphism
  `∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴`.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.exists_lciLocus_of_isFieldObject`: over the spectrum of
  a field, every object of `𝒴` is the object of `𝒴` of a positive-degree object of the local
  complete intersection locus over the same spectrum.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_lciFiniteHilbertCoproductToTarget`: for `F`
  representable by algebraic spaces, flat, surjective and locally of finite presentation, the
  1-morphism `∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is surjective on objects.

## References

* [Stacks Project, Tag 00PJ](https://stacks.math.columbia.edu/tag/00PJ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
* [Stacks Project, Tag 0570](https://stacks.math.columbia.edu/tag/0570)
* [Stacks Project, Tag 069L](https://stacks.math.columbia.edu/tag/069L)
* [Stacks Project, Tag 06C8](https://stacks.math.columbia.edu/tag/06C8)
* [Stacks Project, Tag 06C9](https://stacks.math.columbia.edu/tag/06C9)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
-/

@[expose] public section

open CategoryTheory Opposite

universe u w v₂ u₂

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-! ### The disjoint union of the loci over all positive degrees -/

/-- The canonical functor from the disjoint union `∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴)` of the local
complete intersection loci of all positive degrees to the big fppf site of `S`: on the summand of
degree `d` it is the canonical projection of `ℋ_{d,lci}(𝒳/𝒴)`. -/
noncomputable def lciFiniteHilbertCoproductProjection :
    (Σ d : {n : ℕ // 0 < n},
        (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d.1)).obj) ⥤
      BigFppfOver B S hS :=
  Sigma.desc fun d ↦ (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
    (F := F) (d := d.1)).p

/-- The disjoint union `∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴)` of the local complete intersection loci of all
positive degrees, regarded as a category over the big fppf site of `S`. -/
noncomputable def lciFiniteHilbertCoproductCategory : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (lciFiniteHilbertCoproductProjection (B := B) (S := S) (hS := hS)
    (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F))

/-- The 1-morphism `∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` to the target stack: on the summand of degree
`d` it is the 1-morphism of Stacks 05WD restricted to the local complete intersection locus. -/
noncomputable def lciFiniteHilbertCoproductToTarget :
    (Σ d : {n : ℕ // 0 < n},
        (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d.1)).obj) ⥤
      𝒴.toBasedCategory.obj :=
  Sigma.desc fun d ↦ (lciFiniteHilbertToTarget (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
    (F := F) (d := d.1)).toFunctor

/-! ### The fibre over the spectrum of a field -/

/-- **The structural morphism of Stacks 04SG is tested over the smaller base.** For an algebraic
space `X` over a scheme `U` over `S`, a property of morphisms of schemes holds on every étale
chart of the structural morphism of the image of `X` under the forward functor of Stacks 04SG
exactly when it holds on every étale chart of the structural morphism of `X` to the terminal
object of the big fppf site of `U`. -/
theorem holdsOnEveryEtaleChart_algebraicSpaceMap_iff_toYonedaId
    (P : MorphismProperty Scheme.{u}) (U : BigFppfOver B S hS)
    (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B U.left.1 U.left.2 X) :
    Space.HoldsOnEveryEtaleChart B S hS P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩)).hom ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (Space.toYonedaId B U.left.1 U.left.2 X) := by
  change Space.HoldsOnEveryEtaleChart B S hS P
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩).1.hom ↔ _
  rw [← Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS P
      ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).inv.app ⟨X, hX⟩) _,
    Space.relocalizeToYoneda_eq B U.left.1 S U.left.2 hS U.hom ⟨X, hX⟩]
  exact Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom P X

/-- **An algebraic space surjective over the spectrum of a field has a point.** If the structural
morphism of Stacks 04SG of an algebraic space `X` over an object `U` of the big fppf site whose
underlying scheme is the spectrum of a field is surjective, then `X` has a section over some
object of the big fppf site of `U` with nonempty underlying scheme. -/
theorem exists_nonempty_section_of_isSurjective (U : BigFppfOver B S hS)
    (hU : IsFieldObject B S hS U) (X : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B U.left.1 U.left.2 X)
    (hsurj : Space.IsSurjective B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨X, hX⟩)).hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      Nonempty ((BigFppfOver.toScheme B U.left.1 U.left.2).obj V) ∧ Nonempty (X.obj (op V)) := by
  obtain ⟨k, hk, ⟨eU⟩⟩ := hU
  let := hk
  have hk' : B.Contains (Spec (.of k)) := BigFppfSite.contains_of_mono B eU.inv U.left.2
  let toBase : Spec (.of k) ⟶ S := eU.inv ≫ B.inclusion.map U.hom
  let p₀ : Space.FieldValuedPoint B S hS (yoneda.obj (Over.mk U.hom)) :=
    { carrier := k
      contained := hk'
      toBase := toBase
      value := Over.homMk (⟨eU.inv⟩ : B.obj hk' ⟶ U.left) rfl }
  obtain ⟨pt, -⟩ := hsurj (p₀.class B S hS _)
  obtain ⟨q, -⟩ := Quot.exists_rep pt
  let r := Space.FieldValuedPoint.derelocalize B U.left.1 S U.left.2 hS U.hom X
    (Space.FieldValuedPoint.map B S hS _
      ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).hom.app ⟨X, hX⟩)
      q)
  refine ⟨r.siteObject, ?_, ⟨r.value⟩⟩
  change Nonempty (Spec (.of r.carrier))
  infer_instance

namespace FiniteHilbert

/-- Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of `S` which is
representable by algebraic spaces, flat, surjective and locally of finite presentation. For every
object `U` of the site whose underlying scheme is the spectrum of a field and every object `y` of
`𝒴` over `U` there are a degree `d ≥ 1` and an object `(U, Z, y, x, α)` of `ℋ_{d,lci}(𝒳/𝒴)` with
the given `U` and `y`. -/
theorem exists_lciLocus_of_isFieldObject
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
    (U : BigFppfOver B S hS) (hU : IsFieldObject B S hS U) (y₀ : 𝒴.toBasedCategory.obj)
    (hy₀ : 𝒴.toBasedCategory.p.obj y₀ = U) :
    ∃ (d : ℕ) (_ : 0 < d) (P : Object B S hS 𝒳 𝒴 F d),
      lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P ∧
        P.U = U ∧ P.y = y₀ := by
  have hY := 𝒴.isStackInGroupoids.isFiberedInGroupoids
  obtain ⟨y, hy, ξ, hξ⟩ :=
    StacksRepresentableCFG.exists_pointOverMap_of_obj 𝒴.toBasedCategory.p hY U y₀ hy₀
  obtain ⟨Xy, hXy, ⟨e⟩⟩ := hFrep U y hy
  have chart := fun P => (holdsOnEveryEtaleChart_algebraicSpaceMap_iff_toYonedaId P U Xy hXy).1
  have hflat := chart _ (hFflat U y hy Xy hXy ⟨e⟩)
  have hlfp := chart _ (hFlfp U y hy Xy hXy ⟨e⟩)
  obtain ⟨V, hV, ⟨s⟩⟩ := exists_nonempty_section_of_isSurjective U hU Xy hXy
    (hFsurj U y hy Xy hXy ⟨e⟩)
  obtain ⟨k, hk, ⟨eU⟩⟩ := hU
  let := hk
  obtain ⟨Z, d, hd, hZfl, f, hfu, hfl⟩ :=
    Space.exists_isUnramified_isLocalCompleteIntersection_of_field B U.left.1 U.left.2 eU hXy
      hflat hlfp V s
  obtain ⟨x, hx, α, hα, hsec⟩ := TwoFibreProductOver.exists_mk_of_section e Z (yonedaEquiv f)
  let t := StacksRepresentableCFG.toTautological Z
  have hb : (Over.map U.hom).obj (Over.mk (𝟙 U.left)) = U :=
    (Functor.congr_obj hy (Over.mk (𝟙 U.left))).symm.trans
      (IsHomLift.domain_eq 𝒴.toBasedCategory.p (𝟙 U) ξ.hom)
  have ht : 𝒴.toBasedCategory.p.IsHomLift ((Over.map U.hom).map t) (y.map t) :=
    StacksRepresentableCFG.isHomLift_map_toTautological U.hom y hy Z
  have hξt : 𝒴.toBasedCategory.p.IsHomLift ((Over.map U.hom).map t) (y.map t ≫ ξ.hom) :=
    IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p ((Over.map U.hom).map t) (y.map t) U ξ.hom
  let q : (Over.map U.hom).obj Z ⟶ U := Over.homMk Z.hom rfl
  have hαq : 𝒴.toBasedCategory.p.IsHomLift q (α.inv ≫ y.map t ≫ ξ.hom) :=
    Functor.isHomLift_of_base_eq _ _
      (IsHomLift.comp_lift_id_left' 𝒴.toBasedCategory.p ((Over.map U.hom).obj Z) α.inv
        ((Over.map U.hom).map t) (y.map t ≫ ξ.hom)) q rfl hb
      (Over.OverMorphism.ext (by simp [q, t]))
  let P : Object B S hS 𝒳 𝒴 F d :=
    { U := U
      Z := (Over.map U.hom).obj Z
      q := q
      finiteLocallyFree := hZfl
      y := y₀
      y_over := hy₀
      x := x
      x_over := hx
      α := α.inv ≫ y.map t ≫ ξ.hom
      α_over := hαq }
  let D : RelativeMapData P :=
    { y := y
      y_comp := hy
      yUnit := ξ.hom
      yUnit_over := hξ
      Xy := Xy
      isAlgebraicSpace := hXy
      e := e
      α := α
      α_over := hα
      α_comp := by
        rw [Object.coverToBase_eq_toTautological]
        rfl }
  have hmap : D.map.hom = f := by
    change yonedaEquiv.symm (PresheafOfCategories.sectionOfObj e
      ⟨(Over.map U.hom).obj Z, Z, x, rfl, hx, α, hα⟩ rfl) = f
    rw [hsec]
    exact yonedaEquiv.symm_apply_apply f
  exact ⟨d, hd, P, lciLocus_of_relativeMapData D (hmap ▸ ⟨hfu, hfl⟩), rfl, rfl⟩

end FiniteHilbert

/-- Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of `S` which is
representable by algebraic spaces, flat, surjective and locally of finite presentation. Then the
1-morphism `∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is surjective on objects. -/
@[stacks 06DA "∐_{d ≥ 1} ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴 is surjective on objects, for F representable by \
algebraic spaces, flat, surjective and locally of finite presentation"]
theorem isSurjectiveOnObjects_lciFiniteHilbertCoproductToTarget
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
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom) :
    IsSurjectiveOnObjects B S hS
      (lciFiniteHilbertCoproductProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F))
      𝒴.toBasedCategory.p
      (lciFiniteHilbertCoproductToTarget (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F)) := by
  intro U hU y hy
  obtain ⟨d, hd, P, hP, hPU, rfl⟩ :=
    FiniteHilbert.exists_lciLocus_of_isFieldObject hFrep hFflat hFsurj hFlfp U hU y hy
  exact ⟨U, hU, 𝟙 U, ⟨⟨d, hd⟩, ⟨P, hP⟩⟩, hPU, 𝟙 P.y, IsHomLift.id hy⟩

end AlgebraicGeometry.Stack

end
