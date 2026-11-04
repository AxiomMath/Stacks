module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSmoothSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# Independence of the chart in the dimension of an algebraic stack at a point

The formula of Stacks 0AFN for the dimension of a locally Noetherian algebraic stack `𝒳` at a
point `x` reads `dim_t(T) - dim_t(T_x)` at a smooth, locally of finite type 1-morphism
`T ⟶ 𝒳` from an algebraic space and a point `t ∈ |T|` above `x`. This file proves that the
value does not depend on either choice (Stacks 0AFM), and deduces the dimension formula of
Stacks 0DRJ.

## Main results

* `AlgebraicGeometry.Stack.representedDimensionAtPoint_eq_of_inverse`: the dimension at a point
  of a category fibred in groupoids represented by an algebraic space is invariant under a
  1-morphism admitting a quasi-inverse.
* `AlgebraicGeometry.Stack.representedDimensionAtPoint_eq_fieldFibreDimensionAt_of_fst`: the
  value of the formula of Stacks 0DRG is read off *any* 2-fibre product of `f` and the
  1-morphism of a field-valued point, not only off the canonical apex of Stacks 003Q.
* `AlgebraicGeometry.Stack.hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt`:
  base-change invariance of the relative dimension of Stacks 0DRG.
* `AlgebraicGeometry.Stack.dimensionSubNat_eq_dimensionSubNat_of_isSmooth`: the two values of
  the formula of Stacks 0AFN at two smooth charts and points above `x` agree, at relative
  dimensions given as natural numbers.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`: the dimension of `𝒳`
  at `x` is the value of the formula at any smooth chart and point above `x`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFI](https://stacks.math.columbia.edu/tag/0AFI)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Invariance of the dimension of a represented category under an equivalence -/

section RepresentedEquivalenceInvariance

variable {𝒲 𝒲' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The morphism of representing presheaves of Stacks 04SW attached to a 1-morphism admitting a
quasi-inverse, as an isomorphism. -/
noncomputable def representingIsoOfInverse
    (E E' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eE : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p
      (presheafOfCategories (E ⋙ typeToCat)).p)
    (eE' : StacksRepresentableCFG.EquivalenceOver 𝒲'.val.p
      (presheafOfCategories (E' ⋙ typeToCat)).p)
    {a : 𝒲 ⟶ 𝒲'} {b : 𝒲' ⟶ 𝒲} (θ : a ≫ b ≅ 𝟙 𝒲) (θ' : b ≫ a ≅ 𝟙 𝒲') :
    E ≅ E' where
  hom := representingMap B S hS 𝒲 𝒲' E E' eE eE' a
  inv := representingMap B S hS 𝒲' 𝒲 E' E eE' eE b
  hom_inv_id := by
    rw [← representingMap_comp B S hS E E' E eE eE' eE a b,
      representingMap_congr_twoIso B S hS E E eE eE θ, representingMap_id]
  inv_hom_id := by
    rw [← representingMap_comp B S hS E' E E' eE' eE eE' b a,
      representingMap_congr_twoIso B S hS E' E' eE' eE' θ', representingMap_id]

/-- The dimension at a point of a category fibred in groupoids represented by an algebraic space
is invariant under an equivalence: if `a : 𝒲 ⟶ 𝒲'` admits a quasi-inverse `b`, then the
dimension of `𝒲'` at the image of a point of `𝒲` is the dimension of `𝒲` at that point. -/
theorem representedDimensionAtPoint_eq_of_inverse
    (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)
    (h𝒲' : IsRepresentableByAlgebraicSpace B S hS 𝒲')
    {a : 𝒲 ⟶ 𝒲'} {b : 𝒲' ⟶ 𝒲} (θ : a ≫ b ≅ 𝟙 𝒲) (θ' : b ≫ a ≅ 𝟙 𝒲')
    (y : points B S hS 𝒲.val 𝒲.property) :
    representedDimensionAtPoint B S hS 𝒲' h𝒲'
        (pointsMap B S hS 𝒲.val 𝒲.property 𝒲'.property a.hom y) =
      representedDimensionAtPoint B S hS 𝒲 h𝒲 y := by
  classical
  obtain ⟨E, hE, ⟨eE⟩⟩ := id h𝒲
  obtain ⟨E', hE', ⟨eE'⟩⟩ := id h𝒲'
  obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS E 𝒲 eE).surjective y
  have h₁ : representedDimensionAtPoint B S hS 𝒲 h𝒲 y =
      Space.dimensionAtPoint B S hS E hE z := by
    rw [← hz]
    exact representedDimensionAtPoint_eq B S hS 𝒲 h𝒲 E hE eE z
  have h₂ : representedDimensionAtPoint B S hS 𝒲' h𝒲'
        (pointsMap B S hS 𝒲.val 𝒲.property 𝒲'.property a.hom y) =
      Space.dimensionAtPoint B S hS E' hE'
        (Space.pointsMap B S hS E
          (representingMap B S hS 𝒲 𝒲' E E' eE eE' a) z) := by
    rw [← hz, ← spacePointMap_representing_naturality B S hS E E' 𝒲 𝒲' eE eE' a z]
    exact representedDimensionAtPoint_eq B S hS 𝒲' h𝒲' E' hE' eE' _
  rw [h₁, h₂]
  exact (Space.dimensionAtPoint_eq_of_isEtale B S hS hE hE'
    (representingIsoOfInverse B S hS E E' eE eE' θ θ').hom
    (Space.isEtale_of_iso B S hS (representingIsoOfInverse B S hS E E' eE eE' θ θ')) z).symm

end RepresentedEquivalenceInvariance

/-! ### The relative dimension of Stacks 0DRG on a recognised fibre -/

section RecognisedFibre

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- Let `P` be any 2-commutative square which is a 2-fibre product of `f : 𝒯 ⟶ 𝒳` and the
1-morphism `Spec k ⟶ 𝒳` of a field-valued point `p` of `𝒳`, and let `y ∈ |P|` and
`q ∈ |𝒯 ×_𝒳 Spec k|` have the same image in `|𝒯|`. Then the dimension of `P` at `y` is the value
of `AlgebraicGeometry.Stack.fieldFibreDimensionAt` at `p` and `q`. -/
theorem representedDimensionAtPoint_eq_fieldFibreDimensionAt_of_fst
    (f : 𝒯 ⟶ 𝒳) (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    {P : Bicategory.TwoCommSq f.hom (fieldValuedPointMorphism B S hS 𝒳.val p)}
    (hP : Bicategory.IsTwoFibreProduct P)
    (hPpt : IsRepresentableByAlgebraicSpace B S hS P.pt)
    (y : points B S hS P.pt.val P.pt.property)
    (q : points B S hS (fieldFibreSquare B S hS f.hom p).pt.val
      (fieldFibreSquare B S hS f.hom p).pt.property)
    (hy : pointsMap B S hS P.pt.val P.pt.property 𝒯.val.property P.fst.hom y =
      pointsMap B S hS (fieldFibreSquare B S hS f.hom p).pt.val
        (fieldFibreSquare B S hS f.hom p).pt.property 𝒯.val.property
        (fieldFibreSquare B S hS f.hom p).fst.hom q) :
    representedDimensionAtPoint B S hS P.pt hPpt y =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p q := by
  classical
  have hCan := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    f.hom (fieldValuedPointMorphism B S hS 𝒳.val p)
  have hCanRep :=
    isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS f.hom 𝒳.property h𝒯 p
  have A := Bicategory.twoFibreProductPreHom hCan P
  have D := Bicategory.twoFibreProductPreHom hP (fieldFibreSquare B S hS f.hom p)
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hP (A.comp D)
    (Bicategory.TwoCommSq.PreHom.id P)
  obtain ⟨θ', -, -⟩ := Bicategory.twoFibreProductPreHom_rel hCan (D.comp A)
    (Bicategory.TwoCommSq.PreHom.id (fieldFibreSquare B S hS f.hom p))
  have hinv := representedDimensionAtPoint_eq_of_inverse B S hS hPpt hCanRep θ θ' y
  have hfst : pointsMap B S hS P.pt.val P.pt.property 𝒯.val.property P.fst.hom y =
      pointsMap B S hS (fieldFibreSquare B S hS f.hom p).pt.val
        (fieldFibreSquare B S hS f.hom p).pt.property 𝒯.val.property
        (fieldFibreSquare B S hS f.hom p).fst.hom
        (pointsMap B S hS P.pt.val P.pt.property
          (fieldFibreSquare B S hS f.hom p).pt.property A.hom.hom y) :=
    (congrFun (pointsMap_eq_of_basedNatTrans B S hS P.pt.val P.pt.property 𝒯.val.property
        A.isoFst.hom.hom) y).trans
      (pointsMap_comp B S hS P.pt.val P.pt.property
        (fieldFibreSquare B S hS f.hom p).pt.property 𝒯.val.property
        A.hom.hom (fieldFibreSquare B S hS f.hom p).fst.hom y).symm
  have hdef : fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p
        (pointsMap B S hS P.pt.val P.pt.property
          (fieldFibreSquare B S hS f.hom p).pt.property A.hom.hom y) =
      representedDimensionAtPoint B S hS (fieldFibreSquare B S hS f.hom p).pt hCanRep
        (pointsMap B S hS P.pt.val P.pt.property
          (fieldFibreSquare B S hS f.hom p).pt.property A.hom.hom y) := rfl
  rw [← hinv, ← hdef]
  exact fieldFibreDimensionAt_eq_of_pointsMap_eq.{u, w} B S hS f h𝒯 hf p _ q
    (hfst.symm.trans hy)

end RecognisedFibre

/-! ### Base-change invariance of the relative dimension of Stacks 0DRG -/

section BaseChange

variable {𝒯 𝒯' 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- Let `f : 𝒯 ⟶ 𝒳` and `f' : 𝒯' ⟶ 𝒳` be 1-morphisms of algebraic stacks with `𝒯` and `𝒯'`
representable by algebraic spaces and `f'` locally of finite type, and let `Q` be a 2-fibre
product of that cospan with apex representable by an algebraic space. Let `pr : P ⟶ T₀` be the
morphism of representing presheaves of Stacks 04SW attached to the first projection `Q.fst`.
Then the relative dimension of Stacks 04NM of `pr` at a point `z` of `P` is the value of the
formula of Stacks 0DRG for `f'` at the image of the corresponding point of `|Q|` in `|𝒯'|`. -/
theorem hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt
    (f : 𝒯 ⟶ 𝒳) (f' : 𝒯' ⟶ 𝒳)
    (h𝒯' : IsRepresentableByAlgebraicSpace B S hS 𝒯'.val)
    (hf' : AlgebraicStacks.IsLocallyOfFiniteType B S hS f')
    {Q : Bicategory.TwoCommSq f.hom f'.hom} (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQpt : IsRepresentableByAlgebraicSpace B S hS Q.pt)
    (T₀ P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hT₀ : IsAlgebraicSpace B S hS T₀) (hP : IsAlgebraicSpace B S hS P)
    (eT₀ : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p
      (presheafOfCategories (T₀ ⋙ typeToCat)).p)
    (eP : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    {pr : P ⟶ T₀} (hftpr : Space.IsLocallyOfFiniteType B S hS pr)
    (hpr : representingMap B S hS Q.pt 𝒯.val P T₀ eP eT₀ Q.fst = pr)
    (ζ : points B S hS Q.pt.val Q.pt.property) (z : Space.points B S hS P)
    (hz : spacePointMap B S hS P Q.pt (representingEquivalence B S hS P Q.pt eP).functor z = ζ)
    (p' : FieldValuedPoint B S hS 𝒳.val.val)
    (q' : points B S hS (fieldFibreSquare B S hS f'.hom p').pt.val
      (fieldFibreSquare B S hS f'.hom p').pt.property)
    (hq' : pointsMap B S hS (fieldFibreSquare B S hS f'.hom p').pt.val
        (fieldFibreSquare B S hS f'.hom p').pt.property 𝒯'.val.property
        (fieldFibreSquare B S hS f'.hom p').fst.hom q' =
      pointsMap B S hS Q.pt.val Q.pt.property 𝒯'.val.property Q.snd.hom ζ)
    (d : ℕ∞)
    (hd : fieldFibreDimensionAt.{u, w} B S hS f'.hom 𝒳.property h𝒯' p' q' =
      (d : WithBot ℕ∞)) :
    Space.HasRelativeDimensionAt d B S hS pr z := by
  classical
  subst hpr
  set τ := Quotient.out (pointsMap B S hS Q.pt.val Q.pt.property 𝒯.val.property Q.fst.hom ζ)
    with hτdef
  have hτ : pointClass B S hS 𝒯.val.val 𝒯.val.property τ =
      pointsMap B S hS Q.pt.val Q.pt.property 𝒯.val.property Q.fst.hom ζ := Quotient.out_eq _
  have hInner := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    Q.fst (fieldValuedPointMorphism B S hS 𝒯.val τ)
  have hInnerRep : IsRepresentableByAlgebraicSpace B S hS
      (fieldFibreSquare B S hS Q.fst τ).pt :=
    isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS Q.fst 𝒯.property hQpt τ
  obtain ⟨y, hy⟩ := exists_point_fieldFibreSquare B S hS Q.fst ζ τ hτ
  have hPasted := Bicategory.isTwoFibreProduct_paste
    (Bicategory.isTwoFibreProduct_swap hQ) hInner
  have hRe := Bicategory.isTwoFibreProduct_reindexSnd
    (Bicategory.InducedBicategory.isoMk
      (fieldValuedPointMorphism_comp_iso B S hS f.hom.hom τ)) hPasted
  have himg : pointClass B S hS 𝒳.val.val 𝒳.val.property
        (fieldValuedPointMap B S hS 𝒯.val.val f.hom.hom τ) =
      pointsMap B S hS 𝒯'.val.val 𝒯'.val.property 𝒳.val.property f'.hom.hom
        (pointsMap B S hS Q.pt.val Q.pt.property 𝒯'.val.property Q.snd.hom ζ) := by
    rw [← pointsMap_class B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom τ, hτ]
    exact ((pointsMap_comp B S hS Q.pt.val Q.pt.property 𝒯.val.property 𝒳.val.property
        Q.fst.hom f.hom.hom ζ).trans
      ((congrFun (pointsMap_eq_of_basedNatTrans B S hS Q.pt.val Q.pt.property 𝒳.val.property
          Q.iso.hom.hom) ζ).trans
        (pointsMap_comp B S hS Q.pt.val Q.pt.property 𝒯'.val.property 𝒳.val.property
          Q.snd.hom f'.hom.hom ζ).symm))
  obtain ⟨q₀, hq₀⟩ := exists_point_fieldFibreSquare B S hS f'.hom
    (pointsMap B S hS Q.pt.val Q.pt.property 𝒯'.val.property Q.snd.hom ζ)
    (fieldValuedPointMap B S hS 𝒯.val.val f.hom.hom τ) himg
  have hvalue : representedDimensionAtPoint B S hS (fieldFibreSquare B S hS Q.fst τ).pt
      hInnerRep y = (d : WithBot ℕ∞) := by
    rw [← hd]
    refine (representedDimensionAtPoint_eq_fieldFibreDimensionAt_of_fst.{u, w} B S hS f' h𝒯' hf'
      (fieldValuedPointMap B S hS 𝒯.val.val f.hom.hom τ) hRe hInnerRep y q₀ ?_).trans
      (fieldFibreDimensionAt_eq_fieldFibreDimensionAt_of_pointsMap_eq.{u, w} B S hS f' h𝒯' hf'
        _ p' q₀ q' (hq₀.trans hq'.symm))
    exact ((pointsMap_comp B S hS (fieldFibreSquare B S hS Q.fst τ).pt.val
      (fieldFibreSquare B S hS Q.fst τ).pt.property Q.pt.property 𝒯'.val.property
      (fieldFibreSquare B S hS Q.fst τ).fst.hom Q.snd.hom y).symm.trans
      (congrArg (pointsMap B S hS Q.pt.val Q.pt.property 𝒯'.val.property Q.snd.hom) hy)).trans
      hq₀.symm
  obtain ⟨E, hE, ⟨eE⟩⟩ := id hInnerRep
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing B S hS E
    (fieldFibreSquare B S hS Q.fst τ).pt eE).surjective y
  have hsq := (isPullback_representingMap_of_isTwoFibreProduct B S hS hInner
    P (yoneda.obj τ.base) T₀ E E eP
    (PresheafOfCategories.sliceElementsEquivalenceOver τ.base) eT₀ eE eE).flip
  have hbx : Space.pointsMap B S hS E
      (representingMap B S hS (fieldFibreSquare B S hS Q.fst τ).pt Q.pt E P eE eP
        (fieldFibreSquare B S hS Q.fst τ).fst) x = z := by
    refine (bijective_spacePointMap_representing B S hS P Q.pt eP).injective ?_
    rw [spacePointMap_representing_naturality B S hS E P
      (fieldFibreSquare B S hS Q.fst τ).pt Q.pt eE eP
      (fieldFibreSquare B S hS Q.fst τ).fst x, hx, hy, hz]
  have hdimE : Space.dimensionAtPoint B S hS E hE x = (d : WithBot ℕ∞) := by
    rw [← hvalue, ← hx]
    exact (representedDimensionAtPoint_eq B S hS _ hInnerRep E hE eE x).symm
  rw [← hbx]
  exact (dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback B S hS τ hsq hE hP hT₀
    hftpr x d).mp hdimE

end BaseChange

/-! ### Stacks 0AFM -/

section ChartIndependence

/-- If `m + d' = m' + d` for `m, m' ≠ ⊥` and natural numbers `d`, `d'`, then `m - d = m' - d'` as
extended integers. -/
theorem dimensionSubNat_eq_dimensionSubNat_of_add_eq {m m' : WithBot ℕ∞} {d d' : ℕ}
    (hm : m ≠ ⊥) (hm' : m' ≠ ⊥)
    (h : m + ((d' : ℕ∞) : WithBot ℕ∞) = m' + ((d : ℕ∞) : WithBot ℕ∞)) :
    dimensionSubNat m d = dimensionSubNat m' d' := by
  induction m using WithBot.recBotCoe with
  | bot => exact absurd rfl hm
  | coe a =>
    induction m' using WithBot.recBotCoe with
    | bot => exact absurd rfl hm'
    | coe b =>
      induction a using ENat.recTopCoe with
      | top =>
        induction b using ENat.recTopCoe with
        | top => rfl
        | coe n =>
          rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_eq_coe, top_add,
            ← Nat.cast_add] at h
          exact absurd h.symm (ENat.natCast_ne_top (n + d))
      | coe k =>
        induction b using ENat.recTopCoe with
        | top =>
          rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_eq_coe, top_add,
            ← Nat.cast_add] at h
          exact absurd h (ENat.natCast_ne_top (k + d'))
        | coe n =>
          rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_eq_coe] at h
          have hkn : k + d' = n + d := by exact_mod_cast h
          have hL : dimensionSubNat ((k : ℕ∞) : WithBot ℕ∞) d =
            (((k : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
          have hR : dimensionSubNat ((n : ℕ∞) : WithBot ℕ∞) d' =
            (((n : ℤ) - (d' : ℤ) : ℤ) : EInt) := rfl
          rw [hL, hR]
          congr 1
          lia

/-- If `𝒳` is a locally Noetherian algebraic stack and `f : T ⟶ 𝒳` is a 1-morphism locally of
finite type from an algebraic space, then `T` is locally Noetherian, as the étale-local property
of Stacks 03E6. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_chart
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    Space.HasEtaleLocalProperty B S hS T (fun Z : Scheme.{u} => IsLocallyNoetherian Z) := by
  let : ObjectProperty.IsLocal (fun Z : Scheme.{u} => IsLocallyNoetherian Z)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  exact (scheme_atlas_iff_etaleLocalProperty.{u, w} B S hS
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z) T hT).mp
    (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS f hf h𝒳)

/-- Let `Q` be a 2-fibre product of `f` and `f'`, and let `pr : P ⟶ T₀` be the morphism of
representing presheaves attached to its first projection, assumed smooth, with `T₀` locally
Noetherian. If the value of the formula of Stacks 0DRG for `f'` at the point of `|𝒯'|` below `z`
is `d`, then `dim_z(P) = dim_{pr(z)}(T₀) + d`. -/
private theorem dimensionAtPoint_eq_add_of_leg
    {𝒯 𝒯' 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒯 ⟶ 𝒳) (f' : 𝒯' ⟶ 𝒳)
    (h𝒯' : IsRepresentableByAlgebraicSpace B S hS 𝒯'.val)
    (hf' : AlgebraicStacks.IsLocallyOfFiniteType B S hS f')
    {Q : Bicategory.TwoCommSq f.hom f'.hom} (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQpt : IsRepresentableByAlgebraicSpace B S hS Q.pt)
    (T₀ P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hT₀ : IsAlgebraicSpace B S hS T₀) (hP : IsAlgebraicSpace B S hS P)
    (hNT₀ : Space.HasEtaleLocalProperty B S hS T₀
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (eT₀ : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p
      (presheafOfCategories (T₀ ⋙ typeToCat)).p)
    (eP : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    {pr : P ⟶ T₀} (hsmpr : Space.IsSmooth B S hS pr)
    (hpr : representingMap B S hS Q.pt 𝒯.val P T₀ eP eT₀ Q.fst = pr)
    (ζ : points B S hS Q.pt.val Q.pt.property) (z : Space.points B S hS P)
    (hz : spacePointMap B S hS P Q.pt (representingEquivalence B S hS P Q.pt eP).functor z = ζ)
    (t₀ : Space.points B S hS T₀)
    (hzt : Space.pointsMap B S hS P pr z = t₀)
    (p' : FieldValuedPoint B S hS 𝒳.val.val)
    (q' : points B S hS (fieldFibreSquare B S hS f'.hom p').pt.val
      (fieldFibreSquare B S hS f'.hom p').pt.property)
    (hq' : pointsMap B S hS (fieldFibreSquare B S hS f'.hom p').pt.val
        (fieldFibreSquare B S hS f'.hom p').pt.property 𝒯'.val.property
        (fieldFibreSquare B S hS f'.hom p').fst.hom q' =
      pointsMap B S hS Q.pt.val Q.pt.property 𝒯'.val.property Q.snd.hom ζ)
    (d : ℕ∞)
    (hd : fieldFibreDimensionAt.{u, w} B S hS f'.hom 𝒳.property h𝒯' p' q' =
      (d : WithBot ℕ∞)) :
    Space.dimensionAtPoint B S hS P hP z =
      Space.dimensionAtPoint B S hS T₀ hT₀ t₀ + (d : WithBot ℕ∞) := by
  have hft := Space.isLocallyOfFiniteType_of_isSmooth B S hS hsmpr
  have hNP := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hP hT₀ _ hft hNT₀
  have hrel := hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt.{u, w}
    B S hS f f' h𝒯' hf' hQ hQpt T₀ P hT₀ hP eT₀ eP hft hpr ζ z hz p' q' hq' d hd
  rw [← hzt]
  exact Space.dimensionAtPoint_eq_add_of_isSmooth B S hS hP hT₀ hNP hNT₀ _ hsmpr z hrel

/-- If `z ∈ |P|` corresponds to `ζ ∈ |𝒬|`, and `ζ` maps to the point of `|fibredCategory T|` of
`t` under `g`, then `z` maps to `t` under the representing morphism of `g`. -/
private theorem pointsMap_representingMap_fibredCategory_eq
    {𝒬 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (P T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eP : StacksRepresentableCFG.EquivalenceOver 𝒬.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (g : 𝒬 ⟶ fibredCategory B S hS T) (ζ : points B S hS 𝒬.val 𝒬.property)
    (z : Space.points B S hS P) (t : Space.points B S hS T)
    (hz : spacePointMap B S hS P 𝒬 (representingEquivalence B S hS P 𝒬 eP).functor z = ζ)
    (hζ : pointsMap B S hS 𝒬.val 𝒬.property (fibredCategory B S hS T).property g.hom ζ =
      stackPointOfSpacePoint B S hS T t) :
    Space.pointsMap B S hS P
      (representingMap B S hS 𝒬 (fibredCategory B S hS T) P T eP
        (StacksRepresentableCFG.EquivalenceOver.refl _) g) z = t := by
  refine (bijective_spacePointMap_representing B S hS T (fibredCategory B S hS T)
    (StacksRepresentableCFG.EquivalenceOver.refl _)).injective ?_
  rw [spacePointMap_representing_naturality B S hS P T 𝒬 (fibredCategory B S hS T) eP
    (StacksRepresentableCFG.EquivalenceOver.refl _) g z, hz, hζ]
  rfl

/-- Let `𝒳` be a locally Noetherian algebraic stack over `S`, and let `f : T ⟶ 𝒳` and
`f' : T' ⟶ 𝒳` be two smooth, locally-of-finite-type 1-morphisms from algebraic spaces, with
points `t ∈ |T|` and `t' ∈ |T'|` with the same image in `|𝒳|`. If the relative dimensions of
Stacks 0DRG of `f` at `t` and of `f'` at `t'` are the natural numbers `d` and `d'`, then
`dim_t(T) - d = dim_{t'}(T') - d'`. -/
@[stacks 0AFM]
theorem dimensionSubNat_eq_dimensionSubNat_of_isSmooth
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hT' : IsAlgebraicSpace B S hS T')
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (f' : algebraicSpaceStack.{u, w} B S hS T' hT' ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f) (hsm' : AlgebraicStacks.IsSmooth B S hS f')
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hf' : AlgebraicStacks.IsLocallyOfFiniteType B S hS f')
    (t : Space.points B S hS T) (t' : Space.points B S hS T')
    (hx : pointsMap B S hS (fibredCategory B S hS T).val
        (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
        (stackPointOfSpacePoint B S hS T t) =
      pointsMap B S hS (fibredCategory B S hS T').val
        (fibredCategory B S hS T').property 𝒳.val.property f'.hom.hom
        (stackPointOfSpacePoint B S hS T' t'))
    (d d' : ℕ)
    (hd : relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞))
    (hd' : relativeDimensionAt.{u, w} B S hS T' hT' 𝒳 f' hf' t' = (d' : WithBot ℕ∞)) :
    dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d =
      dimensionSubNat (Space.dimensionAtPoint B S hS T' hT' t') d' := by
  classical
  have hNT := hasEtaleLocalProperty_isLocallyNoetherian_of_chart.{u, w} B S hS 𝒳 h𝒳 hT f hf
  have hNT' := hasEtaleLocalProperty_isLocallyNoetherian_of_chart.{u, w} B S hS 𝒳 h𝒳 hT' f' hf'
  have hTrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT
  have hT'rep := isRepresentableByAlgebraicSpace_fibredCategory B S hS T' hT'
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f f'
  have hQc : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquareAlgebraicStacks B S hS f f').underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom f'.hom
  have hQpt : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f f').underlying.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS T') 𝒳.val (fibredCategory B S hS T) f'.hom f.hom _ hQc
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hT'rep
        f'.hom)
      hTrep
  obtain ⟨P, hP, ⟨eP⟩⟩ := id hQpt
  have hsmfst :=
    isSmooth_representingMap_of_isSmooth.{u, w} B S hS
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) P T hP hT eP
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS f f').fst
      (AlgebraicStacks.isSmooth_baseChange B S hS f' f
        (twoFibreProductSquareAlgebraicStacks B S hS f f') hQ hsm')
  have hsmsnd :=
    isSmooth_representingMap_of_isSmooth.{u, w} B S hS
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) P T' hP hT' eP
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS f f').snd
      (AlgebraicStacks.isSmooth_baseChange B S hS f f'
        (twoFibreProductSquareAlgebraicStacks B S hS f f').swap
        (Bicategory.isTwoFibreProduct_swap hQ) hsm)
  obtain ⟨ζ, hζ, hζ'⟩ := exists_point_of_isTwoFibreProduct B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f f').underlying hQc
    (stackPointOfSpacePoint B S hS T t) (stackPointOfSpacePoint B S hS T' t') hx
  obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS P
    (twoFibreProductSquareAlgebraicStacks B S hS f f').underlying.pt eP).surjective ζ
  obtain ⟨p, q, -, hq, hvald⟩ := exists_eq_fieldFibreDimensionAt B S hS T hT 𝒳 f hf t
  obtain ⟨p', q', -, hq', hvald'⟩ := exists_eq_fieldFibreDimensionAt B S hS T' hT' 𝒳 f' hf' t'
  have heq₁ := dimensionAtPoint_eq_add_of_leg.{u, w} B S hS f f' hT'rep hf' hQc hQpt T P hT hP
    hNT (StacksRepresentableCFG.EquivalenceOver.refl _) eP hsmfst rfl ζ z hz t
    (pointsMap_representingMap_fibredCategory_eq B S hS P T eP _ ζ z t hz hζ) p' q'
    (hq'.trans hζ'.symm) (d' : ℕ∞) (by rw [← hvald', hd']; rfl)
  have heq₂ := dimensionAtPoint_eq_add_of_leg.{u, w} B S hS f' f hTrep hf
    (Q := (twoFibreProductSquareAlgebraicStacks B S hS f f').underlying.swap)
    (Bicategory.isTwoFibreProduct_swap hQc) hQpt T' P hT' hP hNT'
    (StacksRepresentableCFG.EquivalenceOver.refl _) eP hsmsnd rfl ζ z hz t'
    (pointsMap_representingMap_fibredCategory_eq B S hS P T' eP _ ζ z t' hz hζ') p q
    (hq.trans hζ.symm) (d : ℕ∞) (by rw [← hvald, hd]; rfl)
  exact dimensionSubNat_eq_dimensionSubNat_of_add_eq
    (Space.dimensionAtPoint_ne_bot B S hS T hT t)
    (Space.dimensionAtPoint_ne_bot B S hS T' hT' t') (heq₁.symm.trans heq₂)

/-- Let `𝒳` be a locally Noetherian algebraic stack over `S`, let `f : T ⟶ 𝒳` be a smooth,
locally-of-finite-type 1-morphism from an algebraic space, and let `t ∈ |T|` lie above
`x ∈ |𝒳|`. If the relative dimension of Stacks 0DRG of `f` at `t` is the natural number `d`, then
`dim_x(𝒳) = dim_t(T) - d`. -/
@[stacks 0DRJ "dimension via a smooth algebraic space"]
theorem dimensionAtPoint_eq_dimensionSubNat_of_isSmooth
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : Space.points B S hS T)
    (ht : pointsMap B S hS (fibredCategory B S hS T).val
      (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
      (stackPointOfSpacePoint B S hS T t) = x)
    (d : ℕ) (hd : relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞)) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x =
      dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d := by
  refine le_antisymm (dimensionAtPoint_le B S hS 𝒳 h𝒳 x T hT f hsm hf t ht d hd) (le_sInf ?_)
  rintro b ⟨T', hT', f', hsm', hf', t', ht', d', hd', rfl⟩
  exact (dimensionSubNat_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 hT hT'
    f f' hsm hsm' hf hf' t t' (ht.trans ht'.symm) d d' hd hd').le

end ChartIndependence

end AlgebraicGeometry.Stack

end
