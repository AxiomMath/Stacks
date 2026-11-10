module

public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The diagonals of the finite part of a morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. Two pairs `(a, Z₁)` and
`(a, Z₂)` of Stacks 04PC over a scheme `T` with the same morphism `a : T ⟶ Y` agree after base
change along `h : T' ⟶ T` exactly when the image of `T'` avoids the closed set

`pr₀(Z₁ \ Z₁ ∩ Z₂) ∪ pr₀(Z₂ \ Z₁ ∩ Z₂)`,

which is closed because the projections of `Z₁` and `Z₂` to `T` are finite, hence proper. Its
open complement therefore represents the fibre product of `T` with the diagonal of
`(X/Y)_fin` over `Y`, so that diagonal is representable by schemes and an open immersion. The
absolute diagonal follows, being the relative diagonal composed with a base change of the
diagonal of `Y`.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_diagonal_finiteOpenSubspacePresheaf` — Stacks 04PK:
  the diagonal of `(X/Y)_fin ⟶ Y` is a representable open immersion.
* `AlgebraicGeometry.Space.relativelyRepresentable_diag_finiteOpenSubspacePresheaf` — Stacks
  04PK: the absolute diagonal of `(X/Y)_fin` is representable by schemes.

## Implementation notes

Representability by schemes together with the open-immersion property is the single condition
`AlgebraicGeometry.Space.IsOpenImmersion` of Stacks 02YU, so one declaration carries both
assertions about the relative diagonal.

The open subscheme `V ⊂ T` is produced as an object of the big fppf site: the closed set above
is obtained from the point topology of Stacks 03BX, its complement corresponds to an open
subscheme of the scheme underlying `T` by Stacks 03BZ, and that open subscheme again lies in
the site, being smaller than `T`. Its universal property is checked against field-valued
points, which is where the point-set description of the closed set is used.

## References

* [Stacks Project, Tag 04PK](https://stacks.math.columbia.edu/tag/04PK)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullbacks_presheaf_finitePartDiagonal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

private instance (priority := high) hasPullback_presheaf_finitePartDiagonal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_finitePartDiagonal B S hS).has_limit _

private theorem pointsMap_range_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W Z X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : AlgebraicGeometry.IsAlgebraicSpace B S hS W)
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S hS Z)
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f) :
    Set.range (pointsMap B S hS W p) =
      pointsMap B S hS Z g ⁻¹'
        Set.range (pointsMap B S hS X f) := by
  classical
  let W' : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let p' : W' ⟶ Z' := ObjectProperty.homMk p
  let q' : W' ⟶ X' := ObjectProperty.homMk q
  let g' : Z' ⟶ Y' := ObjectProperty.homMk g
  let f' : X' ⟶ Y' := ObjectProperty.homMk f
  have sq' : IsPullback p' q' g' f' := IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      AlgebraicGeometry.IsAlgebraicSpace B S hS F)) sq
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨pointsMap B S hS W q w, ?_⟩
    calc
      pointsMap B S hS X f (pointsMap B S hS W q w) = pointsMap B S hS W (q ≫ f) w :=
          (congrFun (pointsMap_comp B S hS _ q f) w).symm
      _ = pointsMap B S hS W (p ≫ g) w :=
          congrArg (fun a : W ⟶ Y => pointsMap B S hS W a w) sq.w.symm
      _ = pointsMap B S hS Z g (pointsMap B S hS W p w) :=
          congrFun (pointsMap_comp B S hS _ p g) w
  · rintro ⟨x, hx⟩
    obtain ⟨w, hwZ, -⟩ := exists_point_of_isPullback B S hS sq' z x hx.symm
    exact ⟨w, hwZ⟩

private theorem finiteSubspace_projection_isClosed
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p : FiniteOpenSubspace B S hS f
      (schemeSpace T)) :
    IsClosedMorphism B S hS (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) := by
  apply isClosed_of_universallyClosed B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
  exact ((isFinite_iff_isAffineHom_and_isProper B S hS
    p.isOpen.1 (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
    (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom)).mp p.finite_projection).2.2.2

private theorem finiteOpenDifference_closedImage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {M : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : AlgebraicGeometry.IsAlgebraicSpace B S hS M)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    {U V : Subfunctor M}
    (hU : IsOpenSubspace B S hS U)
    (hV : IsOpenSubspace B S hS V)
    (r : U.toFunctor ⟶ yoneda.obj T)
    (hr : @IsClosedMap _ _
      (pointTopology B S hS U.toFunctor)
      (pointTopology B S hS (yoneda.obj T))
      (pointsMap B S hS U.toFunctor r)) :
    @IsClosed _ (pointTopology B S hS (yoneda.obj T))
      (pointsMap B S hS U.toFunctor r ''
        ((pointsMap B S hS U.toFunctor U.ι) ⁻¹'
          (Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ)) := by
  let _ := pointTopology B S hS U.toFunctor
  let _ := pointTopology B S hS M
  let _ := pointTopology B S hS (yoneda.obj T)
  have hVopen : IsOpen (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
    rw [← openSubspacesOrderIso_apply B S hS M hM ⟨V, hV⟩]
    exact (openSubspacesOrderIso B S hS M hM ⟨V, hV⟩).2
  exact hr _
    (hVopen.preimage ((pointTopologyFamily B S hS).continuous hU.1 hM U.ι)).isClosed_compl

private theorem finiteSubspaceAgreement_openPoints
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {M : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : AlgebraicGeometry.IsAlgebraicSpace B S hS M)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    {U V : Subfunctor M}
    (hU : IsOpenSubspace B S hS U)
    (hV : IsOpenSubspace B S hS V)
    (rU : U.toFunctor ⟶ yoneda.obj T)
    (rV : V.toFunctor ⟶ yoneda.obj T)
    (hrU : @IsClosedMap _ _
      (pointTopology B S hS U.toFunctor)
      (pointTopology B S hS (yoneda.obj T))
      (pointsMap B S hS U.toFunctor rU))
    (hrV : @IsClosedMap _ _
      (pointTopology B S hS V.toFunctor)
      (pointTopology B S hS (yoneda.obj T))
      (pointsMap B S hS V.toFunctor rV)) :
    @IsOpen _ (pointTopology B S hS (yoneda.obj T))
      ((pointsMap B S hS U.toFunctor rU ''
        ((pointsMap B S hS U.toFunctor U.ι) ⁻¹'
          (Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ)) ∪
        (pointsMap B S hS V.toFunctor rV ''
        ((pointsMap B S hS V.toFunctor V.ι) ⁻¹'
          (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ)))ᶜ := by
  let _ := pointTopology B S hS (yoneda.obj T)
  exact ((finiteOpenDifference_closedImage B S hS hM T hU hV rU hrU).union
    (finiteOpenDifference_closedImage B S hS hM T hV hU rV hrV)).isOpen_compl

private structure OpenPointSetOfScheme
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS) where
  points : Set (_root_.AlgebraicGeometry.Space.points B S hS (yoneda.obj T))
  isOpen : @IsOpen _ (pointTopology B S hS (yoneda.obj T)) points
  disagreement : Set (_root_.AlgebraicGeometry.Space.points B S hS (yoneda.obj T))
  points_eq_compl_disagreement : points = disagreementᶜ
  schemeOpen : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)
  point_iff : ∀ z : FieldValuedPoint B S hS (yoneda.obj T),
    (z.class B S hS (yoneda.obj T) ∈ points ↔
      schemePoint B S hS T z ∈ schemeOpen)

private noncomputable def finiteSubspaceAgreementOpenData
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p q : FiniteOpenSubspace B S hS f
      (schemeSpace T))
    (hbase : p.toBase.hom = q.toBase.hom) : OpenPointSetOfScheme B S hS T := by
  cases p with
  | mk pBase pSub pOpen pFinite =>
    cases q with
    | mk qBase qSub qOpen qFinite =>
      have hbase' : pBase = qBase := ObjectProperty.hom_ext _ hbase
      cases hbase'
      let p : FiniteOpenSubspace B S hS f
          (schemeSpace T) :=
        ⟨pBase, pSub, pOpen, pFinite⟩
      let q : FiniteOpenSubspace B S hS f
          (schemeSpace T) :=
        ⟨pBase, qSub, qOpen, qFinite⟩
      let hM := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p.toBase.hom f.hom
        (schemeSpace T).property X.property Y.property
      let U := p.subspace
      let V := q.subspace
      let rU : U.toFunctor ⟶ yoneda.obj T := U.ι ≫ pullback.fst p.toBase.hom f.hom
      let rV : V.toFunctor ⟶ yoneda.obj T := V.ι ≫ pullback.fst p.toBase.hom f.hom
      have hrU : @IsClosedMap _ _
          (pointTopology B S hS U.toFunctor)
          (pointTopology B S hS (yoneda.obj T))
          (pointsMap B S hS U.toFunctor rU) :=
        finiteSubspace_projection_isClosed B S hS f T p
      have hrV : @IsClosedMap _ _
          (pointTopology B S hS V.toFunctor)
          (pointTopology B S hS (yoneda.obj T))
          (pointsMap B S hS V.toFunctor rV) :=
        finiteSubspace_projection_isClosed B S hS f T q
      let D := (pointsMap B S hS U.toFunctor rU ''
            ((pointsMap B S hS U.toFunctor U.ι) ⁻¹'
              (Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ)) ∪
          (pointsMap B S hS V.toFunctor rV ''
            ((pointsMap B S hS V.toFunctor V.ι) ⁻¹'
              (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ))
      let W := Dᶜ
      have hW : @IsOpen _ (pointTopology B S hS (yoneda.obj T)) W :=
        finiteSubspaceAgreement_openPoints B S hS hM T p.isOpen q.isOpen rU rV hrU hrV
      classical
      letI : TopologicalSpace (points B S hS (yoneda.obj T)) :=
        pointTopology B S hS (yoneda.obj T)
      let ex := (pointTopologyFamily B S hS).scheme T W |>.mp hW
      let O := Classical.choose ex
      have hO := (Classical.choose_spec ex).1
      have hchar := (Classical.choose_spec ex).2
      exact ⟨W, hW, D, rfl, ⟨O, hO⟩, hchar⟩

private theorem openSubspaces_eq_of_same_pointImage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {M : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM : AlgebraicGeometry.IsAlgebraicSpace B S hS M)
    (U V : Subfunctor M)
    (hU : IsOpenSubspace B S hS U)
    (hV : IsOpenSubspace B S hS V)
    (hpoints : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      Set.range (pointsMap B S hS V.toFunctor V.ι)) : U = V := by
  let _ : TopologicalSpace (points B S hS M) :=
    pointTopology B S hS M
  let e := openSubspacesOrderIso B S hS M hM
  have he : e ⟨U, hU⟩ = e ⟨V, hV⟩ := by
    refine SetLike.ext fun x => ?_
    change x ∈ (openSubspacesOrderIso B S hS M hM ⟨U, hU⟩).1 ↔
      x ∈ (openSubspacesOrderIso B S hS M hM ⟨V, hV⟩).1
    rw [openSubspacesOrderIso_apply B S hS M hM ⟨U, hU⟩,
      openSubspacesOrderIso_apply B S hS M hM ⟨V, hV⟩, hpoints]
  exact congrArg Subtype.val (e.injective he)

private theorem point_mem_iff_away_from_finite_difference_images
    {A B M N : Type*} (i : A → M) (j : B → M)
    (r : A → N) (s : B → N) (q : M → N)
    (hri : ∀ a, q (i a) = r a) (hsj : ∀ b, q (j b) = s b)
    (t : N)
    (ht : t ∉
      (r '' (i ⁻¹' (Set.range j)ᶜ) ∪ s '' (j ⁻¹' (Set.range i)ᶜ)))
    (z : M) (hz : q z = t) : z ∈ Set.range i ↔ z ∈ Set.range j := by
  constructor
  · rintro ⟨a, rfl⟩
    by_contra hnot
    exact ht (Or.inl ⟨a, hnot, by rw [← hri, hz]⟩)
  · rintro ⟨b, rfl⟩
    by_contra hnot
    exact ht (Or.inr ⟨b, hnot, by rw [← hsj, hz]⟩)

private theorem contains_toScheme_opens
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    B.Contains V.toScheme := by
  change V.toScheme.size < B.cutoff
  exact (Scheme.size_coe_opens_le _ V).trans_lt T.left.2

private noncomputable def siteObjectOfSchemeOpen
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    AlgebraicGeometry.BigFppfOver B S hS := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hV := contains_toScheme_opens B S hS T V
  let vhom : B.inclusion.obj (B.obj hV) ⟶ B.inclusion.obj T.left := V.ι
  let m := B.inclusion.preimage vhom
  exact Over.mk (m ≫ T.hom)

private noncomputable def siteObjectOfSchemeOpen_inclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    siteObjectOfSchemeOpen B S hS T V ⟶ T := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hV := contains_toScheme_opens B S hS T V
  let vhom : B.inclusion.obj (B.obj hV) ⟶ B.inclusion.obj T.left := V.ι
  let m := B.inclusion.preimage vhom
  exact Over.homMk m (by simp [siteObjectOfSchemeOpen, m, vhom])

private theorem siteObjectOfSchemeOpen_inclusion_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (siteObjectOfSchemeOpen_inclusion B S hS T V) = V.ι := by
  have hV := contains_toScheme_opens B S hS T V
  let vhom : B.inclusion.obj (B.obj hV) ⟶ B.inclusion.obj T.left := V.ι
  change B.inclusion.map (B.inclusion.preimage vhom) = vhom
  exact B.inclusion.map_preimage vhom

private theorem exists_siteMap_factor_schemeOpen
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (V : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))
    (hrange : Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map h) ⊆ V.1) :
    ∃ k : T' ⟶ siteObjectOfSchemeOpen B S hS T V,
      k ≫ siteObjectOfSchemeOpen_inclusion B S hS T V = h := by
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  have hV := contains_toScheme_opens B S hS T V
  let vhom : B.inclusion.obj (B.obj hV) ⟶ B.inclusion.obj T.left := V.ι
  let m : B.obj (B.obj hV).property ⟶ T.left := B.inclusion.preimage vhom
  let g : Q.obj T' ⟶ Q.obj T := Q.map h
  have hrange' : Set.range g ⊆ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
  let l : Q.obj T' ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hrange'
  let l' : T'.left ⟶ B.obj hV := B.inclusion.preimage l
  have hleft : l' ≫ m = h.left := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
    exact IsOpenImmersion.lift_fac V.ι g hrange'
  let k : T' ⟶ siteObjectOfSchemeOpen B S hS T V :=
    Over.homMk l' (by
      change l' ≫ (m ≫ T.hom) = T'.hom
      rw [← Category.assoc, hleft]
      exact h.w)
  refine ⟨k, ?_⟩
  ext
  exact congrArg B.inclusion.map hleft

private theorem schemePoint_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (p : FieldValuedPoint B S hS (yoneda.obj T')) :
    schemePoint B S hS T
        (FieldValuedPoint.map B S hS (yoneda.obj T')
          (yoneda.map h) p) =
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map h
        (schemePoint B S hS T' p) :=
  rfl

private noncomputable def finiteSubspaceBaseChangeMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (p : FiniteOpenSubspace B S hS f
      (schemeSpace T))
    (q : FiniteOpenSubspace B S hS f
      (schemeSpace T'))
    (hbase : q.toBase.hom = (schemeSpaceMap h).hom ≫ p.toBase.hom) :
    pullback q.toBase.hom f.hom ⟶ pullback p.toBase.hom f.hom :=
  pullback.map q.toBase.hom f.hom p.toBase.hom f.hom
    ((schemeSpaceMap h).hom) (𝟙 X.1) (𝟙 Y.1) hbase (by simp)

private theorem ambientBaseChange_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (p : FiniteOpenSubspace B S hS f
      (schemeSpace T))
    (q : FiniteOpenSubspace B S hS f
      (schemeSpace T'))
    (hbase : q.toBase.hom = (schemeSpaceMap h).hom ≫ p.toBase.hom) :
    IsPullback (finiteSubspaceBaseChangeMap B S hS f h p q hbase)
      (pullback.fst q.toBase.hom f.hom)
      (pullback.fst p.toBase.hom f.hom)
      ((schemeSpaceMap h).hom) := by
  let k := finiteSubspaceBaseChangeMap B S hS f h p q hbase
  have hcond : k ≫ pullback.fst p.toBase.hom f.hom =
      pullback.fst q.toBase.hom f.hom ≫ (schemeSpaceMap h).hom := by
    dsimp [k, finiteSubspaceBaseChangeMap]
    simp only [pullback.lift_fst]
  have hksnd : k ≫ pullback.snd p.toBase.hom f.hom =
      pullback.snd q.toBase.hom f.hom := by
    dsimp [k, finiteSubspaceBaseChangeMap, pullback.map]
    rw [pullback.lift_snd]
    simp
  have houter : IsPullback
      (k ≫ pullback.snd p.toBase.hom f.hom)
      (pullback.fst q.toBase.hom f.hom) f.hom
      ((schemeSpaceMap h).hom ≫ p.toBase.hom) := by
    rw [hksnd, ← hbase]
    exact (IsPullback.of_hasPullback q.toBase.hom f.hom).flip
  exact IsPullback.of_right houter hcond
    (IsPullback.of_hasPullback p.toBase.hom f.hom).flip

private theorem finiteSubspace_baseChange_ambient_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (p : FiniteOpenSubspace B S hS f
      (schemeSpace T))
    (q : FiniteOpenSubspace B S hS f
      (schemeSpace T'))
    (hbc : FiniteOpenSubspace.IsBaseChange B S hS f h p q) :
    ∃ j : q.subspace.toFunctor ⟶ p.subspace.toFunctor,
      IsPullback q.subspace.ι j (finiteSubspaceBaseChangeMap B S hS f h p q hbc.1)
        p.subspace.ι := by
  obtain ⟨j, hj, hX⟩ := hbc.2
  have hbase : q.toBase.hom = (schemeSpaceMap h).hom ≫ p.toBase.hom := hbc.1
  have hj' : IsPullback
      (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j
      (schemeSpaceMap h).hom
      (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) := hj
  have hcomm : q.subspace.ι ≫ finiteSubspaceBaseChangeMap B S hS f h p q hbase =
      j ≫ p.subspace.ι := by
    apply pullback.hom_ext
    · dsimp [finiteSubspaceBaseChangeMap, pullback.map]
      simp only [Category.assoc, pullback.lift_fst]
      exact hj'.w
    · dsimp [finiteSubspaceBaseChangeMap, pullback.map]
      simp only [Category.assoc, pullback.lift_snd]
      exact hX.symm
  exact ⟨j, IsPullback.of_right hj' hcomm
    (ambientBaseChange_isPullback B S hS f h p q hbase).flip⟩

private theorem finiteSubspace_baseChange_pointImage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (p : FiniteOpenSubspace B S hS f
      (schemeSpace T))
    (q : FiniteOpenSubspace B S hS f
      (schemeSpace T'))
    (hbc : FiniteOpenSubspace.IsBaseChange B S hS f h p q) :
    Set.range (pointsMap B S hS q.subspace.toFunctor q.subspace.ι) =
      pointsMap B S hS (pullback q.toBase.hom f.hom)
        (finiteSubspaceBaseChangeMap B S hS f h p q hbc.1) ⁻¹'
          Set.range (pointsMap B S hS p.subspace.toFunctor p.subspace.ι) := by
  obtain ⟨j, hsq⟩ := finiteSubspace_baseChange_ambient_isPullback
    B S hS f h p q hbc
  exact pointsMap_range_of_isPullback B S hS q.isOpen.1
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS
      q.toBase.hom f.hom (schemeSpace T').property X.property Y.property) p.isOpen.1
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS
      p.toBase.hom f.hom (schemeSpace T).property X.property Y.property) hsq

private theorem openSubspaces_eq_after_baseChange_of_pointsInAgreement
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {M M' N : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hM' : AlgebraicGeometry.IsAlgebraicSpace B S hS M')
    (k : M' ⟶ M) (q : M ⟶ N)
    {U V : Subfunctor M} {U' V' : Subfunctor M'}
    (hU' : IsOpenSubspace B S hS U')
    (hV' : IsOpenSubspace B S hS V')
    (hUimage : Set.range (pointsMap B S hS U'.toFunctor U'.ι) =
      pointsMap B S hS M' k ⁻¹'
        Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hVimage : Set.range (pointsMap B S hS V'.toFunctor V'.ι) =
      pointsMap B S hS M' k ⁻¹'
        Set.range (pointsMap B S hS V.toFunctor V.ι))
    (W : Set (points B S hS N))
    (hpoints : ∀ z : points B S hS M',
      pointsMap B S hS M q
        (pointsMap B S hS M' k z) ∈ W)
    (haway : ∀ t : points B S hS N, t ∈ W →
      t ∉
        (pointsMap B S hS U.toFunctor (U.ι ≫ q) ''
          ((pointsMap B S hS U.toFunctor U.ι) ⁻¹'
            (Set.range (pointsMap B S hS V.toFunctor V.ι))ᶜ) ∪
         pointsMap B S hS V.toFunctor (V.ι ≫ q) ''
          ((pointsMap B S hS V.toFunctor V.ι) ⁻¹'
            (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ))) :
    U' = V' := by
  classical
  have himage : Set.range (pointsMap B S hS U'.toFunctor U'.ι) =
      Set.range (pointsMap B S hS V'.toFunctor V'.ι) := by
    ext z
    rw [hUimage, hVimage]
    exact point_mem_iff_away_from_finite_difference_images
      (pointsMap B S hS U.toFunctor U.ι)
      (pointsMap B S hS V.toFunctor V.ι)
      (pointsMap B S hS U.toFunctor (U.ι ≫ q))
      (pointsMap B S hS V.toFunctor (V.ι ≫ q))
      (pointsMap B S hS M q)
      (fun x => (congrFun (pointsMap_comp B S hS _ U.ι q) x).symm)
      (fun x => (congrFun (pointsMap_comp B S hS _ V.ι q) x).symm)
      _ (haway _ (hpoints z)) (pointsMap B S hS M' k z) rfl
  exact openSubspaces_eq_of_same_pointImage B S hS hM' U' V' hU' hV' himage

private theorem pointMap_not_in_finite_difference_image
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (pBase : schemeSpace T ⟶ Y)
    (pSub qSub : Subfunctor (pullback pBase.hom f.hom))
    (pOpen : IsOpenSubspace B S hS pSub)
    (qOpen : IsOpenSubspace B S hS qSub)
    (pFinite : IsFinite B S hS
      (pSub.ι ≫ pullback.fst pBase.hom f.hom))
    (qFinite : IsFinite B S hS
      (qSub.ι ≫ pullback.fst pBase.hom f.hom))
    (pBase' : schemeSpace T' ⟶ Y)
    (pSub' qSub' : Subfunctor (pullback pBase'.hom f.hom))
    (pOpen' : IsOpenSubspace B S hS pSub')
    (qOpen' : IsOpenSubspace B S hS qSub')
    (pFinite' : IsFinite B S hS
      (pSub'.ι ≫ pullback.fst pBase'.hom f.hom))
    (qFinite' : IsFinite B S hS
      (qSub'.ι ≫ pullback.fst pBase'.hom f.hom))
    (hbc : FiniteOpenSubspace.IsBaseChange B S hS f h
      (⟨pBase, pSub, pOpen, pFinite⟩ : FiniteOpenSubspace B S hS f
        (schemeSpace T))
      ⟨pBase', pSub', pOpen', pFinite'⟩)
    (hbc' : FiniteOpenSubspace.IsBaseChange B S hS f h
      (⟨pBase, qSub, qOpen, qFinite⟩ : FiniteOpenSubspace B S hS f
        (schemeSpace T))
      ⟨pBase', qSub', qOpen', qFinite'⟩)
    (hsub : pSub' = qSub')
    (z : points B S hS (yoneda.obj T')) :
    pointsMap B S hS (yoneda.obj T') (yoneda.map h) z ∉
      pointsMap B S hS pSub.toFunctor
        (pSub.ι ≫ pullback.fst pBase.hom f.hom) ''
        ((pointsMap B S hS pSub.toFunctor pSub.ι) ⁻¹'
          (Set.range (pointsMap B S hS qSub.toFunctor qSub.ι))ᶜ) := by
  let p : FiniteOpenSubspace B S hS f (schemeSpace T) := ⟨pBase, pSub, pOpen, pFinite⟩
  let q : FiniteOpenSubspace B S hS f (schemeSpace T) := ⟨pBase, qSub, qOpen, qFinite⟩
  let p' : FiniteOpenSubspace B S hS f (schemeSpace T') := ⟨pBase', pSub', pOpen', pFinite'⟩
  let q' : FiniteOpenSubspace B S hS f (schemeSpace T') := ⟨pBase', qSub', qOpen', qFinite'⟩
  have hbaseMap : pBase'.hom = (schemeSpaceMap h).hom ≫ pBase.hom := hbc.1
  let M' := pullback p'.toBase.hom f.hom
  let K := finiteSubspaceBaseChangeMap B S hS f h p p' hbaseMap
  let hM := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p.toBase.hom f.hom
    (schemeSpace T).property X.property Y.property
  let hM' := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS p'.toBase.hom f.hom
    (schemeSpace T').property X.property Y.property
  have hsq := ambientBaseChange_isPullback B S hS f h p p' hbaseMap
  have himage := finiteSubspace_baseChange_pointImage B S hS f h p p' hbc
  have himage' := finiteSubspace_baseChange_pointImage B S hS f h q q' hbc'
  have himage'' : Set.range
      (pointsMap B S hS q'.subspace.toFunctor q'.subspace.ι) =
      pointsMap B S hS M' K ⁻¹'
        Set.range (pointsMap B S hS q.subspace.toFunctor q.subspace.ι) := by
    simpa [K, M', finiteSubspaceBaseChangeMap] using himage'
  rintro ⟨v, hv, hvt⟩
  let zM := pointsMap B S hS p.subspace.toFunctor p.subspace.ι v
  have hcompat : pointsMap B S hS
      (pullback p.toBase.hom f.hom) (pullback.fst p.toBase.hom f.hom) zM =
      pointsMap B S hS (yoneda.obj T') (schemeSpaceMap h).hom z :=
    (congrFun (pointsMap_comp B S hS _ p.subspace.ι
      (pullback.fst p.toBase.hom f.hom)) v).symm.trans hvt
  have hlift : zM ∈ Set.range (pointsMap B S hS M' K) := by
    rw [pointsMap_range_of_isPullback B S hS hM' hM
      (schemeSpace T').property (schemeSpace T).property hsq]
    exact ⟨z, hcompat.symm⟩
  obtain ⟨w, hw⟩ := hlift
  have hwP : pointsMap B S hS M' K w ∈
      Set.range (pointsMap B S hS p.subspace.toFunctor p.subspace.ι) := by
    rw [hw]
    exact ⟨v, rfl⟩
  have hwP' : w ∈ Set.range (pointsMap B S hS p'.subspace.toFunctor p'.subspace.ι) := by
    rw [himage]
    exact hwP
  have hwQ : w ∈ Set.range (pointsMap B S hS q'.subspace.toFunctor q'.subspace.ι) := by
    change w ∈ Set.range (pointsMap B S hS qSub'.toFunctor qSub'.ι)
    exact hsub ▸ hwP'
  rw [himage'', Set.mem_preimage, hw] at hwQ
  exact hv hwQ

private theorem pullbackDiagonal_isPullback_absoluteDiagonal
    {C : Type u} [Category C] [HasPullbacks C] [HasBinaryProducts C]
    {F G : C} (a : F ⟶ G) :
    IsPullback
      (pullback.fst a a ≫ a)
      (prod.lift (pullback.fst a a) (pullback.snd a a))
      (Limits.diag G)
      (prod.map a a) := by
  let q := prod.lift (pullback.fst a a) (pullback.snd a a)
  let b := pullback.fst a a ≫ a
  have hq : b ≫ Limits.diag G = q ≫ prod.map a a := by
    apply prod.hom_ext
    · simp [q, b]
    · simpa [q, b] using pullback.condition (f := a) (g := a)
  have hproj : ∀ (s : PullbackCone (Limits.diag G) (prod.map a a)) (π : G ⨯ G ⟶ G)
      (π' : F ⨯ F ⟶ F), prod.map a a ≫ π = π' ≫ a → Limits.diag G ≫ π = 𝟙 G →
      (s.snd ≫ π') ≫ a = s.fst := fun s π π' h1 h2 => by
    calc
      _ = (s.snd ≫ prod.map a a) ≫ π := by rw [Category.assoc, Category.assoc, h1]
      _ = (s.fst ≫ Limits.diag G) ≫ π := by rw [← s.condition]
      _ = s.fst := by rw [Category.assoc, h2, Category.comp_id]
  have hfst : ∀ s : PullbackCone (Limits.diag G) (prod.map a a),
      (s.snd ≫ prod.fst) ≫ a = s.fst := fun s =>
    hproj s prod.fst prod.fst (by simp) (by simp [Limits.diag])
  have hsnd : ∀ s : PullbackCone (Limits.diag G) (prod.map a a),
      (s.snd ≫ prod.snd) ≫ a = s.fst := fun s =>
    hproj s prod.snd prod.snd (by simp) (by simp [Limits.diag])
  refine ⟨⟨hq⟩, ⟨PullbackCone.IsLimit.mk hq (fun s => pullback.lift
    (s.snd ≫ prod.fst) (s.snd ≫ prod.snd) ((hfst s).trans (hsnd s).symm)) ?_ ?_ ?_⟩⟩
  · intro s
    dsimp [b]
    rw [← Category.assoc, pullback.lift_fst]
    exact hfst s
  · intro s
    apply prod.hom_ext
    · simp only [q, prod.comp_lift, prod.lift_fst, pullback.lift_fst]
    · simp only [q, prod.comp_lift, prod.lift_snd, pullback.lift_snd]
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · simpa only [q, prod.comp_lift, prod.lift_fst, pullback.lift_fst] using
        congrArg (fun k => k ≫ prod.fst) hm₂
    · simpa only [q, prod.comp_lift, prod.lift_snd, pullback.lift_snd] using
        congrArg (fun k => k ≫ prod.snd) hm₂

/-- If the diagonal of `a` followed by a retraction `π` is the identity, a section agreeing
with the diagonal is the pullback of `g ≫ π`. -/
private theorem eq_map_yonedaEquiv_of_diagonal_app_eq
    {C : Type*} [Category.{u} C] {F G : Cᵒᵖ ⥤ Type u} (a : F ⟶ G) {T : C}
    (g : yoneda.obj T ⟶ pullback a a) (π : pullback a a ⟶ F)
    (hπ : pullback.diagonal a ≫ π = 𝟙 F) {T' : Cᵒᵖ} {x₂ : F.obj T'} {x₃ : T'.unop ⟶ T}
    (hx : (pullback.diagonal a).app T' x₂ = g.app T' x₃) :
    x₂ = F.map x₃.op (yonedaEquiv (g ≫ π)) := by
  have hproj := congrArg (fun z => π.app T' z) hx
  have hcomp : (pullback.diagonal a).app T' ≫ π.app T' = 𝟙 _ := by
    simpa only [NatTrans.comp_app, NatTrans.id_app] using congrArg (fun k => k.app T') hπ
  have hdiag : π.app T' ((pullback.diagonal a).app T' x₂) = x₂ := by
    simpa [ConcreteCategory.comp_apply] using
      congrArg (fun k => (ConcreteCategory.hom k) x₂) hcomp
  have hnat := (g ≫ π).naturality_apply x₃.op (𝟙 T)
  have hξ : yonedaEquiv (g ≫ π) = (ConcreteCategory.hom ((g ≫ π).app (Opposite.op T))) (𝟙 T) :=
    rfl
  rw [← hξ] at hnat
  calc
    x₂ = π.app T' (g.app T' x₃) := hdiag.symm.trans hproj
    _ = F.map x₃.op (yonedaEquiv (g ≫ π)) := by simpa using hnat

private theorem mono_siteObjectOfSchemeOpen_inclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    Mono (siteObjectOfSchemeOpen_inclusion B S hS T V) := by
  have hmono : Mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (siteObjectOfSchemeOpen_inclusion B S hS T V)) := by
    rw [siteObjectOfSchemeOpen_inclusion_map]
    exact AlgebraicGeometry.IsOpenImmersion.mono V.ι
  exact (AlgebraicGeometry.BigFppfOver.toScheme B S hS).mono_of_mono_map hmono

private theorem map_eq_of_range_subset_agreementOpen
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (fin : FinitePartPresheaf B S hS f)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    {ξ η : fin.toFunctor.obj (Opposite.op T)}
    {pBase : schemeSpace T ⟶ Y} {pSub qSub : Subfunctor (pullback pBase.hom f.hom)}
    {pOpen : IsOpenSubspace B S hS pSub} {qOpen : IsOpenSubspace B S hS qSub}
    {pFinite : IsFinite B S hS (pSub.ι ≫ pullback.fst pBase.hom f.hom)}
    {qFinite : IsFinite B S hS (qSub.ι ≫ pullback.fst pBase.hom f.hom)}
    (hP : fin.sections T ξ = ⟨pBase, pSub, pOpen, pFinite⟩)
    (hQ : fin.sections T η = ⟨pBase, qSub, qOpen, qFinite⟩)
    (hrange : Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map h) ⊆
      (finiteSubspaceAgreementOpenData B S hS f T ⟨pBase, pSub, pOpen, pFinite⟩
        ⟨pBase, qSub, qOpen, qFinite⟩ rfl).schemeOpen.1) :
    fin.toFunctor.map h.op ξ = fin.toFunctor.map h.op η := by
  let pN : FiniteOpenSubspace B S hS f (schemeSpace T) := ⟨pBase, pSub, pOpen, pFinite⟩
  let qN : FiniteOpenSubspace B S hS f (schemeSpace T) := ⟨pBase, qSub, qOpen, qFinite⟩
  let data := finiteSubspaceAgreementOpenData B S hS f T pN qN rfl
  have hpbc := fin.map_isBaseChange h ξ
  have hqbc := fin.map_isBaseChange h η
  cases hR : fin.sections T' (fin.toFunctor.map h.op ξ) with
  | mk prBase prSub prOpen prFinite =>
  cases hS' : fin.sections T' (fin.toFunctor.map h.op η) with
  | mk qrBase qrSub qrOpen qrFinite =>
  rw [hP, hR] at hpbc
  rw [hQ, hS'] at hqbc
  obtain rfl : prBase = qrBase := ObjectProperty.hom_ext _ (hpbc.1.trans hqbc.1.symm)
  let prFinal : FiniteOpenSubspace B S hS f (schemeSpace T') := ⟨prBase, prSub, prOpen, prFinite⟩
  let qrFinal : FiniteOpenSubspace B S hS f (schemeSpace T') := ⟨prBase, qrSub, qrOpen, qrFinite⟩
  let M := pullback pN.toBase.hom f.hom
  let M' := pullback prFinal.toBase.hom f.hom
  let fstM := pullback.fst pN.toBase.hom f.hom
  let fstM' := pullback.fst prFinal.toBase.hom f.hom
  let K := finiteSubspaceBaseChangeMap B S hS f h pN prFinal hpbc.1
  have hVimage : Set.range
      (pointsMap B S hS qrFinal.subspace.toFunctor qrFinal.subspace.ι) =
      pointsMap B S hS M' K ⁻¹'
        Set.range (pointsMap B S hS qN.subspace.toFunctor qN.subspace.ι) := by
    simpa [K, M', finiteSubspaceBaseChangeMap] using
      finiteSubspace_baseChange_pointImage B S hS f h qN qrFinal hqbc
  have hpoints : ∀ z : points B S hS M',
      pointsMap B S hS M fstM (pointsMap B S hS M' K z) ∈ data.points := by
    intro z
    induction z using Quot.inductionOn with
    | _ z =>
      let zBase := FieldValuedPoint.map B S hS M' fstM' z
      let z' := FieldValuedPoint.map B S hS (yoneda.obj T') (yoneda.map h) zBase
      have hx : schemePoint B S hS T z' ∈ data.schemeOpen.1 := by
        rw [schemePoint_map B S hS h zBase]
        exact hrange ⟨_, rfl⟩
      have hclass : pointsMap B S hS M fstM
          (pointsMap B S hS M' K (z.class B S hS M')) =
            z'.class B S hS (yoneda.obj T) := by
        have hw := congrFun (congrArg (pointsMap B S hS M')
          (ambientBaseChange_isPullback B S hS f h pN prFinal hpbc.1).w) (z.class B S hS M')
        simp only [pointsMap_comp, Function.comp_apply] at hw
        exact hw
      exact hclass ▸ (data.point_iff z').2 hx
  have hsubeq : prSub = qrSub :=
    openSubspaces_eq_after_baseChange_of_pointsInAgreement B S hS
      (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS prFinal.toBase.hom f.hom
        (schemeSpace T').property X.property Y.property)
      K fstM prFinal.isOpen qrFinal.isOpen
      (finiteSubspace_baseChange_pointImage B S hS f h pN prFinal hpbc) hVimage data.points
      hpoints fun t ht => by rwa [data.points_eq_compl_disagreement] at ht
  subst hsubeq
  exact (fin.sections T').injective (hR.trans hS'.symm)

private theorem range_subset_agreementOpen_of_map_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (fin : FinitePartPresheaf B S hS f)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    {ξ η : fin.toFunctor.obj (Opposite.op T)}
    {pBase : schemeSpace T ⟶ Y} {pSub qSub : Subfunctor (pullback pBase.hom f.hom)}
    {pOpen : IsOpenSubspace B S hS pSub} {qOpen : IsOpenSubspace B S hS qSub}
    {pFinite : IsFinite B S hS (pSub.ι ≫ pullback.fst pBase.hom f.hom)}
    {qFinite : IsFinite B S hS (qSub.ι ≫ pullback.fst pBase.hom f.hom)}
    (hP : fin.sections T ξ = ⟨pBase, pSub, pOpen, pFinite⟩)
    (hQ : fin.sections T η = ⟨pBase, qSub, qOpen, qFinite⟩)
    (hsec : fin.toFunctor.map h.op ξ = fin.toFunctor.map h.op η) :
    Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map h) ⊆
      (finiteSubspaceAgreementOpenData B S hS f T ⟨pBase, pSub, pOpen, pFinite⟩
        ⟨pBase, qSub, qOpen, qFinite⟩ rfl).schemeOpen.1 := by
  let pN : FiniteOpenSubspace B S hS f (schemeSpace T) := ⟨pBase, pSub, pOpen, pFinite⟩
  let qN : FiniteOpenSubspace B S hS f (schemeSpace T) := ⟨pBase, qSub, qOpen, qFinite⟩
  let data := finiteSubspaceAgreementOpenData B S hS f T pN qN rfl
  have hbcP := fin.map_isBaseChange h ξ
  have hbcQ := fin.map_isBaseChange h η
  rw [hP] at hbcP
  rw [hQ, ← hsec] at hbcQ
  cases hR : fin.sections T' (fin.toFunctor.map h.op ξ) with
  | mk pBase' pSub' pOpen' pFinite' =>
  rw [hR] at hbcP hbcQ
  rintro y ⟨x, rfl⟩
  let r := schemePointRepresentative B S hS T' x
  let z := r.class B S hS (yoneda.obj T')
  have hnotD : pointsMap B S hS (yoneda.obj T') (yoneda.map h) z ∉ data.disagreement :=
    not_or.mpr
      ⟨pointMap_not_in_finite_difference_image B S hS f h pBase pSub qSub pOpen qOpen
        pFinite qFinite pBase' pSub' pSub' pOpen' pOpen' pFinite' pFinite' hbcP hbcQ rfl z,
      pointMap_not_in_finite_difference_image B S hS f h pBase qSub pSub qOpen pOpen
        qFinite pFinite pBase' pSub' pSub' pOpen' pOpen' pFinite' pFinite' hbcQ hbcP rfl z⟩
  have hpointsT : pointsMap B S hS (yoneda.obj T') (yoneda.map h) z ∈ data.points := by
    rw [data.points_eq_compl_disagreement]
    simpa using hnotD
  rw [← schemePointRepresentative_point B S hS T' x, ← schemePoint_map B S hS h r]
  exact (data.point_iff _).mp hpointsT

private theorem range_toScheme_map_siteObjectOfSchemeOpen_inclusion_subset
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    Set.range ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (siteObjectOfSchemeOpen_inclusion B S hS T V)) ⊆ V.1 := by
  rw [siteObjectOfSchemeOpen_inclusion_map]
  rintro x ⟨y, rfl⟩
  exact y.2

private theorem isOpenImmersion_toScheme_map_siteObjectOfSchemeOpen_inclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : Scheme.Opens ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T)) :
    AlgebraicGeometry.IsOpenImmersion ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
      (siteObjectOfSchemeOpen_inclusion B S hS T V)) := by
  rw [siteObjectOfSchemeOpen_inclusion_map]
  exact Scheme.Opens.instIsOpenImmersionι V

private theorem sections_toBase_fst_eq_snd
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (fin : FinitePartPresheaf B S hS f)
    {T : AlgebraicGeometry.BigFppfOver B S hS}
    (g : yoneda.obj T ⟶ pullback fin.baseMap fin.baseMap) :
    (fin.sections T (yonedaEquiv (g ≫ pullback.fst fin.baseMap fin.baseMap))).toBase.hom =
      (fin.sections T (yonedaEquiv (g ≫ pullback.snd fin.baseMap fin.baseMap))).toBase.hom := by
  rw [← fin.baseMap_spec, ← fin.baseMap_spec,
    ← yonedaEquiv_symm_naturality_right T fin.baseMap,
    ← yonedaEquiv_symm_naturality_right T fin.baseMap]
  simp only [Equiv.symm_apply_apply, Category.assoc]
  rw [pullback.condition]

private theorem exists_lift_of_diagonal_app_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (fin : FinitePartPresheaf B S hS f)
    {T : AlgebraicGeometry.BigFppfOver B S hS}
    (g : yoneda.obj T ⟶ pullback fin.baseMap fin.baseMap)
    {pBase : schemeSpace T ⟶ Y} {pSub qSub : Subfunctor (pullback pBase.hom f.hom)}
    {pOpen : IsOpenSubspace B S hS pSub} {qOpen : IsOpenSubspace B S hS qSub}
    {pFinite : IsFinite B S hS (pSub.ι ≫ pullback.fst pBase.hom f.hom)}
    {qFinite : IsFinite B S hS (qSub.ι ≫ pullback.fst pBase.hom f.hom)}
    (hP : fin.sections T (yonedaEquiv (g ≫ pullback.fst fin.baseMap fin.baseMap)) =
      ⟨pBase, pSub, pOpen, pFinite⟩)
    (hQ : fin.sections T (yonedaEquiv (g ≫ pullback.snd fin.baseMap fin.baseMap)) =
      ⟨pBase, qSub, qOpen, qFinite⟩)
    {T' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ} {x₂ : fin.toFunctor.obj T'}
    {x₃ : T'.unop ⟶ T} (hx : (pullback.diagonal fin.baseMap).app T' x₂ = g.app T' x₃) :
    ∃ x₁, (yonedaEquiv.symm (fin.toFunctor.map (siteObjectOfSchemeOpen_inclusion B S hS T
          (finiteSubspaceAgreementOpenData B S hS f T ⟨pBase, pSub, pOpen, pFinite⟩
            ⟨pBase, qSub, qOpen, qFinite⟩ rfl).schemeOpen).op
          (yonedaEquiv (g ≫ pullback.fst fin.baseMap fin.baseMap)))).app T' x₁ = x₂ ∧
      (yoneda.map (siteObjectOfSchemeOpen_inclusion B S hS T
          (finiteSubspaceAgreementOpenData B S hS f T ⟨pBase, pSub, pOpen, pFinite⟩
            ⟨pBase, qSub, qOpen, qFinite⟩ rfl).schemeOpen)).app T' x₁ = x₃ := by
  let ξ := yonedaEquiv (g ≫ pullback.fst fin.baseMap fin.baseMap)
  let V := (finiteSubspaceAgreementOpenData B S hS f T ⟨pBase, pSub, pOpen, pFinite⟩
    ⟨pBase, qSub, qOpen, qFinite⟩ rfl).schemeOpen
  let i := siteObjectOfSchemeOpen_inclusion B S hS T V
  let h : T'.unop ⟶ T := x₃
  have hxξ : x₂ = fin.toFunctor.map h.op ξ :=
    eq_map_yonedaEquiv_of_diagonal_app_eq _ g _ (pullback.diagonal_fst _) hx
  have hxη : x₂ = fin.toFunctor.map h.op
      (yonedaEquiv (g ≫ pullback.snd fin.baseMap fin.baseMap)) :=
    eq_map_yonedaEquiv_of_diagonal_app_eq _ g _ (pullback.diagonal_snd _) hx
  obtain ⟨k, hki⟩ := exists_siteMap_factor_schemeOpen B S hS h V
    (range_subset_agreementOpen_of_map_eq B S hS fin h hP hQ (hxξ.symm.trans hxη))
  let x₁ := yonedaEquiv (yoneda.map k)
  have hsecond : (yoneda.map i).app T' x₁ = x₃ := hki
  refine ⟨x₁, ?_, hsecond⟩
  rw [← yonedaEquiv_symm_naturality_left i fin.toFunctor ξ]
  change (ConcreteCategory.hom ((yonedaEquiv.symm ξ).app T'))
    ((ConcreteCategory.hom ((yoneda.map i).app T')) x₁) = x₂
  rw [hsecond]
  calc
    _ = fin.toFunctor.map h.op ξ := by simp [h]
    _ = x₂ := hxξ.symm

private instance (priority := high) hasPullback_baseMap_finitePartDiagonal
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    HasLimit (cospan (finiteOpenSubspacePresheaf B S hS f).baseMap
      (finiteOpenSubspacePresheaf B S hS f).baseMap) :=
  hasPullback_presheaf_finitePartDiagonal B S hS _ _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is expensive in this proof
/-- **Stacks 04PK, the relative diagonal.** For a morphism `f : X ⟶ Y` of algebraic spaces
over `S`, the diagonal `(X/Y)_fin ⟶ (X/Y)_fin ×_Y (X/Y)_fin` is representable by schemes and
an open immersion. -/
@[stacks 04PK "relative diagonal"]
theorem isOpenImmersion_diagonal_finiteOpenSubspacePresheaf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsOpenImmersion B S hS
      (pullback.diagonal (finiteOpenSubspacePresheaf B S hS f).baseMap) := by
  classical
  let a := (finiteOpenSubspacePresheaf B S hS f).baseMap
  let Q : MorphismProperty Scheme.{u} := @AlgebraicGeometry.IsOpenImmersion.{u}
  let P := MorphismProperty.inverseImage Q (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  change P.presheaf (pullback.diagonal a)
  apply MorphismProperty.relative.of_exists (P := P) (F := yoneda)
  intro T g
  let fin := finiteOpenSubspacePresheaf B S hS f
  let ξ := yonedaEquiv (g ≫ pullback.fst a a)
  let η := yonedaEquiv (g ≫ pullback.snd a a)
  have hbase : (fin.sections T ξ).toBase.hom = (fin.sections T η).toBase.hom :=
    sections_toBase_fst_eq_snd B S hS fin g
  cases hP : fin.sections T ξ with
  | mk pBase pSub pOpen pFinite =>
  cases hQ : fin.sections T η with
  | mk qBase qSub qOpen qFinite =>
  obtain rfl : pBase = qBase := ObjectProperty.hom_ext _ (by simpa [hP, hQ] using hbase)
  let V := (finiteSubspaceAgreementOpenData B S hS f T ⟨pBase, pSub, pOpen, pFinite⟩
    ⟨pBase, qSub, qOpen, qFinite⟩ rfl).schemeOpen
  let Usite := siteObjectOfSchemeOpen B S hS T V
  let i := siteObjectOfSchemeOpen_inclusion B S hS T V
  have hsections : fin.toFunctor.map i.op ξ = fin.toFunctor.map i.op η :=
    map_eq_of_range_subset_agreementOpen B S hS fin i hP hQ
      (range_toScheme_map_siteObjectOfSchemeOpen_inclusion_subset B S hS T V)
  let fst : yoneda.obj Usite ⟶ fin.toFunctor := yonedaEquiv.symm (fin.toFunctor.map i.op ξ)
  have hfst : fst = yoneda.map i ≫ yonedaEquiv.symm ξ :=
    (yonedaEquiv_symm_naturality_left i fin.toFunctor ξ).symm
  have hsnd : fst = yoneda.map i ≫ yonedaEquiv.symm η :=
    (congrArg yonedaEquiv.symm hsections).trans
      (yonedaEquiv_symm_naturality_left i fin.toFunctor η).symm
  have hcomm : fst ≫ pullback.diagonal a = yoneda.map i ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, hfst, Category.assoc]
      exact congrArg (yoneda.map i ≫ ·) (yonedaEquiv.symm_apply_apply _)
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hsnd, Category.assoc]
      exact congrArg (yoneda.map i ≫ ·) (yonedaEquiv.symm_apply_apply _)
  refine ⟨Usite, fst, i, ?_,
    isOpenImmersion_toScheme_map_siteObjectOfSchemeOpen_inclusion B S hS T V⟩
  refine IsPullback.of_forall_isPullback_app fun T' => ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k => k.app T') hcomm, ?_, ?_⟩
  · rintro x y ⟨_, hxyi⟩
    have _ : Mono i := mono_siteObjectOfSchemeOpen_inclusion B S hS T V
    have _ : Mono (yoneda.map i) := inferInstance
    have _ : Mono ((yoneda.map i).app T') := inferInstance
    exact (mono_iff_injective _).mp inferInstance hxyi
  · exact fun x₂ x₃ hx => exists_lift_of_diagonal_app_eq B S hS fin g hP hQ hx

/-- **Stacks 04PK, the absolute diagonal.** For a morphism `f : X ⟶ Y` of algebraic spaces
over `S`, the absolute diagonal `(X/Y)_fin ⟶ (X/Y)_fin × (X/Y)_fin` is representable by
schemes: it is the relative diagonal followed by a base change of the diagonal of `Y`. -/
@[stacks 04PK "absolute diagonal"]
theorem relativelyRepresentable_diag_finiteOpenSubspacePresheaf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    yoneda.relativelyRepresentable
      (diag (finiteOpenSubspacePresheaf B S hS f).toFunctor) := by
  classical
  let F := (finiteOpenSubspacePresheaf B S hS f).toFunctor
  let a := (finiteOpenSubspacePresheaf B S hS f).baseMap
  let q := prod.lift (pullback.fst a a) (pullback.snd a a)
  have hq : yoneda.relativelyRepresentable q :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (pullbackDiagonal_isPullback_absoluteDiagonal a) Y.property.diagonal_representable
  have hd : yoneda.relativelyRepresentable (pullback.diagonal a) :=
    isOpenImmersion_diagonal_finiteOpenSubspacePresheaf B S hS f |>.1
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let _ : MorphismProperty.IsMultiplicative
      (yoneda.relativelyRepresentable : MorphismProperty (Cᵒᵖ ⥤ Type u)) :=
    Functor.relativelyRepresentable.isMultiplicative (F := yoneda)
  have hcomp : yoneda.relativelyRepresentable ((pullback.diagonal a) ≫ q) :=
    MorphismProperty.comp_mem _ _ _ hd hq
  have hfac : (pullback.diagonal a) ≫ q = diag F := by
    apply prod.hom_ext <;>
      simp only [Category.assoc, q, prod.lift_fst, prod.lift_snd, pullback.diagonal_fst,
        pullback.diagonal_snd, Limits.diag] <;>
      first
        | rw [prod.lift_fst]
        | rw [prod.lift_snd]
  exact hfac ▸ hcomp

end AlgebraicGeometry.Space

end
