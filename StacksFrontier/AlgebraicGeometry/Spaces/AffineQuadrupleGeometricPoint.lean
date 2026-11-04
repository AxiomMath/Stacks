module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuadrupleEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompCondition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
import all StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# An affine étale quadruple through a geometric point

Let `g' ≫ f = f' ≫ g` be a cartesian square of algebraic spaces and `x̄'` a geometric point of
`X' = Y' ×_Y X`. There are affine schemes `U ⟶ V ⟵ V'` étale over `X ⟶ Y ⟵ Y'` such that, with
`U' = V' ×_V U` and its induced morphism `a' : U' ⟶ X'`, the point `x̄'` lifts to `U'`. These are
the affine quadruples of condition (2) of Stacks 0DKG, and the lift is how condition (2) is read
at a geometric point of `X'`.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_geometricPoint_lift`: a geometric point of an
  algebraic space lifts to an affine étale chart.
* `AlgebraicGeometry.Space.geometricPoint_eq_of_isPullback`: a geometric point of a fibre
  product of presheaves is determined by its two images.
* `AlgebraicGeometry.Space.exists_affineQuadruple_geometricPoint`: the affine quadruple through
  a geometric point of `X'`.
* `AlgebraicGeometry.Space.exists_etaleDiagram_isSurjective`: an étale diagram of schemes with
  `U' ⟶ X'` surjective, as in condition (3) of Stacks 0DKG.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A geometric point lifts to an affine étale chart.** For a geometric point `x̄` of an
algebraic space `F` there is an étale morphism `a : U ⟶ F` from an affine scheme of the site and
a geometric point of `U` over `x̄`. -/
theorem exists_affine_etale_geometricPoint_lift (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) :
    ∃ (U : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (a : yoneda.obj U ⟶ X.1) (_ : IsEtale B S hS a) (u : GeometricPoint B S hS (yoneda.obj U)),
      geometricPointMap a u = x := by
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  obtain ⟨N⟩ : Nonempty (SmallEtaleNeighborhood x) := IsCofiltered.nonempty
  obtain ⟨M, -, hM⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS X x N
  exact ⟨(SmallEtale.toOver B S hS X.1).obj M.chart, hM, M.chart.obj.hom,
    (isEtale_iff_presheaf_of_yoneda B S hS _).2 M.chart.property,
    chartPresheafGeometricPoint B S hS x M,
    geometricPointMap_chartPresheafGeometricPoint B S hS x M⟩

/-- **A geometric point of a fibre product is determined by its two images.** In a cartesian
square of presheaves, two geometric points of the upper left corner with the same images in the
two middle terms are equal. -/
theorem geometricPoint_eq_of_isPullback {Q Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : Q ⟶ Z} {q : Q ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (w₁ w₂ : GeometricPoint B S hS Q) (hp : geometricPointMap p w₁ = geometricPointMap p w₂)
    (hq : geometricPointMap q w₁ = geometricPointMap q w₂) : w₁ = w₂ := by
  obtain ⟨⟨k₁, hc₁, t₁, v₁⟩, h₁⟩ := w₁
  obtain ⟨⟨k₂, hc₂, t₂, v₂⟩, h₂⟩ := w₂
  have hv := congrArg Subtype.val hp
  have hv' := congrArg Subtype.val hq
  simp only [geometricPointMap, FieldValuedPoint.map, FieldValuedPoint.mk.injEq] at hv hv'
  obtain ⟨rfl, hfi, hto, he⟩ := hv
  obtain rfl := eq_of_heq hfi
  obtain rfl := eq_of_heq hto
  obtain rfl : v₁ = v₂ := by
    apply (yonedaEquiv (X := Over.mk (⟨t₁⟩ : B.obj hc₁ ⟶ B.obj hS)) (F := Q)).symm.injective
    refine sq.hom_ext ?_ ?_ <;> apply yonedaEquiv.injective <;>
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exacts [eq_of_heq he, eq_of_heq hv'.2.2.2]
  rfl

section Quadruple

variable {B S hS}

/-- The map `U ⟶ V` induced by a chart `m` of `V ×_Y X` commutes over `Y` with `U ⟶ X`. -/
private theorem representedSpaceMap_comp_eq_homMk_comp {V U : BigFppfOver B S hS}
    {X Y : AlgebraicSpaces B S hS}
    (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (f : X ⟶ Y) (m : yoneda.obj U ⟶ (pullback b f).1) (f₀ : U ⟶ V)
    (hf₀ : yoneda.map f₀ = m ≫ (pullback.fst b f).hom) :
    representedSpaceMap B S hS f₀ ≫ b = ObjectProperty.homMk (m ≫ (pullback.snd b f).hom) ≫ f := by
  refine ObjectProperty.hom_ext _ ?_
  show yoneda.map f₀ ≫ b.hom = (m ≫ (pullback.snd b f).hom) ≫ f.hom
  rw [hf₀, Category.assoc, Category.assoc]
  exact congrArg (fun k => m ≫ k.hom) (pullback.condition (f := b) (g := f))

/-- The compatibility of the two charts over `Y`, used to lift into the fibre product `X'`. -/
private theorem comp_eq_comp_of_pullback_charts {V U V' : BigFppfOver B S hS}
    {X Y Y' : AlgebraicSpaces B S hS}
    {a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X}
    {b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y}
    {c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f₀ : U ⟶ V} {g₀ : V' ⟶ V}
    (hfa : representedSpaceMap B S hS f₀ ≫ b = a ≫ f)
    (hgc : representedSpaceMap B S hS g₀ ≫ b = c ≫ g) :
    (representedSpaceMap B S hS (pullback.fst f₀ g₀) ≫ a) ≫ f =
      (representedSpaceMap B S hS (pullback.snd f₀ g₀) ≫ c) ≫ g := by
  rw [Category.assoc, ← hfa, Category.assoc, ← hgc, ← Category.assoc, ← Category.assoc,
    representedSpaceMap_comp, representedSpaceMap_comp, pullback.condition]

/-- A geometric point of `X'` lifts to `U' = V' ×_V U` once its images in `X` and `Y'` lift
along the charts `U ⟶ V ×_Y X` and `V' ⟶ V ×_Y Y'`. -/
private theorem exists_geometricPoint_map_lift_eq {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    {V U V' : BigFppfOver B S hS}
    (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (m : yoneda.obj U ⟶ (pullback b f).1) (n : yoneda.obj V' ⟶ (pullback b g).1)
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (hf₀ : yoneda.map f₀ = m ≫ (pullback.fst b f).hom)
    (hg₀ : yoneda.map g₀ = n ≫ (pullback.fst b g).hom)
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (ha : a = ObjectProperty.homMk (m ≫ (pullback.snd b f).hom))
    (hc : c = ObjectProperty.homMk (n ≫ (pullback.snd b g).hom))
    (hlift : (representedSpaceMap B S hS (pullback.fst f₀ g₀) ≫ a) ≫ f =
      (representedSpaceMap B S hS (pullback.snd f₀ g₀) ≫ c) ≫ g)
    (x' : GeometricPoint B S hS X'.1) {v₀ : GeometricPoint B S hS (yoneda.obj V)}
    {p₀ : GeometricPoint B S hS (pullback b f).1} {r₀ : GeometricPoint B S hS (pullback b g).1}
    {u₀ : GeometricPoint B S hS (yoneda.obj U)} {v'₀ : GeometricPoint B S hS (yoneda.obj V')}
    (hu₀ : geometricPointMap m u₀ = p₀) (hv'₀ : geometricPointMap n v'₀ = r₀)
    (hp₁ : geometricPointMap (pullback.fst b f).hom p₀ = v₀)
    (hp₂ : geometricPointMap (pullback.snd b f).hom p₀ = geometricPointMap g'.hom x')
    (hr₁ : geometricPointMap (pullback.fst b g).hom r₀ = v₀)
    (hr₂ : geometricPointMap (pullback.snd b g).hom r₀ = geometricPointMap f'.hom x') :
    ∃ x'' : GeometricPoint B S hS (yoneda.obj (pullback f₀ g₀)),
      geometricPointMap (sq.lift _ _ hlift).hom x'' = x' := by
  subst ha hc
  obtain ⟨x'', hx₁, hx₂⟩ := exists_geometricPoint_of_isPullback B S hS
    ((IsPullback.of_hasPullback f₀ g₀).map yoneda) u₀ v'₀ <| by
    rw [hf₀, hg₀]
    exact ((congrArg (geometricPointMap (pullback.fst b f).hom) hu₀).trans hp₁).trans
      ((congrArg (geometricPointMap (pullback.fst b g).hom) hv'₀).trans hr₁).symm
  refine ⟨x'', geometricPoint_eq_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS sq) _ _ ?_ ?_⟩
  · show geometricPointMap (sq.lift _ _ hlift ≫ g').hom x'' = _
    rw [sq.lift_fst]
    exact (congrArg (fun z => geometricPointMap (pullback.snd b f).hom (geometricPointMap m z))
      hx₁).trans ((congrArg (geometricPointMap (pullback.snd b f).hom) hu₀).trans hp₂)
  · show geometricPointMap (sq.lift _ _ hlift ≫ f').hom x'' = _
    rw [sq.lift_snd]
    exact (congrArg (fun z => geometricPointMap (pullback.snd b g).hom (geometricPointMap n z))
      hx₂).trans ((congrArg (geometricPointMap (pullback.snd b g).hom) hv'₀).trans hr₂)

/-- **An affine étale quadruple through a geometric point.** Let `g' ≫ f = f' ≫ g` be a
cartesian square of algebraic spaces and `x̄'` a geometric point of `X'`. There are affine
schemes `U`, `V`, `V'` of the site, étale morphisms `a : U ⟶ X`, `b : V ⟶ Y`, `c : V' ⟶ Y'`,
morphisms `f₀ : U ⟶ V` over `f` and `g₀ : V' ⟶ V` over `g`, the fibre product
`U' = V' ×_V U` (affine), a morphism `a' : U' ⟶ X'` compatible with `a` and `c`, and a geometric
point of `U'` over `x̄'`. -/
theorem exists_affineQuadruple_geometricPoint {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (x' : GeometricPoint B S hS X'.1) :
    ∃ (U V V' U' : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V'))
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj U'))
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
      (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U),
      IsEtale B S hS a.hom ∧ IsEtale B S hS b.hom ∧ IsEtale B S hS c.hom ∧
      IsPullback g₀' f₀' f₀ g₀ ∧
      representedSpaceMap B S hS f₀ ≫ b = a ≫ f ∧
      representedSpaceMap B S hS g₀ ≫ b = c ≫ g ∧
      representedSpaceMap B S hS f₀' ≫ c = a' ≫ f' ∧
      representedSpaceMap B S hS g₀' ≫ a = a' ≫ g' ∧
      ∃ x'' : GeometricPoint B S hS (yoneda.obj U'), geometricPointMap a'.hom x'' = x' := by
  let x := geometricPointMap g'.hom x'
  let y' := geometricPointMap f'.hom x'
  obtain ⟨V, hV, bp, hbp, v₀, hv₀⟩ :=
    exists_affine_etale_geometricPoint_lift B S hS Y (geometricPointMap f.hom x)
  let b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y :=
    ObjectProperty.homMk bp
  obtain ⟨p₀, hp₁, hp₂⟩ := exists_geometricPoint_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback b f)) v₀ x hv₀
  obtain ⟨U, hU, m, hm, u₀, hu₀⟩ :=
    exists_affine_etale_geometricPoint_lift B S hS (pullback b f) p₀
  let a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk (m ≫ (pullback.snd b f).hom)
  let f₀ : U ⟶ V := Yoneda.fullyFaithful.preimage (m ≫ (pullback.fst b f).hom)
  have hf₀ : yoneda.map f₀ = m ≫ (pullback.fst b f).hom := Yoneda.fullyFaithful.map_preimage _
  obtain ⟨r₀, hr₁, hr₂⟩ := exists_geometricPoint_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback b g)) v₀ y'
    (hv₀.trans (congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') sq.w))
  obtain ⟨V', hV', n, hn, v'₀, hv'₀⟩ :=
    exists_affine_etale_geometricPoint_lift B S hS (pullback b g) r₀
  let c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y' :=
    ObjectProperty.homMk (n ≫ (pullback.snd b g).hom)
  let g₀ : V' ⟶ V := Yoneda.fullyFaithful.preimage (n ≫ (pullback.fst b g).hom)
  have hg₀ : yoneda.map g₀ = n ≫ (pullback.fst b g).hom := Yoneda.fullyFaithful.map_preimage _
  have hfa := representedSpaceMap_comp_eq_homMk_comp b f m f₀ hf₀
  have hgc := representedSpaceMap_comp_eq_homMk_comp b g n g₀ hg₀
  have hlift := comp_eq_comp_of_pullback_charts hfa hgc
  refine ⟨U, V, V', pullback f₀ g₀, hU, hV, hV', isAffine_toScheme_pullback B S hS f₀ g₀, a, b, c,
    sq.lift _ _ hlift, f₀, g₀, pullback.snd f₀ g₀, pullback.fst f₀ g₀,
    isEtale_comp B S hS hm (isEtale_of_isPullback B S hS _ _ b f (.of_hasPullback b f) hbp), hbp,
    isEtale_comp B S hS hn (isEtale_of_isPullback B S hS _ _ b g (.of_hasPullback b g) hbp),
    .of_hasPullback f₀ g₀, hfa, hgc, (sq.lift_snd _ _ _).symm, (sq.lift_fst _ _ _).symm, ?_⟩
  exact exists_geometricPoint_map_lift_eq sq b m n f₀ g₀ hf₀ hg₀ a c rfl rfl hlift x' hu₀ hv'₀
    hp₁ hp₂ hr₁ hr₂

/-- **A geometric point lifts along a surjective étale chart.** For an étale morphism
`a : U ⟶ X` from a scheme of the site to an algebraic space, surjective on points, every geometric
point of `X` is the image of a geometric point of `U` over the same field. -/
theorem exists_geometricPoint_lift_of_isEtale_of_isSurjective {X : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X.1) (ha : IsEtale B S hS a)
    (hs : IsSurjective B S hS a) (x : GeometricPoint B S hS X.1) :
    ∃ u : GeometricPoint B S hS (yoneda.obj U), geometricPointMap a u = x := by
  obtain ⟨u, hu⟩ := hs x.image
  obtain ⟨ū, -, hū⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (isAlgebraicSpace_yoneda B S hS U) X.2 a ha x u hu
  exact ⟨ū, Subtype.ext hū⟩

/-- **A surjective étale atlas.** Every algebraic space has an étale morphism from a scheme of
the site which is surjective on points. -/
theorem exists_isEtale_isSurjective_atlas (X : AlgebraicSpaces B S hS) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1), IsEtale B S hS a ∧
      IsSurjective B S hS a := by
  obtain ⟨U, a, hs, he⟩ := X.2.exists_atlas
  exact ⟨U, a, (isEtale_iff_presheaf_of_yoneda B S hS a).2 he,
    (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U a).mp hs⟩

/-- **An étale diagram of schemes with surjective `U' ⟶ X'`.** Let `g' ≫ f = f' ≫ g` be a
cartesian square of algebraic spaces. There are schemes `U`, `V`, `V'` of the site, étale
morphisms `a : U ⟶ X`, `b : V ⟶ Y`, `c : V' ⟶ Y'`, morphisms `f₀ : U ⟶ V` over `f` and
`g₀ : V' ⟶ V` over `g`, the fibre product `U' = V' ×_V U` and a morphism `a' : U' ⟶ X'`
compatible with `a` and `c`, such that `a'` is surjective. -/
theorem exists_etaleDiagram_isSurjective {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) :
    ∃ (U V V' U' : BigFppfOver B S hS)
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
      (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U),
      IsEtale B S hS a.hom ∧ IsEtale B S hS b.hom ∧ IsEtale B S hS c.hom ∧
      IsPullback g₀' f₀' f₀ g₀ ∧
      representedSpaceMap B S hS f₀ ≫ b = a ≫ f ∧
      representedSpaceMap B S hS g₀ ≫ b = c ≫ g ∧
      representedSpaceMap B S hS f₀' ≫ c = a' ≫ f' ∧
      representedSpaceMap B S hS g₀' ≫ a = a' ≫ g' ∧
      IsSurjective B S hS a'.hom := by
  obtain ⟨V, bp, hbp, hbs⟩ := exists_isEtale_isSurjective_atlas Y
  let b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y :=
    ObjectProperty.homMk bp
  obtain ⟨U, m, hm, hms⟩ := exists_isEtale_isSurjective_atlas (pullback b f)
  let a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk (m ≫ (pullback.snd b f).hom)
  let f₀ : U ⟶ V := Yoneda.fullyFaithful.preimage (m ≫ (pullback.fst b f).hom)
  have hf₀ : yoneda.map f₀ = m ≫ (pullback.fst b f).hom := Yoneda.fullyFaithful.map_preimage _
  obtain ⟨V', n, hn, hns⟩ := exists_isEtale_isSurjective_atlas (pullback b g)
  let c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y' :=
    ObjectProperty.homMk (n ≫ (pullback.snd b g).hom)
  let g₀ : V' ⟶ V := Yoneda.fullyFaithful.preimage (n ≫ (pullback.fst b g).hom)
  have hg₀ : yoneda.map g₀ = n ≫ (pullback.fst b g).hom := Yoneda.fullyFaithful.map_preimage _
  have hfa := representedSpaceMap_comp_eq_homMk_comp b f m f₀ hf₀
  have hgc := representedSpaceMap_comp_eq_homMk_comp b g n g₀ hg₀
  have hlift := comp_eq_comp_of_pullback_charts hfa hgc
  refine ⟨U, V, V', pullback f₀ g₀, a, b, c, sq.lift _ _ hlift, f₀, g₀, pullback.snd f₀ g₀,
    pullback.fst f₀ g₀,
    isEtale_comp B S hS hm (isEtale_of_isPullback B S hS _ _ b f (.of_hasPullback b f) hbp), hbp,
    isEtale_comp B S hS hn (isEtale_of_isPullback B S hS _ _ b g (.of_hasPullback b g) hbp),
    .of_hasPullback f₀ g₀, hfa, hgc, (sq.lift_snd _ _ _).symm, (sq.lift_fst _ _ _).symm,
    fun z => ?_⟩
  obtain ⟨x', rfl⟩ := exists_geometricRepresentative B S hS X'.1 z
  let x := geometricPointMap g'.hom x'
  let y' := geometricPointMap f'.hom x'
  obtain ⟨v₀, hv₀⟩ := exists_geometricPoint_lift_of_isEtale_of_isSurjective bp hbp hbs
    (geometricPointMap f.hom x)
  obtain ⟨p₀, hp₁, hp₂⟩ := exists_geometricPoint_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback b f)) v₀ x hv₀
  obtain ⟨u₀, hu₀⟩ := exists_geometricPoint_lift_of_isEtale_of_isSurjective m hm hms p₀
  obtain ⟨r₀, hr₁, hr₂⟩ := exists_geometricPoint_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback b g)) v₀ y'
    (hv₀.trans (congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') sq.w))
  obtain ⟨v'₀, hv'₀⟩ := exists_geometricPoint_lift_of_isEtale_of_isSurjective n hn hns r₀
  obtain ⟨x'', hx⟩ := exists_geometricPoint_map_lift_eq sq b m n f₀ g₀ hf₀ hg₀ a c rfl rfl hlift
    x' hu₀ hv'₀ hp₁ hp₂ hr₁ hr₂
  exact ⟨x''.image, by rw [← geometricPointMap_image, hx]⟩

end Quadruple

end AlgebraicGeometry.Space
