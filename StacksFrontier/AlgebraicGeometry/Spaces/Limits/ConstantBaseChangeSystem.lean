module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# Base change of an inverse system of morphisms along a map into the limit of the targets

Let `φ : X ⟶ Y` be a morphism of inverse systems of presheaves on the big fppf site of a scheme
`S`, indexed by a directed set `I`, let `cY` be a limit cone of `Y`, and let `k : K ⟶ cY.pt` be a
morphism. Base changing each stage `φᵢ : Xᵢ ⟶ Yᵢ` along `K ⟶ cY.pt ⟶ Yᵢ` gives an inverse system
`Xᵢ ×_{Yᵢ} K`, and its limit is the base change `X ×_Y K` of the limit `X ⟶ Y`: limits commute with
fibre products. In the proof of Stacks 0D3D this system, with `K` the spectrum of the residue
field of a point, is the system `X_{i, y_i}` of fibres whose limit is the fibre `X_y`.

## Main definitions

* `AlgebraicGeometry.Space.constantBaseChangeSystem`: the inverse system `Xᵢ ×_{Yᵢ} K`.
* `AlgebraicGeometry.Space.constantBaseChangeDescentSituation`: for affine transition
  morphisms of `X` and `Y`, affine `K` and quasi-compact quasi-separated `φᵢ`, the system is a
  situation of Stacks 084R (`AlgebraicGeometry.Space.DescentSituation`) with limit `X ×_Y K`.

## Main results

* `AlgebraicGeometry.Space.constantBaseChangeSystemObjIso`: its stages are the fibre products.
* `AlgebraicGeometry.Space.constantBaseChangeSystemLimitIso`: its limit is `X ×_Y K`, for a cone
  of `X` over the limit cone of `Y`.
* `AlgebraicGeometry.Space.isAffineHom_of_isPullback_of_isPullback`: the morphism between two
  base changes `X_b ×_{Y_b} K ⟶ X_a ×_{Y_a} K` induced by affine `X_b ⟶ X_a` and `Y_b ⟶ Y_a` is
  affine; it is the base change of the diagonal of `Y_b ⟶ Y_a` followed by a base change of
  `X_b ⟶ X_a`.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {X Y : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (φ : X ⟶ Y)
  {cY : Cone Y} {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : K ⟶ cY.pt)

/-- The morphism from the constant system on `K` to `Y` induced by `k : K ⟶ cY.pt`. -/
def constantBaseChangeMap : (Functor.const Iᵒᵖ).obj K ⟶ Y where
  app i := k ≫ cY.π.app i
  naturality i j g := by simp

/-- **The inverse system `Xᵢ ×_{Yᵢ} K`.** -/
abbrev constantBaseChangeSystem : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  pullback φ (constantBaseChangeMap k)

/-- The stages of the base change system are the fibre products. -/
def constantBaseChangeSystemObjIso (i : Iᵒᵖ) :
    (constantBaseChangeSystem φ k).obj i ≅ pullback (φ.app i) (k ≫ cY.π.app i) :=
  pullbackObjIso φ (constantBaseChangeMap k) i

variable {φ k}

/-- **The limit of the base change system is the base change of the limit.** For a cone `cX`
of `X` which is a limit, a limit cone `cY` of `Y` and `f : cX.pt ⟶ cY.pt` compatible with `φ`,
the limit of `Xᵢ ×_{Yᵢ} K` is `cX.pt ×_{cY.pt} K`. -/
def constantBaseChangeSystemLimitIso {cX : Cone X} (hcX : IsLimit cX) (hcY : IsLimit cY)
    (f : cX.pt ⟶ cY.pt) (hf : ∀ i, f ≫ cY.π.app i = cX.π.app i ≫ φ.app i) :
    limit (constantBaseChangeSystem φ k) ≅ pullback f k := by
  have _ : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  let e₁ : limit X ≅ cX.pt := (limit.isLimit X).conePointUniqueUpToIso hcX
  let e₂ : limit ((Functor.const Iᵒᵖ).obj K) ≅ K :=
    (limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone Iᵒᵖ K)
  let e₃ : limit Y ≅ cY.pt := (limit.isLimit Y).conePointUniqueUpToIso hcY
  have w₁ : lim.map φ ≫ e₃.hom = e₁.hom ≫ f := by
    refine hcY.hom_ext fun i => ?_
    simp only [Category.assoc, e₃, e₁, IsLimit.conePointUniqueUpToIso_hom_comp, hf]
    rw [IsLimit.conePointUniqueUpToIso_hom_comp_assoc]
    simp
  have h₂ : ∀ i, e₂.hom = limit.π ((Functor.const Iᵒᵖ).obj K) i := fun i => by
    have := IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit ((Functor.const Iᵒᵖ).obj K))
      (isLimitConstCone Iᵒᵖ K) i
    simp only [constCone] at this
    exact this
  have w₂ : lim.map (constantBaseChangeMap k) ≫ e₃.hom = e₂.hom ≫ k := by
    refine hcY.hom_ext fun i => ?_
    rw [Category.assoc, IsLimit.conePointUniqueUpToIso_hom_comp, Category.assoc, h₂ i]
    exact limMap_π _ _
  exact PreservesPullback.iso lim φ (constantBaseChangeMap k) ≪≫
    asIso (pullback.map _ _ _ _ e₁.hom e₂.hom e₃.hom w₁ w₂)

/-- The isomorphism `lim (Xᵢ ×_{Yᵢ} K) ≅ cX.pt ×_{cY.pt} K` is compatible with the first
projections to the stages of `X`. -/
theorem constantBaseChangeSystemLimitIso_hom_fst_π {cX : Cone X} (hcX : IsLimit cX)
    (hcY : IsLimit cY) (f : cX.pt ⟶ cY.pt) (hf : ∀ i, f ≫ cY.π.app i = cX.π.app i ≫ φ.app i)
    (i : Iᵒᵖ) :
    (constantBaseChangeSystemLimitIso hcX hcY f hf).hom ≫ pullback.fst f k ≫ cX.π.app i =
      limit.π (constantBaseChangeSystem φ k) i ≫
        (pullback.fst φ (constantBaseChangeMap k)).app i := by
  have _ : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  simp only [constantBaseChangeSystemLimitIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.lift_fst_assoc, IsLimit.conePointUniqueUpToIso_hom_comp,
    PreservesPullback.iso_hom_fst_assoc]
  exact limMap_π _ _

/-- The isomorphism `lim (Xᵢ ×_{Yᵢ} K) ≅ cX.pt ×_{cY.pt} K` is compatible with the second
projections to `K`. -/
theorem constantBaseChangeSystemLimitIso_hom_snd {cX : Cone X} (hcX : IsLimit cX)
    (hcY : IsLimit cY) (f : cX.pt ⟶ cY.pt) (hf : ∀ i, f ≫ cY.π.app i = cX.π.app i ≫ φ.app i)
    (i : Iᵒᵖ) :
    (constantBaseChangeSystemLimitIso hcX hcY f hf).hom ≫ pullback.snd f k =
      limit.π (constantBaseChangeSystem φ k) i ≫
        (pullback.snd φ (constantBaseChangeMap k)).app i := by
  have _ : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  have h₂ : ((limit.isLimit ((Functor.const Iᵒᵖ).obj K)).conePointUniqueUpToIso
      (isLimitConstCone Iᵒᵖ K)).hom = limit.π ((Functor.const Iᵒᵖ).obj K) i := by
    have := IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit ((Functor.const Iᵒᵖ).obj K))
      (isLimitConstCone Iᵒᵖ K) i
    simp only [constCone] at this
    exact this
  simp only [constantBaseChangeSystemLimitIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.lift_snd, h₂, PreservesPullback.iso_hom_snd_assoc]
  exact limMap_π _ _

variable (φ k)

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- The base change system at a stage is a cartesian square. -/
theorem isPullback_constantBaseChangeSystem (i : Iᵒᵖ) :
    IsPullback ((pullback.fst φ (constantBaseChangeMap k)).app i)
      ((pullback.snd φ (constantBaseChangeMap k)).app i) (φ.app i) (k ≫ cY.π.app i) :=
  (IsPullback.of_hasPullback φ (constantBaseChangeMap k)).map ((evaluation _ _).obj i)

omit [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- **The morphism between two base changes induced by affine morphisms is affine.** Let
`E_b = X_b ×_{Y_b} K` and `E_a = X_a ×_{Y_a} K` be cartesian squares over `fb : X_b ⟶ Y_b` and
`fa : X_a ⟶ Y_a`, related by `x : X_b ⟶ X_a` and `y : Y_b ⟶ Y_a` with `gb ≫ y = ga`, and let
`t : E_b ⟶ E_a` be compatible with the projections. If `x` and `y` are affine then so is `t`:
it factors through `X_b ×_{Y_a} K`, as the base change `E_b ⟶ X_b ×_{Y_a} K` of the diagonal of
`y` (affine, since `y` is separated) followed by the base change `X_b ×_{Y_a} K ⟶ E_a` of `x`. -/
theorem isAffineHom_of_isPullback_of_isPullback
    {Xb Yb Xa Ya K' Eb Ea : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fb : Xb ⟶ Yb} {gb : K' ⟶ Yb} {fa : Xa ⟶ Ya} {ga : K' ⟶ Ya} {x : Xb ⟶ Xa} {y : Yb ⟶ Ya}
    (hx : x ≫ fa = fb ≫ y) (hy : gb ≫ y = ga)
    {pb₁ : Eb ⟶ Xb} {pb₂ : Eb ⟶ K'} {pa₁ : Ea ⟶ Xa} {pa₂ : Ea ⟶ K'}
    (hb : IsPullback pb₁ pb₂ fb gb) (ha : IsPullback pa₁ pa₂ fa ga)
    (t : Eb ⟶ Ea) (ht₁ : t ≫ pa₁ = pb₁ ≫ x) (ht₂ : t ≫ pa₂ = pb₂)
    (hYb : IsAlgebraicSpace B S hS Yb) (hYa : IsAlgebraicSpace B S hS Ya)
    (hxaff : IsAffineHom B S hS x) (hyaff : IsAffineHom B S hS y) :
    IsAffineHom B S hS t := by
  -- the diagonal of `y` is affine
  have hΔ : IsAffineHom B S hS (pullback.diagonal y) :=
    isAffineHom_of_isClosedImmersion B S hS _ (isSeparated_of_isAffineHom B S hS y hYb hYa hyaff)
  -- `E_b ⟶ X_b ×_{Y_a} K`
  let m := pullback.map fb gb (fb ≫ y) (gb ≫ y) (𝟙 _) (𝟙 _) y (Category.id_comp _).symm
    (Category.id_comp _).symm
  have hm : IsAffineHom B S hS m :=
    IsAffineHom.of_isPullback (pullback_map_diagonal_isPullback fb gb y) hΔ
  let u : Eb ⟶ pullback (x ≫ fa) ga :=
    hb.isoPullback.hom ≫ m ≫ (pullback.congrHom hx.symm hy).hom
  have hu : IsAffineHom B S hS u :=
    isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _)
      (isAffineHom_comp B S hS _ _ hm (isAffineHom_of_isIso _))
  -- `X_b ×_{Y_a} K ⟶ E_a`
  let v : pullback (x ≫ fa) ga ⟶ Ea := ha.lift (pullback.fst _ _ ≫ x) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])
  have hv₁ : v ≫ pa₁ = pullback.fst _ _ ≫ x := ha.lift_fst _ _ _
  have hv₂ : v ≫ pa₂ = pullback.snd _ _ := ha.lift_snd _ _ _
  have hsq : IsPullback (pullback.fst (x ≫ fa) ga) v x pa₁ := by
    refine IsPullback.of_bot (h₂₁ := pa₁) (v₂₁ := pa₂) (v₂₂ := fa) (h₃₁ := ga) ?_ hv₁.symm ha
    rw [hv₂]
    exact IsPullback.of_hasPullback _ _
  have hv : IsAffineHom B S hS v := IsAffineHom.of_isPullback hsq hxaff
  have ht : t = u ≫ v := by
    refine ha.hom_ext ?_ ?_
    · rw [ht₁, Category.assoc, hv₁]
      simp [u, m]
    · rw [ht₂, Category.assoc, hv₂]
      simp [u, m]
  rw [ht]
  exact isAffineHom_comp B S hS _ _ hu hv

variable (B S hS) in
/-- **The base change system as a situation of Stacks 084R.** If the transition morphisms of
`X` and of `Y` are affine, `K` is affine and the morphisms `φᵢ` are quasi-compact and
quasi-separated, then the base change system `Xᵢ ×_{Yᵢ} K` has affine transition morphisms and
quasi-compact, quasi-separated stages, and its limit is an algebraic space. The stages of `Y`
need not be affine: the transition morphisms of the base change system are affine by
`AlgebraicGeometry.Space.isAffineHom_of_isPullback_of_isPullback`. -/
def constantBaseChangeDescentSituation (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : ∀ i : I, IsAlgebraicSpace B S hS (X.obj (op i)))
    (hXaff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (X.map g))
    (hY : ∀ i : I, IsAlgebraicSpace B S hS (Y.obj (op i)))
    (hYaff : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B S hS (Y.map g))
    (hK : IsAffineSpace B S hS K)
    (hqc : ∀ i : I, IsQuasiCompact B S hS (φ.app (op i)))
    (hqs : ∀ i : I, IsQuasiSeparated B S hS (φ.app (op i)))
    {cX : Cone X} (hcX : IsLimit cX) (hcY : IsLimit cY) (hXlim : IsAlgebraicSpace B S hS cX.pt)
    (hYlim : IsAlgebraicSpace B S hS cY.pt)
    (f : cX.pt ⟶ cY.pt) (hf : ∀ i, f ≫ cY.π.app i = cX.π.app i ≫ φ.app i) (i₀ : I) :
    DescentSituation B S hS hZ I where
  system := constantBaseChangeSystem φ k
  algebraicSpace i := by
    refine (isAlgebraicSpace_pullback B S hS (φ.app (op i)) (k ≫ cY.π.app (op i)) (hX i)
      hK.isAlgebraicSpace (hY i)).of_iso
        (constantBaseChangeSystemObjIso φ k (op i)).symm
  transition_affine {i j} g :=
    isAffineHom_of_isPullback_of_isPullback (φ.naturality g)
      (by rw [Category.assoc, ← cY.w g])
      (isPullback_constantBaseChangeSystem φ k i) (isPullback_constantBaseChangeSystem φ k j)
      ((constantBaseChangeSystem φ k).map g)
      ((pullback.fst φ (constantBaseChangeMap k)).naturality g)
      (by rw [(pullback.snd φ (constantBaseChangeMap k)).naturality g]; exact Category.comp_id _)
      (hY i.unop) (hY j.unop) (hXaff g) (hYaff g)
  quasiCompact i := isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS
    ((pullback.snd φ (constantBaseChangeMap k)).app (op i)) hK
    (isQuasiCompact_of_isPullback B S hS (isPullback_constantBaseChangeSystem φ k (op i)) (hqc i))
  quasiSeparated i := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ
    ((pullback.snd φ (constantBaseChangeMap k)).app (op i))
    ((isAlgebraicSpace_pullback B S hS (φ.app (op i)) (k ≫ cY.π.app (op i)) (hX i)
      hK.isAlgebraicSpace (hY i)).of_iso
        (constantBaseChangeSystemObjIso φ k (op i)).symm) hK
    (isQuasiSeparated_of_isPullback B S hS (isPullback_constantBaseChangeSystem φ k (op i))
      (hqs i))
  limitCone := limit.cone (constantBaseChangeSystem φ k)
  isLimit := limit.isLimit _
  limitAlgebraicSpace := (isAlgebraicSpace_pullback B S hS f k hXlim hK.isAlgebraicSpace
    hYlim).of_iso (constantBaseChangeSystemLimitIso hcX hcY f hf).symm
  base := i₀

end AlgebraicGeometry.Space

end
