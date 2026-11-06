module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# One chart with a finite relation fibre forces every chart to have one

Stacks 03JU compares four conditions on a point `x` of an algebraic space `X` over a scheme `S`.
Condition (1) is that *some* étale chart `U ⟶ X` has two points `u`, `u'` above `x` whose
relation fibre — the fibre of `|R| → |U| ×_{|X|} |U|` over `(u, u')`, where `R = U ×_X U` — is
finite; condition (2) is that *every* étale chart and every such pair have finite relation fibre.
This file proves that (1) implies (2), which is the substance of the equivalence of those two
conditions, and the converse, which is
`AlgebraicGeometry.Space.hasFiniteRelationFiberAt_of_everyEtaleChart` with its hypothesis
discharged by an étale atlas. Conditions (1) and (2) are therefore equivalent; conditions (3)
and (4) are untouched.

## Main definitions

No new definitions are introduced.

## Main results

* `CategoryTheory.IsPullback.selfPullback_comp` decomposes the self-fibre-product of a composite
  `θ ≫ χ` as a two-step fibre product over the intermediate object through the self-fibre-product
  of `χ`.
* `AlgebraicGeometry.Space.HasFiniteRelationFiberAt.hasFiniteRelationFiberAtEveryEtaleChart` is
  Stacks 03JU, part (1) implies part (2), and
  `AlgebraicGeometry.Space.HasFiniteRelationFiberAtEveryEtaleChart.hasFiniteRelationFiberAt` is
  part (2) implies part (1), so conditions (1) and (2) of Stacks 03JU become equivalent. Nothing
  is claimed about conditions (3) and (4), which have no arrow in or out.

## Implementation notes

The source argues with the residue fields of the two points: it passes to `W ×_X U`, where the
residue field extensions over those of `U` and of `W` are finite separable because both
projections are étale, and compares `w ×_X w'` with `u ×_X u'` through `\tilde w ×_X \tilde w'`,
whose two comparison morphisms are étale and quasi-compact because `Spec(k) ×_S Spec(k')` is
affine. That route needs the structure theory of étale schemes over a field and Stacks 03DP.

The route taken here replaces it by the already-available Tag 0AC3 machinery, and needs neither.
Write `T = h_W ×_X h_U` with projections `σ : T ⟶ W` and `π : T ⟶ U`, both étale, and
`τ : h_T ⟶ X` for the common composite. Points `\tilde c`, `\tilde d` of `|T|` above the given
`c`, `d` of `|W|` and above the given `a`, `b` of `|U|` exist by Tag 03H4. The whole proof is
then two instances of one observation, `CategoryTheory.IsPullback.selfPullback_comp`: for
`τ = θ ≫ χ` the presheaf `h_T ×_X h_T` is `h_T ×_H (H ×_X H) ×_H h_T`, where `H` is the
intermediate object. Instantiated at `(θ, χ) = (σ, ψ)` it gives, by two applications of Tag 03H4,
that the relation fibre of `ψ` above `(c, d)` is covered by the relation fibre of `τ` above
`(\tilde c, \tilde d)`; instantiated at `(θ, χ) = (π, φ)` it writes the relation fibre of `τ`
above `(\tilde c, \tilde d)` as a union, indexed by the relation fibre of `φ` above `(a, b)`
— finite by hypothesis — of two nested sets of Tag 0AC2, each attached to a cartesian square all
of whose corners are *representable* and whose lower horizontal morphism is étale, hence finite
by Tag 0AC3.

Both instantiations are taken with the fibre products formed *in the site*, which has them by
Tag 021U, so that every corner of the two squares of Tag 0AC1 is representable; `yoneda` preserves
fibre products, so the squares of presheaves are cartesian. The self-fibre-products `R = U ×_X U`
and `W ×_X W` likewise appear as objects of the site, through the representability that étaleness
of a chart carries, and the comparison with the chosen presheaf pullback of
`AlgebraicGeometry.Space.HasFiniteRelationFiber` is the canonical isomorphism of two cartesian
squares over one cospan.

The algebraic-space hypothesis on `X` is retained from the source statement as `_hF` but is not
used: every square the proof builds has representable corners, and Tag 03H4 needs no
algebraicity.

## References

* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 0AC1](https://stacks.math.columbia.edu/tag/0AC1)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 0AC3](https://stacks.math.columbia.edu/tag/0AC3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.IsPullback

/-- The self-fibre-product of a composite `θ ≫ χ`, decomposed over the intermediate object.

If `A` is the fibre product of `θ : G ⟶ H` with the first projection of a self-fibre-product
square of `χ : H ⟶ F`, and `N` is the fibre product of `A ⟶ H` — the second projection of that
square, read on `A` — with `θ`, then `N` together with its composite projection to `G` and its
other projection to `G` is a self-fibre-product square of `θ ≫ χ`. -/
theorem selfPullback_comp {C : Type*} [Category C] {G H F R A N : C}
    {θ : G ⟶ H} {χ : H ⟶ F} {h₁ h₂ : R ⟶ H} {α₁ : A ⟶ G} {α₂ : A ⟶ R}
    {ν₁ : N ⟶ A} {ν₂ : N ⟶ G}
    (sqR : IsPullback h₁ h₂ χ χ) (sqA : IsPullback α₁ α₂ θ h₁)
    (sqN : IsPullback ν₁ ν₂ (α₂ ≫ h₂) θ) :
    IsPullback (ν₁ ≫ α₁) ν₂ (θ ≫ χ) (θ ≫ χ) :=
  sqN.paste_horiz (sqA.paste_vert sqR)

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_relFibreTransfer
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is étale has
locally quasi-finite Yoneda image, in the sense of Tag 03XJ. -/
theorem isLocallyQuasiFinite_yoneda_map_of_etale {X Y : BigFppfOver B S hS} (k : X ⟶ Y)
    (hk : Etale ((BigFppfOver.toScheme B S hS).map k)) :
    IsLocallyQuasiFinite B S hS (yoneda.map k) :=
  isLocallyQuasiFinite_of_isEtale' B S hS
    (isEtale_of_presheaf_etale B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ k).2 hk))

/-! ### Transfer of a relation fibre down an étale morphism of charts -/

/-- The two layers of the decomposition of the self-fibre-product of `σ ≫ ψ` as cartesian squares
of representable presheaves, built by taking fibre products in the category. -/
private theorem exists_selfPullback_comp_squares {C : Type*} [Category C] [HasPullbacks C]
    {F : Cᵒᵖ ⥤ Type _} {T W R : C} (σ : T ⟶ W) {h₁ h₂ : R ⟶ W} {ψ : yoneda.obj W ⟶ F}
    (sqR : IsPullback (yoneda.map h₁) (yoneda.map h₂) ψ ψ) :
    ∃ (A N : C) (β₁ : A ⟶ T) (β₂ : A ⟶ R) (μ₁ : N ⟶ A) (μ₂ : N ⟶ T),
      IsPullback (yoneda.map β₁) (yoneda.map β₂) (yoneda.map σ) (yoneda.map h₁) ∧
      IsPullback (yoneda.map μ₁) (yoneda.map μ₂) (yoneda.map β₂ ≫ yoneda.map h₂)
        (yoneda.map σ) ∧
      IsPullback (yoneda.map μ₁ ≫ yoneda.map β₁) (yoneda.map μ₂) (yoneda.map σ ≫ ψ)
        (yoneda.map σ ≫ ψ) := by
  have sqA := (IsPullback.of_hasPullback σ h₁).map yoneda
  have sqN : IsPullback (yoneda.map (pullback.fst (pullback.snd σ h₁ ≫ h₂) σ))
      (yoneda.map (pullback.snd (pullback.snd σ h₁ ≫ h₂) σ))
      (yoneda.map (pullback.snd σ h₁) ≫ yoneda.map h₂) (yoneda.map σ) := by
    have hsq := (IsPullback.of_hasPullback (pullback.snd σ h₁ ≫ h₂) σ).map yoneda
    rwa [Functor.map_comp] at hsq
  exact ⟨_, _, _, _, _, _, sqA, sqN, IsPullback.selfPullback_comp sqR sqA sqN⟩

/-- If a relation fibre of the composite chart `h_T ⟶ h_U ⟶ F` above a pair of points of `|T|`
is finite, then so is the relation fibre of `h_U ⟶ F` above the pair of their images in `|U|`.

The self-fibre-product of `h_T` over `F` is `h_T ×_{h_U} (h_U ×_F h_U) ×_{h_U} h_T` by
`CategoryTheory.IsPullback.selfPullback_comp`, so two applications of Tag 03H4 lift a point of
the relation of `h_U` above the prescribed pair to a point of the relation of `h_T` above the
prescribed pair of points of `|T|`. -/
private theorem hasFiniteRelationFiber_of_comp
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T W : BigFppfOver B S hS} (σ : T ⟶ W)
    {ψ : yoneda.obj W ⟶ F} (hψ : IsEtale B S hS ψ) (ct dt : points B S hS (yoneda.obj T))
    (hfin : HasFiniteRelationFiber B S hS F T (yoneda.map σ ≫ ψ) ct dt) :
    HasFiniteRelationFiber B S hS F W ψ
      (pointsMap B S hS (yoneda.obj T) (yoneda.map σ) ct)
      (pointsMap B S hS (yoneda.obj T) (yoneda.map σ) dt) := by
  have hψp := presheaf_etale_of_isEtale B S hS hψ
  set RW : BigFppfOver B S hS := hψp.rep.pullback ψ
  set h₁ : RW ⟶ W := hψp.rep.fst' ψ
  set h₂ : RW ⟶ W := hψp.rep.snd ψ
  have sqRW : IsPullback (yoneda.map h₁) (yoneda.map h₂) ψ ψ := hψp.rep.isPullback' ψ
  obtain ⟨A, N, β₁, β₂, μ₁, μ₂, sqA, sqN, sqL⟩ := exists_selfPullback_comp_squares σ sqRW
  set τ : yoneda.obj T ⟶ F := yoneda.map σ ≫ ψ
  set e := (IsPullback.of_hasPullback τ τ).isoIsPullback _ _ sqL
  set ιψ := sqRW.isoIsPullback _ _ (IsPullback.of_hasPullback ψ ψ)
  set ρ : Limits.pullback τ τ ⟶ Limits.pullback ψ ψ :=
    e.hom ≫ yoneda.map μ₁ ≫ yoneda.map β₂ ≫ ιψ.hom with hρ
  refine Set.Finite.subset (hfin.image (pointsMap B S hS _ ρ)) ?_
  rintro r ⟨hr₁, hr₂⟩
  set r₀ := pointsMap B S hS (Limits.pullback ψ ψ) ιψ.inv r with hr₀
  have hιinv₁ : ιψ.inv ≫ yoneda.map h₁ = pullback.fst ψ ψ :=
    IsPullback.isoIsPullback_inv_fst _ _ _ _
  have hιinv₂ : ιψ.inv ≫ yoneda.map h₂ = pullback.snd ψ ψ :=
    IsPullback.isoIsPullback_inv_snd _ _ _ _
  have hr₀₁ : pointsMap B S hS (yoneda.obj RW) (yoneda.map h₁) r₀ =
      pointsMap B S hS (yoneda.obj T) (yoneda.map σ) ct := by
    rw [← pointsMap_comp_apply, hιinv₁]
    exact hr₁
  have hr₀₂ : pointsMap B S hS (yoneda.obj RW) (yoneda.map h₂) r₀ =
      pointsMap B S hS (yoneda.obj T) (yoneda.map σ) dt := by
    rw [← pointsMap_comp_apply, hιinv₂]
    exact hr₂
  obtain ⟨α, hα₁, hα₂⟩ := exists_points_of_isPullback B S hS sqA ct r₀ hr₀₁.symm
  obtain ⟨n, hn₁, hn₂⟩ := exists_points_of_isPullback B S hS sqN α dt (by
    rw [pointsMap_comp_apply, hα₂, hr₀₂])
  refine ⟨pointsMap B S hS (yoneda.obj N) e.inv n, ⟨?_, ?_⟩, ?_⟩
  · rw [← pointsMap_comp_apply, IsPullback.isoIsPullback_inv_fst, pointsMap_comp_apply, hn₁]
    exact hα₁
  · rw [← pointsMap_comp_apply, IsPullback.isoIsPullback_inv_snd]
    exact hn₂
  · rw [← pointsMap_comp_apply]
    have hcomp : e.inv ≫ ρ = yoneda.map μ₁ ≫ yoneda.map β₂ ≫ ιψ.hom := by
      rw [hρ, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    rw [hcomp, pointsMap_comp_apply, hn₁, pointsMap_comp_apply, hα₂, hr₀,
      ← pointsMap_comp_apply, ιψ.inv_hom_id]
    exact congrFun (pointsMap_id B S hS (Limits.pullback ψ ψ)) r

/-! ### Transfer of a relation fibre up an étale morphism of charts -/

/-- If a relation fibre of the chart `h_U ⟶ F` above the pair of images of two points of `|T|`
is finite, then so is the relation fibre of the composite chart `h_T ⟶ h_U ⟶ F` above the two
points themselves, provided the morphism `T ⟶ U` of the site is étale.

The self-fibre-product of `h_T` over `F` is `h_T ×_{h_U} (h_U ×_F h_U) ×_{h_U} h_T` by
`CategoryTheory.IsPullback.selfPullback_comp`, and the prescribed relation fibre is therefore the
union, indexed by the — finite — relation fibre of `h_U ⟶ F` above the pair of images, of two
nested sets of Tag 0AC2, each attached to a cartesian square of representable presheaves whose
lower horizontal morphism is étale. Tag 0AC3 makes those finite. -/
private theorem hasFiniteRelationFiber_comp
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T U : BigFppfOver B S hS} (π : T ⟶ U)
    {φ : yoneda.obj U ⟶ F} (hφ : IsEtale B S hS φ)
    (hπ : Etale ((BigFppfOver.toScheme B S hS).map π)) (ct dt : points B S hS (yoneda.obj T))
    (hfin : HasFiniteRelationFiber B S hS F U φ
      (pointsMap B S hS (yoneda.obj T) (yoneda.map π) ct)
      (pointsMap B S hS (yoneda.obj T) (yoneda.map π) dt)) :
    HasFiniteRelationFiber B S hS F T (yoneda.map π ≫ φ) ct dt := by
  have hφp := presheaf_etale_of_isEtale B S hS hφ
  set RU : BigFppfOver B S hS := hφp.rep.pullback φ
  set g₁ : RU ⟶ U := hφp.rep.fst' φ
  set g₂ : RU ⟶ U := hφp.rep.snd φ
  have sqRU : IsPullback (yoneda.map g₁) (yoneda.map g₂) φ φ := hφp.rep.isPullback' φ
  have hg₁Et : Etale ((BigFppfOver.toScheme B S hS).map g₁) :=
    hφp.property φ (yoneda.map g₂) g₁ sqRU.flip
  obtain ⟨A, N, β₁, β₂, μ₁, μ₂, sqA, sqN, sqL⟩ := exists_selfPullback_comp_squares π sqRU
  set τ : yoneda.obj T ⟶ F := yoneda.map π ≫ φ
  set e := (IsPullback.of_hasPullback τ τ).isoIsPullback _ _ sqL
  -- The relation of `h_U`, as an object of the site.
  set ιφ := sqRU.isoIsPullback _ _ (IsPullback.of_hasPullback φ φ)
  have hιhom₁ : ιφ.hom ≫ pullback.fst φ φ = yoneda.map g₁ :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hιhom₂ : ιφ.hom ≫ pullback.snd φ φ = yoneda.map g₂ :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hSUfin : {r : points B S hS (yoneda.obj RU) |
      pointsMap B S hS (yoneda.obj RU) (yoneda.map g₁) r =
          pointsMap B S hS (yoneda.obj T) (yoneda.map π) ct ∧
        pointsMap B S hS (yoneda.obj RU) (yoneda.map g₂) r =
          pointsMap B S hS (yoneda.obj T) (yoneda.map π) dt}.Finite := by
    have hpre : {r : points B S hS (yoneda.obj RU) |
        pointsMap B S hS (yoneda.obj RU) (yoneda.map g₁) r =
            pointsMap B S hS (yoneda.obj T) (yoneda.map π) ct ∧
          pointsMap B S hS (yoneda.obj RU) (yoneda.map g₂) r =
            pointsMap B S hS (yoneda.obj T) (yoneda.map π) dt} =
        pointsMap B S hS (yoneda.obj RU) ιφ.hom ⁻¹'
        {r | pointsMap B S hS (Limits.pullback φ φ) (pullback.fst φ φ) r =
            pointsMap B S hS (yoneda.obj T) (yoneda.map π) ct ∧
          pointsMap B S hS (Limits.pullback φ φ) (pullback.snd φ φ) r =
            pointsMap B S hS (yoneda.obj T) (yoneda.map π) dt} := by
      ext r
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← pointsMap_comp_apply, hιhom₁, hιhom₂]
    rw [hpre]
    exact hfin.preimage ((pointsEquivOfIso B S hS ιφ).injective.injOn)
  -- The two layers of the decomposition, as cartesian squares of representable presheaves.
  set D₁ : PointsFibresDiagram B S hS :=
    { W := yoneda.obj A
      Z := yoneda.obj RU
      X := yoneda.obj T
      Y := yoneda.obj U
      W_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS A
      Z_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS RU
      X_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS T
      Y_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS U
      q := yoneda.map β₂
      p := yoneda.map β₁
      f := yoneda.map π
      g := yoneda.map g₁
      isPullback := sqA }
  set D₂ : PointsFibresDiagram B S hS :=
    { W := yoneda.obj N
      Z := yoneda.obj T
      X := yoneda.obj A
      Y := yoneda.obj U
      W_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS N
      Z_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS T
      X_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS A
      Y_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS U
      q := yoneda.map μ₂
      p := yoneda.map μ₁
      f := yoneda.map β₂ ≫ yoneda.map g₂
      g := yoneda.map π
      isPullback := sqN }
  have hfib₁ : ∀ r : points B S hS (yoneda.obj RU),
      pointsMap B S hS (yoneda.obj RU) (yoneda.map g₁) r =
          pointsMap B S hS (yoneda.obj T) (yoneda.map π) ct →
      {α : points B S hS (yoneda.obj A) |
        pointsMap B S hS (yoneda.obj A) (yoneda.map β₁) α = ct ∧
        pointsMap B S hS (yoneda.obj A) (yoneda.map β₂) α = r}.Finite := by
    intro r hr
    exact finite_fibrePoints_of_representable D₁ inferInstance inferInstance
      inferInstance ct r hr.symm
      (isLocallyQuasiFinite_yoneda_map_of_etale B S hS g₁ hg₁Et)
  have hfib₂ : ∀ α : points B S hS (yoneda.obj A),
      pointsMap B S hS (yoneda.obj A) (yoneda.map β₂ ≫ yoneda.map g₂) α =
        pointsMap B S hS (yoneda.obj T) (yoneda.map π) dt →
      {n : points B S hS (yoneda.obj N) |
        pointsMap B S hS (yoneda.obj N) (yoneda.map μ₁) n = α ∧
        pointsMap B S hS (yoneda.obj N) (yoneda.map μ₂) n = dt}.Finite := by
    intro α hα
    exact finite_fibrePoints_of_representable D₂ inferInstance inferInstance
      inferInstance α dt hα
      (isLocallyQuasiFinite_yoneda_map_of_etale B S hS π hπ)
  -- The relation fibre of `τ`, transported to `N`.
  have hefst : e.hom ≫ (yoneda.map μ₁ ≫ yoneda.map β₁) = pullback.fst τ τ :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hesnd : e.hom ≫ yoneda.map μ₂ = pullback.snd τ τ :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hSNfin : {n : points B S hS (yoneda.obj N) |
      pointsMap B S hS (yoneda.obj N) (yoneda.map μ₁ ≫ yoneda.map β₁) n = ct ∧
        pointsMap B S hS (yoneda.obj N) (yoneda.map μ₂) n = dt}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion hSUfin fun r hr =>
      Set.Finite.biUnion (hfib₁ r hr.1) fun α hα => hfib₂ α
        (by rw [pointsMap_comp_apply, hα.2]; exact hr.2)) ?_
    rintro n ⟨hn₁, hn₂⟩
    rw [pointsMap_comp_apply] at hn₁
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨pointsMap B S hS (yoneda.obj A) (yoneda.map β₂)
      (pointsMap B S hS (yoneda.obj N) (yoneda.map μ₁) n), ⟨?_, ?_⟩,
      pointsMap B S hS (yoneda.obj N) (yoneda.map μ₁) n, ⟨hn₁, rfl⟩, rfl, hn₂⟩
    · rw [← pointsMap_comp_apply, ← sqA.w, pointsMap_comp_apply, hn₁]
    · rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, sqN.w, pointsMap_comp_apply, hn₂]
  refine Set.Finite.subset (hSNfin.preimage
    ((pointsEquivOfIso B S hS e).injective.injOn)) ?_
  rintro m ⟨hm₁, hm₂⟩
  refine ⟨?_, ?_⟩
  · rw [pointsEquivOfIso_apply, ← pointsMap_comp_apply, hefst]
    exact hm₁
  · rw [pointsEquivOfIso_apply, ← pointsMap_comp_apply, hesnd]
    exact hm₂

/-! ### Stacks 03JU, part (1) implies part (2) -/

/-- **Stacks 03JU, part (1) implies part (2).** If some étale chart of an algebraic space `F`
over `S` has two points above `x` with finite relation fibre, then every pair of points above
`x` in every étale chart of `F` has finite relation fibre.

Let `φ : h_U ⟶ F` be the chart of part (1), with points `a`, `b` above `x`, and let
`ψ : h_W ⟶ F` be any étale chart with points `c`, `d` above `x`. The fibre product
`T = h_W ×_F h_U` is representable with both projections étale, and Tag 03H4 lifts `(a, c)` and
`(b, d)` to points of `|T|`. The relation fibre of `h_T ⟶ F` above that pair of lifts is finite
because the relation fibre of `φ` above `(a, b)` is, and the relation fibre of `ψ` above `(c, d)`
is finite because that one is.

The hypothesis `_hF` that `F` is an algebraic space is retained from the source statement but is
not used. -/
@[stacks 03JU "part (1) implies part (2)"]
theorem HasFiniteRelationFiberAt.hasFiniteRelationFiberAtEveryEtaleChart
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (h : HasFiniteRelationFiberAt B S hS F x) :
    HasFiniteRelationFiberAtEveryEtaleChart B S hS F x := by
  obtain ⟨U, φ, a, b, hφ, ha, hb, hfin⟩ := h
  intro W ψ c d hψ hc hd
  have hφp := presheaf_etale_of_isEtale B S hS hφ
  set T : BigFppfOver B S hS := hφp.rep.pullback ψ
  set π : T ⟶ U := hφp.rep.fst' ψ
  set σ : T ⟶ W := hφp.rep.snd ψ
  have sqT : IsPullback (yoneda.map π) (yoneda.map σ) φ ψ := hφp.rep.isPullback' ψ
  have hπEt : Etale ((BigFppfOver.toScheme B S hS).map π) :=
    (presheaf_etale_of_isEtale B S hS hψ).property φ (yoneda.map σ) π sqT.flip
  obtain ⟨ct, hct₁, hct₂⟩ := exists_points_of_isPullback B S hS sqT a c (ha.trans hc.symm)
  obtain ⟨dt, hdt₁, hdt₂⟩ := exists_points_of_isPullback B S hS sqT b d (hb.trans hd.symm)
  have key : HasFiniteRelationFiber B S hS F T (yoneda.map π ≫ φ) ct dt := by
    refine hasFiniteRelationFiber_comp B S hS π hφ hπEt ct dt ?_
    rw [hct₁, hdt₁]
    exact hfin
  rw [sqT.w] at key
  have hres := hasFiniteRelationFiber_of_comp B S hS σ hψ ct dt key
  rwa [hct₂, hdt₂] at hres

/-- **Stacks 03JU, part (2) implies part (1).** An algebraic space over `S` has a surjective
étale chart, which carries a point above `x`, so the universally quantified condition (2) is
witnessed and condition (1) holds.

This is `AlgebraicGeometry.Space.hasFiniteRelationFiberAt_of_everyEtaleChart` with its
hypothesis that some étale chart has a point above `x` discharged by an atlas of Tag 03FQ, which
is surjective on the points of Tag 03BU by Tag 03H5. Together with
`AlgebraicGeometry.Space.HasFiniteRelationFiberAt.hasFiniteRelationFiberAtEveryEtaleChart` it
makes conditions (1) and (2) of Stacks 03JU equivalent. -/
@[stacks 03JU "part (2) implies part (1)"]
theorem HasFiniteRelationFiberAtEveryEtaleChart.hasFiniteRelationFiberAt
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (h : HasFiniteRelationFiberAtEveryEtaleChart B S hS F x) :
    HasFiniteRelationFiberAt B S hS F x := by
  obtain ⟨U, f, hfS, hfE⟩ := hF.exists_atlas
  obtain ⟨a, ha⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U f).mp hfS x
  exact hasFiniteRelationFiberAt_of_everyEtaleChart B S hS F h U f
    (isEtale_of_presheaf_etale B S hS hfE) a ha

end AlgebraicGeometry.Space

end
