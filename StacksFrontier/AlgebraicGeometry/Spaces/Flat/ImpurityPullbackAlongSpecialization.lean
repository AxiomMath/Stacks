module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ImpurityFlatAscent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty

/-!
# Pulling an impurity back along a morphism of test schemes

In the situation of Stacks 0CV6, let `(T ⟶ Y, t' ⤳ t, ξ)` be an impurity of `F` above `y` and
let `k : T₁ ⟶ T` be a morphism of test schemes with a specialization `t₁' ⤳ t₁` in `T₁` lying
over `t' ⤳ t`. Then `ξ` lifts to a point `ξ₁` of `X_{T₁}` over `t₁'`, and `(T₁ ⟶ Y, t₁' ⤳ t₁,
ξ₁)` is again an impurity of `F` above `y`. This is the argument the proof of Stacks 0CVA runs
for the étale chart it builds, isolated so that it can be applied to an open subscheme of the
test scheme, which is how the proof of Stacks 0CVB shrinks its test schemes.

## Main definitions

* `AlgebraicGeometry.Space.ImpurityDiagram.pullbackAlong`: the diagram over `T₁`.
* `AlgebraicGeometry.Space.PointedOver.ofTestScheme`: the pointed base change along a test
  scheme.

## Main results

* `AlgebraicGeometry.Space.ImpurityDiagram.exists_isImpurity_pullbackAlong`: the lifted
  diagram is an impurity, for a suitable lift `ξ₁`.
* `AlgebraicGeometry.Space.exists_specializes_of_isOpenImmersion`: a generalization of the image
  of a point under an open immersion of test schemes lifts.
* `AlgebraicGeometry.Space.exists_isImpurity_isLocallyQuasiFinite_of_isQuasiFiniteAt`: an
  impurity whose structure morphism is quasi-finite at `t` can be replaced by one whose structure
  morphism is locally quasi-finite.
* `AlgebraicGeometry.Space.exists_isImpurity_of_isImpurity_ofTestScheme`: an impurity of the base
  change to a pointed test scheme `(T₀, y₀)`, over a test scheme universally closed over `T₀` with
  a single point over `y₀`, pushes down to an impurity over `T₀` with specialized point `y₀`.

## Implementation notes

The lift `ξ₁` is produced by Stacks 0CV2, part (2), at a field-valued representative of `t₁'`
over which the membership of `ξ` in the relative weak assassin is witnessed; that
representative is the algebraic space form of Stacks 05DC,
`AlgebraicGeometry.Space.ImpurityDiagram.hasFibreWitnessAboveGeneralization`. No specialization
of `ξ₁` lies over `t₁`, because its image would be a specialization of `ξ` over `t`.

## References

* [Stacks Project, Tag 0CVA](https://stacks.math.columbia.edu/tag/0CVA)
* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_ImpurityPullbackAlongSpecialization
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

namespace ImpurityDiagram

variable {P : PrePureSituation.{u, u} B S hS}

/-- The impurity diagram over a test scheme `T₁` mapping to the test scheme of `D` by `k`, for
a specialization `t₁' ⤳ t₁` in `T₁` with `t₁` over `t` and a point `ξ₁` of `X_{T₁}` over
`t₁'`. -/
@[reducible] noncomputable def pullbackAlong (D : ImpurityDiagram P) {T₁ : BigFppfOver B S hS}
    (k : yoneda.obj T₁ ⟶ yoneda.obj D.T) {t₁ t₁' : points B S hS (yoneda.obj T₁)}
    (hs : pointsToScheme B S hS T₁ t₁' ⤳ pointsToScheme B S hS T₁ t₁)
    (ht : pointsMap B S hS (yoneda.obj T₁) k t₁ = D.t)
    (xi : points B S hS (pullback (k ≫ D.g) P.f))
    (hxi : pointsMap B S hS (pullback (k ≫ D.g) P.f) (pullback.fst (k ≫ D.g) P.f) xi = t₁') :
    ImpurityDiagram P where
  T := T₁
  g := k ≫ D.g
  t' := t₁'
  t := t₁
  specializes := hs
  mapsToChosenPoint := by rw [pointsMap_comp_apply, ht, D.mapsToChosenPoint]
  xi := xi
  xi_liesOver := hxi

/-- **An impurity pulls back along a morphism of test schemes lifting its specialization.** If
`D` is an impurity of `F` above `y` and `k : T₁ ⟶ T` carries a specialization `t₁' ⤳ t₁` of
`T₁` to `t' ⤳ t`, then some point `ξ₁` of `X_{T₁}` over `t₁'` and over `ξ` makes the diagram
over `T₁` an impurity of `F` above `y`. -/
theorem exists_isImpurity_pullbackAlong (D : ImpurityDiagram P) (hD : D.IsImpurity)
    {T₁ : BigFppfOver B S hS} (k : yoneda.obj T₁ ⟶ yoneda.obj D.T)
    {t₁ t₁' : points B S hS (yoneda.obj T₁)}
    (hs : pointsToScheme B S hS T₁ t₁' ⤳ pointsToScheme B S hS T₁ t₁)
    (ht : pointsMap B S hS (yoneda.obj T₁) k t₁ = D.t)
    (ht' : pointsMap B S hS (yoneda.obj T₁) k t₁' = D.t') :
    ∃ (xi : points B S hS (pullback (k ≫ D.g) P.f))
      (hxi : pointsMap B S hS (pullback (k ≫ D.g) P.f) (pullback.fst (k ≫ D.g) P.f) xi = t₁'),
      (D.pullbackAlong k hs ht xi hxi).IsImpurity := by
  obtain ⟨hD₁, hDcl⟩ := hD
  -- The total space `T₁ ×_Y X` is the base change of `X_T` along `k`.
  have tD : IsPullback D.toX D.toT P.f D.g := (IsPullback.of_hasPullback D.g P.f).flip
  set Ψ := tD.lift (pullback.snd (k ≫ D.g) P.f) (pullback.fst (k ≫ D.g) P.f ≫ k)
    (by rw [← pullback.condition, Category.assoc])
  have hΨT : Ψ ≫ D.toT = pullback.fst (k ≫ D.g) P.f ≫ k := tD.lift_snd _ _ _
  have sq : IsPullback Ψ (pullback.fst (k ≫ D.g) P.f) D.toT k :=
    IsPullback.of_right' (IsPullback.of_hasPullback (k ≫ D.g) P.f).flip tD
  set Nspace : AlgebraicSpaces B S hS := ⟨pullback (k ≫ D.g) P.f,
    isAlgebraicSpace_pullback B S hS (k ≫ D.g) P.f (isAlgebraicSpace_yoneda B S hS T₁) P.hX P.hY⟩
  set T₁space : AlgebraicSpaces B S hS := ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩
  set NtoT : Nspace ⟶ T₁space := ObjectProperty.homMk (pullback.fst (k ≫ D.g) P.f)
  set NtoX : Nspace ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) :=
    ObjectProperty.homMk (pullback.snd (k ≫ D.g) P.f)
  set kSpace : T₁space ⟶ (⟨yoneda.obj D.T, isAlgebraicSpace_yoneda B S hS D.T⟩ :
    AlgebraicSpaces B S hS) := ObjectProperty.homMk k
  set ΨSpace : Nspace ⟶ D.baseChangeSpace := ObjectProperty.homMk Ψ
  -- The point `ξ₁` of `T₁ ×_Y X`, from Stacks 0CV2, part (2).
  obtain ⟨q, hqclass, hqwit⟩ := D.hasFibreWitnessAboveGeneralization hD₁ T₁ k t₁' ht'
  obtain ⟨xi₁, hxi₁ass, hxi₁X, hxi₁T⟩ :=
    exists_isRelativeWeaklyAssociatedPoint_baseChange B S hS (f := D.toTSpace)
      (g := kSpace) (f' := NtoT) (g' := ΨSpace) sq D.baseChangeModule q hqwit
  have hxi₁X' : pointsMap B S hS (pullback (k ≫ D.g) P.f) Ψ xi₁ = D.xi := hxi₁X
  -- The pulled-back module on `T₁ ×_Y X` is the base change of `F`.
  have hpath : ΨSpace ≫ D.toXSpace = NtoX := ObjectProperty.hom_ext _ (tD.lift_fst _ _ _)
  have hmod : (modulePullback B S hS ΨSpace).obj D.baseChangeModule ≅
      (modulePullback B S hS NtoX).obj P.F :=
    (modulePullbackCompIso B S hS ΨSpace D.toXSpace).app P.F ≪≫
      eqToIso (congrArg (fun m : Nspace ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) =>
        (modulePullback B S hS m).obj P.F) hpath)
  refine ⟨xi₁, hxi₁T.trans hqclass,
    (isRelativeWeaklyAssociatedPoint_congr NtoT hmod xi₁).mp hxi₁ass, ?_⟩
  rintro ⟨θ, hθcl, hθT⟩
  refine hDcl ⟨pointsMap B S hS (pullback (k ≫ D.g) P.f) Ψ θ, ?_, ?_⟩
  · have hmem := image_closure_subset_closure_image
      (continuous_pointsMap B S hS (F := pullback (k ≫ D.g) P.f) Ψ) (s := {xi₁}) ⟨θ, hθcl, rfl⟩
    rwa [Set.image_singleton, hxi₁X'] at hmem
  · have hθT' : pointsMap B S hS (pullback (k ≫ D.g) P.f) (pullback.fst (k ≫ D.g) P.f) θ =
        t₁ := hθT
    rw [← pointsMap_comp_apply, hΨT, pointsMap_comp_apply, hθT', ht]

end ImpurityDiagram

/-! ### Open immersions of test schemes -/

/-- **Generalizations lift along an open immersion of test schemes.** If `j : T₀ ⟶ T` is an
open immersion of test schemes and `t'` is a generalization of the image of a point `t₀` of
`T₀`, then `t'` is the image of a generalization of `t₀`. -/
theorem exists_specializes_of_isOpenImmersion {T₀ T : BigFppfOver B S hS} (j : T₀ ⟶ T)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (t₀ : points B S hS (yoneda.obj T₀)) (t' : points B S hS (yoneda.obj T))
    (hs : pointsToScheme B S hS T t' ⤳
      pointsToScheme B S hS T (pointsMap B S hS (yoneda.obj T₀) (yoneda.map j) t₀)) :
    ∃ t₀' : points B S hS (yoneda.obj T₀),
      pointsToScheme B S hS T₀ t₀' ⤳ pointsToScheme B S hS T₀ t₀ ∧
        pointsMap B S hS (yoneda.obj T₀) (yoneda.map j) t₀' = t' := by
  set a := (BigFppfOver.toScheme B S hS).map j
  rw [pointsToScheme_pointsMap_yoneda] at hs
  obtain ⟨z, hz⟩ : pointsToScheme B S hS T t' ∈ Set.range a :=
    hs.mem_open a.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  have hzs : z ⤳ pointsToScheme B S hS T₀ t₀ := by
    rwa [← a.isOpenEmbedding.toIsInducing.specializes_iff, hz]
  refine ⟨(pointsEquivScheme B S hS T₀).symm z, ?_, ?_⟩
  · rwa [show pointsToScheme B S hS T₀ ((pointsEquivScheme B S hS T₀).symm z) = z from
      (pointsEquivScheme B S hS T₀).apply_symm_apply z]
  · refine injective_pointsToScheme B S hS T ?_
    rw [pointsToScheme_pointsMap_yoneda, ← hz]
    exact congrArg a ((pointsEquivScheme B S hS T₀).apply_symm_apply z)

/-! ### Shrinking the test scheme of an impurity -/

/-- **Shrinking an impurity to a locally quasi-finite one.** An impurity of `F` above `y` whose
structure morphism is quasi-finite at `t` gives an impurity whose structure morphism is locally
quasi-finite: replace `T` by the open subscheme representing an open subspace of `T` around `t`
on which `T ⟶ Y` is locally quasi-finite. -/
theorem exists_isImpurity_isLocallyQuasiFinite_of_isQuasiFiniteAt
    {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P) (hD : D.IsImpurity)
    (hqf : IsQuasiFiniteAt B S hS D.g D.t) :
    ∃ E : ImpurityDiagram P, E.IsImpurity ∧ IsLocallyQuasiFinite B S hS E.g := by
  obtain ⟨U, hU, x', hx', hUg⟩ := hqf
  have hrep := hU.2.rep
  set T₀ := hrep.pullback (𝟙 (yoneda.obj D.T))
  set j : T₀ ⟶ D.T := hrep.snd (𝟙 (yoneda.obj D.T))
  set fst : yoneda.obj T₀ ⟶ U.toFunctor := hrep.fst (𝟙 (yoneda.obj D.T))
  have hpb : IsPullback fst (yoneda.map j) U.ι (𝟙 (yoneda.obj D.T)) :=
    hrep.isPullback (𝟙 (yoneda.obj D.T))
  have hjfst : yoneda.map j = fst ≫ U.ι := (Category.comp_id _).symm.trans hpb.w.symm
  have : IsIso fst := hpb.isIso_fst_of_isIso
  -- The point `t₀` of `T₀` over `t`, and a generalization over `t'`.
  set t₀ := pointsMap B S hS U.toFunctor (inv fst) x' with ht₀
  have ht₀map : pointsMap B S hS (yoneda.obj T₀) (yoneda.map j) t₀ = D.t := by
    rw [ht₀, hjfst, ← pointsMap_comp_apply, IsIso.inv_hom_id_assoc, hx']
  obtain ⟨t₀', hs, ht₀'⟩ := exists_specializes_of_isOpenImmersion j
    (hU.2.property_snd (𝟙 (yoneda.obj D.T))) t₀ D.t' (ht₀map ▸ D.specializes)
  obtain ⟨_, _, himp⟩ := D.exists_isImpurity_pullbackAlong hD (yoneda.map j) hs ht₀map ht₀'
  refine ⟨_, himp, ?_⟩
  show IsLocallyQuasiFinite B S hS (yoneda.map j ≫ D.g)
  rw [hjfst, Category.assoc]
  exact isLocallyQuasiFinite_comp B S hS (isAlgebraicSpace_yoneda B S hS T₀) hU.1 P.hY fst
    (U.ι ≫ D.g)
    (isLocallyQuasiFinite_of_isEtale B S hS hU.1
      (isEtale_of_presheaf_etale B S hS (presheaf_etale_of_iso B S hS (asIso fst)))) hUg

/-! ### Pushing an impurity down to a pointed test scheme -/

/-- The pointed base change of a situation along a test scheme `T₀ ⟶ Y` with a point `y₀` over
`y`. -/
@[reducible] noncomputable def PointedOver.ofTestScheme {P : PrePureSituation.{u, u} B S hS}
    (T₀ : BigFppfOver B S hS) (g₀ : yoneda.obj T₀ ⟶ P.Y) (y₀ : points B S hS (yoneda.obj T₀))
    (hy₀ : pointsMap B S hS (yoneda.obj T₀) g₀ y₀ = P.y) : PointedOver P where
  Y' := yoneda.obj T₀
  hY' := isAlgebraicSpace_yoneda B S hS T₀
  g := g₀
  y' := y₀
  mapsPoint := hy₀

/-- **An impurity over a test scheme which is universally closed over `T₀` with a single point
over `y₀` pushes down to `T₀`.** Let `E = (T₁ ⟶ T₀, t₁' ⤳ t₁, ξ₁)` be an impurity of the base
change of `F` to `X_{T₀}` above `y₀`, with `T₁ ⟶ T₀` universally closed and `t₁` the only point of
`T₁` over `y₀`. Then `(T₀ ⟶ Y, y' ⤳ y₀, θ)` is an impurity of `F` above `y`, where `y'` is the
image of `t₁'` and `θ` that of `ξ₁`.

This is the last step of the proof of Stacks 0CVB, (4) ⟹ (1): `θ` lies in the relative assassin
by Stacks 0CV2, part (1), and since `X_{T₁} ⟶ X_{T₀}` is a closed map the closure of `{θ}` is the
image of the closure of `{ξ₁}`, none of whose points lies over `t₁`. -/
theorem exists_isImpurity_of_isImpurity_ofTestScheme {P : PrePureSituation.{u, u} B S hS}
    {T₀ : BigFppfOver B S hS} {g₀ : yoneda.obj T₀ ⟶ P.Y} {y₀ : points B S hS (yoneda.obj T₀)}
    {hy₀ : pointsMap B S hS (yoneda.obj T₀) g₀ y₀ = P.y}
    (E : ImpurityDiagram (PointedOver.ofTestScheme T₀ g₀ y₀ hy₀).baseChange)
    (hE : E.IsImpurity) (huc : UniversallyClosed B S hS E.g)
    (huniq : ∀ u : points B S hS (yoneda.obj E.T),
      pointsMap B S hS (yoneda.obj E.T) E.g u = y₀ → u = E.t) :
    ∃ (t' : points B S hS (yoneda.obj T₀))
      (hs : pointsToScheme B S hS T₀ t' ⤳ pointsToScheme B S hS T₀ y₀)
      (xi : points B S hS (pullback g₀ P.f))
      (hxi : pointsMap B S hS (pullback g₀ P.f) (pullback.fst g₀ P.f) xi = t'),
      ({ T := T₀, g := g₀, t' := t', t := y₀, specializes := hs, mapsToChosenPoint := hy₀,
          xi := xi, xi_liesOver := hxi } : ImpurityDiagram P).IsImpurity := by
  obtain ⟨kk, hkk⟩ : ∃ kk : E.T ⟶ T₀, yoneda.map kk = E.g := ⟨_, Functor.map_preimage _ _⟩
  have hsq : IsPullback E.toX E.toT (pullback.fst g₀ P.f) E.g :=
    (IsPullback.of_hasPullback E.g (pullback.fst g₀ P.f)).flip
  have hcomm : ∀ z, pointsMap B S hS (pullback g₀ P.f) (pullback.fst g₀ P.f)
      (pointsMap B S hS E.baseChange E.toX z) =
        pointsMap B S hS (yoneda.obj E.T) E.g (pointsMap B S hS E.baseChange E.toT z) := fun z => by
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hsq.w]
  refine ⟨pointsMap B S hS (yoneda.obj E.T) E.g E.t', ?_,
    pointsMap B S hS E.baseChange E.toX E.xi, ?_, ?_⟩
  · have h := E.specializes.map ((BigFppfOver.toScheme B S hS).map kk).continuous
    rw [← pointsToScheme_pointsMap_yoneda, ← pointsToScheme_pointsMap_yoneda, hkk] at h
    exact h.trans (specializes_of_eq (congrArg (pointsToScheme B S hS T₀) E.mapsToChosenPoint))
  · rw [hcomm, E.xi_liesOver]
  · refine ⟨?_, ?_⟩
    · -- Stacks 0CV2, part (1)
      let T₀sp : AlgebraicSpaces B S hS := ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩
      let T₁sp : AlgebraicSpaces B S hS := ⟨yoneda.obj E.T, isAlgebraicSpace_yoneda B S hS E.T⟩
      let fsp : (PointedOver.ofTestScheme T₀ g₀ y₀ hy₀).source ⟶ T₀sp :=
        ObjectProperty.homMk (pullback.fst g₀ P.f)
      let gsp : T₁sp ⟶ T₀sp := ObjectProperty.homMk E.g
      exact isRelativeWeaklyAssociatedPoint_of_baseChange B S hS (g' := E.toXSpace)
        (f' := E.toTSpace) (f := fsp) (g := gsp) hsq
        (PointedOver.ofTestScheme T₀ g₀ y₀ hy₀).module hE.1
    · -- the closure of `{θ}` is the image of the closure of `{ξ₁}`
      rintro ⟨θ, hθ, hθy⟩
      have hclosedMap : IsClosedMap (pointsMap B S hS E.baseChange E.toX) :=
        isClosedMap_pointsMap_of_comp_isIso B S hS
          (pullbackSymmetry E.g (pullback.fst g₀ P.f)).hom
          (pullbackSymmetry_hom_comp_fst E.g (pullback.fst g₀ P.f))
          (huc _ (isAlgebraicSpace_pullback B S hS g₀ P.f
            (isAlgebraicSpace_yoneda B S hS T₀) P.hX P.hY) (pullback.fst g₀ P.f))
      obtain ⟨ζ, hζ, rfl⟩ := (hclosedMap (closure {E.xi}) isClosed_closure).closure_subset_iff.2
        (Set.singleton_subset_iff.2 ⟨E.xi, subset_closure rfl, rfl⟩) hθ
      exact hE.2 ⟨ζ, hζ, huniq _ (by rwa [← hcomm])⟩

end AlgebraicGeometry.Space

end
