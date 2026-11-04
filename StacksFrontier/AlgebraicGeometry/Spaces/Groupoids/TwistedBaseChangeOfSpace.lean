module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.TwistedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment

/-!
# The twisted base change of a groupoid scheme along an étale morphism to an algebraic space

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S` whose object and arrow schemes lie in the
big fppf site of `S`, let `ψ : h_U ⟶ Y` be a morphism to an algebraic space which is invariant
under `s` and `t`, and let `v : h_V ⟶ Y` be a morphism from an object of the site. Because the
diagonal of `Y` is representable, the fibre product `U' = U ×_Y V` is an object of the site, and
this file shows that it carries the structure of a twisted base change of `G`
(`AlgebraicGeometry.GroupoidScheme.TwistedBaseChange`) with auxiliary scheme `V`: the projections
to `U` and `V` are jointly monic, and an arrow `r` acts on a point `(u, x)` over its target by
`(s(r), x)`, which is a point of `U'` because `ψ(s(r)) = ψ(t(r)) = ψ(u) = v(x)`.

When `v` is étale, so is the projection `U' ⟶ U`, and when `V` is separated over `S`, so is the
projection; these are the hypotheses under which
`AlgebraicGeometry.GroupoidScheme.TwistedBaseChange.exists_etale_chart` applies.

## Main definitions

* `AlgebraicGeometry.Space.twistedBaseChangeOfSpace`: the twisted base change `U ×_Y V`.

## Main results

* `AlgebraicGeometry.Space.etale_twistedBaseChangeOfSpace_proj` and
  `AlgebraicGeometry.Space.isSeparated_twistedBaseChangeOfSpace_proj`: the projection to `U` is
  étale, respectively separated.
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

noncomputable section

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {G : GroupoidScheme S} (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (ψ : yoneda.obj (schemeSiteObject B hS hU) ⟶ Y)
  (hψ : yoneda.map (schemeSiteMap B hS hR hU G.source) ≫ ψ =
    yoneda.map (schemeSiteMap B hS hR hU G.target) ≫ ψ)
  {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y)

/-- The object `U ×_Y V` of the site. -/
abbrev twistedObject : BigFppfOver B S hS :=
  (Functor.relativelyRepresentable.of_diag hY.diagonal_representable v).pullback ψ

/-- The projection `U ×_Y V ⟶ U`. -/
abbrev twistedProj : twistedObject hU hY ψ v ⟶ schemeSiteObject B hS hU :=
  (Functor.relativelyRepresentable.of_diag hY.diagonal_representable v).snd ψ

/-- The projection `U ×_Y V ⟶ V`. -/
abbrev twistedToAux : twistedObject hU hY ψ v ⟶ V :=
  (Functor.relativelyRepresentable.of_diag hY.diagonal_representable v).fst' ψ

/-- The square formed by the two projections of `U ×_Y V`, `v` and `ψ` commutes. -/
theorem twisted_w :
    yoneda.map (twistedToAux hU hY ψ v) ≫ v = yoneda.map (twistedProj hU hY ψ v) ≫ ψ :=
  ((Functor.relativelyRepresentable.of_diag hY.diagonal_representable v).isPullback' ψ).w

/-- The two projections of `U ×_Y V` are jointly monic on the objects of the site. -/
theorem twisted_hom_ext {T : BigFppfOver B S hS} {a b : T ⟶ twistedObject hU hY ψ v}
    (h₁ : a ≫ twistedProj hU hY ψ v = b ≫ twistedProj hU hY ψ v)
    (h₂ : a ≫ twistedToAux hU hY ψ v = b ≫ twistedToAux hU hY ψ v) : a = b :=
  (Functor.relativelyRepresentable.of_diag hY.diagonal_representable v).hom_ext' h₂ h₁

/-- The scheme underlying `U ×_Y V` lies in the site. -/
theorem contains_twistedObject :
    B.Contains ((siteToOver B hS).obj (twistedObject hU hY ψ v)).left :=
  (twistedObject hU hY ψ v).left.2

/-- The projection `U ×_Y V ⟶ U`, read in schemes over `S`. -/
def twistedProjOver : (siteToOver B hS).obj (twistedObject hU hY ψ v) ⟶ G.objects :=
  (siteToOver B hS).map (twistedProj hU hY ψ v)

/-- The comparison of `U ×_Y V` with the product of `U` and `V` in schemes over `S`. -/
abbrev twistedToProd : (siteToOver B hS).obj (twistedObject hU hY ψ v) ⟶
    G.objects ⨯ (siteToOver B hS).obj V :=
  prod.lift (twistedProjOver hU hY ψ v) ((siteToOver B hS).map (twistedToAux hU hY ψ v))

/-- The comparison of `U ×_Y V` with the product of `U` and `V` is a monomorphism of schemes over
`S`. -/
instance mono_twistedToProd : Mono (twistedToProd hU hY ψ v) := by
  let m := twistedToProd hU hY ψ v
  have hK := BigFppfSite.contains_pullback_left B m m (contains_twistedObject hU hY ψ v)
    (contains_twistedObject hU hY ψ v)
  let k₁ : schemeSiteObject B hS hK ⟶ twistedObject hU hY ψ v :=
    (siteToOver B hS).preimage (pullback.fst m m)
  let k₂ : schemeSiteObject B hS hK ⟶ twistedObject hU hY ψ v :=
    (siteToOver B hS).preimage (pullback.snd m m)
  have hc := pullback.condition (f := m) (g := m)
  have hk₁ : (siteToOver B hS).map k₁ = pullback.fst m m := Functor.map_preimage _ _
  have hk₂ : (siteToOver B hS).map k₂ = pullback.snd m m := Functor.map_preimage _ _
  have hk : k₁ = k₂ := by
    refine twisted_hom_ext hU hY ψ v ?_ ?_
    · apply (siteToOver B hS).map_injective
      rw [Functor.map_comp, Functor.map_comp, hk₁, hk₂]
      change _ ≫ twistedProjOver hU hY ψ v = _ ≫ twistedProjOver hU hY ψ v
      have := congrArg (· ≫ prod.fst) hc
      simp only [Category.assoc, m, twistedToProd, prod.lift_fst] at this
      exact this
    · apply (siteToOver B hS).map_injective
      rw [Functor.map_comp, Functor.map_comp, hk₁, hk₂]
      have := congrArg (· ≫ prod.snd) hc
      simp only [Category.assoc, m, twistedToProd, prod.lift_snd] at this
      exact this
  refine (mono_iff_fst_eq_snd (pullbackIsPullback m m)).2 ?_
  have := congrArg (siteToOver B hS).map hk
  rwa [hk₁, hk₂] at this

include hR in
/-- The fibre product of the projection `U ×_Y V ⟶ U` with the target map lies in the site. -/
theorem contains_twistedArrows :
    B.Contains (pullback (twistedProjOver hU hY ψ v) G.target).left :=
  BigFppfSite.contains_pullback_left B _ _ (contains_twistedObject hU hY ψ v) hR

/-- The projection of `(U ×_Y V) ×_{U, t} R` to `U ×_Y V`, on the site. -/
abbrev twistedArrowsFst :
    schemeSiteObject B hS (contains_twistedArrows hU hR hY ψ v) ⟶ twistedObject hU hY ψ v :=
  (siteToOver B hS).preimage (X := schemeSiteObject B hS (contains_twistedArrows hU hR hY ψ v))
    (Y := twistedObject hU hY ψ v)
    (pullback.fst (twistedProjOver hU hY ψ v) G.target)

/-- The projection of `(U ×_Y V) ×_{U, t} R` to `R`, on the site. -/
abbrev twistedArrowsSnd :
    schemeSiteObject B hS (contains_twistedArrows hU hR hY ψ v) ⟶ schemeSiteObject B hS hR :=
  (siteToOver B hS).preimage (X := schemeSiteObject B hS (contains_twistedArrows hU hR hY ψ v))
    (Y := schemeSiteObject B hS hR)
    (pullback.snd (twistedProjOver hU hY ψ v) G.target)

/-- The projection of `(U ×_Y V) ×_{U, t} R` to `U ×_Y V`, read in schemes over `S`, is the first
pullback projection. -/
theorem map_twistedArrowsFst : (siteToOver B hS).map (twistedArrowsFst hU hR hY ψ v) =
    pullback.fst (twistedProjOver hU hY ψ v) G.target :=
  Functor.map_preimage _ _

/-- The projection of `(U ×_Y V) ×_{U, t} R` to `R`, read in schemes over `S`, is the second
pullback projection. -/
theorem map_twistedArrowsSnd : (siteToOver B hS).map (twistedArrowsSnd hU hR hY ψ v) =
    pullback.snd (twistedProjOver hU hY ψ v) G.target :=
  Functor.map_preimage _ _

include hψ in
/-- The action on the site: an arrow `r` and a point `(u, x)` over its target go to `(s(r), x)`. -/
def twistedActSite :
    schemeSiteObject B hS (contains_twistedArrows hU hR hY ψ v) ⟶ twistedObject hU hY ψ v :=
  (Functor.relativelyRepresentable.of_diag hY.diagonal_representable v).lift'
    (twistedArrowsFst hU hR hY ψ v ≫ twistedToAux hU hY ψ v)
    (twistedArrowsSnd hU hR hY ψ v ≫ schemeSiteMap B hS hR hU G.source) (by
    have hcond : twistedArrowsFst hU hR hY ψ v ≫ twistedProj hU hY ψ v =
        twistedArrowsSnd hU hR hY ψ v ≫ schemeSiteMap B hS hR hU G.target := by
      apply (siteToOver B hS).map_injective
      rw [Functor.map_comp, Functor.map_comp, siteToOver_map_schemeSiteMap,
        map_twistedArrowsFst, map_twistedArrowsSnd]
      exact (pullback.condition : pullback.fst (twistedProjOver hU hY ψ v) G.target ≫
        twistedProjOver hU hY ψ v = _)
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, twisted_w,
      ← Category.assoc, ← Functor.map_comp, hcond, Functor.map_comp, Category.assoc, ← hψ])

/-- The action followed by the projection to `U` is the source map: `(r, (u, x))` goes to
`s(r)`. -/
theorem twistedActSite_snd :
    twistedActSite hU hR hY ψ hψ v ≫ twistedProj hU hY ψ v =
      twistedArrowsSnd hU hR hY ψ v ≫ schemeSiteMap B hS hR hU G.source :=
  Functor.relativelyRepresentable.lift'_snd _ _ _ _

/-- The action does not change the `V`-coordinate: `(r, (u, x))` goes to `x`. -/
theorem twistedActSite_fst :
    twistedActSite hU hR hY ψ hψ v ≫ twistedToAux hU hY ψ v =
      twistedArrowsFst hU hR hY ψ v ≫ twistedToAux hU hY ψ v :=
  Functor.relativelyRepresentable.lift'_fst _ _ _ _

/-- **The twisted base change `U ×_Y V` of `G`.** -/
def twistedBaseChangeOfSpace : GroupoidScheme.TwistedBaseChange G where
  obj := (siteToOver B hS).obj (twistedObject hU hY ψ v)
  aux := (siteToOver B hS).obj V
  proj := twistedProjOver hU hY ψ v
  toAux := (siteToOver B hS).map (twistedToAux hU hY ψ v)
  ext a b h₁ h₂ := by
    rw [← cancel_mono (twistedToProd hU hY ψ v)]
    refine prod.hom_ext ?_ ?_
    · simpa only [Category.assoc, twistedToProd, prod.lift_fst] using h₁
    · simpa only [Category.assoc, twistedToProd, prod.lift_snd] using h₂
  act := (siteToOver B hS).map (twistedActSite hU hR hY ψ hψ v)
  act_proj := by
    have h := congrArg (siteToOver B hS).map (twistedActSite_snd hU hR hY ψ hψ v)
    rwa [Functor.map_comp, Functor.map_comp, siteToOver_map_schemeSiteMap,
      map_twistedArrowsSnd] at h
  act_toAux := by
    have h := congrArg (siteToOver B hS).map (twistedActSite_fst hU hR hY ψ hψ v)
    rwa [Functor.map_comp, Functor.map_comp, map_twistedArrowsFst] at h

/-- The object scheme of the twisted base change is `U ×_Y V`. -/
@[simp]
theorem twistedBaseChangeOfSpace_obj :
    (twistedBaseChangeOfSpace hU hR hY ψ hψ v).obj =
      (siteToOver B hS).obj (twistedObject hU hY ψ v) := rfl

/-- The auxiliary scheme of the twisted base change is `V`. -/
@[simp]
theorem twistedBaseChangeOfSpace_aux :
    (twistedBaseChangeOfSpace hU hR hY ψ hψ v).aux = (siteToOver B hS).obj V := rfl

/-- The projection of the twisted base change is the projection `U ×_Y V ⟶ U`. -/
@[simp]
theorem twistedBaseChangeOfSpace_proj :
    (twistedBaseChangeOfSpace hU hR hY ψ hψ v).proj = twistedProjOver hU hY ψ v := rfl

/-- The map to the auxiliary scheme of the twisted base change is the projection
`U ×_Y V ⟶ V`. -/
@[simp]
theorem twistedBaseChangeOfSpace_toAux :
    (twistedBaseChangeOfSpace hU hR hY ψ hψ v).toAux =
      (siteToOver B hS).map (twistedToAux hU hY ψ v) := rfl

/-- The projection `U ×_Y V ⟶ U` is étale as soon as `v` is. -/
theorem etale_twistedBaseChangeOfSpace_proj
    (hv : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) v) :
    Etale (twistedBaseChangeOfSpace hU hR hY ψ hψ v).proj.left :=
  MorphismProperty.relative.property_snd hv ψ

/-- The projection `U ×_Y V ⟶ U` is separated as soon as `V` is separated over `S`. -/
theorem isSeparated_twistedBaseChangeOfSpace_proj
    [_root_.AlgebraicGeometry.IsSeparated ((siteToOver B hS).obj V).hom] :
    _root_.AlgebraicGeometry.IsSeparated (twistedBaseChangeOfSpace hU hR hY ψ hψ v).proj.left := by
  have hpb := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd G.objects
    ((siteToOver B hS).obj V))
  have hfst : IsSeparated (prod.fst : G.objects ⨯ (siteToOver B hS).obj V ⟶ G.objects).left :=
    MorphismProperty.of_isPullback hpb.flip ‹_›
  have hfac : (twistedBaseChangeOfSpace hU hR hY ψ hψ v).proj.left =
      (twistedToProd hU hY ψ v).left ≫
        (prod.fst : G.objects ⨯ (siteToOver B hS).obj V ⟶ G.objects).left := by
    rw [← Over.comp_left, prod.lift_fst]
    rfl
  rw [hfac]
  have : Mono (twistedToProd hU hY ψ v).left := Over.mono_left_of_mono _
  exact MorphismProperty.comp_mem (@IsSeparated) (twistedToProd hU hY ψ v).left
    (prod.fst : G.objects ⨯ (siteToOver B hS).obj V ⟶ G.objects).left
    (AlgebraicGeometry.IsSeparated.isSeparated_of_mono _) hfst

end AlgebraicGeometry.Space

end

end
