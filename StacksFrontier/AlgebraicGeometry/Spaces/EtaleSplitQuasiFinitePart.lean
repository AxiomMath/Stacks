module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitFibrePointsIndexed
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitPresheafAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae

/-!
# Étale localization of the quasi-finite part of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type and
separated, let `y` be a point of `|Y|` and let `x₁, …, x_n` be points of `|X|` over `y` at which
`f` is quasi-finite, and assume that `f` is quasi-compact or that `Y` is decent. This file proves
**Stacks 082H**: after an étale base change `U ⟶ Y` carrying a point `u` to `y`, the space
`U ×_Y X` decomposes into two open-and-closed subspaces `W` and `V` with `V ⟶ U` **finite**, such
that every point of the fibre of `|V| ⟶ |U|` over `u` maps to one of the `xᵢ` and no point of the
fibre of `|W| ⟶ |U|` over `u` does.

Every ingredient of the proof is already in the library; what this file contributes is the
composite, which did not exist. The three paragraphs of the source proof are
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSplitFibrePointsIndexed.lean` (the replacement of the
prescribed points by the finitely many points of the fibre product, so that the base may be taken
affine) and `StacksFrontier/AlgebraicGeometry/Spaces/EtaleSplitDecompositionRestriction.lean` (the
affine chart, the splitting of Tag 02LN, and its restriction into the site); the passage from the
resulting open immersion of schemes to an étale morphism of presheaves is
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSplitPresheafAssembly.lean`; and the finiteness clause,
which is the quotient of the chart by its kernel pair, is
`StacksFrontier/AlgebraicGeometry/Spaces/ClopenPartFinite.lean`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isSeparated_pullbackFst`: a separated morphism of presheaves on the
  big fppf category over `S` stays separated after base change, in the orientation in which the
  base change is the *first* projection of the fibre product.
* `AlgebraicGeometry.Space.pointsMap_yoneda_map_symm_eq_of_map_eq`: a morphism of the big fppf
  category over `S` carrying a point of its source scheme to the point of its target scheme
  underlying `v` carries the point of the represented presheaf corresponding to the first to `v`.
* `AlgebraicGeometry.Space.exists_etale_hom_fibre_conditions_of_openImmersion`: the presheaf-level
  step of Stacks 082H, delivering the étale morphism `h_{Z₁} ⟶ U ×_Y X` together with **both**
  conditions on the fibre over the distinguished point in the form the finiteness result consumes.
* `AlgebraicGeometry.Space.exists_etale_decomposition_isFinite_of_isQuasiFiniteAt`: **Stacks
  082H**.

## Implementation notes

*The tag sits on one declaration.* Stacks 082H has a single assertion — its enumerated items
(1)–(4) are hypotheses, not conclusions — so the tag sits on the one theorem which states it,
and the two auxiliary results and the presheaf-level step carry no attribute.

*The étale neighbourhood is produced as an object of the site.* The source asks only for an étale
morphism of pointed algebraic *spaces* `(U, u) ⟶ (Y, y)`; what is produced here is a representable
`U`, which is an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_yoneda`, so the existential statement of the tag is
witnessed by something more specific than it asks for. Likewise the decomposition is stated by the
pair of subfunctors, their openness and closedness, the sheafification of their join being
everything and their meet being the sheafification of nothing — which is this repository's
rendering of `U ×_Y X = W ⨿ V`.

*The standing `HasSheafify` assumption.* The finiteness clause runs through the representability
of the open-and-closed piece as the quotient of an affine chart by its kernel pair, which is
proved in the sheaf category; the instance assumption `HasSheafify (BigFppfOver.topology B S hS)
(Type u)` is therefore carried, exactly as it is by the other tagged results of this cone which
use the same quotient (for instance the sites of `@[stacks 046M]` and `@[stacks 02WU]`). It is an
assumption about the ambient site, not a hypothesis of the lemma.

*Why the presheaf-level step is restated here.* The second condition on the fibre — that a point
of `|U ×_Y X|` over `u` which maps to one of the `xᵢ` lies in the image of `|Z₁|` — cannot be
derived from `AlgebraicGeometry.Space.exists_etale_yoneda_hom_of_openImmersion_pullback`, whose own
implementation notes say so: the factorisation of the étale morphism through the represented
`h_{Z ×_{Y₀} Zu}` is not recoverable from its statement, and that factorisation is exactly what
`AlgebraicGeometry.Space.mem_range_pointsMap_of_schemePoint_range` consumes. So
`AlgebraicGeometry.Space.exists_etale_hom_fibre_conditions_of_openImmersion` rebuilds the morphism
from `AlgebraicGeometry.Space.exists_etale_site_hom_of_openImmersion` and
`AlgebraicGeometry.Space.exists_etale_comparison_of_etale_site_hom` directly and keeps the square,
then transports along `CategoryTheory.Limits.pullbackRightPullbackFstIso` by hand.

*The point of the chart.* Producing the point of `|Z|` that the second condition needs is what the
last clause of
`AlgebraicGeometry.Space.exists_siteObject_isFinite_part_of_isQuasiFiniteAt` supplies — the chart
hits each prescribed point. That clause was present in the scheme-level result all along and was
dropped on the way into the site; it is now carried.

## References

* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_EtaleSplitQuasiFinitePart :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_EtaleSplitQuasiFinitePart
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_EtaleSplitQuasiFinitePart B S hS).has_limit _

/-- **A separated morphism of presheaves on the big fppf category over `S` stays separated under
base change, in the first-projection orientation.** This is Tag 03KL part (1) for
`CategoryTheory.Limits.pullback.fst g f` rather than for
`CategoryTheory.Limits.pullback.snd f g`: the two are the base change of `f` along `g` in the two
fibre products `g ×_Y f` and `f ×_Y g`, and
`AlgebraicGeometry.Space.isSeparated_pullbackSnd` is stated for the second.

The proof is the one of that result with the cartesian square flipped. -/
theorem isSeparated_pullbackFst {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Y)
    {f : X ⟶ Y} (h : IsSeparated B S hS f) : IsSeparated B S hS (pullback.fst g f) := by
  have h1 : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion)
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have h2 := MorphismProperty.relative_isStableUnderBaseChange
    (F := yoneda (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion)
      (BigFppfOver.toScheme B S hS))
  exact (MorphismProperty.IsStableUnderBaseChange.diagonal
    (P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion)
      (BigFppfOver.toScheme B S hS)).presheaf)).of_isPullback
      (IsPullback.of_hasPullback g f).flip h

/-- **Transporting a point of a scheme of the site across the Yoneda embedding.** Let
`α : U ⟶ V` be a morphism of the big fppf category over `S`, let `a` be a point of the underlying
scheme of `U` and let `v` be a point of `|h_V|`. If the morphism of schemes underlying `α` carries
`a` to the point of the underlying scheme of `V` corresponding to `v`, then the morphism of
presheaves `h_α` carries the point of `|h_U|` corresponding to `a` to `v`.

This is clause (1) of Tag 03BX and its naturality,
`AlgebraicGeometry.Space.pointsEquivScheme_pointsMap_yoneda`, read backwards. -/
theorem pointsMap_yoneda_map_symm_eq_of_map_eq {U V : BigFppfOver B S hS} (α : U ⟶ V)
    (a : (BigFppfOver.toScheme B S hS).obj U) (v : points B S hS (yoneda.obj V))
    (h : (BigFppfOver.toScheme B S hS).map α a = pointsToScheme B S hS V v) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map α)
      ((pointsEquivScheme B S hS U).symm a) = v := by
  refine (pointsEquivScheme B S hS V).injective ?_
  rw [pointsEquivScheme_pointsMap_yoneda, (pointsEquivScheme B S hS U).apply_symm_apply]
  exact h

/-- **The presheaf-level step of Stacks 082H, with both conditions on the fibre.** In the
situation delivered by `AlgebraicGeometry.Space.exists_siteObject_isFinite_part_of_isQuasiFiniteAt`
— an étale chart `b : h_Z ⟶ Y₀ ×_Y X` with `τ : Z ⟶ Y₀` underlying `b` followed by the first
projection, a morphism `ν : Zu ⟶ Y₀` of the site, a morphism `ζ : Z₁ ⟶ Zu` of the site, an open
immersion `θ` from the underlying scheme of `Z₁` into `Z ×_{Y₀} Zu` compatible with `ζ`, a point
`u'` of the underlying scheme of `Zu` over the point `u₀` of `|h_{Y₀}|`, the points `z₁, …, z_m`
of the underlying scheme of `Z` and the finitely many points `w₁, …, w_p` of `|Y₀ ×_Y X|` over
`u₀` which lie over the prescribed points `x₁, …, x_n` of `|X|` — there is an **étale** morphism
`z : h_{Z₁} ⟶ Zu ×_Y X` of presheaves whose composite with the first projection is `h_ζ` and
which satisfies the two conditions on the fibre over the point of `|h_{Zu}|` corresponding to
`u'`: every point of `|h_{Z₁}|` over it maps to one of the `xᵢ`, and no point of `|Zu ×_Y X|`
outside the image of `|h_{Z₁}|` which lies over it does.

Those two conditions are the hypotheses `hVpts` and `hWpts` of
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite`, and this is the step
which produces them. The first is
`AlgebraicGeometry.Space.forall_exists_pointsMap_eq_of_fibre_schemePoints`; the second is
`AlgebraicGeometry.Space.mem_range_pointsMap_of_schemePoint_range`, whose point of `|Z|` comes
from the clause of the previous step saying that the chart hits each `wⱼ`, and whose conclusion is
carried across the comparison isomorphism by
`AlgebraicGeometry.Space.mem_range_pointsMap_comp_iso_iff`.

None of the hypotheses is an existential and none contains any part of the conclusion: the
étaleness concluded is of a morphism built here out of `θ`, and the two fibre conditions concluded
are about presheaves while the two assumed are about morphisms of schemes. All of them are
discharged, at the one place they are used, by results proved without them. -/
theorem exists_etale_hom_fibre_conditions_of_openImmersion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    {Y₀ Zu Z₁ Z : BigFppfOver B S hS} (g₀ : yoneda.obj Y₀ ⟶ Y) (ν : Zu ⟶ Y₀)
    {ζ : Z₁ ⟶ Zu} {τ : Z ⟶ Y₀} {b : yoneda.obj Z ⟶ pullback g₀ f}
    (hbE : IsEtale B S hS b) (hτ : yoneda.map τ = b ≫ pullback.fst g₀ f)
    (θ : (BigFppfOver.toScheme B S hS).obj Z₁ ⟶
      pullback ((BigFppfOver.toScheme B S hS).map τ) ((BigFppfOver.toScheme B S hS).map ν))
    (hθoi : _root_.AlgebraicGeometry.IsOpenImmersion θ)
    (hθfac : θ ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
      ((BigFppfOver.toScheme B S hS).map ν) = (BigFppfOver.toScheme B S hS).map ζ)
    (u₀ : points B S hS (yoneda.obj Y₀)) (u' : (BigFppfOver.toScheme B S hS).obj Zu)
    (hνpt : (BigFppfOver.toScheme B S hS).map ν u' = pointsToScheme B S hS Y₀ u₀)
    {m p n : ℕ} (zz : Fin m → (BigFppfOver.toScheme B S hS).obj Z)
    (w : Fin p → points B S hS (pullback g₀ f)) (x : Fin n → points B S hS X)
    (hθpts : ∀ t : (BigFppfOver.toScheme B S hS).obj Z₁,
      (BigFppfOver.toScheme B S hS).map ζ t = u' →
        ∃ j, (θ ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν)) t = zz j)
    (hθrange : ∀ ω : ↥(pullback ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν)),
      pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν) ω = u' →
        (∃ j, pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν) ω = zz j) → ω ∈ Set.range θ)
    (hzrange : ∀ a : (BigFppfOver.toScheme B S hS).obj Z, a ∈ Set.range zz ↔
      pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a) ∈ Set.range w)
    (hhit : ∀ j, ∃ a : (BigFppfOver.toScheme B S hS).obj Z,
      pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a) = w j)
    (hwx : ∀ j, ∃ i, pointsMap B S hS (pullback g₀ f) (pullback.snd g₀ f) (w j) = x i)
    (hwall : ∀ q : points B S hS (pullback g₀ f),
      pointsMap B S hS (pullback g₀ f) (pullback.fst g₀ f) q = u₀ →
        (∃ i, pointsMap B S hS (pullback g₀ f) (pullback.snd g₀ f) q = x i) →
          q ∈ Set.range w) :
    ∃ z : yoneda.obj Z₁ ⟶ pullback (yoneda.map ν ≫ g₀) f,
      IsEtale B S hS z ∧
      z ≫ pullback.fst (yoneda.map ν ≫ g₀) f = yoneda.map ζ ∧
      (∀ t : points B S hS (yoneda.obj Z₁),
        pointsMap B S hS (yoneda.obj Z₁) (z ≫ pullback.fst (yoneda.map ν ≫ g₀) f) t =
            (pointsEquivScheme B S hS Zu).symm u' →
          ∃ i, pointsMap B S hS (yoneda.obj Z₁)
            (z ≫ pullback.snd (yoneda.map ν ≫ g₀) f) t = x i) ∧
      (∀ q : points B S hS (pullback (yoneda.map ν ≫ g₀) f),
        q ∉ Set.range (pointsMap B S hS (yoneda.obj Z₁) z) →
          pointsMap B S hS (pullback (yoneda.map ν ≫ g₀) f)
              (pullback.fst (yoneda.map ν ≫ g₀) f) q =
              (pointsEquivScheme B S hS Zu).symm u' →
            ∀ i, pointsMap B S hS (pullback (yoneda.map ν ≫ g₀) f)
              (pullback.snd (yoneda.map ν ≫ g₀) f) q ≠ x i) := by
  obtain ⟨η, hηE, hηsnd, hηθ⟩ :=
    exists_etale_site_hom_of_openImmersion B S hS ν τ ζ θ hθoi hθfac
  obtain ⟨c, hcsq, hcfst, hzE⟩ :=
    exists_etale_comparison_of_etale_site_hom B S hS (pullback.fst g₀ f) ν hbE hτ η hηE
  have hνu : pointsMap B S hS (yoneda.obj Zu) (yoneda.map ν)
      ((pointsEquivScheme B S hS Zu).symm u') = u₀ :=
    pointsMap_yoneda_map_symm_eq_of_map_eq B S hS ν u' u₀ hνpt
  -- the underlying morphism of schemes of the composite `ξ = η ≫ pullback.fst τ ν`
  have hmapξ : (BigFppfOver.toScheme B S hS).map (η ≫ pullback.fst τ ν) =
      θ ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
        ((BigFppfOver.toScheme B S hS).map ν) := by
    rw [Functor.map_comp, ← hηθ, Category.assoc, PreservesPullback.iso_hom_fst]
  have hzfst : ((yoneda.map η ≫ c) ≫
      (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).hom) ≫
        pullback.fst (yoneda.map ν ≫ g₀) f = yoneda.map ζ := by
    rw [Category.assoc, Category.assoc, pullbackRightPullbackFstIso_hom_fst, hcfst,
      ← Functor.map_comp, hηsnd]
  refine ⟨(yoneda.map η ≫ c) ≫ (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).hom,
    isEtale_comp B S hS hzE (isEtale_of_isIso B S hS _), hzfst, ?_, ?_⟩
  · have hzsnd : ((yoneda.map η ≫ c) ≫
        (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).hom) ≫
          pullback.snd (yoneda.map ν ≫ g₀) f =
          yoneda.map (η ≫ pullback.fst τ ν) ≫ b ≫ pullback.snd g₀ f := by
      rw [Category.assoc, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
        ← Category.assoc c, ← hcsq.w, Functor.map_comp]
      simp only [Category.assoc]
    rw [hzfst, hzsnd]
    refine forall_exists_pointsMap_eq_of_fibre_schemePoints B S hS ζ (η ≫ pullback.fst τ ν)
      (b ≫ pullback.snd g₀ f) u' zz x (fun t ht => ?_) (fun j => ?_)
    · rw [hmapξ]; exact hθpts t ht
    · obtain ⟨j', hj'⟩ := (hzrange (zz j)).1 (Set.mem_range_self j)
      obtain ⟨i, hi⟩ := hwx j'
      exact ⟨i, by rw [pointsMap_comp_apply, ← hj']; exact hi⟩
  · intro q hq hq1 i hq2
    refine hq ?_
    rw [mem_range_pointsMap_comp_iso_iff]
    have hinvfst : (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).inv ≫
        pullback.fst (yoneda.map ν) (pullback.fst g₀ f) =
        pullback.fst (yoneda.map ν ≫ g₀) f := by
      rw [← pullbackRightPullbackFstIso_hom_fst g₀ f (yoneda.map ν), Iso.inv_hom_id_assoc]
    have hinvsnd : (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).inv ≫
        pullback.snd (yoneda.map ν) (pullback.fst g₀ f) ≫ pullback.snd g₀ f =
        pullback.snd (yoneda.map ν ≫ g₀) f := by
      rw [← pullbackRightPullbackFstIso_hom_snd g₀ f (yoneda.map ν), Iso.inv_hom_id_assoc]
    have hfstmid : pointsMap B S hS (pullback (yoneda.map ν) (pullback.fst g₀ f))
        (pullback.fst (yoneda.map ν) (pullback.fst g₀ f))
        (pointsMap B S hS (pullback (yoneda.map ν ≫ g₀) f)
          (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).inv q) =
        (pointsEquivScheme B S hS Zu).symm u' := by
      rw [← pointsMap_comp_apply, hinvfst]; exact hq1
    have hk1 : pointsMap B S hS (pullback g₀ f) (pullback.fst g₀ f)
        (pointsMap B S hS (pullback (yoneda.map ν) (pullback.fst g₀ f))
          (pullback.snd (yoneda.map ν) (pullback.fst g₀ f))
          (pointsMap B S hS (pullback (yoneda.map ν ≫ g₀) f)
            (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).inv q)) = u₀ := by
      rw [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply, hfstmid, hνu]
    have hk2 : pointsMap B S hS (pullback g₀ f) (pullback.snd g₀ f)
        (pointsMap B S hS (pullback (yoneda.map ν) (pullback.fst g₀ f))
          (pullback.snd (yoneda.map ν) (pullback.fst g₀ f))
          (pointsMap B S hS (pullback (yoneda.map ν ≫ g₀) f)
            (pullbackRightPullbackFstIso g₀ f (yoneda.map ν)).inv q)) = x i := by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hinvsnd]; exact hq2
    obtain ⟨j, hj⟩ := hwall _ hk1 ⟨i, hk2⟩
    obtain ⟨a, ha⟩ := hhit j
    refine mem_range_pointsMap_of_schemePoint_range B S hS b
      (pullback.snd (yoneda.map ν) (pullback.fst g₀ f)) c (pullback.fst τ ν) η hcsq _ a
      (ha.trans hj) (fun ω hωa hωc => ?_)
    -- `ω` is a point of the site fibre product; transport it to the scheme fibre product
    have hωsnd : (BigFppfOver.toScheme B S hS).map (pullback.snd τ ν) ω = u' := by
      have h1 : pointsMap B S hS (yoneda.obj (pullback τ ν)) (yoneda.map (pullback.snd τ ν))
          ((pointsEquivScheme B S hS (pullback τ ν)).symm ω) =
          (pointsEquivScheme B S hS Zu).symm u' := by
        rw [← hcfst, pointsMap_comp_apply, hωc, hfstmid]
      have h2 := pointsEquivScheme_pointsMap_yoneda B S hS (pullback.snd τ ν)
        ((pointsEquivScheme B S hS (pullback τ ν)).symm ω)
      rw [h1, (pointsEquivScheme B S hS Zu).apply_symm_apply,
        (pointsEquivScheme B S hS (pullback τ ν)).apply_symm_apply] at h2
      exact h2.symm
    have hmem : (PreservesPullback.iso (BigFppfOver.toScheme B S hS) τ ν).hom ω ∈
        Set.range θ := by
      refine hθrange _ ?_ ?_
      · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_hom_snd]; exact hωsnd
      · refine ⟨?_, ?_⟩
        · exact ((hzrange a).2 ⟨j, ha.symm⟩).choose
        · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_hom_fst, hωa]
          exact ((hzrange a).2 ⟨j, ha.symm⟩).choose_spec.symm
    obtain ⟨t, ht⟩ := hmem
    have hmapη : (BigFppfOver.toScheme B S hS).map η =
        θ ≫ (PreservesPullback.iso (BigFppfOver.toScheme B S hS) τ ν).inv := by
      rw [← hηθ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    refine ⟨t, ?_⟩
    rw [hmapη, Scheme.Hom.comp_apply, ht, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

/-- **Stacks Project, Tag 082H.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`,
let `y` be a point of `|Y|` and let `x₁, …, x_n` be points of `|X|` mapping to `y`. Assume that
`f` is locally of finite type, that `f` is separated, that `f` is quasi-finite at each `xᵢ`, and
that `f` is quasi-compact or `Y` is decent. Then there are an object `U` of the big fppf category
over `S`, an **étale** morphism `g : h_U ⟶ Y` and a point `u` of `|h_U|` over `y`, together with a
decomposition of `U ×_Y X` into two open-and-closed subspaces `W` and `V` — their join sheafifies
to everything and their meet is the sheafification of nothing — such that

* `V ⟶ U` is **finite**;
* every point of the fibre of `|V| ⟶ |U|` over `u` maps to one of the `xᵢ`;
* no point of the fibre of `|W| ⟶ |U|` over `u` maps to any `xᵢ`.

This is the composite of the three paragraphs of the source proof with its finiteness clause; see
the module documentation for which file carries which. The hypotheses are those of the tag and
nothing else, apart from the ambient `HasSheafify` assumption on the site discussed there. -/
@[stacks 082H]
theorem exists_etale_decomposition_isFinite_of_isQuasiFiniteAt
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (y : points B S hS Y) {n : ℕ} (x : Fin n → points B S hS X)
    (hx : ∀ i, pointsMap B S hS X f (x i) = y)
    (hft : IsLocallyOfFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    (hqf : ∀ i, IsQuasiFiniteAt B S hS f (x i))
    (hqc : IsQuasiCompact B S hS f ∨ IsDecentSpace B S hS Y) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y)
      (u : points B S hS (yoneda.obj U)) (W V : Subfunctor (pullback g f)),
      IsEtale B S hS g ∧
      pointsMap B S hS (yoneda.obj U) g u = y ∧
      IsOpenSubspace B S hS W ∧ IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧ IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor (pullback g f)).sheafify (BigFppfOver.topology B S hS) ∧
      IsFinite B S hS (V.ι ≫ pullback.fst g f) ∧
      (∀ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst g f) v = u →
          ∃ i, pointsMap B S hS V.toFunctor (V.ι ≫ pullback.snd g f) v = x i) ∧
      (∀ t : points B S hS W.toFunctor,
        pointsMap B S hS W.toFunctor (W.ι ≫ pullback.fst g f) t = u →
          ∀ i, pointsMap B S hS W.toFunctor (W.ι ≫ pullback.snd g f) t ≠ x i) := by
  obtain ⟨Y₀, g₀, u₀, p, w, hY₀, hg₀E, hg₀u, hwu, hwqf, hwx, hwall⟩ :=
    exists_etale_neighbourhood_fibrePoints_eq B S hS hX hY f y x hx hft hqf hqc
  have hP₀ : IsAlgebraicSpace B S hS (pullback g₀ f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g₀ f
      (isAlgebraicSpace_yoneda B S hS Y₀) hX hY
  have hsep₀ : IsSeparated B S hS (pullback.fst g₀ f) :=
    isSeparated_pullbackFst B S hS g₀ hsep
  have hft₀ : IsLocallyOfFiniteType B S hS (pullback.fst g₀ f) :=
    isLocallyOfFiniteType_pullback_fst B S hS hX hY hft Y₀ g₀
  obtain ⟨Zu, Z₁, Z, ν, ζ, τ, b, θ, u', m, zz, hZuaff, hZaff, hνet, hbE, hτ, hζfin, hθoi,
    hθfac, hνpt, hθpts, hθrange, hzrange, hhit⟩ :=
    exists_siteObject_isFinite_part_of_isQuasiFiniteAt B S hS hP₀ hY₀ (pullback.fst g₀ f)
      hsep₀ hft₀ u₀ w hwu hwqf
  obtain ⟨z, hzE, hzfst, hVpts, hWpts⟩ :=
    exists_etale_hom_fibre_conditions_of_openImmersion B S hS f g₀ ν hbE hτ θ hθoi hθfac u₀ u'
      hνpt zz w x hθpts hθrange hzrange hhit hwx hwall
  have hνE : IsEtale B S hS (yoneda.map ν) :=
    isEtale_of_presheaf_etale B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@_root_.AlgebraicGeometry.Etale) ν).2 hνet)
  have hgE : IsEtale B S hS (yoneda.map ν ≫ g₀) := isEtale_comp B S hS hνE hg₀E
  have hgu : pointsMap B S hS (yoneda.obj Zu) (yoneda.map ν ≫ g₀)
      ((pointsEquivScheme B S hS Zu).symm u') = y := by
    rw [pointsMap_comp_apply,
      pointsMap_yoneda_map_symm_eq_of_map_eq B S hS ν u' u₀ hνpt]
    exact hg₀u
  have hP : IsAlgebraicSpace B S hS (pullback (yoneda.map ν ≫ g₀) f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (yoneda.map ν ≫ g₀) f
      (isAlgebraicSpace_yoneda B S hS Zu) hX hY
  obtain ⟨W, V, hWo, hWc, hVo, hVc, hsup, hinf, hVfin, hVpt, hWpt⟩ :=
    exists_clopen_part_isFinite_of_isEtale_of_isFinite B S hS hP hZuaff
      (pullback.fst (yoneda.map ν ≫ g₀) f) (pullback.snd (yoneda.map ν ≫ g₀) f)
      (isSeparated_pullbackFst B S hS (yoneda.map ν ≫ g₀) hsep)
      (isLocallyOfFiniteType_pullback_fst B S hS hX hY hft Zu (yoneda.map ν ≫ g₀))
      ((pointsEquivScheme B S hS Zu).symm u') x z hzE ζ hzfst hζfin hVpts hWpts
  exact ⟨Zu, yoneda.map ν ≫ g₀, (pointsEquivScheme B S hS Zu).symm u', W, V, hgE, hgu,
    hWo, hWc, hVo, hVc, hsup, hinf, hVfin, hVpt, hWpt⟩

end AlgebraicGeometry.Space

end
