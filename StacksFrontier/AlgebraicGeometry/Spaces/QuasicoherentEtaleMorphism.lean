module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice

/-!
# Quasi-coherence is tested along an étale morphism of algebraic spaces

Let `f : Y ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  This file compares an `𝒪_X`-module with its étale pullback to `Y`, and proves
the equivalence of conditions (1) and (2) of Stacks 03M0: a module is quasi-coherent exactly
when its pullback along an étale morphism surjective on points is.

## Main definitions

* `AlgebraicGeometry.Space.ringedSitePostcomp` is postcomposition of étale charts, restated
  between the underlying categories of the small étale *ringed* sites.

## Main results

* `AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff`: the restriction of the
  étale pullback to a chart `V` of `Y` has a global presentation exactly when the restriction
  of the module itself to the composite chart of `X` does.
* `AlgebraicGeometry.Space.exists_surjective_smallEtale_chart`: every algebraic space has an
  étale chart whose structure morphism is surjective on points, and
  `AlgebraicGeometry.Space.isSurjective_smallEtalePostcomp_obj_hom`: composing such a chart
  with a morphism surjective on points leaves it surjective on points.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_iff`: **Stacks 03M0,
  conditions (1) and (2)**, for a given étale morphism surjective on points.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_exists_etale_surjective`: **Stacks 03M0,
  conditions (1) and (2)** in the existential form in which the source states condition (2).

## Implementation notes

The étale pullback `AlgebraicGeometry.Space.etaleModulePullback` is restriction along
postcomposition, with no change of scalars, so restricting it further to a chart `V` of `Y` is
restriction along `CategoryTheory.Over.forget V ⋙ smallEtalePostcomp`, which
`CategoryTheory.Over.post_forget_eq_forget_comp` identifies with restriction along
`CategoryTheory.Over.post smallEtalePostcomp` of the restriction of the module to the composite
chart.  Both restrictions of the structure sheaves agree on the nose, so the two modules being
compared have the same sections over every object; the comparison isomorphism `key` is built
objectwise from `CategoryTheory.Iso.refl` through
`SheafOfModules.fullyFaithfulForget`.  Comparing the two *functors* of sections instead —
asking for the equality that does hold — exhausts the elaborator, which is why the objectwise
isomorphism is used.

Having a global presentation is transported across the slice comparison
`AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence`, an equivalence of sites by the
two continuity instances of that file, with
`SheafOfModules.pushforwardPushforwardEquivalence` supplying the adjointness that
`Stacks.SheafOfModules.hasGlobalPresentation_map` consumes.  Its two compatibilities `H₁` and
`H₂` hold by `rfl`: the unit and the counit of the slice comparison are the identity on the
underlying objects of `Sch_κ`, which is all that the structure sheaf of global regular
functions sees.

The forward implication of Stacks 03M0 (1) implies (2) needs no surjectivity: a covering of
the composite chart of `X` lifts to a covering of the chart of `Y` by
`AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`, and the members of the
lifted covering inherit global presentations because each of them maps, after
postcomposition, into a member of the original covering.  The converse is where surjectivity
enters, through `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective` applied to the
composite of a surjective étale chart of `Y` with `f`: every chart of `X` is then covered by
charts that map to that one, and the slice equivalence identifies each of those
with the postcomposition of a chart of `Y`.  Quasi-coherence is assembled from the resulting
family by `Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`,
whose covering condition is a family of *objects* and is therefore insensitive to the
transport along that isomorphism.

Everything is phrased with the projections `(smallEtaleRingedSite ..).C` and
`(smallEtaleRingedSite ..).J` of the ringed site rather than with
`AlgebraicGeometry.Space.SmallEtale` and its topology, and `ringedSitePostcomp` exists for the
same reason: instance search does not unfold those projections, and a statement mixing the two
spellings leaves a `Category (Over V)` goal that it cannot discharge.  This is the same
restatement that `AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` performs
for sheafification.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Postcomposition of étale charts with an étale morphism `f : Y ⟶ X` of algebraic spaces,
restated between the underlying categories of the small étale ringed sites.

The content is `AlgebraicGeometry.Space.smallEtalePostcomp`; this restates it for the
projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not
unfold. -/
abbrev ringedSitePostcomp (f : Y ⟶ X) (hf : IsEtale B S hS f.hom) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).C ⥤ (smallEtaleRingedSite B S hS X.1 X.2).C :=
  smallEtalePostcomp B S hS f hf

/-- **The ringed form of Stacks 04M0, for modules.** The restriction of the étale pullback of
an `𝒪_X`-module along an étale `f : Y ⟶ X` to an étale chart `V` of `Y` has a global
presentation if and only if the restriction of the module itself to the composite chart of `X`
does.

Both restrictions have, over an étale chart of `Y` over `V`, the sections of the module over
the corresponding chart of `X`; the comparison is the transport of a global presentation
across the slice equivalence
`AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence`. -/
theorem hasGlobalPresentation_over_postcomp_iff (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) :
    (((etaleModulePullback B S hS f hf).obj M).over V).HasGlobalPresentation ↔
      (M.over ((ringedSitePostcomp B S hS f hf).obj V)).HasGlobalPresentation := by
  let E : Over V ≌ Over ((ringedSitePostcomp B S hS f hf).obj V) :=
    SmallEtale.postcompOverEquivalence B S hS f hf V
  have hc1 : E.functor.IsContinuous ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((ringedSitePostcomp B S hS f hf).obj V)) :=
    SmallEtale.isContinuous_overPostcomp B S hS f hf V
  have hc2 : E.inverse.IsContinuous
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((ringedSitePostcomp B S hS f hf).obj V))
      ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V) :=
    SmallEtale.isContinuous_postcompOverInverse B S hS f hf V
  let RY := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
  let RX := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let φ : RY.over V ⟶ (E.functor.sheafPushforwardContinuous RingCat.{u}
      ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over
        ((ringedSitePostcomp B S hS f hf).obj V))).obj
      (RX.over ((ringedSitePostcomp B S hS f hf).obj V)) := 𝟙 _
  let ψ : RX.over ((ringedSitePostcomp B S hS f hf).obj V) ⟶
      (E.inverse.sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleRingedSite B S hS X.1 X.2).J.over
          ((ringedSitePostcomp B S hS f hf).obj V))
        ((smallEtaleRingedSite B S hS Y.1 Y.2).J.over V)).obj (RY.over V) := 𝟙 _
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit)
      (RX.over ((ringedSitePostcomp B S hS f hf).obj V)).obj =
      ψ.hom ≫ E.inverse.op.whiskerLeft φ.hom := by
    ext : 2
    exact rfl
  have H₂ : φ.hom ≫ E.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) (RY.over V).obj = 𝟙 (RY.over V).obj := by
    ext : 2
    exact rfl
  let e₀ := SheafOfModules.pushforwardPushforwardEquivalence.{u} E φ ψ H₁ H₂
  let eHi := SheafOfModules.pushforwardPushforwardEquivalence.{u + 1} E φ ψ H₁ H₂
  let F₀ := SheafOfModules.pushforward.{u} φ
  let F := SheafOfModules.pushforward.{u + 1} φ
  let G₀ := SheafOfModules.pushforward.{u} ψ
  let G := SheafOfModules.pushforward.{u + 1} ψ
  have hFadj : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  have hGadj : G.IsLeftAdjoint := eHi.symm.isLeftAdjoint_functor
  have hFzero : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hGzero : G.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have key : F₀.obj (M.over ((ringedSitePostcomp B S hS f hf).obj V)) ≅
      ((etaleModulePullback B S hS f hf).obj M).over V :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact SheafOfModules.HasGlobalPresentation.of_iso
      (e₀.unitIso.app (M.over ((ringedSitePostcomp B S hS f hf).obj V))).symm
      (Stacks.SheafOfModules.hasGlobalPresentation_map (F₀ := G₀) (F := G) _
        (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} ψ
          (SheafOfModules.unit (RY.over V)))
        (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} ψ
          (F₀.obj (M.over ((ringedSitePostcomp B S hS f hf).obj V))))
        (SheafOfModules.HasGlobalPresentation.of_iso key.symm h))
  · exact SheafOfModules.HasGlobalPresentation.of_iso key
      (Stacks.SheafOfModules.hasGlobalPresentation_map (F₀ := F₀) (F := F) _
        (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} φ
          (SheafOfModules.unit (RX.over ((ringedSitePostcomp B S hS f hf).obj V))))
        (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} φ
          (M.over ((ringedSitePostcomp B S hS f hf).obj V))) h)

/-- An étale chart of `Y` whose structure morphism is surjective on points, composed with a
morphism `f : Y ⟶ X` of algebraic spaces surjective on points, is an étale chart of `X` whose
structure morphism is surjective on points. -/
theorem isSurjective_smallEtalePostcomp_obj_hom (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (V : SmallEtale B S hS Y.1)
    (hV : IsSurjective B S hS V.1.hom) :
    IsSurjective B S hS ((smallEtalePostcomp B S hS f hf).obj V).1.hom := by
  have h := hsurj.comp hV
  rwa [← pointsMap_comp] at h

/-- Every algebraic space has an étale chart whose structure morphism is surjective on points:
its atlas, read as an object of the small étale site. -/
theorem exists_surjective_smallEtale_chart (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    ∃ V : SmallEtale B S hS F, IsSurjective B S hS V.1.hom := by
  obtain ⟨U, a, haS, haE⟩ := hF.exists_atlas
  exact ⟨⟨CostructuredArrow.mk a, haE⟩,
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).1 haS⟩

/-- A sheaf of `𝒪_X`-modules is quasi-coherent if its pullback along an étale morphism of
algebraic spaces surjective on points is. -/
private theorem isQuasicoherentOnSite_of_etaleModulePullback (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hN : ((etaleModulePullback B S hS f hf).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  obtain ⟨V₀, hV₀⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  have hcovU₀ : (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop
      (fun _ : PUnit.{u + 2} => (ringedSitePostcomp B S hS f hf).obj V₀) :=
    SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2
      ((smallEtalePostcomp B S hS f hf).obj V₀)
      (isSurjective_smallEtalePostcomp_obj_hom B S hS f hf hsurj V₀ hV₀)
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
    M).2 ⟨{Z : (smallEtaleRingedSite B S hS X.1 X.2).C // (M.over Z).HasGlobalPresentation},
      fun z => z.1, fun W => ?_, fun z => z.2⟩
  refine (smallEtaleRingedSite B S hS X.1 X.2).J.transitive (hcovU₀ W) _
    fun W' g hg => ?_
  obtain ⟨-, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ g).mp hg
  obtain ⟨I₁, W₁, g₁, hcov₁, hpres₁⟩ :=
    hN.locally_hasGlobalPresentation
      ((SmallEtale.postcompOverInverse B S hS f hf V₀).obj (Over.mk a)).left
  have hpush := (SmallEtale.coverPreserving_smallEtalePostcomp B S hS f hf).cover_preserve hcov₁
  have hle : Sieve.functorPushforward (ringedSitePostcomp B S hS f hf)
      (Sieve.ofArrows W₁ g₁) ≤
      Sieve.ofObjects (fun z : {Z : (smallEtaleRingedSite B S hS X.1 X.2).C //
        (M.over Z).HasGlobalPresentation} => z.1)
        ((ringedSitePostcomp B S hS f hf).obj
          ((SmallEtale.postcompOverInverse B S hS f hf V₀).obj (Over.mk a)).left) := by
    rintro T p ⟨Z₀, p₀, q, hp₀, rfl⟩
    obtain ⟨i, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hp₀
    exact ⟨⟨_, (hasGlobalPresentation_over_postcomp_iff B S hS f hf M (W₁ i)).1 (hpres₁ i)⟩,
      ⟨q ≫ (ringedSitePostcomp B S hS f hf).map b⟩⟩
  have hα := (smallEtaleRingedSite B S hS X.1 X.2).J.pullback_stable
    ((Over.forget ((smallEtalePostcomp B S hS f hf).obj V₀)).mapIso
      ((SmallEtale.postcompOverCounitIso B S hS f hf V₀).app (Over.mk a))).inv
    ((smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering hle hpush)
  exact (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering (fun _ _ hb => hb) hα

/-- **Stacks 03M0, conditions (1) and (2).** A sheaf of `𝒪_X`-modules on the small étale site
of an algebraic space `X` is quasi-coherent if and only if its pullback along an étale
morphism `f : Y ⟶ X` of algebraic spaces which is surjective on points is quasi-coherent.

The forward implication needs no surjectivity: quasi-coherence of a module is inherited by
every étale pullback, because a covering of the composite chart of `X` lifts to a covering of
the chart of `Y` (`AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`) and
global presentations transfer by
`AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff`.  The converse is where
surjectivity enters: an étale chart of `Y` surjective on points composes with `f` to an étale
chart of `X` surjective on points, which covers the final object of the small étale site of
`X` by `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, so every chart of `X`
is covered by charts that map to it; those are, up to isomorphism, the composites
of the charts of `Y`, which carry global presentations by hypothesis. -/
@[stacks 03M0 "(1) iff (2)"]
theorem isQuasicoherentOnSite_etaleModulePullback_iff (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    M.IsQuasicoherentOnSite ↔
      ((etaleModulePullback B S hS f hf).obj M).IsQuasicoherentOnSite := by
  refine ⟨fun hM => ?_, isQuasicoherentOnSite_of_etaleModulePullback B S hS f hf hsurj M⟩
  refine ⟨fun V => ?_⟩
  obtain ⟨I, Z, h, hcov, hpres⟩ :=
    hM.locally_hasGlobalPresentation ((ringedSitePostcomp B S hS f hf).obj V)
  let Ar := {A : Over V //
    ((Sieve.ofArrows Z h).functorPullback (ringedSitePostcomp B S hS f hf)).arrows A.hom}
  have hEq : Sieve.ofArrows (fun A : Ar => A.1.left) (fun A : Ar => A.1.hom) =
      (Sieve.ofArrows Z h).functorPullback (ringedSitePostcomp B S hS f hf) := by
    refine le_antisymm ?_ ?_
    · intro T g hg
      obtain ⟨A, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
      exact ((Sieve.ofArrows Z h).functorPullback
        (ringedSitePostcomp B S hS f hf)).downward_closed A.2 b
    · intro T g hg
      exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Over.mk g, hg⟩, 𝟙 T, by simp⟩
  refine ⟨Ar, fun A => A.1.left, fun A => A.1.hom, ?_, fun A => ?_⟩
  · rw [hEq]
    exact SmallEtale.smallEtalePostcomp_cover_lift B S hS f hf V _ hcov
  · obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp A.2
    rw [hasGlobalPresentation_over_postcomp_iff B S hS f hf M A.1.left]
    exact Stacks.SheafOfModules.hasGlobalPresentation_overMap M b (hpres j)

/-- **Stacks 03M0, conditions (1) and (2), in the existential form of the source.** A sheaf of
`𝒪_X`-modules on the small étale site of an algebraic space `X` is quasi-coherent if and only
if there is an étale morphism `f : Z ⟶ X` of algebraic spaces, surjective on points, whose
pullback of the module is quasi-coherent.

The witness for the forward implication is the identity of `X`, which is étale because
precomposing an étale chart with it returns the chart, and surjective on points because
`AlgebraicGeometry.Space.pointsMap_id` is the identity.  No comparison of
`AlgebraicGeometry.Space.smallEtalePostcomp` with the identity functor is needed: the pullback
along the identity is quasi-coherent because
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_iff` applies to every étale
morphism, the identity included. -/
@[stacks 03M0 "(1) iff (2), existential form"]
theorem isQuasicoherentOnSite_iff_exists_etale_surjective
    (M : Modules.{u, u} B S hS X.1 X.2) :
    M.IsQuasicoherentOnSite ↔
      ∃ (Z : AlgebraicSpaces B S hS) (f : Z ⟶ X) (hf : IsEtale B S hS f.hom),
        IsSurjective B S hS f.hom ∧
          ((etaleModulePullback B S hS f hf).obj M).IsQuasicoherentOnSite := by
  have hidE : IsEtale B S hS (𝟙 X.1) := fun _ _ hφ => by simpa using hφ
  have hidS : IsSurjective B S hS (𝟙 X.1) := by
    rw [IsSurjective, pointsMap_id]
    exact Function.surjective_id
  exact ⟨fun hM => ⟨X, 𝟙 X, hidE, hidS,
      (isQuasicoherentOnSite_etaleModulePullback_iff B S hS (𝟙 X) hidE hidS M).1 hM⟩,
    fun ⟨_, f, hf, hsurj, hQ⟩ =>
      isQuasicoherentOnSite_of_etaleModulePullback B S hS f hf hsurj M hQ⟩

end AlgebraicGeometry.Space

end
