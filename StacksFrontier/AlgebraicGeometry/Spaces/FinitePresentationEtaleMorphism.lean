module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteFromCover

/-!
# Finite presentation is tested along an étale morphism of algebraic spaces

Let `f : Y ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism` proves the
equivalence of conditions (1) and (2) of Stacks 03M0 for quasi-coherence: a module is
quasi-coherent exactly when its pullback along an étale morphism surjective on points is.  This
file proves the same for *finite presentation*, Stacks 03DL(7).

Every proof is the proof of its quasi-coherent counterpart with the two transport lemmas replaced
by their finite analogues —
`Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_of_functor` for
`Stacks.SheafOfModules.hasGlobalPresentation_map` and
`Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap` for
`Stacks.SheafOfModules.hasGlobalPresentation_overMap` — and with the assembly from a covering
family performed by
`SheafOfModules.isFinitePresentationOnSite_of_coversTop_hasFiniteGlobalPresentation` instead of by
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`, which forgets
the two integers whose finiteness is the point.

## Main results

* `AlgebraicGeometry.Space.hasFiniteGlobalPresentation_over_postcomp_iff`: the restriction of the
  étale pullback to a chart `V` of `Y` has a finite global presentation exactly when the
  restriction of the module itself to the composite chart of `X` does.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_etaleModulePullback_iff`: **Stacks 03M0,
  conditions (1) and (2), for finite presentation**, for a given étale morphism surjective on
  points.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_iff_exists_etale_surjective`: the same in
  the existential form in which the source states condition (2).

## Implementation notes

The slice comparison `key` and the two pushforward data `φ`, `ψ` are those of
`AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff`, and the two compatibilities
`H₁` and `H₂` hold by `rfl` for the reason recorded there: the unit and the counit of the slice
comparison `AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence` are the identity on the
underlying objects of the big fppf site, which is all that the structure sheaf of global regular
functions sees.

`SheafOfModules.HasFiniteGlobalPresentation.of_iso` and
`SheafOfModules.IsFinitePresentationOnSite.of_iso` live in
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian`, which is why a file about
algebraic spaces imports one about algebraic stacks; the two lemmas are statements about a sheaf
of modules on an arbitrary site and mention no stack.

No `@[stacks 03M0]` attribute is placed.  Tag 03M0 is the list of equivalent conditions for
*quasi-coherence*, and it is carried by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_iff`; what is proved here is
the corresponding statement for the finite-presentation clause of Stacks 03DL, which is the
content of Stacks 03DM and 03DN rather than of 03M0.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL), part (7)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.FinitePresentationTransport

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- A finite global presentation is carried by a pushforward-of-modules functor that preserves
colimits and zero morphisms along a map of structure sheaves. -/
private theorem hasFiniteGlobalPresentation_pushforward {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}} {G : D ⥤ C} [G.IsContinuous K J]
    (φ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (e : (SheafOfModules.pushforward.{u} φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit R')
    (hF : PreservesColimitsOfSize.{u + 1, u + 1} (SheafOfModules.pushforward.{u + 1} φ))
    (hF₀ : (SheafOfModules.pushforward.{u + 1} φ).PreservesZeroMorphisms)
    (M : SheafOfModules.{u} R) (h : M.HasFiniteGlobalPresentation) :
    ((SheafOfModules.pushforward.{u} φ).obj M).HasFiniteGlobalPresentation :=
  hasFiniteGlobalPresentation_of_functor.{u + 1, u, u} M _ hF hF₀
    (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} φ (SheafOfModules.unit R)
      ≪≫ SheafOfModules.uliftForPresentationMapIso e)
    (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} φ M) h

/-- **The finite form of the ringed Stacks 04M0 for modules.** The restriction of the étale
pullback of an `𝒪_X`-module along an étale `f : Y ⟶ X` to an étale chart `V` of `Y` has a finite
global presentation if and only if the restriction of the module itself to the composite chart of
`X` does.

Both restrictions have, over an étale chart of `Y` over `V`, the sections of the module over the
corresponding chart of `X`; the comparison is the transport of a finite global presentation
across the slice equivalence
`AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence`. -/
theorem hasFiniteGlobalPresentation_over_postcomp_iff (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) :
    (((etaleModulePullback B S hS f hf).obj M).over V).HasFiniteGlobalPresentation ↔
      (M.over ((ringedSitePostcomp B S hS f hf).obj V)).HasFiniteGlobalPresentation := by
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
  let RY := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O
  let RX := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
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
  have hFcol : PreservesColimitsOfSize.{u + 1, u + 1} F := inferInstance
  have hGcol : PreservesColimitsOfSize.{u + 1, u + 1} G := inferInstance
  have key : F₀.obj (M.over ((ringedSitePostcomp B S hS f hf).obj V)) ≅
      ((etaleModulePullback B S hS f hf).obj M).over V :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact SheafOfModules.HasFiniteGlobalPresentation.of_iso
      (e₀.unitIso.app (M.over ((ringedSitePostcomp B S hS f hf).obj V))).symm
      (hasFiniteGlobalPresentation_pushforward ψ (Iso.refl _) hGcol hGzero _
        (SheafOfModules.HasFiniteGlobalPresentation.of_iso key.symm h))
  · exact SheafOfModules.HasFiniteGlobalPresentation.of_iso key
      (hasFiniteGlobalPresentation_pushforward φ (Iso.refl _) hFcol hFzero _ h)

/-- **Stacks 03M0, conditions (1) and (2), for finite presentation.** A sheaf of `𝒪_X`-modules on
the small étale site of an algebraic space `X` is of finite presentation if and only if its
pullback along an étale morphism `f : Y ⟶ X` of algebraic spaces which is surjective on points
is.

The forward implication needs no surjectivity: a covering of the composite chart of `X` lifts to
a covering of the chart of `Y` by
`AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`, and finite global
presentations transfer by
`AlgebraicGeometry.Space.hasFiniteGlobalPresentation_over_postcomp_iff`.  The converse is where
surjectivity enters: an étale chart of `Y` surjective on points composes with `f` to an étale
chart of `X` surjective on points, which covers the final object of the small étale site of `X`,
so every chart of `X` is covered by charts that map to it; those are, up to isomorphism, the
composites of the charts of `Y`, which carry finite global presentations by hypothesis. -/
theorem isFinitePresentationOnSite_etaleModulePullback_iff (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    M.IsFinitePresentationOnSite ↔
      ((etaleModulePullback B S hS f hf).obj M).IsFinitePresentationOnSite := by
  constructor
  · intro hM
    refine ⟨fun V => ?_⟩
    obtain ⟨I, Z, h, hcov, hpres⟩ :=
      hM.locally_hasFiniteGlobalPresentation ((ringedSitePostcomp B S hS f hf).obj V)
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
      rw [hasFiniteGlobalPresentation_over_postcomp_iff B S hS f hf M A.1.left]
      exact hasFiniteGlobalPresentation_overMap M b (hpres j)
  · intro hN
    obtain ⟨V₀, hV₀⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
    have hcovU₀ : (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop
        (fun _ : PUnit.{u + 2} => (ringedSitePostcomp B S hS f hf).obj V₀) :=
      SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2
        ((smallEtalePostcomp B S hS f hf).obj V₀)
        (isSurjective_smallEtalePostcomp_obj_hom B S hS f hf hsurj V₀ hV₀)
    refine SheafOfModules.isFinitePresentationOnSite_of_coversTop_hasFiniteGlobalPresentation
      M (K := {Z : (smallEtaleRingedSite B S hS X.1 X.2).C //
        (M.over Z).HasFiniteGlobalPresentation}) (fun z => z.1) (fun W => ?_) (fun z => z.2)
    refine (smallEtaleRingedSite B S hS X.1 X.2).J.transitive (hcovU₀ W) _ ?_
    intro W' g hg
    obtain ⟨-, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ g).mp hg
    obtain ⟨I₁, W₁, g₁, hcov₁, hpres₁⟩ :=
      hN.locally_hasFiniteGlobalPresentation
        ((SmallEtale.postcompOverInverse B S hS f hf V₀).obj (Over.mk a)).left
    have hle : Sieve.functorPushforward (ringedSitePostcomp B S hS f hf)
        (Sieve.ofArrows W₁ g₁) ≤
        Sieve.ofObjects (fun z : {Z : (smallEtaleRingedSite B S hS X.1 X.2).C //
          (M.over Z).HasFiniteGlobalPresentation} => z.1)
          ((ringedSitePostcomp B S hS f hf).obj
            ((SmallEtale.postcompOverInverse B S hS f hf V₀).obj (Over.mk a)).left) := by
      rintro T p ⟨Z₀, p₀, q, hp₀, rfl⟩
      obtain ⟨i, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hp₀
      exact ⟨⟨_, (hasFiniteGlobalPresentation_over_postcomp_iff B S hS f hf M (W₁ i)).1
        (hpres₁ i)⟩, ⟨q ≫ (ringedSitePostcomp B S hS f hf).map b⟩⟩
    have hα := (smallEtaleRingedSite B S hS X.1 X.2).J.pullback_stable
      ((Over.forget ((smallEtalePostcomp B S hS f hf).obj V₀)).mapIso
        ((SmallEtale.postcompOverCounitIso B S hS f hf V₀).app (Over.mk a))).inv
      ((smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering hle
        ((SmallEtale.coverPreserving_smallEtalePostcomp B S hS f hf).cover_preserve hcov₁))
    refine (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering ?_ hα
    exact fun _ _ hb => hb

/-- **Stacks 03M0, conditions (1) and (2), for finite presentation, in the existential form of
the source.** A sheaf of `𝒪_X`-modules on the small étale site of an algebraic space `X` is of
finite presentation if and only if there is an étale morphism `f : Z ⟶ X` of algebraic spaces,
surjective on points, whose pullback of the module is of finite presentation.

The witness for the forward implication is the identity of `X`, which is étale because
precomposing an étale chart with it returns the chart, and surjective on points because
`AlgebraicGeometry.Space.pointsMap_id` is the identity. -/
theorem isFinitePresentationOnSite_iff_exists_etale_surjective
    (M : Modules.{u, u} B S hS X.1 X.2) :
    M.IsFinitePresentationOnSite ↔
      ∃ (Z : AlgebraicSpaces B S hS) (f : Z ⟶ X) (hf : IsEtale B S hS f.hom),
        IsSurjective B S hS f.hom ∧
          ((etaleModulePullback B S hS f hf).obj M).IsFinitePresentationOnSite := by
  have hidE : IsEtale B S hS (𝟙 X.1) := fun _ _ hφ => by simpa using hφ
  have hidS : IsSurjective B S hS (𝟙 X.1) := by
    rw [IsSurjective, pointsMap_id]
    exact Function.surjective_id
  exact ⟨fun hM => ⟨X, 𝟙 X, hidE, hidS,
      (isFinitePresentationOnSite_etaleModulePullback_iff B S hS (𝟙 X) hidE hidS M).1 hM⟩,
    fun ⟨Z, f, hf, hsurj, hQ⟩ =>
      (isFinitePresentationOnSite_etaleModulePullback_iff B S hS f hf hsurj M).2 hQ⟩

end AlgebraicGeometry.Space

end
