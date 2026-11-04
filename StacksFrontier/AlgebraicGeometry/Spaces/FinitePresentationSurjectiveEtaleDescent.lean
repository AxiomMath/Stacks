module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence

/-!
# Finite presentation descends along a surjective étale morphism of algebraic spaces

A module on the small étale site of an algebraic space `X` whose pullback along an étale morphism
`f : Y ⟶ X` surjective on points is of finite presentation (Stacks 03DL (7)) is itself of finite
presentation.

## Main results

* `SheafOfModules.isFinitePresentationOnSite_of_coversTop`: a module with a finite global
  presentation on each member of a family of objects covering the site is of finite presentation.
* `AlgebraicGeometry.Space.hasFiniteGlobalPresentation_over_postcomp_of`: a finite global
  presentation of the pullback along an étale morphism `f : Y ⟶ X` over an étale `V ⟶ Y` gives
  one of the module over the composite `V ⟶ X`.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_etaleModulePullback`,
  `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_modulePullback`: finite presentation
  descends along an étale morphism surjective on points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SheafOfModules

universe v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Finite presentation is detected on a family of objects covering the site**: a module with a
finite global presentation on each member of a family covering the final object is of finite
presentation on the site. -/
theorem isFinitePresentationOnSite_of_coversTop (M : SheafOfModules.{w} R) {I : Type*}
    (U : I → C) (hU : J.CoversTop U) (h : ∀ i, (M.over (U i)).HasFiniteGlobalPresentation) :
    M.IsFinitePresentationOnSite where
  locally_hasFiniteGlobalPresentation W := by
    refine ⟨{g : Over W // (Sieve.ofObjects U W).arrows g.hom}, fun g => g.1.left,
      fun g => g.1.hom, ?_, fun g => ?_⟩
    · have hEq : Sieve.ofArrows (fun g : {g : Over W // (Sieve.ofObjects U W).arrows g.hom} =>
          g.1.left) (fun g => g.1.hom) = Sieve.ofObjects U W := by
        refine le_antisymm ?_ ?_
        · intro T a ha
          obtain ⟨g, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp ha
          exact (Sieve.ofObjects U W).downward_closed g.2 b
        · intro T a ha
          exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Over.mk a, ha⟩, 𝟙 T, by simp⟩
      rw [hEq]
      exact hU W
    · obtain ⟨i, ⟨b⟩⟩ := g.2
      exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
        M b (h i)

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- If the pullback of `M` along an étale morphism `f : Y ⟶ X` has a finite global presentation
over an object `V` of the small étale site of `Y`, then `M` has a finite global presentation over
the image of `V` in the small étale site of `X`. -/
theorem hasFiniteGlobalPresentation_over_postcomp_of (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) :
    (((etaleModulePullback B S hS f hf).obj M).over V).HasFiniteGlobalPresentation →
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
  let G := SheafOfModules.pushforward.{u + 1} ψ
  have hGadj : G.IsLeftAdjoint := eHi.symm.isLeftAdjoint_functor
  have hGzero : G.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have key : F₀.obj (M.over ((ringedSitePostcomp B S hS f hf).obj V)) ≅
      ((etaleModulePullback B S hS f hf).obj M).over V :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))
  intro h
  have h₀ :
      (F₀.obj (M.over ((ringedSitePostcomp B S hS f hf).obj V))).HasFiniteGlobalPresentation :=
    SheafOfModules.HasFiniteGlobalPresentation.of_iso key.symm h
  have hGcol : PreservesColimitsOfSize.{u + 1, u + 1} G := inferInstance
  have h' :=
    Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_of_functor
      (F := G) _ _ hGcol hGzero
      (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} ψ
        (SheafOfModules.unit (RY.over V)))
      (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} ψ
        (F₀.obj (M.over ((ringedSitePostcomp B S hS f hf).obj V)))) h₀
  exact SheafOfModules.HasFiniteGlobalPresentation.of_iso
    (e₀.unitIso.app (M.over ((ringedSitePostcomp B S hS f hf).obj V))).symm h'

/-- **Finite presentation descends along an étale morphism surjective on points**: if the
pullback of `M` along `f` is of finite presentation, so is `M`. -/
theorem isFinitePresentationOnSite_of_etaleModulePullback (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hN : ((etaleModulePullback B S hS f hf).obj M).IsFinitePresentationOnSite) :
    M.IsFinitePresentationOnSite := by
  obtain ⟨V₀, hV₀⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  have hcovU₀ : (smallEtaleRingedSite B S hS X.1 X.2).J.CoversTop
      (fun _ : PUnit.{u + 2} => (ringedSitePostcomp B S hS f hf).obj V₀) :=
    SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2
      ((smallEtalePostcomp B S hS f hf).obj V₀)
      (isSurjective_smallEtalePostcomp_obj_hom B S hS f hf hsurj V₀ hV₀)
  refine SheafOfModules.isFinitePresentationOnSite_of_coversTop M
    (fun z : {Z : (smallEtaleRingedSite B S hS X.1 X.2).C //
      (M.over Z).HasFiniteGlobalPresentation} => z.1) (fun W => ?_) (fun z => z.2)
  refine (smallEtaleRingedSite B S hS X.1 X.2).J.transitive (hcovU₀ W) _ ?_
  intro W' g hg
  obtain ⟨-, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ g).mp hg
  obtain ⟨I₁, W₁, g₁, hcov₁, hpres₁⟩ :=
    hN.locally_hasFiniteGlobalPresentation
      ((SmallEtale.postcompOverInverse B S hS f hf V₀).obj (Over.mk a)).left
  have hpush := (SmallEtale.coverPreserving_smallEtalePostcomp B S hS f hf).cover_preserve hcov₁
  have hle : Sieve.functorPushforward (ringedSitePostcomp B S hS f hf)
      (Sieve.ofArrows W₁ g₁) ≤
      Sieve.ofObjects (fun z : {Z : (smallEtaleRingedSite B S hS X.1 X.2).C //
        (M.over Z).HasFiniteGlobalPresentation} => z.1)
        ((ringedSitePostcomp B S hS f hf).obj
          ((SmallEtale.postcompOverInverse B S hS f hf V₀).obj (Over.mk a)).left) := by
    rintro T p ⟨Z₀, p₀, q, hp₀, rfl⟩
    obtain ⟨i, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hp₀
    exact ⟨⟨_, hasFiniteGlobalPresentation_over_postcomp_of B S hS f hf M (W₁ i) (hpres₁ i)⟩,
      ⟨q ≫ (ringedSitePostcomp B S hS f hf).map b⟩⟩
  have hobj := (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering hle hpush
  have hα := (smallEtaleRingedSite B S hS X.1 X.2).J.pullback_stable
    ((Over.forget ((smallEtalePostcomp B S hS f hf).obj V₀)).mapIso
      ((SmallEtale.postcompOverCounitIso B S hS f hf V₀).app (Over.mk a))).inv hobj
  exact (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering (fun _ _ hb => hb) hα

/-- **Finite presentation descends along an étale morphism surjective on points**, for the inverse
image of modules of Stacks 03LU: if `f^*M` is of finite presentation, so is `M`. -/
theorem isFinitePresentationOnSite_of_modulePullback (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (hN : ((modulePullback B S hS f).obj M).IsFinitePresentationOnSite) :
    M.IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_of_etaleModulePullback B S hS f hf hsurj M
    (SheafOfModules.IsFinitePresentationOnSite.of_iso
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).app M) hN)

end AlgebraicGeometry.Space

end
