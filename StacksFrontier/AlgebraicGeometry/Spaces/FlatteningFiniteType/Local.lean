module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupStrictTransformSpaceEtaleUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupUniversalLift
import all StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceSquareGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasFlat

/-!
# Flatness of a strict transform, read on étale charts of the blowup

Two local tools for the proof of Stacks 087E by the induction principle of Stacks 08GP.

* Flatness and local finite presentation of a morphism of algebraic spaces may be checked after
  base change to the members of a two-element fppf covering of the target.
* For a blowup `b : A' ⟶ A` and an étale chart `v : V ⟶ A`, the strict transform of
  `X_V = X ×_A V` along the blowup `V' ⟶ V` of the inverse image of the centre is the base change
  of the strict transform of `X` along the induced morphism `V' ⟶ A'` (Stacks 0863, part (2)).

## Main results

* `AlgebraicGeometry.Space.isFlat_and_isLocallyOfFinitePresentation_of_boolCovering`.
* `AlgebraicGeometry.Space.exists_isPullback_strictTransformSpaceToBlowUp_of_isEtale`.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_FlatteningFiniteTypeLocal :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_FlatteningFiniteTypeLocal
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Flatness and local finite presentation are fppf local on the target**, for a covering
indexed by `Bool`: if every base change of `g : P ⟶ Y` along a member of a two-element fppf
covering of `Y` is flat and locally of finite presentation, so is `g`. -/
theorem isFlat_and_isLocallyOfFinitePresentation_of_boolCovering {Y P : AlgebraicSpaces B S hS}
    (g : P ⟶ Y) (Q : Bool → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (e : ∀ j, Q j ⟶ Y.1)
    (hcov : IsFppfCovering B S hS Q e)
    (h : ∀ j, ∃ (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS R)
      (a : R ⟶ P.1) (q : R ⟶ Q j), IsPullback a q g.hom (e j) ∧ IsFlat B S hS q ∧
        IsLocallyOfFinitePresentation B S hS q) :
    IsFlat B S hS g.hom ∧ IsLocallyOfFinitePresentation B S hS g.hom := by
  let Qa : Bool → AlgebraicSpaces B S hS := fun j => ⟨Q j, hcov.source_isAlgebraicSpace j⟩
  let ea : ∀ j, Qa j ⟶ Y := fun j => ObjectProperty.homMk (e j)
  have hR : Presieve.ofArrows Qa ea ∈ Topology.fppf.precoverage.{u, 0} B S hS Y :=
    ⟨Bool, Qa, ea, rfl, Y.2, fun j => (Qa j).property, hcov⟩
  have key : ∀ (P' : MorphismProperty (AlgebraicSpaces B S hS)),
      P'.IsLocalAtTarget (Topology.fppf.precoverage.{u, 0} B S hS) →
      (∀ {R Q' : AlgebraicSpaces B S hS} (q : R ⟶ Q'), IsFlat B S hS q.hom →
        IsLocallyOfFinitePresentation B S hS q.hom → P' q) → P' g := by
    intro P' hloc hP'
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P') hR ?_
    rintro Z g' _ ⟨j⟩
    obtain ⟨R, hR, a, q, hsq, hq, hq'⟩ := h j
    let Ra : AlgebraicSpaces B S hS := ⟨R, hR⟩
    have hsqa : IsPullback (ObjectProperty.homMk a : Ra ⟶ P) (ObjectProperty.homMk q : Ra ⟶ Qa j)
        g (ea j) :=
      IsPullback.of_map_of_faithful (F := ObjectProperty.ι (fun F :
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) hsq
    exact prop_pullback_snd_of_isPullback hsqa (hP' _ hq hq')
  exact ⟨key (fun _ _ f => IsFlat B S hS f.hom)
      (Stack.QuotientAtlas.flatIsLocalAtTargetFppf B S hS) (fun _ hq _ => hq),
    key (fun _ _ f => IsLocallyOfFinitePresentation B S hS f.hom)
      (isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS) (fun _ _ hq => hq)⟩

/-- **The strict transform of an étale chart is a base change of the strict transform**
(Stacks 0863, part (2)).  Let `b : A' ⟶ A` be the blowup of `A` in `Z`, let `f : X ⟶ A`, let
`v : V ⟶ A` be étale, let `X_V` with `u : X_V ⟶ X`, `w : X_V ⟶ V` be the base change of `f`
along `v`, let `v' : V' ⟶ V` be the blowup of `V` in `v⁻¹Z` and let `m : V' ⟶ A'` be the
morphism over `A` (it is unique, by the universal property of `b`).  Then `m` exhibits
`V' = V ×_A A'`, and the strict transform of `X_V` along `v'` is the base change along `m` of
the strict transform of `X` along `b`, compatibly with the projections to `V'` and to `A'`. -/
theorem exists_isPullback_strictTransformSpaceToBlowUp_of_isEtale
    {A A' V V' X XV : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS A.1} {b : A' ⟶ A}
    (hb : IsBlowupAlong B S hS Z b) (f : X ⟶ A) {v : V ⟶ A} (hv : IsEtale B S hS v.hom)
    {u : XV ⟶ X} {w : XV ⟶ V} (hu : IsEtale B S hS u.hom) (hU : IsPullback u.hom w.hom f.hom v.hom)
    {v' : V' ⟶ V} (hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z) v') (m : V' ⟶ A')
    (hm : m ≫ b = v' ≫ v) :
    ∃ (a : (strictTransformSpace B S hS w v' ((preimageClosedSubspace v Z).1.preimage v'.hom)).1 ⟶
        (strictTransformSpace B S hS f b (Z.1.preimage b.hom)).1),
      IsPullback v' m v b ∧
        IsPullback a (strictTransformSpaceToBlowUp B S hS w v'
            ((preimageClosedSubspace v Z).1.preimage v'.hom)).hom
          (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom m.hom := by
  have hcomm : u ≫ f = w ≫ v := ObjectProperty.hom_ext _ hU.w
  obtain ⟨m₀, can, sqm, -, hcanS, hcanB, -, hpre⟩ :=
    exists_strictTransform_eq_preimage B S hS hb hv hu hcomm hv'
  have hcart : IsPullbackDefined B S hS (v' ≫ v) Z :=
    isEffectiveCartierDivisor_of_subfunctor_eq
      (D' := preimageClosedSubspace v' (preimageClosedSubspace v Z))
      (Subfunctor.preimage_comp Z.1 v'.hom v.hom)
      hv'.isPullbackDefined
  have hm₀ : m = m₀ := (hb.existsUnique_lift (v' ≫ v) hcart).unique hm sqm.w.symm
  subst hm₀
  -- the square of the ambient base changes over `m`
  have hcanS' : can.hom ≫ pullback.fst f.hom b.hom = pullback.fst w.hom v'.hom ≫ u.hom :=
    congrArg (fun k => k.hom) hcanS
  have hcanB' : can.hom ≫ pullback.snd f.hom b.hom = pullback.snd w.hom v'.hom ≫ m.hom :=
    congrArg (fun k => k.hom) hcanB
  have hm' : v'.hom ≫ v.hom = m.hom ≫ b.hom := congrArg (fun k => k.hom) sqm.w
  have houter : IsPullback (can.hom ≫ pullback.fst f.hom b.hom) (pullback.snd w.hom v'.hom)
      f.hom (m.hom ≫ b.hom) := by
    rw [hcanS', ← hm']
    exact (IsPullback.of_hasPullback w.hom v'.hom).paste_horiz hU
  have hcan : IsPullback can.hom (pullback.snd w.hom v'.hom) (pullback.snd f.hom b.hom) m.hom :=
    IsPullback.of_right houter hcanB' (IsPullback.of_hasPullback f.hom b.hom)
  -- the strict transform of the chart is the preimage of the strict transform
  have key : ∀ T : Subfunctor (pullback w.hom v'.hom), T =
      (strictTransformSubfunctor B S hS f b (preimageClosedSubspace b Z).1).preimage can.hom →
      ∃ a : T.toFunctor ⟶ (strictTransformSubfunctor B S hS f b (Z.1.preimage b.hom)).toFunctor,
        IsPullback a (T.ι ≫ pullback.snd w.hom v'.hom)
          ((strictTransformSubfunctor B S hS f b (Z.1.preimage b.hom)).ι ≫
            pullback.snd f.hom b.hom) m.hom := by
    rintro T rfl
    exact ⟨_, (Subfunctor.isPullback_preimage can.hom _).paste_vert hcan⟩
  obtain ⟨a, ha⟩ := key _ hpre
  exact ⟨a, sqm, ha⟩

end AlgebraicGeometry.Space

end
