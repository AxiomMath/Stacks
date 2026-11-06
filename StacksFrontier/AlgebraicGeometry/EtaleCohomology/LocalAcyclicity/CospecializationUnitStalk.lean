module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationSize
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.BaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationMapDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.DerivedPushforwardStalkUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StrictHenselizationBaseChangeSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StrictHenselizationSections

/-!
# The comparison `β_{K,s,t}` is an isomorphism on the closed geometric fibre (Tag 0GJU)

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S`, `t` a geometric point of
`S₀ = Spec 𝒪^{sh}_{S,s}`, `Y = X ×_S S₀` with projections `p : Y ⟶ X` and `f₀ : Y ⟶ S₀`, and
`h : X_t ⟶ Y`, `i : X_s ⟶ Y` the fibres of `f₀` over `t` and over the closed point. For a bounded
below object `K` of `D(X_étale)` relative to which `f` is locally acyclic, the inverse image
`i⁻¹β_{K,s,t}` of the comparison `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})` is an isomorphism. This
file proves it from the stalk computation of Tag 03Q9, taken as the named argument
`AlgebraicGeometry.DerivedPushforwardStalkFormula`.

## The route

This is the source's proof. Isomorphy is checked on derived stalks (Tag 03PU). Let `x` be a
geometric point of `X_s` and `y` its image in `Y`.

* Inverse image preserves stalks (Tag 03Q1), so the stalk of `i⁻¹β_{K,s,t}` at `x` is that of
  `β_{K,s,t}` at `y`.
* `β_{K,s,t}` is the unit of `h⁻¹ ⊣ Rh_*` at `M = K|_Y`, followed by an isomorphism; its stalk
  at `y`, followed by the map of Tag 0GIX from the stalk of `Rh_*`, is the map of Tag 0GJN for
  `M` and the scheme `T' = X_t ×_Y Spec 𝒪^{sh}_{Y,y}` over the strict henselization at `y`:
  `AlgebraicGeometry.derivedStalk_unit_comp_derivedPushforwardStalkToStrictHenselizationSections`.
  The map of Tag 0GIX is an isomorphism by Tag 03Q9, `h` being affine. The base change `Y` and
  the strict henselization `S₀` are objects of the big étale site
  (`AlgebraicGeometry.contains_strictHenselization`), so Tag 03Q9 applies to `h`.
* The base `S₀` is strictly henselian and `y` lies over its closed point, so the strict
  henselization of `S₀` at the image of `y` is `S₀` itself
  (`AlgebraicGeometry.isIso_strictHenselizationToBase_of_strictlyHenselian`), and `T'` is the
  variety of vanishing cycles of `f₀` at `y` and the corresponding geometric point `τ`
  (`AlgebraicGeometry.cospecializationStalkFibreIso`).
* `S₀` is the limit of the affine étale neighbourhoods of `s`, so `f₀` is locally acyclic at `y`
  relative to `M` by Tag 0GJS (`AlgebraicGeometry.isLocallyAcyclicAt_of_limit`).

## Main results

* `AlgebraicGeometry.isIso_pullback_cospecializationUnit_of_derivedPushforwardStalkFormula` —
  the statement of Tag 0GJU, from Tag 03Q9. It is not registered while it takes the argument
  `h03Q9`.

## References

* [Stacks Project, Tag 0GJU](https://stacks.math.columbia.edu/tag/0GJU)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- The image in `Spec 𝒪^{sh}_{S,s}` of a geometric point of the closed geometric fibre lies over
the closed point. -/
theorem liesOver_closedPoint_map (x : GeometricPoint (geometricFibre f s)) :
    ((x.map (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
        (strictHenselizationBaseChangeToStrictHenselization B hS f s)).LiesOver
      (closedPoint ↥(etaleLocalRing B S hS s)) := by
  show (x.hom ≫ geometricFibreToStrictHenselizationBaseChange B hS f s ≫
    strictHenselizationBaseChangeToStrictHenselization B hS f s) default = _
  rw [geometricFibreToStrictHenselizationBaseChange, pullback.lift_snd]
  show geometricPointToStrictHenselization B S hS s
    ((geometricFibreToPoint f s) (x.hom default)) = _
  rw [Subsingleton.elim ((geometricFibreToPoint f s) (x.hom default))
    (closedPoint s.residueField)]
  exact geometricPointToStrictHenselization_closedPoint B S hS s

/-! ### The fibre `X_t ×_Y Spec 𝒪^{sh}_{Y,y}` as a variety of vanishing cycles -/

section Fibre

variable (hS₀ : B.Contains (strictHenselization B S hS s))
  (hY : B.Contains (strictHenselizationBaseChange B hS f s))
  (y : GeometricPoint (strictHenselizationBaseChange B hS f s))
  (hy : (y.map (strictHenselizationBaseChangeToStrictHenselization B hS f s)).LiesOver
    (closedPoint ↥(etaleLocalRing B S hS s)))

include hy in
/-- Over the strictly henselian `Spec 𝒪^{sh}_{S,s}`, the strict henselization at a geometric point
over the closed point is the scheme itself. -/
theorem isIso_strictHenselizationToBase_cospecialization :
    IsIso (strictHenselizationToBase B (strictHenselization B S hS s) hS₀
      (y.map (strictHenselizationBaseChangeToStrictHenselization B hS f s))) :=
  isIso_strictHenselizationToBase_of_strictlyHenselian B ↥(etaleLocalRing B S hS s) hS₀ _ hy

/-- The geometric point `t` of `Spec 𝒪^{sh}_{S,s}`, read in the strict henselization of
`Spec 𝒪^{sh}_{S,s}` at the image of `y`, which is `Spec 𝒪^{sh}_{S,s}` itself. -/
def cospecializationStalkPoint :
    GeometricPoint (strictHenselization B (strictHenselization B S hS s) hS₀
      (y.map (strictHenselizationBaseChangeToStrictHenselization B hS f s))) :=
  haveI := isIso_strictHenselizationToBase_cospecialization B hS f s hS₀ y hy
  ⟨t.residueField, t.hom ≫ inv (strictHenselizationToBase B (strictHenselization B S hS s) hS₀
    (y.map (strictHenselizationBaseChangeToStrictHenselization B hS f s)))⟩

/-- The point `cospecializationStalkPoint`, followed by the map to `Spec 𝒪^{sh}_{S,s}` from its
strict henselization at the image of `y`, is the geometric point `t`. -/
theorem cospecializationStalkPoint_hom_comp :
    (cospecializationStalkPoint B hS f s t hS₀ y hy).hom ≫
        strictHenselizationToBase B (strictHenselization B S hS s) hS₀
          (y.map (strictHenselizationBaseChangeToStrictHenselization B hS f s)) = t.hom := by
  have := isIso_strictHenselizationToBase_cospecialization B hS f s hS₀ y hy
  exact (Category.assoc _ _ _).trans ((congrArg (t.hom ≫ ·) (IsIso.inv_hom_id _)).trans
    (Category.comp_id _))

/-- **The fibre of `h` over the strict henselization at `y` is a variety of vanishing cycles.**
The scheme `X_t ×_Y Spec 𝒪^{sh}_{Y,y}` over which the map of Tag 0GIX for `h : X_t ⟶ Y` at `y`
takes derived sections is the variety of vanishing cycles of `f₀ : Y ⟶ Spec 𝒪^{sh}_{S,s}` at `y`
and `t`: both are fibre products of `t` with `Spec 𝒪^{sh}_{Y,y}` over `Spec 𝒪^{sh}_{S,s}`. -/
def cospecializationStalkFibreIso :
    strictHenselizationBaseChange B hY (cospecializationFibreToBaseChange B hS f s t) y ≅
      vanishingCyclesFibre B hY hS₀ (strictHenselizationBaseChangeToStrictHenselization B hS f s) y
        (cospecializationStalkPoint B hS f s t hS₀ y hy) :=
  haveI := isIso_strictHenselizationToBase_cospecialization B hS f s hS₀ y hy
  have hT := (IsPullback.of_hasPullback (cospecializationFibreToBaseChange B hS f s t)
    (strictHenselizationToBase B _ hY y)).flip.paste_vert
      (IsPullback.of_hasPullback (strictHenselizationBaseChangeToStrictHenselization B hS f s)
        t.hom)
  have hF : IsPullback
      (pullback.snd (cospecializationStalkPoint B hS f s t hS₀ y hy).hom
        (strictHenselizationSquareMap B hY hS₀
          (strictHenselizationBaseChangeToStrictHenselization B hS f s) y))
      (pullback.fst (cospecializationStalkPoint B hS f s t hS₀ y hy).hom
        (strictHenselizationSquareMap B hY hS₀
          (strictHenselizationBaseChangeToStrictHenselization B hS f s) y))
      (strictHenselizationToBase B _ hY y ≫
        strictHenselizationBaseChangeToStrictHenselization B hS f s) t.hom :=
    (IsPullback.of_hasPullback (cospecializationStalkPoint B hS f s t hS₀ y hy).hom
      (strictHenselizationSquareMap B hY hS₀
        (strictHenselizationBaseChangeToStrictHenselization B hS f s) y)).flip.of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (strictHenselizationToBase B (strictHenselization B S hS s) hS₀
        (y.map (strictHenselizationBaseChangeToStrictHenselization B hS f s))))
      (by simp) (by simp)
      (by simpa using (strictHenselizationSquareMap_comp B hY hS₀
            (strictHenselizationBaseChangeToStrictHenselization B hS f s) y))
      ((cospecializationStalkPoint_hom_comp B hS f s t hS₀ y hy).trans
        (Category.id_comp _).symm)
  hT.isoIsPullback _ _ hF

/-- The isomorphism `cospecializationStalkFibreIso` is compatible with the projections of both
fibre products to the strict henselization of `Y` at `y`. -/
theorem cospecializationStalkFibreIso_hom_comp :
    (cospecializationStalkFibreIso B hS f s t hS₀ hY y hy).hom ≫
        vanishingCyclesFibreToStrictHenselization B hY hS₀
          (strictHenselizationBaseChangeToStrictHenselization B hS f s) y
          (cospecializationStalkPoint B hS f s t hS₀ y hy) =
      strictHenselizationBaseChangeToStrictHenselization B hY
        (cospecializationFibreToBaseChange B hS f s t) y :=
  by unfold cospecializationStalkFibreIso; exact IsPullback.isoIsPullback_hom_fst _ _ _ _

end Fibre

/-! ### Tag 0GJU -/

/-- **The statement of Stacks 0GJU, from Tag 03Q9.** Let `f : X ⟶ S` be a morphism of schemes of
a big étale site, `s` a geometric point of `S`, `t` a geometric point of `Spec 𝒪^{sh}_{S,s}`, and
`K` a bounded below object of `D(X_étale)` relative to which `f` is locally acyclic. Then the
inverse image `i⁻¹β_{K,s,t}` on the closed geometric fibre of the comparison
`β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})` is an isomorphism.

The argument `h03Q9` is the statement of Stacks 03Q9; since this theorem takes it as a
hypothesis, it is not registered as Stacks 0GJU. -/
theorem isIso_pullback_cospecializationUnit_of_derivedPushforwardStalkFormula
    (h03Q9 : DerivedPushforwardStalkFormula B)
    (K : smallEtaleDerivedCategory X) (m : ℤ) (hK : K.IsGE m)
    (hla : IsLocallyAcyclicRelative B hX hS f K) :
    IsIso ((smallEtaleDerivedPullbackAb
      (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
        (cospecializationUnit B hS f s t K)) := by
  have hS₀ := contains_strictHenselization B S hS s
  have hY := contains_strictHenselizationBaseChange B hS hX f s
  refine isIso_of_forall_isIso_smallEtaleDerivedStalkAb _ fun x => ?_
  -- the stalk of `i⁻¹β` at `x` is the stalk of `β` at the image `y` of `x` (Tag 03Q1)
  refine (NatIso.isIso_map_iff (Functor.mapDerivedCategoryCompIsoOfCompIso
    (smallEtaleStalkPullbackAbIso (geometricFibreToStrictHenselizationBaseChange B hS f s)
      x.hom)) _).2 ?_
  set y := x.map (geometricFibreToStrictHenselizationBaseChange B hS f s)
  set h := cospecializationFibreToBaseChange B hS f s t
  set M := (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K
  have hy := liesOver_closedPoint_map B hS f s x
  -- the map of Tag 0GJN for `M` and `X_t ×_Y Spec 𝒪^{sh}_{Y,y}` is an isomorphism
  have hla₀ := isLocallyAcyclicAt_strictHenselizationBaseChange B hX hS f s K y
    (hla _) (cospecializationStalkPoint B hS f s t hS₀ y hy)
  rw [vanishingCyclesFibreMap_eq] at hla₀
  have hV : IsIso ((vanishingCyclesMap B _ hY y
      (strictHenselizationBaseChangeToStrictHenselization B hY h y)).app M) := by
    rw [← cospecializationStalkFibreIso_hom_comp B hS f s t hS₀ hY y hy,
      vanishingCyclesMap_comp]
    have := isIso_smallEtaleDerivedGlobalSectionsRestriction
      (cospecializationStalkFibreIso B hS f s t hS₀ hY y hy).hom
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ hla₀ (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_)
    · exact NatIso.isIso_app_of_isIso _ _
    · exact Functor.map_isIso _ _
  -- the map of Tag 0GIX from the stalk of `Rh_*` at `y` is an isomorphism (Tag 03Q9)
  have hX₀ := h03Q9 hY h y ((smallEtaleDerivedPullbackAb h).obj M) m
    ((smallEtalePullbackAb h).isGE_obj_mapDerivedCategory M m
      ((smallEtalePullbackAb _).isGE_obj_mapDerivedCategory K m hK))
  -- so the stalk of the unit at `y` is an isomorphism
  have key := derivedStalk_unit_comp_derivedPushforwardStalkToStrictHenselizationSections
    B hY h y M
  have hunit : IsIso ((smallEtaleDerivedStalkAb y.hom).map
      ((smallEtaleDerivedAdjunctionAb h).unit.app M)) := by
    rw [← key] at hV
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance hV
  rw [cospecializationUnit_eq, Functor.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hunit (Functor.map_isIso _ _)

end AlgebraicGeometry

end
