module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange

/-!
# The comparison of two composite pullbacks of modules, read at the unit module

Let a square of morphisms of ringed sites commute, in the sense that the two composite continuous
functors are isomorphic by `e` compatibly with the two composite comparisons of sheaves of rings.
`SheafOfModules.pullbackSquareIso` compares the two composite pullbacks of sheaves of modules
round such a square; it is built by `CategoryTheory.Adjunction.leftAdjointUniq`, so nothing
describes its values.

This file records what a consumer of it needs at the **unit** module.  Each morphism of ringed
sites carries a canonical map `SheafOfModules.pullbackObjUnitToUnit` from the pullback of the unit
module to the unit module — the map `g^*𝒪 ⟶ 𝒪` of pullback of regular functions — and the
comparison carries the composite of the two such maps round one route of the square to the
composite round the other.  No value of the comparison is computed: both sides are morphisms out
of a pullback, so they are determined by their transposes, and
`CategoryTheory.Adjunction.leftAdjointUniq` is exactly the comparison which identifies those.

The instance of the statement at the square of small étale sites of a morphism of schemes says
that the base change `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` of [Stacks Project, Tag 03LC] (1) carries the
scheme-level comparison `r^♯` to the small étale comparison `ε_a^♯`.

## Main results

* `CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp`: **two morphisms out of the two
  left adjoints of one right adjoint which have the same transpose are carried to one another by
  the comparison of the two left adjoints.**  This is the handle on a comparison built by
  `CategoryTheory.Adjunction.leftAdjointUniq`: it cannot describe its own values, but a composite
  out of it has a computable transpose.
* `SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp_map`,
  `SheafOfModules.unitToPushforwardObjUnit_comp_natTrans` and
  `SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr`: the three ways the structure
  comparison at the unit module meets the three constructions
  `SheafOfModules.pushforwardComp`, `SheafOfModules.pushforwardNatTrans` and
  `SheafOfModules.pushforwardCongr` that `SheafOfModules.pullbackSquareIso` is assembled from.
  Each holds on sections.
* `SheafOfModules.pullbackSquareIso_hom_app_unit`: **the comparison of the two composite
  pullbacks is compatible with the canonical maps out of the pullback of the unit module.**
* `AlgebraicGeometry.SmallEtale.pullbackObjUnitToUnit_associatedModuleBaseChangeIso`: that
  statement at the square of [Stacks Project, Tag 03LC] (1) — the base change of the associated
  module carries the scheme-level structure comparison to the small étale one.

## Implementation notes

The two adjunctions `SheafOfModules.pullbackSquareIso` is the `leftAdjointUniq` of are passed to
`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp` as explicit terms, written out as
they are in the definition.  Left to unification they are metavariables whose categories are not
determined, and instance search for `CategoryTheory.Category` is then stuck.

The transposes are computed by `CategoryTheory.Adjunction.comp_homEquiv` and
`CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply` followed by the two naturality laws of
the transpose, in the order left-then-right on each side: the left law has to fire on the whole
composite before the right law splits it, and a `simp only` with both laws available does the
right one first and then the left one no longer matches.

The equality of comparisons the square provides cannot be rewritten with directly: the type of
`SheafOfModules.unitToPushforwardObjUnit` depends on the comparison, so a `rw` of that equality
has an ill-typed motive.  It enters instead through
`SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr`, which is stated with both
comparisons as variables and proved by `subst`.

## References

* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory.Adjunction

/-- **Two morphisms out of the two left adjoints of one right adjoint which have the same
transpose are carried to one another by the comparison of the two left adjoints.**

The two units agree through the comparison
(`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`), so transposing a composite whose first
factor is the comparison returns the transpose along the other adjunction. -/
theorem eq_leftAdjointUniq_hom_app_comp {C : Type*} [Category C] {D : Type*} [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) {c : D}
    (u₁ : F.obj x ⟶ c) (u₂ : F'.obj x ⟶ c)
    (h : adj1.homEquiv x c u₁ = adj2.homEquiv x c u₂) :
    u₁ = (adj1.leftAdjointUniq adj2).hom.app x ≫ u₂ := by
  refine (adj1.homEquiv x c).injective (h.trans ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]

end CategoryTheory.Adjunction

namespace SheafOfModules

section Comparison

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F : C ⥤ D} {G : D ⥤ E} [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
  {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}} {R'' : Sheaf L RingCat.{u}}

/-- **The structure comparison of a composite of two morphisms of ringed sites, read at the unit
module, is the composite of the two structure comparisons.**  The direct image along a composite
is the composite of the direct images on the nose, so the two sides have the same type, and on
sections both are the composite of the two maps of rings. -/
theorem unitToPushforwardObjUnit_comparisonComp_eq_comp_map
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R')
    (ψ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R'') :
    unitToPushforwardObjUnit (comparisonComp φ ψ) =
      unitToPushforwardObjUnit φ ≫ (pushforward φ).map (unitToPushforwardObjUnit ψ) := by
  ext X
  rfl

/-- **The structure comparison twisted by a natural transformation of the index functors, read at
the unit module.**  On sections both sides are the map of rings followed by restriction along the
component of the natural transformation. -/
theorem unitToPushforwardObjUnit_comp_natTrans {H : C ⥤ D} [H.IsContinuous J K] (α : H ⟶ F)
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R') :
    unitToPushforwardObjUnit
        (φ ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat.{u} J K).app R') =
      unitToPushforwardObjUnit φ ≫ (pushforwardNatTrans φ α).app (unit R') := by
  ext X
  rfl

/-- **The structure comparison at the unit module is carried along an equality of comparisons by
the transport of direct images that equality induces.**  The transport is the identity on
sections; the statement exists because the type of
`SheafOfModules.unitToPushforwardObjUnit` depends on the comparison, so the equality cannot be
rewritten with directly. -/
theorem unitToPushforwardObjUnit_comp_pushforwardCongr
    {φ ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R'} (h : φ = ψ) :
    unitToPushforwardObjUnit φ ≫ (pushforwardCongr h).hom.app (unit R') =
      unitToPushforwardObjUnit ψ := by
  subst h
  ext X
  rfl

end Comparison

section Square

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {a : C ⥤ C'} {b : C' ⥤ D'} {c : C ⥤ D} {d : D ⥤ D'}
  [a.IsContinuous J J'] [b.IsContinuous J' K'] [c.IsContinuous J K] [d.IsContinuous K K']
  [(a ⋙ b).IsContinuous J K'] [(c ⋙ d).IsContinuous J K']
  {RC : Sheaf J RingCat.{u}} {RC' : Sheaf J' RingCat.{u}}
  {RD : Sheaf K RingCat.{u}} {RD' : Sheaf K' RingCat.{u}}
  (φa : RC ⟶ (a.sheafPushforwardContinuous RingCat.{u} J J').obj RC')
  (φb : RC' ⟶ (b.sheafPushforwardContinuous RingCat.{u} J' K').obj RD')
  (φc : RC ⟶ (c.sheafPushforwardContinuous RingCat.{u} J K).obj RD)
  (φd : RD ⟶ (d.sheafPushforwardContinuous RingCat.{u} K K').obj RD')
  [(pushforward.{u} φa).IsRightAdjoint] [(pushforward.{u} φb).IsRightAdjoint]
  [(pushforward.{u} φc).IsRightAdjoint] [(pushforward.{u} φd).IsRightAdjoint]

/-- **The comparison of the two composite pullbacks of modules round a square of ringed sites is
compatible with the canonical maps out of the pullback of the unit module.**  Going round the
square by `a` then `b`, the composite of the two maps `g^*𝒪 ⟶ 𝒪` of pullback of regular
functions is the comparison `SheafOfModules.pullbackSquareIso` followed by the corresponding
composite along `c` then `d`.

Both sides are morphisms out of a composite pullback, hence determined by their transposes along
the corresponding composite adjunction, and those transposes are the structure comparisons of the
two composite routes; the square's hypothesis says precisely that those agree. -/
theorem pullbackSquareIso_hom_app_unit (e : a ⋙ b ≅ c ⋙ d)
    (he : comparisonComp φc φd ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K').app RD' =
      comparisonComp φa φb) :
    (pullback.{u} φb).map (pullbackObjUnitToUnit φa) ≫ pullbackObjUnitToUnit φb =
      (pullbackSquareIso.{u} φa φb φc φd e he).hom.app (unit RC) ≫
        (pullback.{u} φd).map (pullbackObjUnitToUnit φc) ≫ pullbackObjUnitToUnit φd := by
  refine Adjunction.eq_leftAdjointUniq_hom_app_comp
    ((pullbackPushforwardAdjunction.{u} φa).comp (pullbackPushforwardAdjunction.{u} φb))
    (((pullbackPushforwardAdjunction.{u} φc).comp
        (pullbackPushforwardAdjunction.{u} φd)).ofNatIsoRight
      (pushforwardComp.{u} φc φd ≪≫ pushforwardCongr₂.{u} _ e he ≪≫
        (pushforwardComp.{u} φa φb).symm)) (unit RC) _ _ ?_
  rw [Adjunction.comp_homEquiv, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv, Equiv.trans_apply, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
    Adjunction.homEquiv_naturality_right,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
    Adjunction.homEquiv_naturality_left,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
    Adjunction.homEquiv_naturality_right,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  simp only [← unitToPushforwardObjUnit_comparisonComp_eq_comp_map]
  rw [← unitToPushforwardObjUnit_comp_pushforwardCongr he,
    unitToPushforwardObjUnit_comp_natTrans]
  rfl

end Square

end SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The base change of the associated module carries the scheme-level structure comparison to
the small étale one.**  For a morphism `a : X ⟶ Y` of schemes of the big étale site, with `r` the
underlying morphism of schemes and `ε_a` the morphism of small étale ringed sites of
[Stacks Project, Tag 070R] (2), the comparison `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` of
[Stacks Project, Tag 03LC] (1) identifies the associated module of the Zariski map
`r^*𝒪_Y ⟶ 𝒪_X` with the small étale map `ε_a^*𝒪 ⟶ 𝒪`.

This is `SheafOfModules.pullbackSquareIso_hom_app_unit` at the square whose geometric half is
`AlgebraicGeometry.SmallEtale.baseChangeOpensIso`. -/
theorem pullbackObjUnitToUnit_associatedModuleBaseChangeIso :
    (associatedModule B X.obj X.property).map
          (SheafOfModules.pullbackObjUnitToUnit (schemeHom B a).toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit (structureMap B X.obj X.property) =
      (associatedModuleBaseChangeIso B a).hom.app
          (SheafOfModules.unit Y.obj.ringCatSheaf) ≫
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
            (SheafOfModules.pullbackObjUnitToUnit (structureMap B Y.obj Y.property)) ≫
          SheafOfModules.pullbackObjUnitToUnit (smallEtaleStructureMapRing B a) :=
  SheafOfModules.pullbackSquareIso_hom_app_unit (schemeHom B a).toRingCatSheafHom
    (structureMap B X.obj X.property) (structureMap B Y.obj Y.property)
    (smallEtaleStructureMapRing B a) (baseChangeOpensIso B a)
    (structureMap_comp_baseChangeOpensIso B a)

end AlgebraicGeometry.SmallEtale

end
