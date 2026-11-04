module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# Transport of a global presentation between sites in independent universes

`Stacks.SheafOfModules.hasGlobalPresentation_map` carries a global presentation, Stacks
03DE (6), along a functor of categories of sheaves of modules that preserves colimits and zero
morphisms and matches the structure sheaves.  It is stated for two sites in the *same* pair of
universes, `{C : Type u} [Category.{v} C]` and `{C' : Type u} [Category.{v} C']`, and that is
what forces every consumer — in particular the transport of quasi-coherence along an
equivalence of sites — into the same pair.  A site and its equi-universe model do not satisfy
it: the total Zariski site of a simplicial scheme has objects in `Type u` and morphisms in
`Type 0`, while its model has both in `Type u`.

This file restates the transport with the two sites in independent object *and* morphism
universes.  What makes that possible is recorded in the implementation notes below: the
universe in which a global presentation lives can be made to agree on the two sides.

## Main definitions

* `Stacks.SheafOfModules.SiteTransport.pushforwardUliftIso_ofUniv`:
  `Stacks.SheafOfModules.pushforwardUliftIso` — restriction of sheaves of modules along a
  continuous functor commutes with raising the universe of the sections — with the two sites in
  independent universes.

## Main results

* `Stacks.SheafOfModules.SiteTransport.hasGlobalPresentation_map_ofUniv`:
  `Stacks.SheafOfModules.hasGlobalPresentation_map` with the two sites in independent object and
  morphism universes.

## Implementation notes

A global presentation of a module with sections in `Type m` on a site with objects in `Type u`
and morphisms in `Type v`, over a sheaf of rings with sections in `Type w`, is indexed by types
in `Type (max u v w m)` and is built from modules with sections in that same universe.  So for a
module on `(C, J)` and its image on `(C', J')` the two presentations live in `max u v w m` and in
`max u' v' w m`, which for independent universes are different: the index type of a presentation
on one side is then not even a candidate index type on the other, and no reindexing can move it,
since a type in a larger universe has no equinumerous copy in a smaller one.

The universes are made to agree by *balancing the module universe*: the statements below are
about a module whose sections lie in `max u u' v v' n`, and then

  `max u v w (max u u' v v' n) = max u u' v v' w n = max u' v' w (max u u' v v' n)`,

so both presentations live in `max u u' v v' w n`, both index types are `Type (max u u' v v' w n)`,
and the functor that moves the presentation is a functor between categories of sheaves of modules
at that one universe.  With the two universe pairs equal this is exactly
`Stacks.SheafOfModules.hasGlobalPresentation_map`, and the proof is the same.

The balancing is no restriction where it is needed.  For the total Zariski site and its model,
`v = 0` and `u' = v' = u`, so `max u u' v v' n = max u n`, which is `u` at `n = u` — the universe
in which the modules of `AlgebraicGeometry.SimplicialScheme.Modules` and of the model live.  For
`u = u'` and `v = v'` it reads `max u v n`, so these statements are not a generalisation of the
existing ones, whose module universe is unconstrained; they are the same statements with the module
universe traded for the two universe pairs.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.SiteTransport

/-- Restriction of sheaves of modules along a continuous functor commutes with raising the
universe of the sections, with the two sites in independent object and morphism universes: both
sides have the same sections over every object.

This is `Stacks.SheafOfModules.pushforwardUliftIso` with the universes separated. -/
noncomputable def pushforwardUliftIso_ofUniv.{u, v, u', v', w, s, t}
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{w}} {F : C' ⥤ C} [Functor.IsContinuous F J' J]
    (φ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{w} J' J).obj R)
    (N : SheafOfModules.{s} R) :
    (SheafOfModules.pushforward.{max t s} φ).obj
        (SheafOfModules.uliftForPresentation.{u, v, w, s, t} N) ≅
      SheafOfModules.uliftForPresentation.{u', v', w, s, t}
        ((SheafOfModules.pushforward.{s} φ).obj N) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) fun _ _ _ => by
      ext
      rfl)

/-- **Having a global presentation is carried along a functor of sheaves of modules between
sites in independent universes.**  As in
`Stacks.SheafOfModules.hasGlobalPresentation_map`, the functor is asked for twice: as `F₀` at the
module universe, whose image of `M` the conclusion is about, and as `F` at the universe in which
a global presentation lives, which is what actually moves the presentation; the two are tied
together by `ηM`.

The module universe is `max u u' v v' n`, which is what makes the presentation universes of the
two sites agree — see the implementation notes of this file. -/
theorem hasGlobalPresentation_map_ofUniv.{u, v, u', v', w, n}
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{w}} (M : SheafOfModules.{max u u' v v' n} R)
    {F₀ : SheafOfModules.{max u u' v v' n} R ⥤ SheafOfModules.{max u u' v v' n} R'}
    {F : SheafOfModules.{max u u' v v' w n} R ⥤ SheafOfModules.{max u u' v v' w n} R'}
    [PreservesColimitsOfSize.{max u u' v v' w n, max u u' v v' w n} F]
    [Functor.PreservesZeroMorphisms F]
    (η₁ : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, w, max u u' v v' n}
      (SheafOfModules.unit R)) ≅
      SheafOfModules.uliftForPresentation.{u', v', w, w, max u u' v v' n}
        (SheafOfModules.unit R'))
    (ηM : F.obj (SheafOfModules.uliftForPresentation.{u, v, w, max u u' v v' n, max u v w} M) ≅
      SheafOfModules.uliftForPresentation.{u', v', w, max u u' v v' n, max u' v' w}
        (F₀.obj M)) :
    M.HasGlobalPresentation → (F₀.obj M).HasGlobalPresentation := by
  classical
  let : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink F
  rintro ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩
  have hcof : ∀ {X : Type (max u u' v v' w n)} {P : SheafOfModules.{max u u' v v' w n} R}
      (ι : X → (_ ⟶ P)), Nonempty (IsColimit (Cofan.mk P ι)) →
      Nonempty (IsColimit (Cofan.mk (F.obj P) fun i => η₁.inv ≫ F.map (ι i))) :=
    fun ι h => ⟨Stacks.SheafOfModules.isColimitCofan_precomposeIso η₁.symm _
      ((Cofan.isColimitMapCoconeEquiv F _ (Cofan.mk _ ι)).toFun (isColimitOfPreserves F h.some))⟩
  let b' : F.obj P ⟶ SheafOfModules.uliftForPresentation.{u', v', w,
      max u u' v v' n, max u' v' w} (F₀.obj M) := F.map b ≫ ηM.hom
  have hab' : F.map a ≫ b' = 0 := by
    simp only [b', ← Category.assoc, ← F.map_comp, hab, F.map_zero, zero_comp]
  let c' := CokernelCofork.ofπ b' hab'
  have hc' : IsColimit c' := by
    let d := (parallelPair a 0) ⋙ F
    let i₁ : d ≅ parallelPair (F.map a) (F.map 0) := by
      refine NatIso.ofComponents (fun j => ?_) ?_
      · cases j <;> exact Iso.refl _
      rintro _ _ (_ | _ | _) <;> simp [d]
    let i₂ : parallelPair (F.map a) (F.map 0) ≅ parallelPair (F.map a) 0 :=
      parallelPairIsoMk (Iso.refl (F.obj Q)) (Iso.refl (F.obj P))
    let i := i₁ ≪≫ i₂
    exact (IsColimit.equivOfNatIsoOfIso i (F.mapCocone (CokernelCofork.ofπ b hab)) c'
      (Cocone.ext ηM (by rintro (_ | _) <;>
        simp [c', b', d, i, i₁, i₂, parallelPairIsoMk,
          NatIso.ofComponents_inv_app]))).toFun (isColimitOfPreserves F hc.some)
  exact ⟨I, K, F.obj P, F.obj Q, _, _, hcof ι hP, hcof κ hQ, F.map a, b', hab', ⟨hc'⟩⟩

end Stacks.SheafOfModules.SiteTransport

end
