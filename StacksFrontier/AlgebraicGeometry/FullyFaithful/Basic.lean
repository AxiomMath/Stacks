module

public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.LocalSchemesFpqcCover.Basic

/-!
# Faithfulness of the canonical restriction functor near finitely many closed points

Let `S` be a scheme and let `s : I → S` be a finite family of closed points whose open complement
`U` has quasi-compact inclusion. [Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
asserts that the canonical functor `AlgebraicGeometry.canonicalRestrictionFunctor` from schemes
of finite presentation over `S` to gluing data is an equivalence of categories, and the source
explicitly omits the proof of full faithfulness.

This file proves the **faithful** half.  The mechanism is fpqc descent: the family consisting of
`U ⟶ S` and of the canonical morphisms `Spec 𝒪_{S, s i} ⟶ S` is an fpqc covering family of `S`
(`AlgebraicGeometry.LocalSchemesCover.presieve₀_mem_fpqcPrecoverage`), the fpqc precoverage is
stable under base change, and `Scheme.fpqcTopology` is subcanonical.  So for *any* scheme `T`
over `S` the base-changed family covers `T`, and a morphism out of `T` is determined by its
restrictions to the members.  Applied to the source of a morphism of schemes of finite
presentation over `S`, this says exactly that a morphism over `S` is determined by its base
changes to `U` and to the local schemes — which is the faithfulness of the canonical restriction
functor.

## Main results

* `AlgebraicGeometry.LocalSchemesCover.presieve_pullback_mem_fpqcPrecoverage`: the base change of
  the covering family along an arbitrary morphism `T ⟶ S` is an fpqc covering family of `T`.
* `AlgebraicGeometry.LocalSchemesCover.hom_ext_of_baseChange`: a morphism out of a scheme `T` over
  `S` is determined by its restrictions to the base changes of the members of the family.
* `AlgebraicGeometry.faithful_canonicalRestrictionFunctor`: the canonical restriction functor of
  Tag 0E8Q is faithful.

## Implementation notes

`AlgebraicGeometry.LocalSchemesCover.hom_ext` already covers the case `T = S`, but faithfulness of
the restriction functor needs the statement over the source of the morphism being restricted, not
over `S`, because restriction of a morphism of `S`-schemes is base change rather than composition.
Hence the base-change step, which is `Precoverage.mem_coverings_of_isPullback` against the derived
`Precoverage.IsStableUnderBaseChange` instance on `AlgebraicGeometry.Scheme.fpqcPrecoverage`.

No tag is attached.  Tag 0E8Q's third label asserts that the canonical restriction functor is an
equivalence, and the covering set for that label is the single assertion
`IsEquivalence`; faithfulness is one of its three constituents, so it earns no partial credit on
its own.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

namespace LocalSchemesCover

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)
  (hqc : QuasiCompact (complementOfClosedPoints s hs).ι)

include hs hqc in
/-- **The base change of the covering family to any scheme over `S` is again an fpqc covering
family.**  The fpqc precoverage is stable under base change, so the family of first projections
`T ×_S T_a ⟶ T` covers `T` as soon as the family `T_a ⟶ S` covers `S`. -/
theorem presieve_pullback_mem_fpqcPrecoverage {T : Scheme.{u}} (g : T ⟶ S) :
    Presieve.ofArrows (fun a ↦ pullback g (map s hs a))
        (fun a ↦ pullback.fst g (map s hs a)) ∈ Scheme.fpqcPrecoverage T :=
  Precoverage.mem_coverings_of_isPullback (map s hs)
    (presieve₀_mem_fpqcPrecoverage s hs hqc) g _ _
    fun _ ↦ IsPullback.of_hasPullback _ _

include hs hqc in
/-- **A morphism out of a scheme `T` over `S` is determined by its restrictions to the base
changes of the open complement and of the local schemes at the points of the family.**  This is
the faithfulness half of fpqc descent of morphisms for the covering family, over an arbitrary
base `T ⟶ S` rather than over `S` itself. -/
theorem hom_ext_of_baseChange {T : Scheme.{u}} (g : T ⟶ S) {Y : Scheme.{u}} (f₁ f₂ : T ⟶ Y)
    (h : ∀ a, pullback.fst g (map s hs a) ≫ f₁ = pullback.fst g (map s hs a) ≫ f₂) :
    f₁ = f₂ := by
  have hsf : Presieve.IsSheafFor (yoneda.obj Y)
      (Presieve.ofArrows (fun a ↦ pullback g (map s hs a))
        (fun a ↦ pullback.fst g (map s hs a))) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck
        (presieve_pullback_mem_fpqcPrecoverage s hs hqc g))
  refine hsf.isSeparatedFor.ext ?_
  rintro Z p ⟨a⟩
  exact h a

include hs hqc in
/-- **A morphism of schemes over `S` is determined by its base changes to the members of the
covering family.**  This is `AlgebraicGeometry.LocalSchemesCover.hom_ext_of_baseChange` transported
from morphisms out of the source to morphisms in the over category, using that the first pullback
projection intertwines a morphism with its base change. -/
theorem over_hom_ext_of_baseChange {X Y : Over S} (f₁ f₂ : X ⟶ Y)
    (h : ∀ a, (Over.pullback (map s hs a)).map f₁ = (Over.pullback (map s hs a)).map f₂) :
    f₁ = f₂ := by
  refine Over.OverMorphism.ext
    (hom_ext_of_baseChange s hs hqc X.hom f₁.left f₂.left fun a ↦ ?_)
  have := congrArg (fun m ↦ CommaMorphism.left m ≫ pullback.fst Y.hom (map s hs a)) (h a)
  simpa only [Over.pullback_map_left, pullback.lift_fst] using this

end LocalSchemesCover

/-- **Stacks Project, Tag 0E8Q**, the faithfulness constituent of the equivalence.  The canonical
restriction functor from schemes of finite presentation over `S` to gluing data near a finite
family of closed points is faithful: a morphism over `S` is determined by its base changes to the
open complement and to the local schemes at the points.

The source of Tag 0E8Q omits the proof of full faithfulness; this is its faithful half, and it is
fpqc descent for the covering family of
`AlgebraicGeometry.LocalSchemesCover.presieve₀_mem_fpqcPrecoverage`. -/
theorem faithful_canonicalRestrictionFunctor {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
    (hs : ∀ i, s i ∈ closedPoints S)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    (canonicalRestrictionFunctor s hs).Faithful where
  map_injective := by
    intro X Y f₁ f₂ h
    -- The two components of the image of a morphism are its base changes to the open complement
    -- and to the local schemes: this is `openComponent_comp_canonicalRestrictionFunctor` and
    -- `localComponent_comp_canonicalRestrictionFunctor`, both of which hold by `rfl`.
    have hU : (restrictToComplementOfClosedPoints s hs).map f₁ =
        (restrictToComplementOfClosedPoints s hs).map f₂ :=
      congrArg (openComponent s hs).map h
    have hL : (restrictToLocalSchemes s).map f₁ = (restrictToLocalSchemes s).map f₂ :=
      congrArg (localComponent s hs).map h
    -- `ObjectProperty.ι` is faithful, so it is enough to equate the underlying morphisms of
    -- `Over S`, where the covering family's descent statement applies.
    refine (ObjectProperty.ι _).map_injective
      (LocalSchemesCover.over_hom_ext_of_baseChange s hs hqc _ _ ?_)
    rintro (_ | i)
    · exact congrArg (ObjectProperty.ι _).map hU
    · exact congrArg (ObjectProperty.ι _).map (congrFun hL i)

end AlgebraicGeometry

end
