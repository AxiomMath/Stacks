module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduced induced closed subscheme structure is smooth-local

Let `f : X ⟶ Y` be a smooth morphism of schemes and let `I` be a quasi-coherent ideal of `Y`
whose closed subscheme is reduced. Then the closed subscheme of the pullback ideal `I.comap f`
is reduced, and consequently the pullback of the vanishing ideal of a closed set of `Y` is the
vanishing ideal of its preimage in `X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_comap_of_smooth`: the pullback
  of a reduced closed subscheme along a smooth morphism is reduced.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_of_smooth`: the pullback along
  a smooth morphism of the vanishing ideal of a closed set is the vanishing ideal of the
  preimage of that set.
* `AlgebraicGeometry.Scheme.IdealSheafData.pullback_subobject_eq_of_support_comap_eq_of_smooth`:
  two pullbacks of a reduced closed subscheme along smooth morphisms agree as subobjects as
  soon as the two pullback ideals have the same support.

## Implementation notes

These are the three statements of
`StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspace.lean` for étale morphisms, with
étaleness relaxed to smoothness. Étaleness is used there only through
`AlgebraicGeometry.isReduced_of_etale`, which is itself the smooth statement
`AlgebraicGeometry.isReduced_of_smooth` of **Stacks 033B**, so the whole argument goes through
unchanged; the statements for étale morphisms are the special case.

The generality matters for an algebraic stack rather than an algebraic space: the two legs of
the relation `R = U ×_𝒳 U` of a chart of an algebraic stack are smooth and not étale, so the
invariance of the reduced induced closed subscheme of the chart — the step at which the
subschemes constructed chart-locally glue — is a statement about smooth morphisms.

The preimage in `AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_of_smooth` is
passed as a closed set together with the equation describing it, so that no continuity proof
has to be named in the statement.

## References

* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- The pullback of a reduced closed subscheme along a smooth morphism is reduced: the pullback
subscheme is, up to isomorphism, a fibre product which is smooth over the subscheme one started
with, and the source of a smooth morphism with reduced target is reduced. -/
@[sga "3 XV 6.9" "(a)"]
theorem isReduced_subscheme_comap_of_smooth {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) [Smooth f] (hI : IsReduced I.subscheme) :
    IsReduced (I.comap f).subscheme := by
  have : IsReduced I.subscheme := hI
  have hs : Smooth (pullback.snd f I.subschemeι) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback f I.subschemeι) ‹Smooth f›
  have : IsReduced (pullback f I.subschemeι) :=
    isReduced_of_smooth (pullback.snd f I.subschemeι)
  exact ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z)
    (I.comapIso f).symm ‹_›

/-- The pullback along a smooth morphism of the vanishing ideal of a closed set is the vanishing
ideal of the preimage of that set. This is the sense in which the reduced induced closed
subscheme structure is smooth-local. -/
theorem comap_vanishingIdeal_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (C : Closeds Y) (D : Closeds X) (hD : (D : Set X) = f.base ⁻¹' (C : Set Y)) :
    (vanishingIdeal C).comap f = vanishingIdeal D := by
  refine eq_of_isReduced_subscheme_of_support_eq _ _
    (isReduced_subscheme_comap_of_smooth _ f (isReduced_subscheme_vanishingIdeal C))
    (isReduced_subscheme_vanishingIdeal D) (Closeds.ext ?_)
  rw [support_comap]
  change f.base ⁻¹' ((vanishingIdeal C).support : Set Y) = _
  rw [coe_support_vanishingIdeal, coe_support_vanishingIdeal, hD]

/-- Two pullbacks of a reduced closed subscheme, viewed as subobjects of the two sources, agree
as soon as the two pullback ideals have the same support. Both legs are required to be smooth,
which is what makes the pullback ideals reduced. -/
theorem pullback_subobject_eq_of_support_comap_eq_of_smooth {U R : Scheme.{u}}
    (I : U.IdealSheafData) (f g : R ⟶ U) [Smooth f] [Smooth g] (hI : IsReduced I.subscheme)
    (hfg : (I.comap f).support = (I.comap g).support) :
    (Subobject.pullback f).obj (Subobject.mk I.subschemeι) =
      (Subobject.pullback g).obj (Subobject.mk I.subschemeι) := by
  have hideal : I.comap f = I.comap g :=
    eq_of_isReduced_subscheme_of_support_eq _ _ (isReduced_subscheme_comap_of_smooth I f hI)
      (isReduced_subscheme_comap_of_smooth I g hI) hfg
  have key : ∀ (h : R ⟶ U), (Subobject.pullback h).obj (Subobject.mk I.subschemeι) =
      Subobject.mk (I.comap h).subschemeι := by
    intro h
    have hh : (I.comapIso h).hom ≫ (pullbackSymmetry h I.subschemeι).hom ≫
        pullback.snd I.subschemeι h = (I.comap h).subschemeι := by
      calc (I.comapIso h).hom ≫ (pullbackSymmetry h I.subschemeι).hom ≫
            pullback.snd I.subschemeι h
          _ = (I.comapIso h).hom ≫ pullback.fst h I.subschemeι := by
            simp only [pullbackSymmetry_hom_comp_snd]
          _ = _ := comapIso_hom_fst I h
    rw [Subobject.pullback_obj_mk (IsPullback.of_hasPullback I.subschemeι h)]
    refine Subobject.mk_eq_mk_of_comm _ _
      (I.comapIso h ≪≫ pullbackSymmetry h I.subschemeι).symm ?_
    rw [← hh]
    simp
  rw [key f, key g, hideal]

end AlgebraicGeometry.Scheme.IdealSheafData

end
