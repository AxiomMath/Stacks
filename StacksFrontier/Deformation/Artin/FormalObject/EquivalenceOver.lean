module

public import StacksFrontier.Deformation.Artin.FormalObject.Realization
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion

/-!
# Formal objects along morphisms over the big fppf site

A functor `G : 𝒳 ⥤ 𝒴` commuting on the nose with the projections `p : 𝒳 ⥤ (Sch/S)_{fppf}` and
`q : 𝒴 ⥤ (Sch/S)_{fppf}` takes formal objects of `p` (Stacks 07X3) to formal objects of `q`, and
realizations to realizations. Along an equivalence over the site this shows that effectiveness of
formal objects (Stacks 07X7) is invariant: a formal object is effective as soon as its image is
effective. The two total categories may have hom types in different
universes, which is the situation of the small model of an algebraic stack.

## Main definitions

* `Deformation.Artin.FormalObject.mapOver`: the image of a formal object under a morphism over
  the site.
* `Deformation.Artin.FormalObject.Realization.mapOver`: the image of a realization.

## Main results

* `Deformation.Artin.FormalObject.isEffective_of_isEffective_mapOver`: a formal object whose
  image along an equivalence over the site is effective is effective.

## References

* [Stacks Project, Tag 07X3](https://stacks.math.columbia.edu/tag/07X3)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory

universe u v w v' w'

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}
  {F' : Type v'} [Category.{w'} F'] {q : F' ⥤ BigFppfOver B S hS}

namespace FormalObject

/-- The image of a formal object of `p` under a functor `G` commuting on the nose with the
projections: the same complete local base, with every level and every transition pushed
forward. -/
def mapOver (G : StacksRepresentableCFG.MorphismOver p q) (ξ : FormalObject B S hS p) :
    FormalObject B S hS q where
  base := ξ.base
  contains := ξ.contains
  level n := G.functor.obj (ξ.level n)
  level_eq n := (Functor.congr_obj G.w (ξ.level n)).trans (ξ.level_eq n)
  transition n := G.functor.map (ξ.transition n)
  transition_lift n := by
    have := ξ.transition_lift n
    have hmap := Functor.congr_hom G.w (ξ.transition n)
    have hfac := IsHomLift.fac' p (truncationOverSucc B S hS ξ.base ξ.contains n)
      (ξ.transition n)
    refine IsHomLift.of_fac' q _ _
      ((Functor.congr_obj G.w (ξ.level n)).trans (ξ.level_eq n))
      ((Functor.congr_obj G.w (ξ.level (n + 1))).trans (ξ.level_eq (n + 1))) ?_
    change (G.functor ⋙ q).map (ξ.transition n) = _
    rw [hmap, hfac]
    simp

/-- The image of a realization of a formal object along a functor commuting on the nose with
the projections is a realization of the image formal object. -/
def Realization.mapOver (G : StacksRepresentableCFG.MorphismOver p q) {ξ : FormalObject B S hS p}
    {hA : B.Contains (Spec (.of ξ.base.R))} {x : F} {hx : p.obj x = baseOver B S hS ξ.base hA}
    (R : Realization ξ hA x hx) :
    Realization (ξ.mapOver G) hA (G.functor.obj x)
      ((Functor.congr_obj G.w x).trans hx) where
  r n := G.functor.map (R.r n)
  comp_transition n := by
    change G.functor.map (ξ.transition n) ≫ G.functor.map (R.r (n + 1)) = _
    rw [← Functor.map_comp, R.comp_transition]
  map_eq n := by
    change (G.functor ⋙ q).map (R.r n) = _
    rw [Functor.congr_hom G.w (R.r n), R.map_eq n]
    simp
    rfl

/-- The isomorphism of formal objects between a formal object and its image along the
composite of the two halves of an equivalence over the site, given by the unit. -/
def unitIsoMapOver (E : StacksRepresentableCFG.EquivalenceOver p q) (ξ : FormalObject B S hS p) :
    ξ ≅ (ξ.mapOver E.hom).mapOver E.inv where
  hom :=
    { app := fun n => E.unitIso.hom.app (ξ.level n)
      naturality := fun n => E.unitIso.hom.naturality (ξ.transition n) }
  inv :=
    { app := fun n => E.unitIso.inv.app (ξ.level n)
      naturality := fun n => E.unitIso.inv.naturality (ξ.transition n) }
  hom_inv_id := Hom.ext fun n => E.unitIso.hom_inv_id_app (ξ.level n)
  inv_hom_id := Hom.ext fun n => E.unitIso.inv_hom_id_app (ξ.level n)

/-- **Effectiveness descends along an equivalence over the site.** If the image of a formal
object `ξ` of `p` along an equivalence over the big fppf site is effective (Stacks 07X7), then
`ξ` is effective. The two total categories may have hom types in different universes. -/
theorem isEffective_of_isEffective_mapOver (hp : p.IsFiberedInGroupoids)
    (hq : q.IsFiberedInGroupoids) (E : StacksRepresentableCFG.EquivalenceOver p q)
    (ξ : FormalObject B S hS p)
    (heff : IsEffective B S hS q hq (ξ.mapOver E.hom)) :
    IsEffective B S hS p hp ξ := by
  obtain ⟨y, hy, ⟨R⟩⟩ :=
    exists_realization_of_isEffective (ξ := ξ.mapOver E.hom) (hA := ξ.contains_spec_base) hq heff
  have h' := isEffective_of_realization hp (R.mapOver E.inv)
  exact Functor.essImage.ofIso (unitIsoMapOver E ξ).symm h'

end FormalObject

end Deformation.Artin

end
