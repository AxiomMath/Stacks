module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantFibreBijection
public import
  StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantResidueFieldPurelyInseparable
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.SeparablyClosedResidueField

/-!
# The bijection of fibres over a strictly henselian invariant ring

Let `F : G' ⟶ G` be a morphism of groupoid schemes with `U`, `R`, `U'`, `R'` affine and `s`, `t`,
`s'`, `t'` finite locally free, write `C` and `C'` for the two rings of invariant functions, and
assume the squares formed by `F` and the two source maps, the two target maps and the two
stabilizer group schemes are cartesian. If `C` is **strictly henselian** and `p'` is a point of
`Spec C'` lying over the closed point of `Spec C`, then the map of fibres
`U'_{p'} ⟶ U_p` is **bijective**.

## Main results

* `AlgebraicGeometry.GroupoidScheme.separating_of_strictlyHenselian`: over a strictly henselian
  invariant ring a field-valued point of `U` at a point of the closed fibre is determined by its
  composite with the quotient morphism `q : U ⟶ Spec C`.
* `AlgebraicGeometry.GroupoidScheme.bijective_invariantFibreMap_of_strictlyHenselian`: the
  bijection `U'_{p'} ⟶ U_p` of fibres over the closed point, over a strictly henselian invariant
  ring.
* `AlgebraicGeometry.GroupoidScheme.isSepClosed_residueField_of_strictlyHenselian`: the residue
  field of `U` at a point of the closed fibre is separably closed.
* `AlgebraicGeometry.GroupoidScheme.bijective_residueFieldMap_mapObjects_of_strictlyHenselian`:
  the residue field map of an étale `f : U' ⟶ U` at a point of the closed fibre is bijective.

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-- At a point over the closed point, the residue field extension of the quotient morphism is
purely inseparable for the algebra structure given by the residue field map. -/
private theorem exists_algebra_isPurelyInseparable_residueField (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [StrictlyHenselianLocalRing (invariantRing G)]
    (u : G.objects.left)
    (hu : (objectsToInvariantSpectrum G).base u =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    ∃ _ : Algebra ((Spec (.of (invariantRing G))).residueField
        ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u),
      algebraMap ((Spec (.of (invariantRing G))).residueField
          ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u) =
        ((objectsToInvariantSpectrum G).residueFieldMap u).hom ∧
      IsPurelyInseparable ((Spec (.of (invariantRing G))).residueField
        ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u) :=
  let : Algebra ((Spec (.of (invariantRing G))).residueField
      ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u) :=
    ((objectsToInvariantSpectrum G).residueFieldMap u).hom.toAlgebra
  ⟨this, rfl, isPurelyInseparable_residueField_objectsToInvariantSpectrum G u hu rfl⟩

/-- **Over a strictly henselian invariant ring a field-valued point of `U` at a point of the
closed fibre is determined by its composite with the quotient morphism.** -/
theorem separating_of_strictlyHenselian (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [StrictlyHenselianLocalRing (invariantRing G)]
    (u : G.objects.left)
    (hu : (objectsToInvariantSpectrum G).base u =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G))))
    (K : Type u) (_ : Field K) (α β : Spec (.of K) ⟶ G.objects.left)
    (hα : α.base (IsLocalRing.closedPoint K) = u)
    (hβ : β.base (IsLocalRing.closedPoint K) = u)
    (hcomp : α ≫ objectsToInvariantSpectrum G = β ≫ objectsToInvariantSpectrum G) :
    α = β := by
  obtain ⟨_, hcompat, _⟩ := exists_algebra_isPurelyInseparable_residueField G u hu
  exact eq_of_comp_eq_of_isPurelyInseparable (objectsToInvariantSpectrum G) hα hβ hcomp hcompat

/-- **The bijection of fibres over a strictly henselian invariant ring.** If `C` is strictly
henselian and `p'` is a point of `Spec C'` lying over the closed point of `Spec C`, then
`U'_{p'} ⟶ U_p` is bijective. -/
theorem bijective_invariantFibreMap_of_strictlyHenselian
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
    [StrictlyHenselianLocalRing (invariantRing G)]
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (p' : Spec (.of (invariantRing G')))
    (hp' : (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    Function.Bijective (invariantFibreMap F p') :=
  bijective_invariantFibreMap F hsource htarget hstab p' fun v hv ↦
    separating_of_strictlyHenselian G v (hv.trans hp')

/-! ### The residue fields of the closed fibre -/

/-- **The residue field of `U` at a point of the closed fibre is separably closed**, when the
invariant ring `C` is strictly henselian. -/
theorem isSepClosed_residueField_of_strictlyHenselian (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [StrictlyHenselianLocalRing (invariantRing G)]
    (u : G.objects.left)
    (hu : (objectsToInvariantSpectrum G).base u =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    IsSepClosed (G.objects.left.residueField u) := by
  obtain ⟨_, hcompat, _⟩ := exists_algebra_isPurelyInseparable_residueField G u hu
  have : IsSepClosed ((Spec (.of (invariantRing G))).residueField
      ((objectsToInvariantSpectrum G).base u)) :=
    isSepClosed_residueField_spec_of_asIdeal_eq_maximalIdeal _ _ (by rw [hu]; rfl)
  exact Algebra.IsAlgebraic.isSepClosed (F := (Spec (.of (invariantRing G))).residueField
    ((objectsToInvariantSpectrum G).base u))

/-- **The residue field map of `f : U' ⟶ U` at a point of the closed fibre is bijective**, when
`f` is étale and the invariant ring `C` is strictly henselian. -/
theorem bijective_residueFieldMap_mapObjects_of_strictlyHenselian
    [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [StrictlyHenselianLocalRing (invariantRing G)]
    [Etale F.mapObjects.left] (u' : G'.objects.left)
    (hu' : (objectsToInvariantSpectrum G).base (F.mapObjects.left.base u') =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    Function.Bijective (F.mapObjects.left.residueFieldMap u').hom :=
  have := isSepClosed_residueField_of_strictlyHenselian G _ hu'
  Scheme.Hom.bijective_residueFieldMap_of_etale F.mapObjects.left u'

end AlgebraicGeometry.GroupoidScheme

end

end
