module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackCriterion

/-!
# What an equivalence onto the two-fibre product says about the fibre categories

Conditions (2) and (3) of Stacks 0EX9 assert that a comparison functor
`AlgebraicGeometry.BigHOver.twoFibreProductComparison` is an equivalence of categories.  That
functor lands in Mathlib's `CategoryTheory.Limits.CategoricalPullback`, whose morphisms are *pairs*
of morphisms of the two fibre categories agreeing over the exceptional corner, and it sends a
morphism of the fibre over the base to the pair of its two pullbacks.  So the two halves of the
equivalence read as follows, and that is what this file records:

* *faithfulness* says that a morphism of the fibre over the base is determined by its pullbacks to
  the centre and to the modification;
* *fullness* says that a pair consisting of a morphism over the centre and a morphism over the
  modification which agree over the exceptional corner is the pair of pullbacks of a morphism over
  the base.

Essential surjectivity is recorded in the same style: an object over the centre and an object over
the modification with an isomorphism between their pullbacks to the exceptional corner come from
an object over the base.

The agreement condition over the exceptional corner is `CategoricalPullback.Hom.w` for the
structural isomorphism of the comparison functor, which is
`CategoryTheory.Functor.IsFibered.CartStruct.cmpIso` of the two cartesian structures around the
square.

## Main results

* `AlgebraicGeometry.BigHOver.twoFibreProductComparison_map_fst` and
  `AlgebraicGeometry.BigHOver.twoFibreProductComparison_map_snd`: the comparison functor sends a
  morphism to the pair of its pullbacks.
* `AlgebraicGeometry.BigHOver.eq_of_fiberPullback_map_eq`: faithfulness, unfolded.
* `AlgebraicGeometry.BigHOver.exists_fiberHom`: fullness, unfolded.
* `AlgebraicGeometry.BigHOver.exists_fiberObj`: essential surjectivity, unfolded.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]
variable {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
  (hsq : IsPullback e d z b)

/-- The first component of the comparison functor of a cartesian square is the pullback functor
to the centre. -/
public theorem twoFibreProductComparison_obj_fst (x : p.Fiber X) :
    ((twoFibreProductComparison B S hS p b z d e hsq).obj x).fst =
      (Functor.IsFibered.fiberPullback (p := p) z).obj x := rfl

/-- The second component of the comparison functor of a cartesian square is the pullback functor
to the modification. -/
public theorem twoFibreProductComparison_obj_snd (x : p.Fiber X) :
    ((twoFibreProductComparison B S hS p b z d e hsq).obj x).snd =
      (Functor.IsFibered.fiberPullback (p := p) b).obj x := rfl

/-- On morphisms the comparison functor of a cartesian square is the pullback to the centre in
its first component. -/
public theorem twoFibreProductComparison_map_fst {x y : p.Fiber X} (h : x ⟶ y) :
    ((twoFibreProductComparison B S hS p b z d e hsq).map h).fst =
      (Functor.IsFibered.fiberPullback (p := p) z).map h := rfl

/-- On morphisms the comparison functor of a cartesian square is the pullback to the modification
in its second component. -/
public theorem twoFibreProductComparison_map_snd {x y : p.Fiber X} (h : x ⟶ y) :
    ((twoFibreProductComparison B S hS p b z d e hsq).map h).snd =
      (Functor.IsFibered.fiberPullback (p := p) b).map h := rfl

/-- **Faithfulness of the comparison functor of a cartesian square, unfolded.** A morphism of the
fibre over the base of a cartesian square along which the comparison functor is an equivalence is
determined by its pullbacks to the centre and to the modification. -/
public theorem eq_of_fiberPullback_map_eq
    (heq : (twoFibreProductComparison B S hS p b z d e hsq).IsEquivalence)
    {x y : p.Fiber X} (h h' : x ⟶ y)
    (hz : (Functor.IsFibered.fiberPullback (p := p) z).map h =
      (Functor.IsFibered.fiberPullback (p := p) z).map h')
    (hb : (Functor.IsFibered.fiberPullback (p := p) b).map h =
      (Functor.IsFibered.fiberPullback (p := p) b).map h') :
    h = h' := by
  have := heq
  exact (twoFibreProductComparison B S hS p b z d e hsq).map_injective
    (CategoricalPullback.hom_ext hz hb)

/-- **Fullness of the comparison functor of a cartesian square, unfolded.** A morphism over the
centre and a morphism over the modification which agree over the exceptional corner are the two
pullbacks of a morphism over the base. -/
public theorem exists_fiberHom
    (heq : (twoFibreProductComparison B S hS p b z d e hsq).IsEquivalence)
    {x y : p.Fiber X}
    (a : (Functor.IsFibered.fiberPullback (p := p) z).obj x ⟶
      (Functor.IsFibered.fiberPullback (p := p) z).obj y)
    (c : (Functor.IsFibered.fiberPullback (p := p) b).obj x ⟶
      (Functor.IsFibered.fiberPullback (p := p) b).obj y)
    (w : (Functor.IsFibered.fiberPullback (p := p) e).map a ≫
        ((twoFibreProductComparison B S hS p b z d e hsq).obj y).iso.hom =
      ((twoFibreProductComparison B S hS p b z d e hsq).obj x).iso.hom ≫
        (Functor.IsFibered.fiberPullback (p := p) d).map c) :
    ∃ h : x ⟶ y, (Functor.IsFibered.fiberPullback (p := p) z).map h = a ∧
      (Functor.IsFibered.fiberPullback (p := p) b).map h = c := by
  have := heq
  obtain ⟨h, hh⟩ := (twoFibreProductComparison B S hS p b z d e hsq).map_surjective
    (⟨a, c, w⟩ : (twoFibreProductComparison B S hS p b z d e hsq).obj x ⟶
      (twoFibreProductComparison B S hS p b z d e hsq).obj y)
  exact ⟨h, congrArg CategoricalPullback.Hom.fst hh, congrArg CategoricalPullback.Hom.snd hh⟩

/-- **Essential surjectivity of the comparison functor of a cartesian square, unfolded.** An
object over the centre and an object over the modification with an isomorphism between their
pullbacks to the exceptional corner are the two pullbacks of an object over the base, compatibly
with that isomorphism. -/
public theorem exists_fiberObj
    (heq : (twoFibreProductComparison B S hS p b z d e hsq).IsEquivalence)
    (xZ : p.Fiber Z) (xX' : p.Fiber X')
    (ε : (Functor.IsFibered.fiberPullback (p := p) e).obj xZ ≅
      (Functor.IsFibered.fiberPullback (p := p) d).obj xX') :
    ∃ (x : p.Fiber X) (αZ : (Functor.IsFibered.fiberPullback (p := p) z).obj x ≅ xZ)
      (αX' : (Functor.IsFibered.fiberPullback (p := p) b).obj x ≅ xX'),
      (Functor.IsFibered.fiberPullback (p := p) e).map αZ.hom ≫ ε.hom =
        ((twoFibreProductComparison B S hS p b z d e hsq).obj x).iso.hom ≫
          (Functor.IsFibered.fiberPullback (p := p) d).map αX'.hom := by
  have := heq
  set Φ := twoFibreProductComparison B S hS p b z d e hsq
  set y : CategoricalPullback (Functor.IsFibered.fiberPullback (p := p) e)
    (Functor.IsFibered.fiberPullback (p := p) d) := ⟨xZ, xX', ε⟩
  refine ⟨Φ.objPreimage y, (CategoricalPullback.π₁ _ _).mapIso (Φ.objObjPreimageIso y),
    (CategoricalPullback.π₂ _ _).mapIso (Φ.objObjPreimageIso y), ?_⟩
  exact (Φ.objObjPreimageIso y).hom.w

end BigHOver

end AlgebraicGeometry

end
