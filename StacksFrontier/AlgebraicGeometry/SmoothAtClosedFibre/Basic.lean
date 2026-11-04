module

public import Mathlib.RingTheory.Smooth.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion

/-!
# The closed fibre of the stalk map, and condition (2) of Tag 01V9 read on it

Condition (2) of Stacks Tag 01V9 is the conjunction of flatness of the induced map of local
rings `𝒪_{S,f x} → 𝒪_{X,x}` with smoothness, at the point determined by `x`, of the
scheme-theoretic fibre of `f` through `x` viewed as a scheme over `κ(f x)`.  This file shows that
the second conjunct makes the local ring of the fibre formally smooth over `κ(f x)`, and that the
`κ(f x)`-algebra structure on that local ring coming from the structure morphism
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` of the fibre is the one induced through
the stalk map of `f`.

## Main definitions

* `Stacks.SmoothAtClosedFibre.kappaToFibreStalk`: the action of `κ(f x)` on the local ring of
  the scheme-theoretic fibre, read off the structure morphism of the fibre.
* `Stacks.SmoothAtClosedFibre.residueFieldToFibreStalkIso` and
  `Stacks.SmoothAtClosedFibre.arrowIso_kappaToFibreStalk`: that action presented as the stalk
  map of the structure morphism of the fibre, up to isomorphism of arrows.

## Main results

* `Stacks.SmoothAtClosedFibre.stalkClosedPointTo_fromSpecResidueField`: the local homomorphism
  induced by `AlgebraicGeometry.Scheme.fromSpecResidueField` on the stalk at the closed point is
  the residue map.
* `Stacks.SmoothAtClosedFibre.residue_kappaToFibreStalk`: precomposing the action of `κ(f x)`
  on the fibre stalk with the residue map of `𝒪_{S,f x}` gives the stalk map of `f` followed by
  the stalk map of the embedding of the fibre.
* `Stacks.SmoothAtClosedFibre.formallySmooth_kappaToFibreStalk`: if the fibre of `f` through `x`
  is smooth at `x` over `κ(f x)`, then its local ring is formally smooth over `κ(f x)`.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SmoothAtClosedFibre

/-- The germ along a stalk congruence coming from an equality of points is the germ at the other
point. -/
public theorem germ_stalkCongr_hom {Z : Scheme.{u}} {a b : Z} (h : a = b) (U : Z.Opens)
    (ha : a ∈ U) :
    Z.presheaf.germ U a ha ≫ (Z.presheaf.stalkCongr (Inseparable.of_eq h)).hom =
      Z.presheaf.germ U b (h ▸ ha) := by
  subst h
  simp

/-- The inverse of a stalk congruence coming from an equality of points. -/
public theorem stalkCongr_inv_of_eq {Z : TopCat} (F : Z.Presheaf CommRingCat) {a b : Z}
    (h : a = b) :
    (F.stalkCongr (Inseparable.of_eq h)).inv = eqToHom (congrArg F.stalk h).symm := by
  subst h
  simp

/-- Any two composites of stalk congruences between stalks at equal points, with the same source
and target, agree. -/
public theorem stalkCongr_collapse {Z : TopCat} (F : Z.Presheaf CommRingCat) {a b c d : Z}
    (hb : b = a) (hc : c = a) (hd : d = a)
    (i1 : Inseparable b a) (i2 : Inseparable b c) (i3 : Inseparable a d)
    (i4 : Inseparable d c) {W : CommRingCat} (k : F.stalk c ⟶ W) :
    (F.stalkCongr i1).inv ≫ (F.stalkCongr i2).hom ≫ k =
      (F.stalkCongr i3).hom ≫ (F.stalkCongr i4).hom ≫ k := by
  subst hb hc hd
  simp [TopCat.Presheaf.stalkCongr]

/-- The local homomorphism induced by the canonical morphism from the residue field is the
residue map. -/
public theorem stalkClosedPointTo_fromSpecResidueField {S : Scheme.{u}} (y : S) :
    Scheme.stalkClosedPointTo (S.fromSpecResidueField y) =
      (S.presheaf.stalkCongr
        (Inseparable.of_eq (Scheme.fromSpecResidueField_apply y _))).hom ≫ S.residue y := by
  have _ : IsLocalHom (S.residue y).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  refine (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (S.residue y) U hU).trans ?_
  refine (congrArg (fun t => t ≫ S.residue y)
    (germ_stalkCongr_hom (Scheme.fromSpecResidueField_apply y
      (IsLocalRing.closedPoint (S.residueField y))) U hU)).symm.trans ?_
  exact Category.assoc _ _ _

/-- The residue map, read through the closed-point stalk isomorphism of the spectrum of the
residue field. -/
public theorem residue_stalkClosedPointIso_inv {S : Scheme.{u}} (y : S) :
    S.residue y ≫ (AlgebraicGeometry.stalkClosedPointIso (S.residueField y)).inv =
      (S.presheaf.stalkCongr (Inseparable.of_eq
          (Scheme.fromSpecResidueField_apply y
            (IsLocalRing.closedPoint (S.residueField y))))).inv ≫
        (S.fromSpecResidueField y).stalkMap
          (IsLocalRing.closedPoint (S.residueField y)) := by
  rw [Iso.eq_inv_comp, ← Category.assoc]
  have h := stalkClosedPointTo_fromSpecResidueField y
  rw [Scheme.stalkClosedPointTo] at h
  rw [← h]
  simp

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The action of `κ(f x)` on the local ring of the scheme-theoretic fibre of `f` through `x`,
read off the structure morphism of the fibre over `Spec κ(f x)`. -/
public noncomputable def kappaToFibreStalk :
    S.residueField (f x) ⟶ (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
  (AlgebraicGeometry.stalkClosedPointIso (S.residueField (f x))).inv ≫
    ((Spec (S.residueField (f x))).presheaf.stalkCongr
      (Inseparable.of_eq
        (Scheme.Hom.fiberToSpecResidueField_apply f (f x) (f.asFiber x)).symm)).hom ≫
    (f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)

/-- Composing the residue map of `𝒪_{S,f x}` with the action of `κ(f x)` on the fibre stalk
gives the stalk map of `f` followed by the stalk map of the embedding of the fibre. -/
public theorem residue_kappaToFibreStalk :
    S.residue (f x) ≫ kappaToFibreStalk f x =
      f.stalkMap x ≫
        (X.presheaf.stalkCongr (Inseparable.of_eq (f.fiberι_asFiber x).symm)).hom ≫
        (f.fiberι (f x)).stalkMap (f.asFiber x) := by
  rw [kappaToFibreStalk, ← Category.assoc, residue_stalkClosedPointIso_inv]
  simp only [Category.assoc]
  rw [Scheme.Hom.stalkMap_congr_point_assoc (S.fromSpecResidueField (f x))
      (IsLocalRing.closedPoint (S.residueField (f x)))
      ((f.fiberToSpecResidueField (f x)) (f.asFiber x))
      (Scheme.Hom.fiberToSpecResidueField_apply f (f x) (f.asFiber x)).symm,
    ← Scheme.Hom.stalkMap_comp,
    Scheme.Hom.stalkMap_congr_point_assoc f x (f.fiberι (f x) (f.asFiber x))
      (f.fiberι_asFiber x).symm,
    ← Scheme.Hom.stalkMap_comp,
    Scheme.Hom.stalkMap_congr_hom (f.fiberι (f x) ≫ f)
      (f.fiberToSpecResidueField (f x) ≫ S.fromSpecResidueField (f x))
      (f.fiber_fac (f x)) (f.asFiber x)]
  exact stalkCongr_collapse S.presheaf
    (Scheme.fromSpecResidueField_apply (f x)
      (IsLocalRing.closedPoint (S.residueField (f x))))
    (Scheme.fromSpecResidueField_apply (f x) _)
    (congrArg f (f.fiberι_asFiber x)) _ _ _ _ _

/-- The comparison of `κ(f x)` with the stalk of `Spec κ(f x)` at the image of the fibre
point. -/
public noncomputable def residueFieldToFibreStalkIso :
    S.residueField (f x) ≅
      (Spec (S.residueField (f x))).presheaf.stalk
        ((f.fiberToSpecResidueField (f x)) (f.asFiber x)) :=
  (AlgebraicGeometry.stalkClosedPointIso (S.residueField (f x))).symm ≪≫
    (Spec (S.residueField (f x))).presheaf.stalkCongr
      (Inseparable.of_eq
        (Scheme.Hom.fiberToSpecResidueField_apply f (f x) (f.asFiber x)).symm)

/-- The action of `κ(f x)` on the fibre stalk is the stalk map of the structure morphism of the
fibre, up to an isomorphism of arrows. -/
public noncomputable def arrowIso_kappaToFibreStalk :
    Arrow.mk (kappaToFibreStalk f x) ≅
      Arrow.mk ((f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)) :=
  Arrow.isoMk (residueFieldToFibreStalkIso f x) (Iso.refl _) (by
    simp [kappaToFibreStalk, residueFieldToFibreStalkIso])

/-- If the scheme-theoretic fibre of `f` through `x` is smooth at `x`
over the residue field of `f x`, then the local ring of that fibre is a formally smooth
`κ(f x)`-algebra for the canonical structure of
`Stacks.SmoothAtClosedFibre.residue_kappaToFibreStalk`. -/
public theorem formallySmooth_kappaToFibreStalk [LocallyOfFinitePresentation f]
    (h : InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)) :
    (kappaToFibreStalk f x).hom.FormallySmooth := by
  have hfp : LocallyOfFinitePresentation (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFinitePresentation
      (pullback.snd f (S.fromSpecResidueField (f x))))
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (arrowIso_kappaToFibreStalk f x)).mpr <| Scheme.Hom.mem_smoothLocus.mp <|
      (Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus
        (f.fiberToSpecResidueField (f x)) (f.asFiber x)).mp h

end Stacks.SmoothAtClosedFibre

end
