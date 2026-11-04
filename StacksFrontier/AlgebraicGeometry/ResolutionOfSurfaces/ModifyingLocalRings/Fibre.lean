module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibres over the distinguished points after base change to the local rings

For a finitely presented morphism to `S` which is an isomorphism away from the distinguished
closed points, the fibre over `s i` is unchanged by base change to `Spec 𝒪_{S, s i}`: the
canonical map `Spec κ(s i) ⟶ S` factors through `Spec 𝒪_{S, s i}`, so the two fibres are
pullbacks of one another along that factorisation.

## Main definitions

* `AlgebraicGeometry.FinitePresentationAwayPointsSituation.fromSpecResidueFieldLocal` is the
  canonical morphism `Spec κ(s i) ⟶ Spec 𝒪_{S, s i}` onto the closed point.
* `AlgebraicGeometry.FinitePresentationAwayPointsSituation.globalFibre` and
  `AlgebraicGeometry.FinitePresentationAwayPointsSituation.localFibre` are the two fibre
  functors to schemes over `κ(s i)`.

## Main results

* `AlgebraicGeometry.baseChangeFibreNatIso` identifies the two fibre functors after passage to
  the `i`th local category, naturally in the object over `S`.
* `AlgebraicGeometry.baseChangeFibreIso` identifies the fibre of `X ⟶ S` over `s i` with the
  fibre over the closed point of the object of the `i`th local category corresponding to it,
  as schemes over `κ(s i)`.

## References

* [Stacks Project, Tag 0BFX](https://stacks.math.columbia.edu/tag/0BFX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u}) (i : Fin D.n)

/-- The canonical morphism from the spectrum of the residue field at the `i`th distinguished
point to the spectrum of the local ring there, hitting the closed point. -/
noncomputable def fromSpecResidueFieldLocal :
    Spec (D.S.residueField (D.points i)) ⟶ D.localScheme i :=
  Spec.map (D.S.residue (D.points i))

/-- Every point of `Spec κ(s i)` maps to the closed point of `Spec 𝒪_{S, s i}`. -/
@[simp]
lemma fromSpecResidueFieldLocal_apply (x : Spec (D.S.residueField (D.points i))) :
    D.fromSpecResidueFieldLocal i x =
      IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i)) :=
  Scheme.SpecMap_residue_apply _ x

/-- The image of `Spec κ(s i) ⟶ Spec 𝒪_{S, s i}` is the closed point. -/
lemma range_fromSpecResidueFieldLocal :
    Set.range (D.fromSpecResidueFieldLocal i) =
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} := by
  ext x
  exact ⟨fun ⟨w, h⟩ ↦ h.symm.trans (D.fromSpecResidueFieldLocal_apply i w),
    fun h ↦ ⟨default, (D.fromSpecResidueFieldLocal_apply i default).trans h.symm⟩⟩

/-- The canonical map `Spec κ(s i) ⟶ S` factors through the spectrum of the local ring. -/
lemma fromSpecResidueFieldLocal_comp_fromSpecStalk :
    D.fromSpecResidueFieldLocal i ≫ D.S.fromSpecStalk (D.points i) =
      D.S.fromSpecResidueField (D.points i) :=
  rfl

/-- The fibre over the `i`th distinguished point, viewed as a scheme over `κ(s i)`. -/
noncomputable abbrev globalFibre :
    D.globalCategory ⥤ Over (Spec (D.S.residueField (D.points i))) :=
  ObjectProperty.ι (IsFinitePresentationAway D.complement) ⋙
    Over.pullback (D.S.fromSpecResidueField (D.points i))

/-- The fibre over the closed point of `Spec 𝒪_{S, s i}`, viewed as a scheme over `κ(s i)`. -/
noncomputable abbrev localFibre :
    D.localCategory i ⥤ Over (Spec (D.S.residueField (D.points i))) :=
  ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i)) ⋙
    Over.pullback (D.fromSpecResidueFieldLocal i)

end FinitePresentationAwayPointsSituation

/-- Taking the fibre over the `i`th distinguished point agrees with passing to the `i`th local
category and taking the fibre over its closed point, naturally in the object over `S`. -/
noncomputable def baseChangeFibreNatIso (D : FinitePresentationAwayPointsSituation.{u})
    (BC : BaseChangeFunctor D) (i : Fin D.n) :
    D.globalFibre i ≅
      BC.functor ⋙ Pi.eval (fun i ↦ D.localCategory i) i ⋙ D.localFibre i :=
  Functor.isoWhiskerLeft _
      (eqToIso (congrArg (fun f ↦ Over.pullback f)
        (D.fromSpecResidueFieldLocal_comp_fromSpecStalk i).symm) ≪≫
      Over.pullbackComp (D.fromSpecResidueFieldLocal i) (D.S.fromSpecStalk (D.points i))) ≪≫
    Functor.isoWhiskerRight (BC.pullbackIso i).symm
      (Over.pullback (D.fromSpecResidueFieldLocal i))

/-- **Stacks Project, Tag 0BFX.** If `f : X ⟶ S` corresponds to `g i : Y i ⟶ Spec 𝒪_{S, s i}`
under the base-change functor, then the fibre of `f` over `s i` is isomorphic to the fibre of
`g i` over the closed point, as schemes over `κ(s i)`. -/
@[stacks 0BFX]
noncomputable def baseChangeFibreIso (D : FinitePresentationAwayPointsSituation.{u})
    (BC : BaseChangeFunctor D) (X : D.globalCategory) (i : Fin D.n) :
    (Over.pullback (D.S.fromSpecResidueField (D.points i))).obj
        ((ObjectProperty.ι (IsFinitePresentationAway D.complement)).obj X) ≅
      (Over.pullback (D.fromSpecResidueFieldLocal i)).obj
        ((ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))).obj
          (BC.functor.obj X i)) :=
  (baseChangeFibreNatIso D BC i).app X

/-- The fibre comparison of Stacks Tag `0BFX` for the canonical base-change functor. -/
noncomputable def fibreIsoOfBaseChange (D : FinitePresentationAwayPointsSituation.{u})
    (X : D.globalCategory) (i : Fin D.n) :
    (Over.pullback (D.S.fromSpecResidueField (D.points i))).obj
        ((ObjectProperty.ι (IsFinitePresentationAway D.complement)).obj X) ≅
      (Over.pullback (D.fromSpecResidueFieldLocal i)).obj
        ((ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))).obj
          ((finitePresentationAwayPointsBaseChange D).functor.obj X i)) :=
  baseChangeFibreIso D (finitePresentationAwayPointsBaseChange D) X i

end AlgebraicGeometry
