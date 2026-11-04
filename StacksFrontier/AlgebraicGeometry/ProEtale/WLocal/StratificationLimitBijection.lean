module

public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationStrataPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# The limiting closed subscheme maps bijectively to the base

Let `A` be a commutative ring, let `X_w = Spec A_w` be the inverse limit of the finite vanishing
stratifications of `Spec A`, and let `Z ⊆ X_w` be the inverse limit of the finite closed strata.
The composite `Z ⟶ X_w ⟶ Spec A` is a bijection on points.

## Main results

* `AlgebraicGeometry.ProEtale.stratificationLimit_closedScheme_bijective`: the canonical map from
  `Z` to `Spec A` is bijective.
* `AlgebraicGeometry.ProEtale.bijective_stratificationLimitClosedScheme_toBase`: the same
  statement for the canonical limiting data `AlgebraicGeometry.ProEtale.stratificationLimit`.

## References

* [Stacks Project, Tag 0975](https://stacks.math.columbia.edu/tag/0975)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

/-- The limiting closed subscheme `Z` of `X_w` maps bijectively onto `Spec A`. -/
@[stacks 0975 "bijection_on_z"]
theorem stratificationLimit_closedScheme_bijective (L : StratificationLimit A) :
    Function.Bijective (L.inclusion ≫
      Spec.map (CommRingCat.ofHom (stratificationColimitAlgebraMap (A := A)))).base := by
  classical
  let D := L.closedDiagram
  let : ∀ {i j : (Finset A)ᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
    closedDiagram_hasAffineTransitions L
  let : PreservesLimit D Scheme.forget :=
    preservesLimit_forget_of_isCofiltered_of_isAffineHom D
  let c : Cone D := Cone.mk L.closedScheme L.closedProjection
  have hlim : IsLimit (Scheme.forget.mapCone c) :=
    isLimitOfPreserves Scheme.forget L.closedIsLimit
  let stageEquiv (E : Finset A) : closedStrata E ≃ Spec (.of A) :=
    Equiv.ofBijective (closedStrataToBase E).base (bijective_closedStrataToBase E)
  let yStage (p : PrimeSpectrum A) (E : Finset A) : closedStrata E :=
    (stageEquiv E).symm (specPointEquiv A p)
  have hyStage (p : PrimeSpectrum A) (E : Finset A) :
      (closedStrataToBase E).base (yStage p E) = specPointEquiv A p :=
    (stageEquiv E).apply_symm_apply _
  have htransition (p : PrimeSpectrum A) (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
      (closedStrataTransition E₁ E₂ h).val.base (yStage p E₂) = yStage p E₁ := by
    refine (bijective_closedStrataToBase E₁).1 ?_
    have heq := congrArg (fun g : closedStrata E₂ ⟶ Spec (.of A) => g.base (yStage p E₂))
      (closedStrataTransition_comp_closedStrataToBase E₁ E₂ h)
    rw [hyStage p E₁, ← hyStage p E₂]
    simpa [Scheme.Hom.comp_apply] using heq
  let zStage (p : PrimeSpectrum A) (E : Finset A) : D.obj (Opposite.op E) :=
    (L.closedStage E).inv.base (yStage p E)
  have hzStage (p : PrimeSpectrum A) {i j : (Finset A)ᵒᵖ} (f : i ⟶ j) :
      (D.map f).base (zStage p i.unop) = zStage p j.unop := by
    let E₁ := j.unop
    let E₂ := i.unop
    have h : E₁ ⊆ E₂ := leOfHom f.unop
    obtain rfl : f = (homOfLE h).op := Subsingleton.elim _ _
    refine schemeIso_base_injective (L.closedStage E₁) ?_
    have hcomm := congrArg (fun g : D.obj (Opposite.op E₂) ⟶ closedStrata E₁ =>
      g.base (zStage p E₂)) (L.closedTransition E₁ E₂ h)
    change (L.closedStage E₁).hom.base ((D.map (homOfLE h).op).base (zStage p E₂)) =
      (closedStrataTransition E₁ E₂ h).val.base
        ((L.closedStage E₂).hom.base (zStage p E₂)) at hcomm
    simpa [E₁, E₂, zStage, Iso.hom_inv_id_apply, htransition p E₁ E₂ h] using hcomm
  have hstageValue (x : L.closedScheme) (E : Finset A) :
      (L.inclusion ≫
          Spec.map (CommRingCat.ofHom (stratificationColimitAlgebraMap (A := A)))).base x =
        (closedStrataToBase E).base
          ((L.closedStage E).hom.base ((L.closedProjection.app (Opposite.op E)).base x)) := by
    simpa [closedStrataToBase, Scheme.Hom.comp_apply] using
      congrArg (fun g : L.closedScheme ⟶ Spec (.of A) => g.base x) (inclusion_stage_factor L E)
  let T := ULift.{u, 0} Unit
  constructor
  · intro x y hxy
    have hcoord (E : Finset A) :
        (L.closedProjection.app (Opposite.op E)).base x =
          (L.closedProjection.app (Opposite.op E)).base y := by
      refine schemeIso_base_injective (L.closedStage E)
        ((bijective_closedStrataToBase E).1 ?_)
      rw [← hstageValue x E, ← hstageValue y E, hxy]
    let fx : T ⟶ Scheme.forget.obj L.closedScheme := TypeCat.ofHom fun _ => x
    let fy : T ⟶ Scheme.forget.obj L.closedScheme := TypeCat.ofHom fun _ => y
    have hfx : ∀ E : Finset A,
        fx ≫ Scheme.forget.map (L.closedProjection.app (Opposite.op E)) =
          fy ≫ Scheme.forget.map (L.closedProjection.app (Opposite.op E)) := fun E => by
      ext
      exact hcoord E
    have hxy' : fx = fy := by
      refine hlim.hom_ext fun i => ?_
      simpa [fx, fy] using hfx i.unop
    simpa [fx, fy] using congrArg
      (fun g : T ⟶ Scheme.forget.obj L.closedScheme => TypeCat.Hom.hom g (ULift.up ())) hxy'
  · intro p
    let t : Cone (D ⋙ Scheme.forget) :=
      { pt := T
        π :=
          { app := fun i => TypeCat.ofHom fun _ => zStage p i.unop
            naturality := fun _ _ f => by
              ext
              exact (hzStage p f).symm } }
    let y : L.closedScheme := hlim.lift t (ULift.up ())
    have hycoord (E : Finset A) :
        (L.closedProjection.app (Opposite.op E)).base y = zStage p E := by
      simpa [y, t, zStage] using congrArg
        (fun g : T ⟶ Scheme.forget.obj (D.obj (Opposite.op E)) =>
          TypeCat.Hom.hom g (ULift.up ())) (hlim.fac t (Opposite.op E))
    refine ⟨y, ?_⟩
    rw [hstageValue y (∅ : Finset A), hycoord]
    show (closedStrataToBase (∅ : Finset A)).base
      ((L.closedStage (∅ : Finset A)).hom.base
        ((L.closedStage (∅ : Finset A)).inv.base (yStage p ∅))) = _
    rw [schemeIso_hom_inv_base_apply]
    exact hyStage p (∅ : Finset A)

/-- The morphism `X_w → X` induces a bijection from the limiting closed subscheme `Z` onto
`X = Spec A`. -/
@[stacks 0975 "bijection_on_z"]
theorem bijective_stratificationLimitClosedScheme_toBase :
    Function.Bijective (stratificationLimitInclusion (A := A) ≫
      Spec.map (CommRingCat.ofHom (stratificationColimitAlgebraMap (A := A)))).base :=
  stratificationLimit_closedScheme_bijective (stratificationLimit (A := A))

end AlgebraicGeometry.ProEtale

end
