module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimitOfSize

/-!
# Situation 0DKU at a limit of test schemes is a limit of schemes

The instance `AlgebraicGeometry.Space.ComplexesSituation.relativeDescentSituation` of
Situation 0DKU, built from a directed limit `T = lim Tᵢ` of affine test schemes over `Y` whose
underlying schemes form a limit in `Scheme`, satisfies
`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`: the projection `T ⟶ T_{i₀}` is
a morphism of affine schemes, and a representation of the base changes along an affine chart
`Z ⟶ T_{i₀}` is, on underlying schemes, the base change of the limit cone of the `Tᵢ` along
`Z ⟶ T_{i₀}`, which is a limit cone because pullback along a fixed morphism commutes with limits.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isSchemeLimit_relativeDescentSituation`.

## References

* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DLJ](https://stacks.math.columbia.edu/tag/0DLJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] CategoryTheory.Limits.comp_preservesLimitsOfShape in
/-- The functor to schemes preserves fibre products. -/
local instance preservesPullbacks_bigFppfOverToScheme :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

/-- A square is a pullback if its image under the Yoneda embedding is. -/
private theorem isPullback_of_isPullback_map_yoneda {C : Type*} [Category C] {A X Y Z : C}
    {a : A ⟶ X} {b : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {a' : yoneda.obj A ⟶ yoneda.obj X} {g' : yoneda.obj Y ⟶ yoneda.obj Z}
    (H : IsPullback a' (yoneda.map b) (yoneda.map f) g') (ha : yoneda.map a = a')
    (hg : yoneda.map g = g') : IsPullback a b f g := by
  subst ha hg
  exact IsPullback.of_map yoneda (yoneda.map_injective
    ((yoneda.map_comp _ _).trans (H.w.trans (yoneda.map_comp _ _).symm))) H

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS) {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  [Nonempty I] (hZ : B.Contains (⊤_ Scheme.{u})) (T : Iᵒᵖ ⥤ SchemesOver D.Y) (c : Cone T)

/-- **Situation 0DKU at a limit of affine test schemes is a limit of schemes on affine
charts.** -/
theorem isSchemeLimit_relativeDescentSituation
    (hc : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone c))
    (hT : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj (op i)).left)) (i₀ : I) :
    (D.relativeDescentSituation (hZ := hZ) (T := T) (c := c)
      (hc := hc) (hT := hT) (i₀ := i₀)).IsSchemeLimit := by
  set D' := D.relativeDescentSituation (hZ := hZ) (T := T) (c := c)
    (hc := hc) (hT := hT) (i₀ := i₀)
  let proj := CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y
  let F := proj ⋙ BigFppfOver.toScheme B S hS
  have hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj (proj.obj c.pt)) :=
    @Scheme.isAffine_of_isLimit _ _ _ _ hc (fun i => hT i.unop)
  refine ⟨?_, fun Z z R => ⟨?_⟩⟩
  · have : IsAffine ((BigFppfOver.toScheme B S hS).obj (proj.obj (T.obj (op D'.i₀)))) := hT i₀
    exact isAffineHom_of_presheaf
      ((presheaf_yoneda_map_iff B S hS
          (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance _).mpr
        (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
  · -- the maps of the representation, as morphisms of the site
    let P : ∀ k : D'.LaterIndex, R.W.obj (op k) ⟶ proj.obj (T.obj (op k.1)) := fun k =>
      Yoneda.fullyFaithful.preimage
        (R.p k : yoneda.obj _ ⟶ yoneda.obj (proj.obj (T.obj (op k.1))))
    have hP : ∀ k, yoneda.map (P k) = R.p k := fun k => Yoneda.fullyFaithful.map_preimage _
    let Pc : R.c.pt ⟶ proj.obj c.pt :=
      Yoneda.fullyFaithful.preimage (R.pc : yoneda.obj _ ⟶ yoneda.obj (proj.obj c.pt))
    have hPc : yoneda.map Pc = R.pc := Yoneda.fullyFaithful.map_preimage _
    let z₀ : (BigAffineFppf.inclusion B S hS).obj Z ⟶ proj.obj (T.obj (op i₀)) :=
      Yoneda.fullyFaithful.preimage (z : yoneda.obj _ ⟶ yoneda.obj (proj.obj (T.obj (op i₀))))
    have hz₀ : yoneda.map z₀ = z := Yoneda.fullyFaithful.map_preimage _
    -- the equations of the representation, in the site
    have hsq : ∀ k : D'.LaterIndex, IsPullback (P k) (R.q k)
        (proj.map (T.map (homOfLE k.2).op)) z₀ := fun k => by
      exact isPullback_of_isPullback_map_yoneda (R.isPullback k) (hP k) hz₀
    have hsqc : IsPullback Pc R.qc (proj.map (c.π.app (op i₀))) z₀ := by
      exact isPullback_of_isPullback_map_yoneda R.isPullback_pt hPc hz₀
    have hp : ∀ (i j : D'.LaterIndex) (h : i ≤ j),
        R.W.map (homOfLE h).op ≫ P i = P j ≫ proj.map (T.map (homOfLE h).op) := fun i j h =>
      yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_comp, hP, hP]
        exact R.map_p i j h)
    have hπp : ∀ k : D'.LaterIndex,
        R.c.π.app (op k) ≫ P k = Pc ≫ proj.map (c.π.app (op k.1)) := fun k =>
      yoneda.map_injective (by
        rw [Functor.map_comp, Functor.map_comp, hP, hPc]
        exact R.π_p k)
    -- the limit cone of the stages beyond `i₀`, in schemes
    have hL : IsLimit ((F.mapCone c).whisker D'.laterIndexInclusion.op) :=
      (Functor.Initial.isLimitWhiskerEquiv D'.laterIndexInclusion.op (F.mapCone c)).symm hc
    exact isLimitOfIsPullbackOfIsLimit (Y' := D'.laterIndexInclusion.op ⋙ T ⋙ F)
      D'.initialLaterIndex (fun k => k.2) hL ((BigFppfOver.toScheme B S hS).map z₀)
      ((BigFppfOver.toScheme B S hS).mapCone R.c)
      (fun k => (BigFppfOver.toScheme B S hS).map (P k))
      (fun k => (BigFppfOver.toScheme B S hS).map (R.q k))
      (fun k => (hsq k).map (BigFppfOver.toScheme B S hS))
      (fun i j h => ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        (((BigFppfOver.toScheme B S hS).congr_map (hp i j h)).trans
          ((BigFppfOver.toScheme B S hS).map_comp _ _)))
      (fun i j h => ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        ((BigFppfOver.toScheme B S hS).congr_map (R.map_q i j h)))
      ((BigFppfOver.toScheme B S hS).map Pc) ((BigFppfOver.toScheme B S hS).map R.qc)
      (hsqc.map (BigFppfOver.toScheme B S hS))
      (fun k => ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        (((BigFppfOver.toScheme B S hS).congr_map (hπp k)).trans
          ((BigFppfOver.toScheme B S hS).map_comp _ _)))
      (fun k => ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        ((BigFppfOver.toScheme B S hS).congr_map (R.π_q k)))

end ComplexesSituation

end AlgebraicGeometry.Space

end
