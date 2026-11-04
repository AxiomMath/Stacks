module

public import StacksFrontier.AlgebraicGeometry.Spaces.StalkPointHigherDirectImageVanishing

/-!
# The closed fibre over the local ring at a point

For a point `y` of a Noetherian scheme `Y` of the site, the residue map `𝒪_{Y,y} ⟶ κ(y)` gives a
closed immersion `ι : Spec κ(y) ⟶ Spec 𝒪_{Y,y}` of objects of the site, lying over `Y`.  A
cartesian square exhibiting `h_U ⟶ X` as the base change of `Spec κ(y) ⟶ Y` along `f : X ⟶ h_Y`
factors through any cartesian square `X' = X ×_Y Spec 𝒪_{Y,y}`, and the factor is a cartesian
square over `ι`: "the fibres `X_y` and `X'_y` are identified", as the proof of Stacks 0D39 puts
it.

## Main definitions

* `AlgebraicGeometry.Space.residueToStalkPointHom`: `ι : Spec κ(y) ⟶ Spec 𝒪_{Y,y}`.
* `AlgebraicGeometry.Space.fibreToStalkBaseChange`: the factorization `h_U ⟶ X'`.

## Main results

* `AlgebraicGeometry.Space.isPullback_fibreToStalkBaseChange`: it is cartesian over `ι`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section

variable (Y : BigFppfOver B S hS)
  [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
  (y : (BigFppfOver.toScheme B S hS).obj Y)

/-- **The closed immersion `Spec κ(y) ⟶ Spec 𝒪_{Y,y}`**, as a morphism of the site. -/
def residueToStalkPointHom : residuePointObject Y y ⟶ stalkPointObject Y y :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (((BigFppfOver.toScheme B S hS).obj Y).residue y)))
    (ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm)

/-- On underlying schemes, `ι` is `Spec` of the residue map `𝒪_{Y,y} ⟶ κ(y)`. -/
theorem map_residueToStalkPointHom :
    (BigFppfOver.toScheme B S hS).map (residueToStalkPointHom Y y) =
      Spec.map (((BigFppfOver.toScheme B S hS).obj Y).residue y) :=
  rfl

/-- `ι` followed by `Spec 𝒪_{Y,y} ⟶ Y` is the point `Spec κ(y) ⟶ Y`. -/
theorem residueToStalkPointHom_comp_stalkPointHom :
    residueToStalkPointHom Y y ≫ stalkPointHom Y y = residuePointHom Y y :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ rfl)

/-- `ι : Spec κ(y) ⟶ Spec 𝒪_{Y,y}` is a closed immersion of schemes. -/
instance isClosedImmersion_residueToStalkPointHom :
    AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (residueToStalkPointHom Y y)) :=
  inferInstanceAs (AlgebraicGeometry.IsClosedImmersion
    (Spec.map (((BigFppfOver.toScheme B S hS).obj Y).residue y)))

/-- The scheme `Spec 𝒪_{Y,y}` underlying the stalk point is affine. -/
instance isAffine_stalkPointObject :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (stalkPointObject Y y)) :=
  inferInstanceAs (IsAffine (Spec (.of (((BigFppfOver.toScheme B S hS).obj Y).presheaf.stalk y))))

/-- The scheme `Spec κ(y)` underlying the residue point is affine. -/
instance isAffine_residuePointObject :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (residuePointObject Y y)) :=
  inferInstanceAs (IsAffine (Spec (.of (((BigFppfOver.toScheme B S hS).obj Y).residueField y))))

end

section Square

variable {Y : BigFppfOver B S hS}
  [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
  {y : (BigFppfOver.toScheme B S hS).obj Y} {X : AlgebraicSpaces B S hS}
  {f : X ⟶ representedAlgebraicSpace B S hS Y} {U : BigFppfOver B S hS}
  {p : yoneda.obj U ⟶ X.1} {q : U ⟶ residuePointObject Y y}
  (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map (residuePointHom Y y)))
  {X' : AlgebraicSpaces B S hS} {q' : X' ⟶ X}
  {f' : X' ⟶ representedAlgebraicSpace B S hS (stalkPointObject Y y)}
  (sq : IsPullback q' f' f (representedSpaceMap B S hS (stalkPointHom Y y)))

include hsq sq in
/-- **The fibre factors through the base change to the local ring.** -/
def fibreToStalkBaseChange : yoneda.obj U ⟶ X'.1 :=
  (AlgebraicSpaces.isPullback_hom B S hS sq).lift p
    (yoneda.map (q ≫ residueToStalkPointHom Y y)) (by
      rw [hsq.w, ← residueToStalkPointHom_comp_stalkPointHom, Functor.map_comp,
        Functor.map_comp, Category.assoc]
      rfl)

/-- The factorization `h_U ⟶ X'` followed by `q' : X' ⟶ X` is the given map `h_U ⟶ X`. -/
theorem fibreToStalkBaseChange_comp : fibreToStalkBaseChange hsq sq ≫ q'.hom = p :=
  (AlgebraicSpaces.isPullback_hom B S hS sq).lift_fst _ _ _

/-- The factorization `h_U ⟶ X'` followed by `f' : X' ⟶ h_{Spec 𝒪_{Y,y}}` is `h_U ⟶ h_{Spec κ(y)}`
followed by `ι`. -/
theorem fibreToStalkBaseChange_comp_f' :
    fibreToStalkBaseChange hsq sq ≫ f'.hom =
      yoneda.map q ≫ yoneda.map (residueToStalkPointHom Y y) :=
  ((AlgebraicSpaces.isPullback_hom B S hS sq).lift_snd _ _ _).trans (Functor.map_comp _ _ _)

/-- **The fibre is the fibre of the base change over the closed point.** -/
theorem isPullback_fibreToStalkBaseChange :
    IsPullback (fibreToStalkBaseChange hsq sq) (yoneda.map q) f'.hom
      (yoneda.map (residueToStalkPointHom Y y)) := by
  refine IsPullback.of_right ?_ (fibreToStalkBaseChange_comp_f' hsq sq)
    (AlgebraicSpaces.isPullback_hom B S hS sq)
  rw [fibreToStalkBaseChange_comp]
  have e : yoneda.map (residueToStalkPointHom Y y) ≫
      (representedSpaceMap B S hS (stalkPointHom Y y)).hom = yoneda.map (residuePointHom Y y) := by
    rw [← residueToStalkPointHom_comp_stalkPointHom, Functor.map_comp]
    rfl
  rw [e]
  exact hsq

end Square

end AlgebraicGeometry.Space

end
