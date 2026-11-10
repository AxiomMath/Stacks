module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamily

/-!
# The group of coordinate changes of a Weierstrass equation and its action on `W`

Let `W = Spec(ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ])` be the Weierstrass scheme of Section 072S. A
coordinate change of a Weierstrass equation is a matrix `(u², s, 0; 0, u³, 0; r, t, 1)` of
`GL₃` with `u` a unit, and these form the group scheme `H = Spec(ℤ[u, s, r, t, 1/u])`. The
group `H` acts on `W`: a coordinate change transforms a Weierstrass equation into another one,
whose discriminant is that of the first divided by `u¹²`.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.coordinateChangeGroup` is the scheme `H`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.curveAt` is the Weierstrass equation over
  `Γ(T, ⊤)` classified by a morphism `T ⟶ W`, and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.toBase` is the morphism `T ⟶ W`
  classifying a Weierstrass equation over `Γ(T, ⊤)` with invertible discriminant.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.changeAt` is the coordinate change over
  `Γ(T, ⊤)` classified by a morphism `T ⟶ H`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.act` is the action `H × W ⟶ W` on
  `T`-points.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.smooth_coordinateChangeGroupToSpecZ`:
  the group of coordinate changes is smooth over `Spec(ℤ)`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.curveAt_toBase` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.toBase_curveAt`: a morphism `T ⟶ W` is the
  same thing as a Weierstrass equation over `Γ(T, ⊤)` with invertible discriminant.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.comp_act`: the action is natural in `T`.

## Implementation notes

The coordinate changes are Mathlib's `WeierstrassCurve.VariableChange`, acting through
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)`. The coordinates of `H` are the variables `0`, `1`, `2`,
`3` of `ℤ[u, s, r, t]`, standing for `u`, `s`, `r`, `t`. The integers are the canonical universe
copy `ULift.{u} ℤ`, as in Section 072S.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

/-! ### The group of coordinate changes -/

/-- The ring `ℤ[u, s, r, t, 1/u]` of the group of coordinate changes of a Weierstrass equation:
the polynomial ring on the four entries `u`, `s`, `r`, `t` of the matrices displayed in Section
072S, with `u` inverted. -/
abbrev coordinateChangeRing : Type u :=
  Localization.Away (MvPolynomial.X 0 : MvPolynomial (Fin 4) (ULift.{u} ℤ))

/-- The group `H ⊂ GL₃,ℤ` of coordinate changes of a Weierstrass equation, as a scheme: the
matrices `(u², s, 0; 0, u³, 0; r, t, 1)` with `u` a unit and `s`, `r`, `t` arbitrary form the
spectrum of `ℤ[u, s, r, t, 1/u]`. -/
abbrev coordinateChangeGroup : Scheme.{u} := Spec (CommRingCat.of coordinateChangeRing.{u})

/-- The structure morphism `H ⟶ Spec(ℤ)` of the group of coordinate changes. -/
def coordinateChangeGroupToSpecZ :
    coordinateChangeGroup.{u} ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
  specULiftZIsTerminal.from coordinateChangeGroup.{u}

/-- The group of coordinate changes of a Weierstrass equation is smooth over `Spec(ℤ)`: it is an
open subscheme of affine `4`-space, the locus where the coordinate `u` is invertible. -/
theorem smooth_coordinateChangeGroupToSpecZ : Smooth coordinateChangeGroupToSpecZ.{u} := by
  have hloc : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap (MvPolynomial (Fin 4) (ULift.{u} ℤ)) coordinateChangeRing.{u}))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    simpa only [CommRingCat.hom_ofHom] using RingHom.smooth_algebraMap.mpr
      (Algebra.Smooth.of_isLocalization_Away
        (MvPolynomial.X 0 : MvPolynomial (Fin 4) (ULift.{u} ℤ)))
  have hpoly : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (MvPolynomial (Fin 4) (ULift.{u} ℤ))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    simpa only [CommRingCat.hom_ofHom] using
      RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  have key : coordinateChangeGroupToSpecZ.{u} =
      Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial (Fin 4) (ULift.{u} ℤ)) coordinateChangeRing.{u})) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (ULift.{u} ℤ) (MvPolynomial (Fin 4) (ULift.{u} ℤ)))) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [key]
  exact MorphismProperty.comp_mem _ _ _ hloc hpoly

/-- The universal coordinate change, over the ring of `H`: its entries are the coordinates
`u`, `r`, `s`, `t`. -/
def universalChange : WeierstrassCurve.VariableChange coordinateChangeRing.{u} where
  u := (IsLocalization.Away.algebraMap_isUnit
    (MvPolynomial.X 0 : MvPolynomial (Fin 4) (ULift.{u} ℤ))).unit
  r := algebraMap (MvPolynomial (Fin 4) (ULift.{u} ℤ)) coordinateChangeRing.{u} (X 2)
  s := algebraMap (MvPolynomial (Fin 4) (ULift.{u} ℤ)) coordinateChangeRing.{u} (X 1)
  t := algebraMap (MvPolynomial (Fin 4) (ULift.{u} ℤ)) coordinateChangeRing.{u} (X 3)

/-! ### Points of affine schemes -/

/-- The ring homomorphism `R ⟶ Γ(T, ⊤)` attached to a morphism `T ⟶ Spec R`. -/
def ringOf {T : Scheme.{u}} {R : CommRingCat.{u}} (g : T ⟶ Spec R) : R ⟶ Γ(T, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ g.appTop

/-- The morphism `T ⟶ Spec R` attached to a ring homomorphism `R ⟶ Γ(T, ⊤)`. -/
def homOfRing {T : Scheme.{u}} {R : CommRingCat.{u}} (φ : R ⟶ Γ(T, ⊤)) : T ⟶ Spec R :=
  T.toSpecΓ ≫ Spec.map φ

/-- The ring homomorphism of the morphism attached to `φ : R ⟶ Γ(T, ⊤)` is `φ`. -/
theorem ringOf_homOfRing {T : Scheme.{u}} {R : CommRingCat.{u}} (φ : R ⟶ Γ(T, ⊤)) :
    ringOf (homOfRing φ) = φ := by
  simp [ringOf, homOfRing]

/-- The morphism attached to the ring homomorphism of `g : T ⟶ Spec R` is `g`. -/
theorem homOfRing_ringOf {T : Scheme.{u}} {R : CommRingCat.{u}} (g : T ⟶ Spec R) :
    homOfRing (ringOf g) = g := by
  rw [homOfRing, ringOf, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The ring homomorphism of `f ≫ g` is that of `g` followed by `f.appTop`. -/
theorem ringOf_comp {T T' : Scheme.{u}} {R : CommRingCat.{u}} (f : T' ⟶ T) (g : T ⟶ Spec R) :
    ringOf (f ≫ g) = ringOf g ≫ f.appTop := by
  simp [ringOf]

/-! ### Points of `W` are Weierstrass equations -/

/-- Any two ring homomorphisms `ULift ℤ →+* R` agree at every element. -/
theorem ulift_int_ringHom_ext {R : Type*} [Semiring R] (f g : ULift.{u} ℤ →+* R)
    (n : ULift.{u} ℤ) : f n = g n := by
  have h := RingHom.ext_int (f.comp ULift.ringEquiv.symm.toRingHom)
    (g.comp ULift.ringEquiv.symm.toRingHom)
  have := congrArg (fun φ : ℤ →+* R => φ n.down) h
  exact this

/-- Two ring homomorphisms from a polynomial ring over `ULift ℤ` agreeing on the variables are
equal. -/
private theorem mvPolynomial_ulift_ringHom_ext {σ R : Type*} [Semiring R]
    (f g : MvPolynomial σ (ULift.{u} ℤ) →+* R) (h : ∀ i, f (X i) = g (X i)) : f = g :=
  MvPolynomial.ringHom_ext (fun n => ulift_int_ringHom_ext (f.comp C) (g.comp C) n) h

/-- The morphism attached to a ring homomorphism equal to that of `g : T ⟶ Spec R` is `g`. -/
private theorem homOfRing_ofHom_eq {T : Scheme.{u}} {R : CommRingCat.{u}} {g : T ⟶ Spec R}
    {ψ : R ⟶ Γ(T, ⊤)} (h : ψ.hom = (ringOf g).hom) : homOfRing ψ = g := by
  rw [← homOfRing_ringOf g]
  congr 1
  ext1
  exact h

/-- The Weierstrass equation over `Γ(T, ⊤)` classified by a morphism `T ⟶ W`. -/
def curveAt {T : Scheme.{u}} (b : T ⟶ base.{u}) : WeierstrassCurve Γ(T, ⊤) :=
  curve.{u}.map (ringOf b).hom

/-- The Weierstrass equation classified by a morphism `T ⟶ W` has invertible discriminant. -/
instance {T : Scheme.{u}} (b : T ⟶ base.{u}) : (curveAt b).IsElliptic := by
  unfold curveAt; infer_instance

/-- The evaluation `ℤ[a₁, a₂, a₃, a₄, a₆] → R` at the coefficients of a Weierstrass equation. -/
def coeffEval {R : Type u} [CommRing R] (C : WeierstrassCurve R) : coeffRing.{u} →+* R :=
  MvPolynomial.eval₂Hom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)
    ![C.a₁, C.a₂, C.a₃, C.a₄, C.a₆]

/-- The generic Weierstrass equation, evaluated at the coefficients of `C`, is `C`. -/
theorem generic_map_coeffEval {R : Type u} [CommRing R] (C : WeierstrassCurve R) :
    generic.{u}.map (coeffEval C) = C := by
  ext <;> simp [generic, coeffEval, WeierstrassCurve.map]

/-- The ring homomorphism `ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ] → R` attached to a Weierstrass equation
over `R` with invertible discriminant. -/
def baseRingHom {R : Type u} [CommRing R] (C : WeierstrassCurve R) [C.IsElliptic] :
    baseRing.{u} →+* R :=
  IsLocalization.Away.lift discriminant.{u} (g := coeffEval C) (by
    rw [discriminant, ← WeierstrassCurve.map_Δ, generic_map_coeffEval]
    exact C.isUnit_Δ)

/-- The universal Weierstrass equation over `W`, pushed forward along `baseRingHom C`, is `C`. -/
theorem curve_map_baseRingHom {R : Type u} [CommRing R] (C : WeierstrassCurve R)
    [C.IsElliptic] : curve.{u}.map (baseRingHom C) = C := by
  rw [curve, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  have : (baseRingHom C).comp (algebraMap coeffRing.{u} baseRing.{u}) = coeffEval C :=
    IsLocalization.Away.lift_comp _ _
  rw [this, generic_map_coeffEval]

/-- A ring homomorphism `φ : ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ] → R` pushing the universal Weierstrass
equation forward to `C` is `baseRingHom C`. -/
theorem baseRingHom_eq_of_curve_map {R : Type u} [CommRing R] (φ : baseRing.{u} →+* R)
    (C : WeierstrassCurve R) [C.IsElliptic] (h : curve.{u}.map φ = C) :
    φ = baseRingHom C := by
  refine IsLocalization.ringHom_ext (Submonoid.powers discriminant.{u}) ?_
  refine mvPolynomial_ulift_ringHom_ext _ _ (fun i => ?_)
  rw [baseRingHom, IsLocalization.Away.lift_comp]
  subst h
  fin_cases i <;> simp [coeffEval, curve, generic, WeierstrassCurve.baseChange,
    WeierstrassCurve.map]

/-- The morphism `T ⟶ W` classifying a Weierstrass equation over `Γ(T, ⊤)` with invertible
discriminant. -/
def toBase {T : Scheme.{u}} (C : WeierstrassCurve Γ(T, ⊤)) [C.IsElliptic] : T ⟶ base.{u} :=
  homOfRing (CommRingCat.ofHom (baseRingHom C))

/-- The Weierstrass equation classified by `toBase C` is `C`. -/
@[simp]
theorem curveAt_toBase {T : Scheme.{u}} (C : WeierstrassCurve Γ(T, ⊤)) [C.IsElliptic] :
    curveAt (toBase C) = C := by
  rw [curveAt, toBase, ringOf_homOfRing, CommRingCat.hom_ofHom, curve_map_baseRingHom]

/-- The morphism classifying the Weierstrass equation `curveAt b` is `b`. -/
@[simp]
theorem toBase_curveAt {T : Scheme.{u}} (b : T ⟶ base.{u}) : toBase (curveAt b) = b := by
  exact homOfRing_ofHom_eq (baseRingHom_eq_of_curve_map _ _ rfl).symm

/-- Two morphisms `T ⟶ W` classifying the same Weierstrass equation are equal. -/
theorem eq_of_curveAt_eq {T : Scheme.{u}} {b b' : T ⟶ base.{u}} (h : curveAt b = curveAt b') :
    b = b' := by
  rw [← toBase_curveAt b, ← toBase_curveAt b']
  congr 1

/-- The Weierstrass equation classified by `f ≫ b` is the base change of `curveAt b` along
`f.appTop`. -/
theorem curveAt_comp {T T' : Scheme.{u}} (f : T' ⟶ T) (b : T ⟶ base.{u}) :
    curveAt (f ≫ b) = (curveAt b).map f.appTop.hom := by
  rw [curveAt, curveAt, ringOf_comp, WeierstrassCurve.map_map]
  rfl

/-! ### Points of `H` are coordinate changes -/

/-- The coordinate change over `Γ(T, ⊤)` classified by a morphism `T ⟶ H`. -/
def changeAt {T : Scheme.{u}} (h : T ⟶ coordinateChangeGroup.{u}) :
    WeierstrassCurve.VariableChange Γ(T, ⊤) :=
  universalChange.{u}.map (ringOf h).hom

/-- The coordinate change classified by `f ≫ h` is the base change of `changeAt h` along
`f.appTop`. -/
theorem changeAt_comp {T T' : Scheme.{u}} (f : T' ⟶ T) (h : T ⟶ coordinateChangeGroup.{u}) :
    changeAt (f ≫ h) = (changeAt h).map f.appTop.hom := by
  rw [changeAt, changeAt, ringOf_comp, WeierstrassCurve.VariableChange.map_map]
  rfl

/-- The ring homomorphism `ℤ[u, s, r, t, 1/u] → R` attached to a coordinate change over `R`. -/
def changeRingHom {R : Type u} [CommRing R] (C : WeierstrassCurve.VariableChange R) :
    coordinateChangeRing.{u} →+* R :=
  IsLocalization.Away.lift (MvPolynomial.X 0 : MvPolynomial (Fin 4) (ULift.{u} ℤ))
    (g := MvPolynomial.eval₂Hom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)
      ![(C.u : R), C.s, C.r, C.t]) (by simp)

/-- The universal coordinate change, pushed forward along `changeRingHom C`, is `C`. -/
theorem universalChange_map_changeRingHom {R : Type u} [CommRing R]
    (C : WeierstrassCurve.VariableChange R) :
    universalChange.{u}.map (changeRingHom C) = C := by
  have h : ∀ p, changeRingHom C (algebraMap _ coordinateChangeRing.{u} p) =
      MvPolynomial.eval₂Hom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)
        ![(C.u : R), C.s, C.r, C.t] p := fun p => IsLocalization.Away.lift_eq _ _ p
  ext
  · change changeRingHom C (algebraMap _ coordinateChangeRing.{u} (X 0)) = C.u
    rw [h]; simp
  · change changeRingHom C (algebraMap _ coordinateChangeRing.{u} (X 2)) = C.r
    rw [h]; simp
  · change changeRingHom C (algebraMap _ coordinateChangeRing.{u} (X 1)) = C.s
    rw [h]; simp
  · change changeRingHom C (algebraMap _ coordinateChangeRing.{u} (X 3)) = C.t
    rw [h]; simp

/-- A ring homomorphism `φ : ℤ[u, s, r, t, 1/u] → R` pushing the universal coordinate change
forward to `C` is `changeRingHom C`. -/
theorem changeRingHom_eq_of_map {R : Type u} [CommRing R] (φ : coordinateChangeRing.{u} →+* R)
    (C : WeierstrassCurve.VariableChange R) (h : universalChange.{u}.map φ = C) :
    φ = changeRingHom C := by
  refine IsLocalization.ringHom_ext (Submonoid.powers
    (MvPolynomial.X 0 : MvPolynomial (Fin 4) (ULift.{u} ℤ))) ?_
  refine mvPolynomial_ulift_ringHom_ext _ _ (fun i => ?_)
  rw [changeRingHom, IsLocalization.Away.lift_comp]
  subst h
  fin_cases i <;> simp [universalChange, WeierstrassCurve.VariableChange.map]

/-- The morphism `T ⟶ H` classifying a coordinate change over `Γ(T, ⊤)`. -/
def toGroup {T : Scheme.{u}} (C : WeierstrassCurve.VariableChange Γ(T, ⊤)) :
    T ⟶ coordinateChangeGroup.{u} :=
  homOfRing (CommRingCat.ofHom (changeRingHom C))

/-- The coordinate change classified by `toGroup C` is `C`. -/
@[simp]
theorem changeAt_toGroup {T : Scheme.{u}} (C : WeierstrassCurve.VariableChange Γ(T, ⊤)) :
    changeAt (toGroup C) = C := by
  rw [changeAt, toGroup, ringOf_homOfRing, CommRingCat.hom_ofHom,
    universalChange_map_changeRingHom]

/-- The morphism classifying the coordinate change `changeAt h` is `h`. -/
@[simp]
theorem toGroup_changeAt {T : Scheme.{u}} (h : T ⟶ coordinateChangeGroup.{u}) :
    toGroup (changeAt h) = h := by
  exact homOfRing_ofHom_eq (changeRingHom_eq_of_map _ _ rfl).symm

/-! ### The action of `H` on `W` -/

/-- The action of `H` on `W` on `T`-points: a coordinate change `h` and a Weierstrass equation
`b` give the transformed Weierstrass equation `h • b`. -/
def act {T : Scheme.{u}} (h : T ⟶ coordinateChangeGroup.{u}) (b : T ⟶ base.{u}) :
    T ⟶ base.{u} :=
  toBase (changeAt h • curveAt b)

/-- The Weierstrass equation classified by `act h b` is `changeAt h • curveAt b`. -/
@[simp]
theorem curveAt_act {T : Scheme.{u}} (h : T ⟶ coordinateChangeGroup.{u}) (b : T ⟶ base.{u}) :
    curveAt (act h b) = changeAt h • curveAt b :=
  curveAt_toBase _

/-- The action of `H` on `W` on `T`-points is natural in `T`. -/
theorem comp_act {T T' : Scheme.{u}} (f : T' ⟶ T) (h : T ⟶ coordinateChangeGroup.{u})
    (b : T ⟶ base.{u}) : f ≫ act h b = act (f ≫ h) (f ≫ b) := by
  refine eq_of_curveAt_eq ?_
  rw [curveAt_comp, curveAt_act, curveAt_act, changeAt_comp, curveAt_comp,
    WeierstrassCurve.map_variableChange]

/-! ### The product `H × W` -/

/-- The product `H × W` of the group of coordinate changes with the Weierstrass scheme, over
`Spec(ℤ)`. -/
abbrev coordinateChangeProduct : Scheme.{u} :=
  Limits.pullback coordinateChangeGroupToSpecZ.{u} (specULiftZIsTerminal.from base.{u})

/-- The projection `H × W ⟶ H`. -/
abbrev productToGroup : coordinateChangeProduct.{u} ⟶ coordinateChangeGroup.{u} :=
  Limits.pullback.fst _ _

/-- The projection `H × W ⟶ W`. -/
abbrev productToBase : coordinateChangeProduct.{u} ⟶ base.{u} :=
  Limits.pullback.snd _ _

/-- The action morphism `H × W ⟶ W`. -/
def actionMap : coordinateChangeProduct.{u} ⟶ base.{u} := act productToGroup productToBase

/-- The `T`-point of `H × W` with coordinates `h` and `b`. -/
def productLift {T : Scheme.{u}} (h : T ⟶ coordinateChangeGroup.{u}) (b : T ⟶ base.{u}) :
    T ⟶ coordinateChangeProduct.{u} :=
  Limits.pullback.lift h b (specULiftZIsTerminal.hom_ext _ _)

/-- The `H`-coordinate of `productLift h b` is `h`. -/
@[simp]
theorem productLift_fst {T : Scheme.{u}} (h : T ⟶ coordinateChangeGroup.{u})
    (b : T ⟶ base.{u}) : productLift h b ≫ productToGroup = h :=
  Limits.pullback.lift_fst _ _ _

/-- The `W`-coordinate of `productLift h b` is `b`. -/
@[simp]
theorem productLift_snd {T : Scheme.{u}} (h : T ⟶ coordinateChangeGroup.{u})
    (b : T ⟶ base.{u}) : productLift h b ≫ productToBase = b :=
  Limits.pullback.lift_snd _ _ _

/-- The action morphism `H × W ⟶ W` sends the `T`-point `productLift h b` to `act h b`. -/
theorem productLift_actionMap {T : Scheme.{u}} (h : T ⟶ coordinateChangeGroup.{u})
    (b : T ⟶ base.{u}) : productLift h b ≫ actionMap = act h b := by
  rw [actionMap, comp_act, productLift_fst, productLift_snd]

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end
