module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates of the faces of a commutative cube

Consider eight categories arranged as a cube whose four vertical edges carry adjunctions
`pY ⊣ PY`, `pX ⊣ PX`, `pY' ⊣ PY'`, `pX' ⊣ PX'`, whose four "base-change" edges carry adjunctions
`qY' ⊣ QY'`, `qX' ⊣ QX'`, `rY ⊣ RY`, `rX ⊣ RX`, and whose remaining four edges are functors
`F`, `Fb`, `F'`, `F'b`:

```
   Ys ---F---> Xs           (top face, "small")
   |  \         | \
  pY   rY      pX  rX
   v     v      v    v
   Yb  Y's -F'-> Xb  X's
     \  |         \  |
     qY' pY'      qX' pX'
        v  v         v  v
        Y'b --F'b--> X'b   (bottom face, "big")
```

Each face is a square of right adjoints commuting up to a natural transformation:
`θf : PY ⋙ F ⟶ Fb ⋙ PX`, `θf' : PY' ⋙ F' ⟶ F'b ⋙ PX'`, `cs : RY ⋙ F ⟶ F' ⋙ RX`,
`cb : QY' ⋙ Fb ⟶ F'b ⋙ QX'`, and the two side faces `θg : PX' ⋙ RX ⟶ QX' ⋙ PX`,
`θg' : QY' ⋙ PY ⟶ PY' ⋙ RY`. The cube commutes when the two composites of three faces from
`QY' ⋙ PY ⋙ F` to `F'b ⋙ QX' ⋙ PX` agree.

The main result says that, if the cube of right adjoints commutes, then so does the cube of
mates: the base change of the mate `F ⋙ pX ⟶ pY ⋙ Fb` of the top face along the back face is
the mate of the bottom face composed with the mate of the front face, transported along the
inverse-image squares conjugate to the two side faces.

This is pure 2-category theory: it follows from the compatibility of the mates correspondence
with vertical composition of squares (`CategoryTheory.mateEquiv_hcomp`) and with whiskering by
conjugates (`CategoryTheory.mateEquiv_conjugateEquiv_vcomp`,
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp`), and injectivity of the mates correspondence.

## Main results

* `CategoryTheory.mateEquiv_symm_vComp_eq_of_cube`: the cube of mates commutes.
* `CategoryTheory.isIso_map_mateEquiv_symm_app_of_isIso_unit`: when both vertical units
  are isomorphisms, the mate of an invertible square becomes invertible after applying the right
  adjoint on its target.
-/

@[expose] public section

open CategoryTheory Functor TwoSquare

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

section Cube

variable {Ys : Type u₁} {Xs : Type u₂} {Yb : Type u₃} {Xb : Type u₄}
  {Y's : Type u₅} {X's : Type u₆} {Y'b : Type u₇} {X'b : Type u₈}
  [Category.{v₁} Ys] [Category.{v₂} Xs] [Category.{v₃} Yb] [Category.{v₄} Xb]
  [Category.{v₅} Y's] [Category.{v₆} X's] [Category.{v₇} Y'b] [Category.{v₈} X'b]
  {F : Ys ⥤ Xs} {Fb : Yb ⥤ Xb} {F' : Y's ⥤ X's} {F'b : Y'b ⥤ X'b}
  {pY : Ys ⥤ Yb} {PY : Yb ⥤ Ys} {pX : Xs ⥤ Xb} {PX : Xb ⥤ Xs}
  {pY' : Y's ⥤ Y'b} {PY' : Y'b ⥤ Y's} {pX' : X's ⥤ X'b} {PX' : X'b ⥤ X's}
  {qY' : Yb ⥤ Y'b} {QY' : Y'b ⥤ Yb} {qX' : Xb ⥤ X'b} {QX' : X'b ⥤ Xb}
  {rY : Ys ⥤ Y's} {RY : Y's ⥤ Ys} {rX : Xs ⥤ X's} {RX : X's ⥤ Xs}
  (aY : pY ⊣ PY) (aX : pX ⊣ PX) (aY' : pY' ⊣ PY') (aX' : pX' ⊣ PX')
  (bY : qY' ⊣ QY') (bX : qX' ⊣ QX') (cY : rY ⊣ RY) (cX : rX ⊣ RX)

/-- **The cube of mates commutes.** In a cube of adjunctions whose six faces of right adjoints
commute up to the given natural transformations, and whose cube of right adjoints commutes, the
base change along the back face of the mate of the top face equals the mate of the bottom face
composed with the mate of the front face, transported along the two inverse-image squares
conjugate to the side faces. -/
theorem mateEquiv_symm_vComp_eq_of_cube
    (θf : TwoSquare PY Fb F PX) (θf' : TwoSquare PY' F'b F' PX')
    (cs : TwoSquare RY F' F RX) (cb : TwoSquare QY' F'b Fb QX')
    (ρg : pX ⋙ qX' ⟶ rX ⋙ pX') (ρg' : rY ⋙ pY' ⟶ pY ⋙ qY')
    (cube : cb ≫ₕ θf =
      ((θf' ≫ₕ cs).whiskerBottom (conjugateEquiv (cX.comp aX') (aX.comp bX) ρg)).whiskerTop
        (conjugateEquiv (aY.comp bY) (cY.comp aY') ρg')) :
    (mateEquiv aY aX).symm θf ≫ᵥ (mateEquiv bY bX).symm cb =
      (((mateEquiv cY cX).symm cs ≫ᵥ (mateEquiv aY' aX').symm θf').whiskerRight ρg).whiskerLeft
        ρg' := by
  apply (mateEquiv (aY.comp bY) (aX.comp bX)).injective
  rwa [mateEquiv_hcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    conjugateEquiv_mateEquiv_vcomp (aY.comp bY) (cY.comp aY') (aX.comp bX),
    mateEquiv_conjugateEquiv_vcomp (cY.comp aY') (cX.comp aX') (aX.comp bX),
    mateEquiv_hcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Invertibility through the cube.** In the situation of
`CategoryTheory.mateEquiv_symm_vComp_eq_of_cube`, suppose that the mates of the front and back
faces and the two inverse-image squares are invertible, and that the mate of the bottom face
becomes invertible after applying `PX'`. Then the mate of the top face becomes invertible after
applying `qX'` and then `PX'`. -/
theorem isIso_map_map_mateEquiv_symm_app_of_cube
    (θf : TwoSquare PY Fb F PX) (θf' : TwoSquare PY' F'b F' PX')
    (cs : TwoSquare RY F' F RX) (cb : TwoSquare QY' F'b Fb QX')
    (ρg : pX ⋙ qX' ⟶ rX ⋙ pX') (ρg' : rY ⋙ pY' ⟶ pY ⋙ qY')
    (cube : cb ≫ₕ θf =
      ((θf' ≫ₕ cs).whiskerBottom (conjugateEquiv (cX.comp aX') (aX.comp bX) ρg)).whiskerTop
        (conjugateEquiv (aY.comp bY) (cY.comp aY') ρg'))
    (hcb : IsIso ((mateEquiv bY bX).symm cb))
    (hcs : IsIso ((mateEquiv cY cX).symm cs)) [IsIso ρg] [IsIso ρg']
    (hθf' : ∀ M, IsIso (PX'.map (((mateEquiv aY' aX').symm θf').app M))) (K : Ys) :
    IsIso (PX'.map (qX'.map (((mateEquiv aY aX).symm θf).app K))) := by
  have e := congrArg (fun t => PX'.map (t.app K))
    (mateEquiv_symm_vComp_eq_of_cube aY aX aY' aX' bY bX cY cX θf θf' cs cb ρg ρg' cube)
  simp only [vComp_app, TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
    Functor.comp_obj, Functor.map_comp] at e
  have := hθf' (rY.obj K)
  have h : IsIso (PX'.map (qX'.map (((mateEquiv aY aX).symm θf).app K)) ≫
      PX'.map (((mateEquiv bY bX).symm cb).app (pY.obj K))) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (PX'.map (((mateEquiv bY bX).symm cb).app (pY.obj K)))

end Cube

section UnitIso

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {G : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} G]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ G} {R₂ : G ⥤ E} {H₁ : C ⥤ E} {H₂ : D ⥤ G}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- If the units of both adjunctions are isomorphisms, the mate `H₁ ⋙ L₂ ⟶ L₁ ⋙ H₂` of an
invertible square `R₁ ⋙ H₁ ⟶ H₂ ⋙ R₂` becomes invertible after applying `R₂`: by the unit
description of the mate (`CategoryTheory.unit_mateEquiv_symm`), the unit of `adj₂` followed by
`R₂` of the mate at `c` is `H₁` of the unit of `adj₁` at `c` followed by the square, and the
other three maps are isomorphisms. -/
theorem isIso_map_mateEquiv_symm_app_of_isIso_unit (θ : TwoSquare R₁ H₂ H₁ R₂)
    [IsIso θ] [IsIso adj₁.unit] [IsIso adj₂.unit] (c : C) :
    IsIso (R₂.map (((mateEquiv adj₁ adj₂).symm θ).app c)) := by
  have e : R₂.map (((mateEquiv adj₁ adj₂).symm θ).app c) =
      inv (adj₂.unit.app (H₁.obj c)) ≫ H₁.map (adj₁.unit.app c) ≫ θ.app (L₁.obj c) := by
    rw [IsIso.eq_inv_comp]
    exact (unit_mateEquiv_symm adj₁ adj₂ θ c).symm
  rw [e]
  infer_instance

end UnitIso

end CategoryTheory
