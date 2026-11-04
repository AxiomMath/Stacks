module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Pushforward

/-!
# The base-change comparison carries a unit to a unit

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a commuting square of schemes. Pulling back along `g` and `g'` turns the unit of
`f^* ⊣ f_*` into a morphism `g^* M ⟶ g^* f_* f^* M`, and the degree-zero base-change
comparison `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange` continues it to
`f'_* (g')^* f^* M`. The canonical identification of the two composite inverse images around
the square rewrites the target as `f'_* (f')^* g^* M`, and the resulting morphism is the unit
of `f'^* ⊣ f'_*` at `g^* M`. That is the statement proved here.

Nothing about schemes beyond the four pullback-pushforward adjunctions is used: the identity is
the componentwise form of the fact that the base-change comparison is a mate, together with the
observation that the direct-image identification `g'_* f_* ≅ f'_* g_*` is the conjugate of the
inverse-image identification `f^* g'^* ≅ g^* f'^*`. No flatness, cartesianness or affineness
hypothesis is needed.

## Main definitions

* `Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareNatIso`: the canonical identification
  `f^* ⋙ (g')^* ≅ g^* ⋙ (f')^*` of the two composite inverse images around the square.
* `Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareIso`: its component at a module,
  `(g')^* f^* M ≅ (f')^* g^* M`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChange.conjugateEquiv_pullbackSquareNatIso_inv`: the
  conjugate of `pullbackSquareNatIso.inv` under the two composite adjunctions is the
  identification `g'_* f_* ≅ f'_* g_*` of the composite direct images.
* `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_unit`: **the compatibility.**
  The base-change comparison carries the pullback of the unit of `f^* ⊣ f_*` to the unit of
  `f'^* ⊣ f'_*`.

## Implementation notes

The proof transposes the asserted identity across `g^* ⊣ g_*`, which is the adjunction
`pushforwardBaseChange` is defined by, using
`Stacks.AlgebraicGeometry.FlatBaseChange.homEquiv_pushforwardBaseChange`. Both sides then
become composites beginning with the unit of a composite adjunction, and the identity is
`CategoryTheory.unit_conjugateEquiv` applied to `pullbackSquareNatIso.inv`.

The conjugate of `pullbackSquareNatIso.inv` is computed one factor at a time with
`CategoryTheory.conjugateEquiv_comp`. Two of the three factors are
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`; the remaining one, the
conjugate of `AlgebraicGeometry.Scheme.Modules.pullbackCongr`, is proved by substituting the
equality of morphisms, after which both sides are identities.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChange

variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The identification of the two composite inverse images around a commuting square.** For
`w : g' ≫ f = f' ≫ g` this is the isomorphism `f^* ⋙ (g')^* ≅ g^* ⋙ (f')^*` obtained from the
pseudofunctoriality of the inverse image and the equality `w`. -/
def pullbackSquareNatIso (w : g' ≫ f = f' ≫ g) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g' ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f' :=
  Scheme.Modules.pullbackComp g' f ≪≫ Scheme.Modules.pullbackCongr w ≪≫
    (Scheme.Modules.pullbackComp f' g).symm

/-- The component of `Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareNatIso` at an
`𝒪_Y`-module `M`: the canonical isomorphism `(g')^* f^* M ≅ (f')^* g^* M`. -/
def pullbackSquareIso (w : g' ≫ f = f' ≫ g) (M : Y.Modules) :
    (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj M) ≅
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback g).obj M) :=
  (pullbackSquareNatIso w).app M

/-- The forward map of `pullbackSquareIso w M` is the component at `M` of the forward map of
`pullbackSquareNatIso w`. -/
@[simp]
lemma pullbackSquareIso_hom (w : g' ≫ f = f' ≫ g) (M : Y.Modules) :
    (pullbackSquareIso w M).hom = (pullbackSquareNatIso w).hom.app M :=
  rfl

/-- The inverse of `pullbackSquareIso w M` is the component at `M` of the inverse of
`pullbackSquareNatIso w`. -/
@[simp]
lemma pullbackSquareIso_inv (w : g' ≫ f = f' ≫ g) (M : Y.Modules) :
    (pullbackSquareIso w M).inv = (pullbackSquareNatIso w).inv.app M :=
  rfl

/-- The conjugate of the inverse-image identification along equal morphisms is the
direct-image identification along the same equality. -/
lemma conjugateEquiv_pullbackCongr_inv {Z T : Scheme.{u}} {a b : Z ⟶ T} (h : a = b) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction a)
        (Scheme.Modules.pullbackPushforwardAdjunction b)
        (Scheme.Modules.pullbackCongr h).inv =
      (Scheme.Modules.pushforwardCongr h).hom := by
  subst h
  have h₁ : (Scheme.Modules.pullbackCongr (rfl : a = a)).inv = 𝟙 _ := rfl
  rw [h₁, conjugateEquiv_id]
  ext M U
  simp

/-- **The direct-image identification is the conjugate of the inverse-image identification.**
Under the two composite adjunctions `f^* (g')^* ⊣ g'_* f_*` and `g^* (f')^* ⊣ f'_* g_*`, the
conjugate of the inverse of `Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareNatIso` is
the identification `g'_* f_* ≅ f'_* g_*` of the two composite direct images. -/
lemma conjugateEquiv_pullbackSquareNatIso_inv (w : g' ≫ f = f' ≫ g) :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction g'))
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction f'))
        (pullbackSquareNatIso w).inv =
      (Scheme.Modules.pushforwardComp g' f).hom ≫ (Scheme.Modules.pushforwardCongr w).hom ≫
        (Scheme.Modules.pushforwardComp f' g).inv := by
  have hA := Scheme.Modules.conjugateEquiv_pullbackComp_inv g' f
  have hB := conjugateEquiv_pullbackCongr_inv w
  have hC : conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ g))
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction f'))
        (Scheme.Modules.pullbackComp f' g).hom =
      (Scheme.Modules.pushforwardComp f' g).inv := by
    have := conjugateEquiv_comm
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f'))
      (Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ g))
      (α := (Scheme.Modules.pullbackComp f' g).inv)
      (β := (Scheme.Modules.pullbackComp f' g).hom) (by simp)
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at this
    exact (Iso.hom_comp_eq_id _).mp this
  have hsplit : (pullbackSquareNatIso w).inv =
      ((Scheme.Modules.pullbackComp f' g).hom ≫ (Scheme.Modules.pullbackCongr w).inv) ≫
        (Scheme.Modules.pullbackComp g' f).inv := by
    simp [pullbackSquareNatIso]
  rw [← hA, ← hB, ← hC, conjugateEquiv_comp, conjugateEquiv_comp, hsplit]

/-- The unit of `f^* (g')^* ⊣ g'_* f_*`, followed by the identification of the composite direct
images and by the direct image of
`Stacks.AlgebraicGeometry.FlatBaseChange.pullbackSquareIso`, is the unit of
`g^* (f')^* ⊣ f'_* g_*`. -/
lemma comp_unit_pushforwardSquare (w : g' ≫ f = f' ≫ g) (M : Y.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction g')).unit.app M ≫
        ((Scheme.Modules.pushforwardComp g' f).hom ≫ (Scheme.Modules.pushforwardCongr w).hom ≫
            (Scheme.Modules.pushforwardComp f' g).inv).app
          ((Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback f).obj M)) ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward f').map (pullbackSquareIso w M).hom) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f')).unit.app M := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g'))
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f'))
    (pullbackSquareNatIso w).inv M
  rw [conjugateEquiv_pullbackSquareNatIso_inv] at h
  dsimp only [Functor.comp_obj] at h
  rw [← Category.assoc, h, Category.assoc]
  simp [pullbackSquareIso, ← Functor.map_comp]

/-- **The base-change comparison carries the unit of `f^* ⊣ f_*` to the unit of
`f'^* ⊣ f'_*`.** -/
theorem pushforwardBaseChange_unit (w : g' ≫ f = f' ≫ g) (M : Y.Modules) :
    (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        pushforwardBaseChange w ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pushforward f').map (pullbackSquareIso w M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
        ((Scheme.Modules.pullback g).obj M) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [homEquiv_pushforwardBaseChange, Adjunction.homEquiv_unit]
  have h := comp_unit_pushforwardSquare w M
  simp only [pushforwardBaseChangeUnit, Adjunction.comp_unit_app, NatTrans.comp_app,
    Category.assoc] at h ⊢
  exact h

end Stacks.AlgebraicGeometry.FlatBaseChange

end
