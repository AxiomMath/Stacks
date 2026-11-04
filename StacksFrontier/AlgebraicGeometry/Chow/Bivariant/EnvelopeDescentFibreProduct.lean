module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The fibre products of the descent condition along an envelope

Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of schemes and write `X' = X ×_Y Y'` for the base
change of `f` along `g`, so that `X' ⟶ Y'` is `CategoryTheory.Limits.pullback.snd f g`. The
descent condition of Stacks 0GUC compares the two restrictions of a bivariant class for
`X' ⟶ Y'` along the two projections `Y' ×_Y Y' ⟶ Y'`, and those two restrictions are built on
two *different* chosen fibre products `X' ×_{Y'} (Y' ×_Y Y')`. This module identifies each of
them with `X ×_Y (Y' ×_Y Y')`, and hence with one another.

The underlying fact is transitivity of base change: for `h : T ⟶ Y'` the base change of
`X' ⟶ Y'` along `h` is the base change of `f` along `h ≫ g`
(`CategoryTheory.Limits.pullbackLeftPullbackSndIso`). Its compatibilities with the projections and
with the structure morphism of `X` over a base scheme are recorded.

## Main definitions

* `Stacks.Chow.baseChangeTransIso` — transitivity of base change,
  `(X ×_Y Y') ×_{Y'} T ≅ X ×_Y T`, for `T ⟶ Y'` any morphism.
* `Stacks.Chow.envelopeDescentFstIso`, `Stacks.Chow.envelopeDescentSndIso` — the two sides of the
  descent condition: the base changes of `X' ⟶ Y'` along the first and the second projection
  `Y' ×_Y Y' ⟶ Y'`, each identified with `X ×_Y (Y' ×_Y Y')`.
* `Stacks.Chow.envelopeDescentCompareIso` — the resulting identification of the two chosen fibre
  products with one another.

## Main results

* `Stacks.Chow.baseChangeTransIso_hom_fst`, `Stacks.Chow.baseChangeTransIso_hom_snd` and their
  inverse forms — the identification is compatible with both projections, hence is the canonical
  one; likewise `Stacks.Chow.envelopeDescentFstIso_hom_fst` and the analogues for the other two
  isomorphisms.
* `Stacks.Chow.baseChangeTransIso_hom_comp_fst_comp`,
  `Stacks.Chow.baseChangeTransIso_inv_comp_fst_comp` and the analogues — the identification
  commutes with the structure morphisms over a base scheme.
* `Stacks.Chow.baseChangeTrans_isPullback` — the composite `(X ×_Y Y') ×_{Y'} T ⟶ T` is the base
  change of `f` along `T ⟶ Y' ⟶ Y`, stated as a cartesian square.

## References

* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transitivity of base change -/

section Trans

variable {S X Y Y' T : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (h : T ⟶ Y')

/-- **Transitivity of base change.** Write `X' = X ×_Y Y'` for the base change of `f : X ⟶ Y`
along `g : Y' ⟶ Y`, so that `X' ⟶ Y'` is `pullback.snd f g`. The base change of `X' ⟶ Y'` along
a morphism `h : T ⟶ Y'` is the base change of `f` itself along `h ≫ g`. -/
def baseChangeTransIso : pullback (pullback.snd f g) h ≅ pullback f (h ≫ g) :=
  pullbackLeftPullbackSndIso f g h

/-- The isomorphism `baseChangeTransIso` followed by the projection to `X` is the composite
projection `(X ×_Y Y') ×_{Y'} T ⟶ X ×_Y Y' ⟶ X`. -/
@[reassoc (attr := simp)]
theorem baseChangeTransIso_hom_fst :
    (baseChangeTransIso f g h).hom ≫ pullback.fst f (h ≫ g) =
      pullback.fst (pullback.snd f g) h ≫ pullback.fst f g :=
  pullbackLeftPullbackSndIso_hom_fst f g h

/-- The isomorphism `baseChangeTransIso` followed by the projection to `T` is the projection
`(X ×_Y Y') ×_{Y'} T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem baseChangeTransIso_hom_snd :
    (baseChangeTransIso f g h).hom ≫ pullback.snd f (h ≫ g) =
      pullback.snd (pullback.snd f g) h :=
  pullbackLeftPullbackSndIso_hom_snd f g h

/-- The inverse of `baseChangeTransIso` followed by the composite projection
`(X ×_Y Y') ×_{Y'} T ⟶ X` is the projection `X ×_Y T ⟶ X`. -/
@[reassoc (attr := simp)]
theorem baseChangeTransIso_inv_fst :
    (baseChangeTransIso f g h).inv ≫ pullback.fst (pullback.snd f g) h ≫ pullback.fst f g =
      pullback.fst f (h ≫ g) :=
  pullbackLeftPullbackSndIso_inv_fst f g h

/-- The inverse of `baseChangeTransIso` followed by the projection to `T` is the projection
`X ×_Y T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem baseChangeTransIso_inv_snd :
    (baseChangeTransIso f g h).inv ≫ pullback.snd (pullback.snd f g) h =
      pullback.snd f (h ≫ g) :=
  pullbackLeftPullbackSndIso_inv_snd_snd f g h

/-- Transitivity of base change commutes with the structure morphism of `X` over a base scheme:
the two fibre products carry the same morphism to `S`. -/
theorem baseChangeTransIso_hom_comp_fst_comp (sX : X ⟶ S) :
    (baseChangeTransIso f g h).hom ≫ (pullback.fst f (h ≫ g) ≫ sX) =
      pullback.fst (pullback.snd f g) h ≫ (pullback.fst f g ≫ sX) := by
  simp

/-- Transitivity of base change commutes with the structure morphism of `X` over a base scheme,
read on the inverse isomorphism. -/
theorem baseChangeTransIso_inv_comp_fst_comp (sX : X ⟶ S) :
    (baseChangeTransIso f g h).inv ≫
        (pullback.fst (pullback.snd f g) h ≫ (pullback.fst f g ≫ sX)) =
      pullback.fst f (h ≫ g) ≫ sX := by
  simp

/-- The composite `(X ×_Y Y') ×_{Y'} T ⟶ T` is the base change of `f : X ⟶ Y` along the composite
`T ⟶ Y' ⟶ Y`: the square it forms with the composite projection to `X` is cartesian. -/
theorem baseChangeTrans_isPullback :
    IsPullback (pullback.fst (pullback.snd f g) h ≫ pullback.fst f g)
      (pullback.snd (pullback.snd f g) h) f (h ≫ g) :=
  IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, pullback.condition (f := f) (g := g), ← Category.assoc,
      pullback.condition (f := pullback.snd f g) (g := h), Category.assoc]⟩
    (baseChangeTransIso f g h) (baseChangeTransIso_hom_fst f g h)
    (baseChangeTransIso_hom_snd f g h)

end Trans

/-! ### The two fibre products of the descent condition -/

section Descent

variable {S X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The first side of the descent condition of Stacks 0GUC: the base change of `X' ⟶ Y'` along
the first projection `Y' ×_Y Y' ⟶ Y'`, identified with the base change `X ×_Y (Y' ×_Y Y')` of
`f : X ⟶ Y` itself. -/
def envelopeDescentFstIso :
    pullback (pullback.snd f g) (pullback.fst g g) ≅ pullback f (pullback.fst g g ≫ g) :=
  baseChangeTransIso f g (pullback.fst g g)

/-- The isomorphism `envelopeDescentFstIso` followed by the projection to `X` is the composite
projection `(X ×_Y Y') ×_{Y'} (Y' ×_Y Y') ⟶ X ×_Y Y' ⟶ X`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentFstIso_hom_fst :
    (envelopeDescentFstIso f g).hom ≫ pullback.fst f (pullback.fst g g ≫ g) =
      pullback.fst (pullback.snd f g) (pullback.fst g g) ≫ pullback.fst f g :=
  baseChangeTransIso_hom_fst f g (pullback.fst g g)

/-- The isomorphism `envelopeDescentFstIso` followed by the projection to `Y' ×_Y Y'` is the
projection `(X ×_Y Y') ×_{Y'} (Y' ×_Y Y') ⟶ Y' ×_Y Y'`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentFstIso_hom_snd :
    (envelopeDescentFstIso f g).hom ≫ pullback.snd f (pullback.fst g g ≫ g) =
      pullback.snd (pullback.snd f g) (pullback.fst g g) :=
  baseChangeTransIso_hom_snd f g (pullback.fst g g)

/-- The inverse of `envelopeDescentFstIso` followed by the composite projection to `X` is the
projection `X ×_Y (Y' ×_Y Y') ⟶ X`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentFstIso_inv_fst :
    (envelopeDescentFstIso f g).inv ≫
        pullback.fst (pullback.snd f g) (pullback.fst g g) ≫ pullback.fst f g =
      pullback.fst f (pullback.fst g g ≫ g) :=
  baseChangeTransIso_inv_fst f g (pullback.fst g g)

/-- The inverse of `envelopeDescentFstIso` followed by the projection to `Y' ×_Y Y'` is the
projection `X ×_Y (Y' ×_Y Y') ⟶ Y' ×_Y Y'`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentFstIso_inv_snd :
    (envelopeDescentFstIso f g).inv ≫ pullback.snd (pullback.snd f g) (pullback.fst g g) =
      pullback.snd f (pullback.fst g g ≫ g) :=
  baseChangeTransIso_inv_snd f g (pullback.fst g g)

/-- The second side of the descent condition of Stacks 0GUC: the base change of `X' ⟶ Y'` along
the second projection `Y' ×_Y Y' ⟶ Y'`. It is identified with the *same* fibre product
`X ×_Y (Y' ×_Y Y')` as the first side, the base morphism `Y' ×_Y Y' ⟶ Y` being written through
the first projection in both cases. -/
def envelopeDescentSndIso :
    pullback (pullback.snd f g) (pullback.snd g g) ≅ pullback f (pullback.fst g g ≫ g) :=
  baseChangeTransIso f g (pullback.snd g g) ≪≫ pullback.congrHom rfl pullback.condition.symm

/-- The isomorphism `envelopeDescentSndIso` followed by the projection to `X` is the composite
projection `(X ×_Y Y') ×_{Y'} (Y' ×_Y Y') ⟶ X ×_Y Y' ⟶ X`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentSndIso_hom_fst :
    (envelopeDescentSndIso f g).hom ≫ pullback.fst f (pullback.fst g g ≫ g) =
      pullback.fst (pullback.snd f g) (pullback.snd g g) ≫ pullback.fst f g := by
  simp [envelopeDescentSndIso, pullback.map, pullback.lift_fst]

/-- The isomorphism `envelopeDescentSndIso` followed by the projection to `Y' ×_Y Y'` is the
projection `(X ×_Y Y') ×_{Y'} (Y' ×_Y Y') ⟶ Y' ×_Y Y'`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentSndIso_hom_snd :
    (envelopeDescentSndIso f g).hom ≫ pullback.snd f (pullback.fst g g ≫ g) =
      pullback.snd (pullback.snd f g) (pullback.snd g g) := by
  simp [envelopeDescentSndIso, pullback.map, pullback.lift_snd]

/-- The inverse of `envelopeDescentSndIso` followed by the composite projection to `X` is the
projection `X ×_Y (Y' ×_Y Y') ⟶ X`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentSndIso_inv_fst :
    (envelopeDescentSndIso f g).inv ≫
        pullback.fst (pullback.snd f g) (pullback.snd g g) ≫ pullback.fst f g =
      pullback.fst f (pullback.fst g g ≫ g) := by
  rw [Iso.inv_comp_eq, ← envelopeDescentSndIso_hom_fst f g]

/-- The inverse of `envelopeDescentSndIso` followed by the projection to `Y' ×_Y Y'` is the
projection `X ×_Y (Y' ×_Y Y') ⟶ Y' ×_Y Y'`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentSndIso_inv_snd :
    (envelopeDescentSndIso f g).inv ≫ pullback.snd (pullback.snd f g) (pullback.snd g g) =
      pullback.snd f (pullback.fst g g ≫ g) := by
  rw [Iso.inv_comp_eq, envelopeDescentSndIso_hom_snd]

/-- **The two fibre products of the descent condition of Stacks 0GUC are isomorphic.** The base
changes of `X' ⟶ Y'` along the two projections `Y' ×_Y Y' ⟶ Y'` are canonically isomorphic, both
being `X ×_Y (Y' ×_Y Y')`. -/
def envelopeDescentCompareIso :
    pullback (pullback.snd f g) (pullback.fst g g) ≅
      pullback (pullback.snd f g) (pullback.snd g g) :=
  envelopeDescentFstIso f g ≪≫ (envelopeDescentSndIso f g).symm

/-- The isomorphism `envelopeDescentCompareIso` is compatible with the composite projections of
both fibre products to `X`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentCompareIso_hom_fst :
    (envelopeDescentCompareIso f g).hom ≫
        pullback.fst (pullback.snd f g) (pullback.snd g g) ≫ pullback.fst f g =
      pullback.fst (pullback.snd f g) (pullback.fst g g) ≫ pullback.fst f g := by
  simp [envelopeDescentCompareIso]

/-- The isomorphism `envelopeDescentCompareIso` is compatible with the projections of both fibre
products to `Y' ×_Y Y'`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentCompareIso_hom_snd :
    (envelopeDescentCompareIso f g).hom ≫ pullback.snd (pullback.snd f g) (pullback.snd g g) =
      pullback.snd (pullback.snd f g) (pullback.fst g g) := by
  simp [envelopeDescentCompareIso]

/-- The inverse of `envelopeDescentCompareIso` is compatible with the composite projections of
both fibre products to `X`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentCompareIso_inv_fst :
    (envelopeDescentCompareIso f g).inv ≫
        pullback.fst (pullback.snd f g) (pullback.fst g g) ≫ pullback.fst f g =
      pullback.fst (pullback.snd f g) (pullback.snd g g) ≫ pullback.fst f g := by
  rw [Iso.inv_comp_eq, ← envelopeDescentCompareIso_hom_fst f g]

/-- The inverse of `envelopeDescentCompareIso` is compatible with the projections of both fibre
products to `Y' ×_Y Y'`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentCompareIso_inv_snd :
    (envelopeDescentCompareIso f g).inv ≫ pullback.snd (pullback.snd f g) (pullback.fst g g) =
      pullback.snd (pullback.snd f g) (pullback.snd g g) := by
  rw [Iso.inv_comp_eq, envelopeDescentCompareIso_hom_snd]

/-- The identification of the two sides of the descent condition commutes with the structure
morphism of `X` over a base scheme. -/
theorem envelopeDescentCompareIso_hom_comp_fst_comp (sX : X ⟶ S) :
    (envelopeDescentCompareIso f g).hom ≫
        (pullback.fst (pullback.snd f g) (pullback.snd g g) ≫ (pullback.fst f g ≫ sX)) =
      pullback.fst (pullback.snd f g) (pullback.fst g g) ≫ (pullback.fst f g ≫ sX) := by
  simp

/-- The identification of the two sides of the descent condition commutes with the structure
morphism of `X` over a base scheme, read on the inverse isomorphism. -/
theorem envelopeDescentCompareIso_inv_comp_fst_comp (sX : X ⟶ S) :
    (envelopeDescentCompareIso f g).inv ≫
        (pullback.fst (pullback.snd f g) (pullback.fst g g) ≫ (pullback.fst f g ≫ sX)) =
      pullback.fst (pullback.snd f g) (pullback.snd g g) ≫ (pullback.fst f g ≫ sX) := by
  simp

end Descent

end Stacks.Chow

end
