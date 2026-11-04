module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangePasteIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange

/-!
# Reducing base change for the direct image to geometric points

Let `P` be a class of morphisms of schemes stable under base change (for instance, proper
morphisms). Suppose that for every `φ ∈ P` and every geometric point `t` of its target, the base
change map of every cartesian square of `φ` over `t` is an isomorphism of abelian étale sheaves.
Then the base change map `g^{-1} f_* ⟶ f'_* (g')^{-1}` of every cartesian square with `f ∈ P` is an
isomorphism.

Stalks at geometric points detect isomorphisms, and the stalk at `t` is computed after inverse
image along `t`. Pasting the square of `f` with the square of `f'` over `t` gives a square of `f`
over `t ≫ g`; both of these have invertible base change maps by hypothesis, and the base change
maps compose (`Stacks.EtaleCohomology.etaleAbelianBaseChange_comp_app`), so the inverse image along
`t` of the base change map is invertible.

## Main results

* `Stacks.EtaleCohomology.isIso_stalk_of_isIso_etaleAbelianInverseImage_map` — the stalk at a
  geometric point of a morphism whose inverse image along that point is invertible is invertible.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_geometricPoints` — the reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- If the inverse image of a morphism of abelian étale sheaves along a geometric point is an
isomorphism, so is its stalk at that point: the stalk at `x` is the stalk of the inverse image at
the canonical point. -/
theorem isIso_stalk_of_isIso_etaleAbelianInverseImage_map {X : Scheme.{u}} (x : GeometricPoint X)
    {F G : Sheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (h : IsIso ((etaleAbelianInverseImage.{u, 0} x.hom).map φ)) :
    IsIso ((smallEtaleStalkAb x.hom).map φ) := by
  have h₁ : IsIso ((smallEtalePullbackAb x.hom).map φ) :=
    (NatIso.isIso_map_iff (Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallEtaleBaseChange x.hom) AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
      (Scheme.smallEtaleTopology x.source)) φ).2 h
  have h₂ : IsIso ((smallEtaleStalkAb (𝟙 x.source ≫ x.hom)).map φ) :=
    (NatIso.isIso_map_iff (smallEtaleStalkPullbackAbIso x.hom (𝟙 x.source)) φ).1
      (Functor.map_isIso (smallEtaleStalkAb (𝟙 x.source)) ((smallEtalePullbackAb x.hom).map φ))
  rwa [Category.id_comp] at h₂

/-- **Base change for the direct image, from geometric points.** Let `P` be stable under base
change, `f : X ⟶ Y` in `P` and `g' ≫ f = f' ≫ g` a cartesian square. If for every morphism `φ` in
`P` and every geometric point `t` of its target the base change map of every cartesian square of
`φ` over `t` is an isomorphism, then the base change map of the given square is an isomorphism. -/
theorem isIso_etaleAbelianBaseChange_of_geometricPoints (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    (H : ∀ ⦃A B Z : Scheme.{u}⦄ (φ : A ⟶ B), P φ → ∀ (t : GeometricPoint B) (p : Z ⟶ A)
      (q : Z ⟶ t.source) (sq : IsPullback p q φ t.hom),
        IsIso (etaleAbelianBaseChange.{u, 0} φ t.hom p q sq.w))
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (hf : P f) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' sq.w) := by
  have hf' : P f' := MorphismProperty.of_isPullback sq hf
  refine (NatTrans.isIso_iff_isIso_app _).2 fun K ↦ ?_
  refine (isIso_iff_forall_isIso_smallEtaleStalkAb _).2 fun t ↦ ?_
  refine isIso_stalk_of_isIso_etaleAbelianInverseImage_map t _ ?_
  let k := pullback.fst f' t.hom
  let j := pullback.snd f' t.hom
  have sqU : IsPullback k j f' t.hom := IsPullback.of_hasPullback f' t.hom
  have sqO : IsPullback (k ≫ g') j f (t.hom ≫ g) := sqU.paste_horiz sq
  exact isIso_inverseImage_map_etaleAbelianBaseChange_app_of_paste.{u, 0} g f f' g' t.hom j k
    sq.w sqU.w (t.hom ≫ g) rfl (k ≫ g') rfl sqO.w
    (H f hf (GeometricPoint.mk t.residueField (t.hom ≫ g)) (k ≫ g') j sqO) (H f' hf' t k j sqU) K

end Stacks.EtaleCohomology

end
