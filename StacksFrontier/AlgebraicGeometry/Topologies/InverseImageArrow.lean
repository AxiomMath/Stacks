module

public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageComposition
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Functoriality of the inverse-image ringed space on arrows

For a ringed space `S` and a continuous map `i : Z ⟶ S`, the ringed space
`AlgebraicGeometry.RingedSpace.inverseImage S i` is `(Z, i⁻¹𝒪_S)`. This file makes it a functor on
the arrow category of ringed spaces, sending `h : X ⟶ T` to `(X, h⁻¹𝒪_T)`, together with the
identity-on-spaces unit `(X, 𝒪_X) ⟶ (X, h⁻¹𝒪_T)`, natural in the arrow.

## Main definitions

* `AlgebraicGeometry.RingedSpace.inverseImageLift`: the universal property of `(Z, i⁻¹𝒪_S)`:
  a morphism into it from a map of spaces and a map `𝒪_S ⟶ (g ≫ i)_* 𝒪_W`.
* `AlgebraicGeometry.RingedSpace.inverseImageLiftOfHom`: the lift of a morphism of ringed spaces
  whose underlying map factors through `i`.
* `AlgebraicGeometry.RingedSpace.inverseImageArrow`: the functor `h ↦ (X, h⁻¹𝒪_T)` on
  `Arrow RingedSpace`.
* `AlgebraicGeometry.RingedSpace.inverseImageUnit`: the identity-on-spaces morphism
  `(X, 𝒪_X) ⟶ (X, h⁻¹𝒪_T)` attached to `h : X ⟶ T`.
* `AlgebraicGeometry.RingedSpace.inverseImageArrowUnit`: the natural transformation from the
  source functor to it whose component at `h` is the identity on spaces with sheaf map adjoint to
  `h^♯`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.Adjunction

/-- The transpose of the unit of an adjunction is the identity. -/
theorem homEquiv_symm_unit_app {C : Type*} [Category* C] {D : Type*} [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (X : C) :
    (adj.homEquiv X (L.obj X)).symm (adj.unit.app X) = 𝟙 (L.obj X) := by
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, Functor.map_id]
  exact (Category.comp_id _).symm

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.RingedSpace

/-- The morphism `W ⟶ (Z, i⁻¹𝒪_S)` given by a map of spaces `g : W ⟶ Z` and a map of sheaves of
rings `𝒪_S ⟶ (g ≫ i)_* 𝒪_W`, through the pullback--pushforward adjunction. -/
noncomputable def inverseImageLift (S : RingedSpace.{u, u}) {Z : TopCat.{u}}
    (i : Z ⟶ S.carrier) (W : RingedSpace.{u, u}) (g : W.carrier ⟶ Z)
    (k : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (g ≫ i)).obj W.sheaf) :
    W ⟶ inverseImage S i :=
  InducedCategory.homMk
    { base := g
      c := (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).homEquiv
        S.sheaf ((TopCat.Sheaf.pushforward CommRingCat.{u} g).obj W.sheaf)).symm k).hom }

variable (S : RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ S.carrier)
  (W : RingedSpace.{u, u}) (g : W.carrier ⟶ Z)
  (k : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (g ≫ i)).obj W.sheaf)

/-- The underlying map of spaces of `AlgebraicGeometry.RingedSpace.inverseImageLift` is `g`. -/
@[simp] theorem inverseImageLift_base : (inverseImageLift S i W g k).hom.base = g := rfl

/-- The sheaf map of the lift followed by the projection `(Z, i⁻¹𝒪_S) ⟶ S` is the given map
`k : 𝒪_S ⟶ (g ≫ i)_* 𝒪_W`. -/
theorem inverseImageLift_comp_projection_c :
    (inverseImageLift S i W g k ≫ inverseImageProjection S i).hom.c = k.hom :=
  congrArg (fun t => t.hom)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).homEquiv
      S.sheaf ((TopCat.Sheaf.pushforward CommRingCat.{u} g).obj W.sheaf)).apply_symm_apply k)

/-- The lift is natural under precomposition with a morphism of ringed spaces. -/
theorem comp_inverseImageLift {V : RingedSpace.{u, u}} (γ : V ⟶ W) :
    γ ≫ inverseImageLift S i W g k =
      inverseImageLift S i V (γ.hom.base ≫ g)
        (k ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (g ≫ i)).map
          (⟨γ.hom.c⟩ : W.sheaf ⟶
            (TopCat.Sheaf.pushforward CommRingCat.{u} γ.hom.base).obj V.sheaf)) :=
  InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq
    (congrArg (fun t => t.hom)
      (Adjunction.homEquiv_naturality_right_symm
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i) k
        ((TopCat.Sheaf.pushforward CommRingCat.{u} g).map
          (⟨γ.hom.c⟩ : W.sheaf ⟶
            (TopCat.Sheaf.pushforward CommRingCat.{u} γ.hom.base).obj V.sheaf))).symm)))

/-- The identity of the inverse-image ringed space is the lift of the unit of the
pullback--pushforward adjunction. -/
theorem inverseImageLift_eq_id :
    inverseImageLift S i (inverseImage S i) (𝟙 _)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).unit.app S.sheaf) =
      𝟙 (inverseImage S i) :=
  InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq
    (congrArg (fun t => t.hom)
      (Adjunction.homEquiv_symm_unit_app
        (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i) S.sheaf))))


/-! ### The lift of a morphism of ringed spaces -/

/-- The lift of a morphism `q : W ⟶ S` of ringed spaces whose base factors through `i`. -/
noncomputable def inverseImageLiftOfHom (q : W ⟶ S) (hq : q.hom.base = g ≫ i) :
    W ⟶ inverseImage S i :=
  inverseImageLift S i W g
    ((⟨q.hom.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} q.hom.base).obj W.sheaf) ≫
      eqToHom (congrArg
        (fun t => (TopCat.Sheaf.pushforward CommRingCat.{u} t).obj W.sheaf) hq))

/-- The underlying map of spaces of `AlgebraicGeometry.RingedSpace.inverseImageLiftOfHom` is
`g`. -/
@[simp] theorem inverseImageLiftOfHom_base (q : W ⟶ S) (hq : q.hom.base = g ≫ i) :
    (inverseImageLiftOfHom S i W g q hq).hom.base = g := rfl

private theorem liftOfHom_comp_projection_aux (b : W.carrier ⟶ S.carrier)
    (c : S.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} b).obj W.presheaf)
    (hq : b = g ≫ i) :
    inverseImageLiftOfHom S i W g
        (InducedCategory.homMk
          ({ base := b, c := c } : W.toPresheafedSpace ⟶ S.toPresheafedSpace)) hq ≫
        inverseImageProjection S i =
      InducedCategory.homMk
        ({ base := b, c := c } : W.toPresheafedSpace ⟶ S.toPresheafedSpace) := by
  subst hq
  exact InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq
    (inverseImageLift_comp_projection_c S i W g _)))

/-- The lift of `q`, followed by the projection `(Z, i⁻¹𝒪_S) ⟶ S`, is `q`. -/
theorem inverseImageLiftOfHom_comp_projection (q : W ⟶ S) (hq : q.hom.base = g ≫ i) :
    inverseImageLiftOfHom S i W g q hq ≫ inverseImageProjection S i = q :=
  liftOfHom_comp_projection_aux S i W g q.hom.base q.hom.c hq

private theorem comp_liftOfHom_aux {V : RingedSpace.{u, u}} (γ : V ⟶ W)
    (b : W.carrier ⟶ S.carrier)
    (c : S.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} b).obj W.presheaf)
    (hq : b = g ≫ i) :
    γ ≫ inverseImageLiftOfHom S i W g
        (InducedCategory.homMk
          ({ base := b, c := c } : W.toPresheafedSpace ⟶ S.toPresheafedSpace)) hq =
      inverseImageLiftOfHom S i V (γ.hom.base ≫ g)
        (γ ≫ InducedCategory.homMk
          ({ base := b, c := c } : W.toPresheafedSpace ⟶ S.toPresheafedSpace))
        (by subst hq; rfl) := by
  subst hq
  exact comp_inverseImageLift S i W g _ γ

/-- The lift of a morphism of ringed spaces is natural under precomposition with a morphism of
ringed spaces. -/
theorem comp_inverseImageLiftOfHom {V : RingedSpace.{u, u}} (γ : V ⟶ W) (q : W ⟶ S)
    (hq : q.hom.base = g ≫ i) (hq' : (γ ≫ q).hom.base = (γ.hom.base ≫ g) ≫ i) :
    γ ≫ inverseImageLiftOfHom S i W g q hq =
      inverseImageLiftOfHom S i V (γ.hom.base ≫ g) (γ ≫ q) hq' :=
  comp_liftOfHom_aux S i W g γ q.hom.base q.hom.c hq

/-- Equal morphisms of ringed spaces have equal lifts. -/
theorem inverseImageLiftOfHom_congr {q q' : W ⟶ S} (h : q = q')
    (hq : q.hom.base = g ≫ i) (hq' : q'.hom.base = g ≫ i) :
    inverseImageLiftOfHom S i W g q hq = inverseImageLiftOfHom S i W g q' hq' := by
  subst h; rfl

/-- The lift of the projection `(Z, i⁻¹𝒪_S) ⟶ S` along the identity of `Z` is the identity. -/
theorem inverseImageLiftOfHom_projection_eq_id
    (hq : (inverseImageProjection S i).hom.base = 𝟙 Z ≫ i) :
    inverseImageLiftOfHom S i (inverseImage S i) (𝟙 _) (inverseImageProjection S i) hq =
      𝟙 (inverseImage S i) :=
  inverseImageLift_eq_id S i


/-! ### The arrow-category functor -/

/-- The ringed space `(X, h⁻¹𝒪_S)` attached to an arrow `h : X ⟶ S` of ringed spaces. -/
noncomputable abbrev inverseImageArrowObj (a : Arrow RingedSpace.{u, u}) :
    RingedSpace.{u, u} :=
  inverseImage a.right a.hom.hom.base

/-- For a morphism `u : a ⟶ b` of arrows of ringed spaces, the projection from the inverse-image
ringed space of `a` to `a.right`, followed by `u.right`, has the same underlying map of spaces as
`u.left ≫ b.hom`. -/
theorem arrow_base_comm {a b : Arrow RingedSpace.{u, u}} (u : a ⟶ b) :
    (inverseImageProjection a.right a.hom.hom.base ≫ u.right).hom.base =
      u.left.hom.base ≫ b.hom.hom.base :=
  (congrArg (fun t => t.hom.base) (Arrow.w u)).symm

/-- The morphism of inverse-image ringed spaces attached to a square of ringed spaces. -/
noncomputable def inverseImageArrowMap {a b : Arrow RingedSpace.{u, u}} (u : a ⟶ b) :
    inverseImageArrowObj a ⟶ inverseImageArrowObj b :=
  inverseImageLiftOfHom b.right b.hom.hom.base (inverseImageArrowObj a) u.left.hom.base
    (inverseImageProjection a.right a.hom.hom.base ≫ u.right) (arrow_base_comm u)

/-- The underlying map of spaces of `AlgebraicGeometry.RingedSpace.inverseImageArrowMap u` is
that of `u.left`. -/
@[simp] theorem inverseImageArrowMap_base {a b : Arrow RingedSpace.{u, u}} (u : a ⟶ b) :
    (inverseImageArrowMap u).hom.base = u.left.hom.base := rfl

/-- The morphism of inverse-image ringed spaces attached to `u : a ⟶ b`, followed by the
projection to `b.right`, is the projection to `a.right` followed by `u.right`. -/
theorem inverseImageArrowMap_comp_projection {a b : Arrow RingedSpace.{u, u}} (u : a ⟶ b) :
    inverseImageArrowMap u ≫ inverseImageProjection b.right b.hom.hom.base =
      inverseImageProjection a.right a.hom.hom.base ≫ u.right :=
  inverseImageLiftOfHom_comp_projection _ _ _ _ _ _

/-- The morphism of inverse-image ringed spaces attached to an identity square is the
identity. -/
theorem inverseImageArrowMap_id (a : Arrow RingedSpace.{u, u}) :
    inverseImageArrowMap (𝟙 a) = 𝟙 (inverseImageArrowObj a) := by
  have h0 : (inverseImageProjection a.right a.hom.hom.base).hom.base =
      𝟙 a.left.carrier ≫ a.hom.hom.base := rfl
  refine (inverseImageLiftOfHom_congr _ _ _ _
    (Category.comp_id (inverseImageProjection a.right a.hom.hom.base))
    (arrow_base_comm (𝟙 a)) h0).trans ?_
  exact inverseImageLiftOfHom_projection_eq_id _ _ h0

/-- The morphism of inverse-image ringed spaces attached to a composite of squares is the
composite of the morphisms attached to the squares. -/
theorem inverseImageArrowMap_comp {a b c : Arrow RingedSpace.{u, u}} (u : a ⟶ b) (v : b ⟶ c) :
    inverseImageArrowMap (u ≫ v) = inverseImageArrowMap u ≫ inverseImageArrowMap v := by
  have hq : inverseImageProjection a.right a.hom.hom.base ≫ (u ≫ v).right =
      inverseImageArrowMap u ≫
        (inverseImageProjection b.right b.hom.hom.base ≫ v.right) := by
    rw [← Category.assoc, inverseImageArrowMap_comp_projection, Category.assoc]
    rfl
  have h2 : (inverseImageArrowMap u ≫
      (inverseImageProjection b.right b.hom.hom.base ≫ v.right)).hom.base =
      (u ≫ v).left.hom.base ≫ c.hom.hom.base := by
    rw [← hq]; exact arrow_base_comm (u ≫ v)
  refine (inverseImageLiftOfHom_congr _ _ _ _ hq (arrow_base_comm (u ≫ v)) h2).trans ?_
  exact (comp_inverseImageLiftOfHom _ _ _ _ (inverseImageArrowMap u) _
    (arrow_base_comm v) h2).symm

/-- The functor `h ↦ (X, h⁻¹𝒪_T)` on the arrow category of ringed spaces. -/
noncomputable def inverseImageArrow : Arrow RingedSpace.{u, u} ⥤ RingedSpace.{u, u} where
  obj a := inverseImageArrowObj a
  map u := inverseImageArrowMap u
  map_id a := inverseImageArrowMap_id a
  map_comp u v := inverseImageArrowMap_comp u v


/-! ### The unit -/

/-- The identity-on-spaces morphism of ringed spaces `(X, 𝒪_X) ⟶ (X, h⁻¹𝒪_S)`. -/
noncomputable def inverseImageUnit {X T : RingedSpace.{u, u}} (h : X ⟶ T) :
    X ⟶ inverseImage T h.hom.base :=
  inverseImageLiftOfHom T h.hom.base X (𝟙 _) h rfl

/-- The unit `(X, 𝒪_X) ⟶ (X, h⁻¹𝒪_T)` followed by the projection to `T` is `h`. -/
theorem inverseImageUnit_comp_projection {X T : RingedSpace.{u, u}} (h : X ⟶ T) :
    inverseImageUnit h ≫ inverseImageProjection T h.hom.base = h :=
  inverseImageLiftOfHom_comp_projection _ _ _ _ _ _

/-- The unit `(X, 𝒪_X) ⟶ (X, h⁻¹𝒪_T)` is the lift of the identity of `X` and the sheaf map
of `h`. -/
theorem inverseImageUnit_eq_lift {X T : RingedSpace.{u, u}} (h : X ⟶ T) :
    inverseImageUnit h =
      inverseImageLift T h.hom.base X (𝟙 _)
        (⟨h.hom.c⟩ : T.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).obj X.sheaf) := rfl

/-- The natural transformation from the source functor to
`AlgebraicGeometry.RingedSpace.inverseImageArrow` whose component at `h` is
`AlgebraicGeometry.RingedSpace.inverseImageUnit h`. -/
noncomputable def inverseImageArrowUnit :
    NatTrans (Arrow.leftFunc (C := RingedSpace.{u, u})) inverseImageArrow.{u} where
  app a := inverseImageUnit a.hom
  naturality a b u := by
    have hq : u.left ≫ b.hom = inverseImageUnit a.hom ≫
        (inverseImageProjection a.right a.hom.hom.base ≫ u.right) := by
      rw [← Category.assoc, inverseImageUnit_comp_projection]
      exact Arrow.w u
    have h2 : (inverseImageUnit a.hom ≫
        (inverseImageProjection a.right a.hom.hom.base ≫ u.right)).hom.base =
        ((inverseImageUnit a.hom).hom.base ≫ u.left.hom.base) ≫ b.hom.hom.base := by
      rw [← hq]; rfl
    refine Eq.trans (comp_inverseImageLiftOfHom _ _ _ _ u.left b.hom rfl rfl) ?_
    refine Eq.trans (inverseImageLiftOfHom_congr _ _ _ _ hq rfl h2) ?_
    exact (comp_inverseImageLiftOfHom _ _ _ _ (inverseImageUnit a.hom) _
      (arrow_base_comm u) h2).symm

end AlgebraicGeometry.RingedSpace

end
