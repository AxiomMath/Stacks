module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedBidualNaturality

/-!
# `Ext` out of the dual of a perfect object

Let `Y` be an algebraic space and `K` a perfect object of `D(𝒪_Y)`, with dual `K^∨`.  For every
`M ∈ D(𝒪_Y)` and every `i` there is an isomorphism

`Ext^i(K^∨, M) = Hom(K^∨, M[i]) ≅ Hom(𝒪_Y, (K ⊗^L M)[i])`,

natural in `M`, compatible with the boundary maps of distinguished triangles in `M`: it is
`Hom(E, M[i]) ≅ Hom(𝒪_Y, (E^∨ ⊗^L M)[i])` (Stacks 08J8, 08JJ) at `E = K^∨`, followed by the double
dual isomorphism `K^∨∨ ≅ K` (Stacks 08JJ).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDualExtAddEquiv`: the isomorphism
  `Ext^i(K^∨, M) ≅ Hom(𝒪_Y, (K ⊗^L M)[i])` for a perfect `K`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDualExtAddEquiv_naturality`: naturality in `M`.
* `AlgebraicGeometry.Space.smallEtaleDualExtAddEquiv_shift`: the boundary maps.

## References

* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)

/-- Reassociation of a composite through an equality of its tail. -/
theorem comp_assoc_eq_of_tail_eq {C : Type*} [Category C] {P Q R R' T U U' : C} (X : P ⟶ Q)
    {u : Q ⟶ R} {v : R ⟶ R'} {w : R' ⟶ T} {b : Q ⟶ U} {u' : U ⟶ U'} {v' : U' ⟶ T}
    (h : (u ≫ v) ≫ w = b ≫ u' ≫ v') :
    (X ≫ u ≫ v) ≫ w = (X ≫ b) ≫ u' ≫ v' := by
  rw [Category.assoc, h, Category.assoc]

/-- A transformation compatible with the shifts carries the boundary composite
`a[i] ≫ (N[1][i] ≅ N[i + 1])` of one functor to that of the other. -/
theorem shift_boundary_naturality_of_natTrans {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] (β : F ⟶ G)
    [NatTrans.CommShift β ℤ] {M N : C} (a : M ⟶ N⟦(1 : ℤ)⟧) (i j : ℤ) (h : 1 + i = j) :
    ((F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app N)⟦i⟧' ≫
        (shiftFunctorAdd' D 1 i j h).inv.app (F.obj N)) ≫ (β.app N)⟦j⟧' =
      (β.app M)⟦i⟧' ≫ (G.map a ≫ (G.commShiftIso (1 : ℤ)).hom.app N)⟦i⟧' ≫
        (shiftFunctorAdd' D 1 i j h).inv.app (G.obj N) := by
  have hadd := (shiftFunctorAdd' D 1 i j h).inv.naturality (β.app N)
  dsimp only [Functor.comp_map] at hadd
  have key : (F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app N) ≫ (β.app N)⟦(1 : ℤ)⟧' =
      β.app M ≫ G.map a ≫ (G.commShiftIso (1 : ℤ)).hom.app N := by
    rw [Category.assoc, NatTrans.shift_app_comm β (1 : ℤ) N, ← Category.assoc, β.naturality a,
      Category.assoc]
  rw [Category.assoc, ← hadd, ← Category.assoc, ← Functor.map_comp, key, Functor.map_comp,
    Category.assoc]

/-- The comparison `K^∨∨ ⊗^L - ≅ K ⊗^L -` induced by the double dual isomorphism. -/
abbrev smallEtaleDerivedTensorBidualIso
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K) :
    (smallEtaleDerivedTensor B S hS Y).obj
        (smallEtaleDerivedDual B S hS Y (smallEtaleDerivedDual B S hS Y K)) ≅
      (smallEtaleDerivedTensor B S hS Y).obj K :=
  (smallEtaleDerivedTensor B S hS Y).mapIso (smallEtaleDerivedBidualIso B S hS Y K hK)

/-- **`Ext^i(K^∨, M) ≅ Hom(𝒪_Y, (K ⊗^L M)[i])` for a perfect `K`.** -/
def smallEtaleDualExtAddEquiv
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (i : ℤ) :
    (smallEtaleDerivedDual B S hS Y K ⟶ M⟦i⟧) ≃+
      (structureDerived Y ⟶ (((smallEtaleDerivedTensor B S hS Y).obj K).obj M)⟦i⟧) :=
  (smallEtaleExtAddEquivUnitTensorDual B S hS Y (smallEtaleDerivedDual B S hS Y K)
      (isPerfect_smallEtaleDerivedDual B S hS Y K hK) M i).trans
    { toFun := fun h => h ≫ ((smallEtaleDerivedTensorBidualIso B S hS Y K hK).hom.app M)⟦i⟧'
      invFun := fun h => h ≫ ((smallEtaleDerivedTensorBidualIso B S hS Y K hK).inv.app M)⟦i⟧'
      left_inv := fun h => by
        simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id, Category.comp_id]
      right_inv := fun h => by
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
          CategoryTheory.Functor.map_id, Category.comp_id]
      map_add' := fun h h' => Preadditive.add_comp _ _ _ _ _ _ }

/-- `smallEtaleDualExtAddEquiv` sends `g` to its image under
`smallEtaleExtAddEquivUnitTensorDual` at `E = K^∨`, composed with the shift by `i` of the
comparison `K^∨∨ ⊗^L M ≅ K ⊗^L M`. -/
theorem smallEtaleDualExtAddEquiv_apply
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (i : ℤ)
    (g : smallEtaleDerivedDual B S hS Y K ⟶ M⟦i⟧) :
    smallEtaleDualExtAddEquiv B S hS Y K hK M i g =
      smallEtaleExtAddEquivUnitTensorDual B S hS Y (smallEtaleDerivedDual B S hS Y K)
          (isPerfect_smallEtaleDerivedDual B S hS Y K hK) M i g ≫
        ((smallEtaleDerivedTensorBidualIso B S hS Y K hK).hom.app M)⟦i⟧' :=
  rfl

/-- The identification `smallEtaleDualExtAddEquiv` is natural in `M`. -/
theorem smallEtaleDualExtAddEquiv_naturality
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    {M M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (q : M ⟶ M') (i : ℤ) (g : smallEtaleDerivedDual B S hS Y K ⟶ M⟦i⟧) :
    smallEtaleDualExtAddEquiv B S hS Y K hK M' i (g ≫ q⟦i⟧') =
      smallEtaleDualExtAddEquiv B S hS Y K hK M i g ≫
        (((smallEtaleDerivedTensor B S hS Y).obj K).map q)⟦i⟧' := by
  have hn := congrArg (shiftFunctor (DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS Y))) i).map
      ((smallEtaleDerivedTensorBidualIso B S hS Y K hK).hom.naturality q)
  simp only [Functor.map_comp] at hn
  rw [smallEtaleDualExtAddEquiv_apply, smallEtaleDualExtAddEquiv_apply,
    smallEtaleExtAddEquivUnitTensorDual_naturality, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) hn

/-- **The identification `smallEtaleDualExtAddEquiv` is compatible with boundary maps**: for
`a : M ⟶ N[1]`, composing with `a[i]` and `N[1][i] ≅ N[i + 1]` on `Ext^•(K^∨, -)` corresponds to
composing with `(K ⊗^L a)[i]`, the commutation of `K ⊗^L -` with the shift, and the same
identification on `Hom(𝒪_Y, (K ⊗^L -)[•])`. -/
theorem smallEtaleDualExtAddEquiv_shift
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    {M N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (a : M ⟶ N⟦(1 : ℤ)⟧) (i j : ℤ) (h : 1 + i = j)
    (g : smallEtaleDerivedDual B S hS Y K ⟶ M⟦i⟧) :
    smallEtaleDualExtAddEquiv B S hS Y K hK N j
        (g ≫ a⟦i⟧' ≫ (shiftFunctorAdd' _ 1 i j h).inv.app N) =
      smallEtaleDualExtAddEquiv B S hS Y K hK M i g ≫
        (((smallEtaleDerivedTensor B S hS Y).obj K).map a ≫
          (((smallEtaleDerivedTensor B S hS Y).obj K).commShiftIso (1 : ℤ)).hom.app N)⟦i⟧' ≫
        (shiftFunctorAdd' _ 1 i j h).inv.app
          (((smallEtaleDerivedTensor B S hS Y).obj K).obj N) := by
  let := (smallEtaleDerivedTensorProduct B S hS Y).commShift₂
  have : NatTrans.CommShift (smallEtaleDerivedTensorBidualIso B S hS Y K hK).hom ℤ :=
    (smallEtaleDerivedTensorProduct B S hS Y).commShift₂.commShift_map _
  rw [smallEtaleDualExtAddEquiv_apply, smallEtaleDualExtAddEquiv_apply,
    smallEtaleExtAddEquivUnitTensorDual_shift]
  exact comp_assoc_eq_of_tail_eq _ (shift_boundary_naturality_of_natTrans _ _
    (smallEtaleDerivedTensorBidualIso B S hS Y K hK).hom a i j h)

end AlgebraicGeometry.Space

end
