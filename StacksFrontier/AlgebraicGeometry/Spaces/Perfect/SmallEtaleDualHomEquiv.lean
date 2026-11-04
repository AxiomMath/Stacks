module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Morphisms out of a perfect object as morphisms out of `𝒪_X` into the tensor with its dual

Let `X` be an algebraic space and `E` a perfect object of `D(𝒪_X)` with dual
`E^∨ = RSheafHom(E, 𝒪_X)`.  For every `M` in `D(𝒪_X)`,

`Hom_{D(𝒪_X)}(E, M) ≅ Hom_{D(𝒪_X)}(𝒪_X, E^∨ ⊗^L M)`,

as abelian groups and naturally in `M`.  This is the identification
`Ext^i_{𝒪_X}(E, M) = H^i(X, E^∨ ⊗^L M)` "by construction of `E^∨`" in the proof of Stacks 08JN,
before `Hom(𝒪_X, -[i])` is read as hypercohomology.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomTensorDualNatIso`: `RSheafHom(E, -) ≅
  E^∨ ⊗^L -` for a perfect `E`, as an isomorphism of functors.
* `AlgebraicGeometry.Space.smallEtaleHomAddEquivUnitTensorDual`: the identification
  `Hom(E, M) ≃+ Hom(𝒪_X, E^∨ ⊗^L M)`.
* `AlgebraicGeometry.Space.smallEtaleExtAddEquivUnitTensorDual`: the identification
  `Hom(E, M[i]) ≃+ Hom(𝒪_X, (E^∨ ⊗^L M)[i])`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleHomAddEquivUnitTensorDual_naturality` and
  `AlgebraicGeometry.Space.smallEtaleExtAddEquivUnitTensorDual_naturality`: these
  identifications are natural in `M`.
* `AlgebraicGeometry.Space.smallEtaleExtAddEquivUnitTensorDual_shift`: the identification on
  shifts is compatible with boundary maps `M ⟶ N[1]`.

## References

* [Stacks Project, Tag 08JN](https://stacks.math.columbia.edu/tag/08JN)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

/-- An isomorphism `uncurry T ⋙ G ≅ (F × F) ⋙ uncurry T'`, evaluated with a fixed first
argument `P`: `T(P, -) ⋙ G ≅ F ⋙ T'(F P, -)`. -/
def objIsoOfUncurryIso {C E C' E' : Type*} [Category C] [Category E] [Category C']
    [Category E'] {T : C ⥤ C ⥤ E} {T' : C' ⥤ C' ⥤ E'} {F : C ⥤ C'} {G : E ⥤ E'}
    (τ : Functor.uncurry.obj T ⋙ G ≅ F.prod F ⋙ Functor.uncurry.obj T') (P : C) :
    T.obj P ⋙ G ≅ F ⋙ T'.obj (F.obj P) :=
  NatIso.ofComponents (fun K => τ.app (P, K)) (fun f => by
    simpa using τ.hom.naturality (Prod.mkHom (𝟙 P) f))

/-- For a functor `F` commuting with the shifts and `a : M ⟶ N[1]`, `F` of `a[i]` followed by
`N[1][i] ≅ N[1 + i]` and the commutation of `F` with the shift by `1 + i` is the commutation of `F`
with the shift by `i`, followed by `(F a ≫ (F N[1] ≅ (F N)[1]))[i]` and
`(F N)[1][i] ≅ (F N)[1 + i]`. -/
theorem map_comp_shiftFunctorAdd'_inv_commShiftIso {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] {M N : C} (a : M ⟶ N⟦(1 : ℤ)⟧)
    (i j : ℤ) (h : 1 + i = j) :
    F.map (a⟦i⟧' ≫ (shiftFunctorAdd' C 1 i j h).inv.app N) ≫ (F.commShiftIso j).hom.app N =
      (F.commShiftIso i).hom.app M ≫ (F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app N)⟦i⟧' ≫
        (shiftFunctorAdd' D 1 i j h).inv.app (F.obj N) := by
  rw [F.commShiftIso_add' h, CommShift.isoAdd'_hom_app, F.map_comp, Category.assoc,
    ← F.map_comp_assoc ((shiftFunctorAdd' C 1 i j h).inv.app N), Iso.inv_hom_id_app,
    F.map_id, Category.id_comp, commShiftIso_hom_naturality_assoc, Functor.map_comp,
    Category.assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- For a perfect object `E` on an algebraic space, the isomorphism of functors
`RSheafHom(E, -) ≅ E^∨ ⊗^L -`. -/
def smallEtaleDerivedSheafHomTensorDualNatIso
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    (smallEtaleDerivedSheafHom B S hS X).obj (op E) ≅
      (smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E) :=
  let e := smallEtaleModelDerivedEquivalence B S hS X
  let M := smallEtaleModelRingedSite B S hS X.1 X.2
  let hE' := isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X E hE
  let α : (RingedSite.derivedSheafHomBifunctor M).obj (op (e.functor.obj E)) ≅
      (Stacks.SheafOfModules.derivedTensorProductFunctor M).flip.obj
        (RingedSite.derivedDual M (e.functor.obj E)) :=
    (NatIso.ofComponents
      (fun G => RingedSite.derivedDualTensorSheafHomIso M (e.functor.obj E) G hE')
      (fun f => RingedSite.derivedDualTensorSheafHomIso_naturality M (e.functor.obj E) hE' f)).symm
  let β : (Stacks.SheafOfModules.derivedTensorProductFunctor M).flip.obj
        (RingedSite.derivedDual M (e.functor.obj E)) ≅
      (Stacks.SheafOfModules.derivedTensorProductFunctor M).obj
        (RingedSite.derivedDual M (e.functor.obj E)) :=
    ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso M
      (RingedSite.canonicalRingedSiteDerivedTensorProduct M)).app _).symm
  let γ : (Stacks.SheafOfModules.derivedTensorProductFunctor M).obj
        (RingedSite.derivedDual M (e.functor.obj E)) ≅
      (Stacks.SheafOfModules.derivedTensorProductFunctor M).obj
        (e.functor.obj (smallEtaleDerivedDual B S hS X E)) :=
    (Stacks.SheafOfModules.derivedTensorProductFunctor M).mapIso
      (smallEtaleModelDerivedDualIso B S hS X E).symm
  let δ := Functor.objIsoOfUncurryIso (smallEtaleModelDerivedTensorIso B S hS X)
    (smallEtaleDerivedDual B S hS X E)
  Functor.isoWhiskerLeft e.functor (Functor.isoWhiskerRight (α ≪≫ β ≪≫ γ) e.inverse) ≪≫
    Functor.isoWhiskerRight δ.symm e.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- Tensoring with a fixed object on the right is additive. -/
instance smallEtaleDerivedTensor_flip_obj_additive
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedTensor B S hS X).flip.obj P).Additive := by
  let := (smallEtaleDerivedTensorProduct B S hS X).commShift₂.commShiftFlipObj P
  have := (smallEtaleDerivedTensorProduct B S hS X).exact_left P
  exact inferInstanceAs ((smallEtaleDerivedTensorProduct B S hS X).tensor.flip.obj P).Additive

/-- The identification `Hom(E, M) ≃+ Hom(𝒪_X, E^∨ ⊗^L M)` for a perfect `E`. -/
def smallEtaleHomAddEquivUnitTensorDual
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (E ⟶ M) ≃+ (structureDerived X ⟶
      ((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj M) :=
  let lu : ((smallEtaleDerivedTensor B S hS X).flip.obj E).obj
      (structureDerived X) ≅ E :=
    (smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app E
  let ρ := (smallEtaleDerivedSheafHomTensorDualNatIso B S hS X E hE).app M
  { toFun := fun g => (smallEtaleDerivedTensorSheafHomAdjunction B S hS X E).homEquiv _ _
        (lu.hom ≫ g) ≫ ρ.hom
    invFun := fun h => lu.inv ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X E).homEquiv _ _).symm (h ≫ ρ.inv)
    left_inv := fun g => by simp
    right_inv := fun h => by simp
    map_add' := fun g g' => by
      rw [Preadditive.comp_add,
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X E).homAddEquiv_add,
        Preadditive.add_comp] }

/-- The identification `Hom(E, M) ≃+ Hom(𝒪_X, E^∨ ⊗^L M)` is natural in `M`. -/
theorem smallEtaleHomAddEquivUnitTensorDual_naturality
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    {M M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (q : M ⟶ M') (g : E ⟶ M) :
    smallEtaleHomAddEquivUnitTensorDual B S hS X E hE M' (g ≫ q) =
      smallEtaleHomAddEquivUnitTensorDual B S hS X E hE M g ≫
        ((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).map q := by
  dsimp only [smallEtaleHomAddEquivUnitTensorDual, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, Category.assoc, Iso.app_hom,
    Iso.app_hom, NatTrans.naturality, Category.assoc]

/-- Tensoring with a fixed object on the left commutes with the shifts. -/
instance smallEtaleDerivedTensor_obj_commShift
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedTensor B S hS X).obj P).CommShift ℤ :=
  (smallEtaleDerivedTensorProduct B S hS X).commShift₂.commShiftObj P

/-- The identification `Ext^i(E, M) ≃+ Hom(𝒪_X, (E^∨ ⊗^L M)[i])` for a perfect `E`: the
identification `smallEtaleHomAddEquivUnitTensorDual` at `M[i]`, followed by the commutation of
`E^∨ ⊗^L -` with the shift. -/
def smallEtaleExtAddEquivUnitTensorDual
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (i : ℤ) :
    (E ⟶ M⟦i⟧) ≃+ (structureDerived X ⟶
      (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj M)⟦i⟧) :=
  let c := (((smallEtaleDerivedTensor B S hS X).obj
    (smallEtaleDerivedDual B S hS X E)).commShiftIso i).app M
  (smallEtaleHomAddEquivUnitTensorDual B S hS X E hE (M⟦i⟧)).trans
    { toFun := fun h => h ≫ c.hom
      invFun := fun h => h ≫ c.inv
      left_inv := fun h => by simp
      right_inv := fun h => by simp
      map_add' := fun h h' => Preadditive.add_comp _ _ _ _ _ _ }

/-- The identification `smallEtaleExtAddEquivUnitTensorDual` is natural in `M`. -/
theorem smallEtaleExtAddEquivUnitTensorDual_naturality
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    {M M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (q : M ⟶ M') (i : ℤ) (g : E ⟶ M⟦i⟧) :
    smallEtaleExtAddEquivUnitTensorDual B S hS X E hE M' i (g ≫ q⟦i⟧') =
      smallEtaleExtAddEquivUnitTensorDual B S hS X E hE M i g ≫
        (((smallEtaleDerivedTensor B S hS X).obj
          (smallEtaleDerivedDual B S hS X E)).map q)⟦i⟧' := by
  dsimp only [smallEtaleExtAddEquivUnitTensorDual, AddEquiv.trans_apply, AddEquiv.coe_mk,
    Equiv.coe_fn_mk, Iso.app_hom]
  rw [smallEtaleHomAddEquivUnitTensorDual_naturality, Category.assoc, Category.assoc,
    Functor.commShiftIso_hom_naturality]

/-- The identification `smallEtaleExtAddEquivUnitTensorDual` is compatible with boundary
maps: for `a : M ⟶ N[1]` (the third morphism of a distinguished triangle), composing with
`a[i]` and `N[1][i] ≅ N[i + 1]` on `Ext^•(E, -)` corresponds to composing with
`(E^∨ ⊗^L a)[i]`, the commutation of `E^∨ ⊗^L -` with the shift, and the same identification on
`Hom(𝒪_X, (E^∨ ⊗^L -)[•])`. -/
theorem smallEtaleExtAddEquivUnitTensorDual_shift
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    {M N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (a : M ⟶ N⟦(1 : ℤ)⟧) (i j : ℤ) (h : 1 + i = j) (g : E ⟶ M⟦i⟧) :
    smallEtaleExtAddEquivUnitTensorDual B S hS X E hE N j
        (g ≫ a⟦i⟧' ≫ (shiftFunctorAdd' _ 1 i j h).inv.app N) =
      smallEtaleExtAddEquivUnitTensorDual B S hS X E hE M i g ≫
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).map a ≫
          (((smallEtaleDerivedTensor B S hS X).obj
            (smallEtaleDerivedDual B S hS X E)).commShiftIso (1 : ℤ)).hom.app N)⟦i⟧' ≫
        (shiftFunctorAdd' _ 1 i j h).inv.app
          (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj N) := by
  dsimp only [smallEtaleExtAddEquivUnitTensorDual, AddEquiv.trans_apply, AddEquiv.coe_mk,
    Equiv.coe_fn_mk, Iso.app_hom]
  rw [smallEtaleHomAddEquivUnitTensorDual_naturality, Category.assoc,
    Functor.map_comp_shiftFunctorAdd'_inv_commShiftIso
      ((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)) a i j h,
    Category.assoc]

end AlgebraicGeometry.Space

end
