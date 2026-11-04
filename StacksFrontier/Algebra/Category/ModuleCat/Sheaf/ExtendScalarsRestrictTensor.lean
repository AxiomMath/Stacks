module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatNeighbourhoodTensorUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RestrictScalarsSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorColimits

/-!
# Extension of scalars, read back over the source ring, is tensoring with the target ring

Let `α : 𝒪 ⟶ 𝒪'` be a homomorphism of sheaves of commutative rings on a site. Extension of
scalars `Mod(𝒪) ⥤ Mod(𝒪')` of [Stacks, Tag 03CZ] is the sectionwise tensor product
`𝒪'(U) ⊗_{𝒪(U)} -`, sheafified. This file identifies the composite with restriction of scalars,

`extendScalars α ⋙ restrictScalars α ≅ - ⊗_𝒪 𝒪'`,

where the right-hand side is `(Stacks.SheafOfModules.Tensor.sheafTensor 𝒪).flip.obj 𝒪'`, the
endofunctor of `Mod(𝒪)` that [Stacks, Tag 099H] is stated for.

## Main definitions

* `Stacks.SheafOfModules.ExtendScalarsTensor.presheafExtendRestrictTensorIso`: the identification
  before sheafification, `𝒪' ⊗_{𝒪} P` read over `𝒪` is `P ⊗_𝒪 𝒪'`.
* `Stacks.SheafOfModules.ExtendScalarsTensor.sheafifyRestrictNatIso`: restriction of scalars
  commutes with sheafification, as a natural isomorphism.
* `Stacks.SheafOfModules.ExtendScalarsTensor.extendRestrictScalarsTensorIso`: the identification
  itself.

## Implementation notes

Both sides are sheafifications of a sectionwise tensor product, so the comparison is built in
two steps and then whiskered: the presheaf-level symmetry of the tensor product, and the
commutation of restriction of scalars with sheafification
(`AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso`, whose naturality holds by
`rfl` because the comparison is the identity on sections).

The presheaf step is *not* `rfl` at the level of functors, although it is at the level of
objects: `Stacks.PresheafOfModules.ChangeOfRings.cofObj` and
`AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj` produce the same presheaf of
modules on the nose, while the two actions on morphisms — `LinearMap.baseChange` against
`TensorProduct.map LinearMap.id` — are definitionally equal only at a cost the elaborator will
not pay in one step. So `changeOfRings_restrictScalars_app` records the agreement one object of
the site at a time, which is cheap, and the natural isomorphism is assembled from that.

The identification is assembled by whiskering rather than from components, because a component
of the composite mentions `G.val` at the `Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the
ring sheaf while the change-of-rings machinery is indexed by `Stacks.ringPresheaf`; the two are
the same presheaf but not at the transparency `rw` and `dsimp` check their arguments under.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 099H](https://stacks.math.columbia.edu/tag/099H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules.ExtendScalarsTensor

open AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  {O O' : Sheaf J CommRingCat.{w}} (α : O ⟶ O')

/-- The identity of the presheaf of rings underlying a sheaf of commutative rings is locally
injective. -/
instance isLocallyInjective_id_underlyingRingSheaf :
    Presheaf.IsLocallyInjective J (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h ↦ h

/-- The identity of the presheaf of rings underlying a sheaf of commutative rings is locally
surjective. -/
instance isLocallySurjective_id_underlyingRingSheaf :
    Presheaf.IsLocallySurjective J (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ x ↦ ⟨x, rfl⟩

variable (O) in
/-- Sheafification of presheaves of `O`-modules. -/
abbrev shf : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
    _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)

/-- The morphism of sheaves of rings underlying `α`. -/
abbrev ringSheafMap :
    Stacks.SheafOfModules.Tensor.ringSheaf O ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O' :=
  Stacks.Sheaves.RingedToposModules.commRingSheafMap J α.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf O).cond (Stacks.SheafOfModules.Tensor.ringSheaf O').cond

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
/-- `ringSheafMap α` is the image of `α` under the functor forgetting commutativity of sheaves
of rings. -/
theorem ringSheafMap_eq :
    ringSheafMap α = (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α := rfl

/-- `O'`, read as a presheaf of `O`-modules. -/
abbrev restrictedRingPresheaf :
    PresheafOfModules.{w} (Stacks.ringPresheaf O.obj) :=
  (Stacks.Sheaves.FlatNeighbourhood.RestrictedRingModule α).val

/-! ## The presheaf level -/

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
/-- Sectionwise extension of scalars read back over `O` is, at each object of the site,
tensoring on the left with `O'`: the comparison is the identity on sections. -/
theorem changeOfRings_restrictScalars_app
    {P Q : PresheafOfModules.{w} (Stacks.ringPresheaf O.obj)} (φ : P ⟶ Q) (X : Cᵒᵖ) :
    ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars α.hom).map
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α.hom).map φ)).app X =
      ((PresheafOfModules.tensorLeft (restrictedRingPresheaf α)).map φ).app X := rfl

/-- Sectionwise extension of scalars along `α` for presheaves of modules, read back over `O`,
is tensoring with `O'`. -/
def presheafExtendRestrictTensorIso :
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α.hom ⋙
        Stacks.PresheafOfModules.ChangeOfRings.restrictScalars α.hom ≅
      PresheafOfModules.tensorRight (restrictedRingPresheaf α) :=
  NatIso.ofComponents
    (fun P => (PresheafOfModules.tensorLeftIsoTensorRight (restrictedRingPresheaf α)).app P) (by
      intro P Q φ
      refine PresheafOfModules.hom_ext ?_
      intro X
      have h := congrArg (fun k : _ ⟶ _ => PresheafOfModules.Hom.app k X)
        ((PresheafOfModules.tensorLeftIsoTensorRight
          (restrictedRingPresheaf α)).hom.naturality φ)
      simp only [PresheafOfModules.comp_app, Functor.comp_map] at h ⊢
      rw [changeOfRings_restrictScalars_app α φ X]
      exact h)

/-! ## The sheaf level -/

/-- Restriction of scalars along `α` commutes with sheafification. -/
def sheafifyRestrictIso (P : PresheafOfModules.{w} (Stacks.ringPresheaf O'.obj)) :
    (_root_.SheafOfModules.restrictScalars (ringSheafMap α)).obj
        ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O')
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).obj P) ≅
      (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj
        ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars α.hom).obj P) :=
  restrictScalarsSheafificationIso (ringSheafMap α) P

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The isomorphisms `sheafifyRestrictIso α P` are natural in the presheaf of `O'`-modules `P`.
-/
theorem sheafifyRestrictIso_naturality
    {P Q : PresheafOfModules.{w} (Stacks.ringPresheaf O'.obj)} (f : P ⟶ Q) :
    (_root_.SheafOfModules.restrictScalars (ringSheafMap α)).map
          ((shf O').map f) ≫
        (sheafifyRestrictIso α Q).hom =
      (sheafifyRestrictIso α P).hom ≫
        (shf O).map
          ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars α.hom).map f) := rfl

/-- Restriction of scalars along `α` commutes with sheafification, as a natural isomorphism.
-/
def sheafifyRestrictNatIso :
    shf O' ⋙ _root_.SheafOfModules.restrictScalars (ringSheafMap α) ≅
      Stacks.PresheafOfModules.ChangeOfRings.restrictScalars α.hom ⋙ shf O :=
  NatIso.ofComponents (sheafifyRestrictIso α) (fun f => sheafifyRestrictIso_naturality α f)

/-- Extension of scalars along `α`, for sheaves of modules: the sectionwise tensor product,
sheafified. -/
abbrev extendScalarsSheaf :
    _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O') :=
  Stacks.Sheaves.RingedToposModules.extendScalars J α.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf O).cond (Stacks.SheafOfModules.Tensor.ringSheaf O').cond

/-- Extension of scalars along `α` is left adjoint to restriction of scalars along `α`
([Stacks, Tag 03CZ]). -/
def adjunction :
    extendScalarsSheaf α ⊣ _root_.SheafOfModules.restrictScalars (ringSheafMap α) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction J α.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf O).cond (Stacks.SheafOfModules.Tensor.ringSheaf O').cond

/-- Extension of scalars is a left adjoint. -/
instance isLeftAdjoint_extendScalarsSheaf : (extendScalarsSheaf α).IsLeftAdjoint :=
  (adjunction α).isLeftAdjoint

/-- Extension of scalars preserves all colimits indexed in the module universe: it is a left
adjoint. -/
instance preservesFiniteColimits_extendScalarsSheaf :
    Limits.PreservesFiniteColimits (extendScalarsSheaf α) := inferInstance

/-- Extension of scalars is additive: it is left adjoint to restriction of scalars, which
is. -/
instance additive_extendScalarsSheaf : (extendScalarsSheaf α).Additive :=
  Adjunction.left_adjoint_additive (adjunction α)

/-- Extension of scalars along `α`, read back over `O`, is tensoring with `O'`. -/
def extendRestrictScalarsTensorIso :
    extendScalarsSheaf α ⋙ _root_.SheafOfModules.restrictScalars (ringSheafMap α) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
        (Stacks.Sheaves.FlatNeighbourhood.RestrictedRingModule α) :=
  Functor.isoWhiskerLeft
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α.hom)
      (sheafifyRestrictNatIso α) ≪≫
    Functor.isoWhiskerLeft (_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (Functor.isoWhiskerRight (presheafExtendRestrictTensorIso α) (shf O))

/-- `extendRestrictScalarsTensorIso` is compatible with the units: at every sheaf of
`O`-modules `G` the unit `G ⟶ (G ⊗_O O')_{O}` of the change-of-rings adjunction, read through
`extendRestrictScalarsTensorIso`, is the canonical map `x ↦ x ⊗ 1` of
`Stacks.Sheaves.FlatNeighbourhood.tensorUnitMap` — the map [Stacks, Tag 099H] is stated for.

Both are sections of a sheafification, so the comparison is checked on sections: the unit sends
`x` to the image of `1 ⊗ x`
(`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`),
the comparison is the identity on sections followed by the sheafified braiding, and the
braiding carries `1 ⊗ x` to `x ⊗ 1`. -/
theorem adjunction_unit_comp_extendRestrictScalarsTensorIso
    (G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (adjunction α).unit.app G ≫ (extendRestrictScalarsTensorIso α).hom.app G =
      (Stacks.Sheaves.FlatNeighbourhood.tensorUnitMap α G).val := by
  apply (_root_.SheafOfModules.fullyFaithfulForget
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).map_injective
  refine PresheafOfModules.hom_ext ?_
  intro X
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext (fun x => ?_)
  let := (α.hom.app X).hom.toAlgebra
  let e : ((PresheafOfModules.tensorLeft (restrictedRingPresheaf α)).obj G.val).obj X :=
    (1 : O'.obj.obj X) ⊗ₜ x
  have hnat := (PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.naturality
      ((PresheafOfModules.tensorLeftIsoTensorRight (restrictedRingPresheaf α)).hom.app G.val)
  have key1 := congrArg (fun k : _ ⟶ _ => PresheafOfModules.Hom.app k X) hnat
  have key2 := congrArg (fun m : _ ⟶ _ => (ModuleCat.Hom.hom m) e) key1
  have key :
      ((((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          ((PresheafOfModules.tensorRight (restrictedRingPresheaf α)).obj G.val)).app X).hom
        ((((PresheafOfModules.tensorLeftIsoTensorRight
            (restrictedRingPresheaf α)).hom.app G.val).app X).hom e)) =
      ((((shf O).map ((PresheafOfModules.tensorLeftIsoTensorRight
            (restrictedRingPresheaf α)).hom.app G.val)).val.app X).hom
        ((((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          ((PresheafOfModules.tensorLeft (restrictedRingPresheaf α)).obj G.val)).app X).hom e)) :=
    key2
  have hbridge :
      (ConcreteCategory.hom ((CategoryTheory.toSheafify J
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α.hom).obj
            G.val).presheaf).app X)) e =
      ((((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
          ((PresheafOfModules.tensorLeft (restrictedRingPresheaf α)).obj G.val)).app X).hom e) :=
    rfl
  have hu :=
    (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply
      J α.hom (Stacks.SheafOfModules.Tensor.ringSheaf O).cond
      (Stacks.SheafOfModules.Tensor.ringSheaf O').cond
      G X x).trans hbridge
  have hr := (Stacks.Sheaves.FlatNeighbourhood.tensorUnitMap α G).2 X x
  refine Eq.trans ?_ hr.symm
  exact (congrArg (fun z => ((((shf O).map ((PresheafOfModules.tensorLeftIsoTensorRight
      (restrictedRingPresheaf α)).hom.app G.val)).val.app X).hom z)) hu).trans key.symm

end Stacks.SheafOfModules.ExtendScalarsTensor

end
