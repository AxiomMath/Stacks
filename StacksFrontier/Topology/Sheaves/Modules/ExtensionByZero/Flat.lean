module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.FlatCover
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Flatness of the extension by zero of the structure sheaf

Let `(X, 𝒪)` be a topological space with a sheaf of commutative rings, let `U ⊆ X` be open with
inclusion `j : U → X`, and let `j_! : Mod(𝒪|_U) ⥤ Mod(𝒪)` be the extension-by-zero functor. This
file proves that `j_! (𝒪|_U)` is a flat sheaf of `𝒪`-modules, and deduces that every sheaf of
modules on a ringed space is a quotient of a flat one: the explicit cover by a direct sum of
such extensions by zero is a cover by a flat sheaf.

## Shape of the argument

Flatness of a sheaf of modules on a ringed space is a condition on its stalks
(`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`), and the stalks of `j_! (𝒪|_U)` are
computed as follows.

* Off `U` the stalk vanishes (`ExtensionByZeroModules.isZero_stalk_jShriek`), and a subsingleton
  module is flat.
* At a point of `U` the stalk is the local ring `𝒪_x`, free of rank one and hence flat. The
  identification is induced by an honest morphism `j_! (𝒪|_U) ⟶ 𝒪` of sheaves of `𝒪`-modules —
  the counit of `j_! ⊣ j^*` at the structure sheaf, using that `j^* 𝒪` *is* `𝒪|_U` — so the
  induced map of stalks is `𝒪_x`-linear with no change of scalars to track. That the counit is
  invertible on the stalk at a point of `U` is the right triangle identity together with
  invertibility of the unit, transported through `TopCat.Presheaf.stalkRestrictIso`.

## Main definitions

* `ExtensionByZeroModules.jShriekUnitToUnit`: the canonical morphism `j_! (𝒪|_U) ⟶ 𝒪`.
* `ExtensionByZeroModules.jShriekUnitStalkLEquiv`: at a point of `U` it identifies the stalk of
  `j_! (𝒪|_U)` with the stalk of `𝒪`, linearly over the stalk of the sheaf of rings.

## Main results

* `AlgebraicGeometry.SheafOfModules.flat_stalk_of_linearEquiv_ringCatStalk`: a stalk that is free
  of rank one over the `RingCat`-valued stalk of the structure sheaf is flat over its
  `CommRingCat`-valued stalk.
* `AlgebraicGeometry.SheafOfModules.isFlat_jShriek_unit`: `j_! (𝒪|_U)` is flat.
* `Stacks.SheafOfModules.exists_epi_from_flat`: every sheaf of modules on a ringed space is a
  quotient of a flat sheaf of modules.

## Implementation notes

The scalars on a module stalk come in two spellings, over the stalk of `𝒪` as a sheaf of
commutative rings and over the stalk of the underlying sheaf of rings; the flatness criterion of
Tag 05NE is stated in the first and the stalk-of-a-morphism API of
`LocallyFreeRank.stalkLMap`/`LocallyFreeRank.unitStalkLEquiv` in the second. The two are
reconciled once and for all by `flat_stalk_of_linearEquiv_ringCatStalk`, which transports the
scalars along `SemilinearStalk.commStalkRingEquiv`; stating it for an abstract presheaf of
modules over `R ⋙ forget₂ CommRingCat RingCat` is what makes the module instances on the two
stalks the ones that instance search finds.

## References

* [Stacks Project, Tag 05NH](https://stacks.math.columbia.edu/tag/05NH)
* [Stacks Project, Tag 05NI](https://stacks.math.columbia.edu/tag/05NI)
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace ExtensionByZeroModules

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

variable {X : TopCat.{u}} (U : Opens X) (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The canonical morphism `j_! (𝒪|_U) ⟶ 𝒪`: the counit of `j_! ⊣ j^*` at `𝒪`, viewed as a sheaf
of modules over itself, using that `j^* 𝒪` is `𝒪|_U`. -/
def jShriekUnitToUnit :
    (jShriek U O).obj (SheafOfModules.unit (resRing U O)) ⟶ SheafOfModules.unit O :=
  (jShriekAdjunction U O).counit.app (SheafOfModules.unit O)

/-- `jShriekUnitToUnit` is invertible on the stalk at a point of `U`: the right triangle identity
makes `j^*` of the counit a split epimorphism with invertible section, hence invertible, and the
stalk of `j^*` of a morphism at `u ∈ U` is the stalk of the morphism at `j u`
(`TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff`). -/
lemma isIso_stalk_jShriekUnitToUnit (x : X) (hx : x ∈ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toAb O).map (jShriekUnitToUnit U O))) := by
  have := isIso_jShriekAdjunction_unit U O
  set φ := (jShriekAdjunction U O).counit.app (SheafOfModules.unit O) with hφ
  have hR : IsIso ((jStar U O).map φ) :=
    isIso_of_hom_comp_eq_id _
      ((jShriekAdjunction U O).right_triangle_components (SheafOfModules.unit O))
  have hab : IsIso ((toAb (resRing U O)).map ((jStar U O).map φ)) :=
    Functor.map_isIso (toAb (resRing U O)) ((jStar U O).map φ)
  have hwhisk : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op ((toAb O).map φ)) := by
    rw [← toAb_jStar_map U O φ]; exact hab
  have hw : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : Usp U)).map
      (Functor.whiskerLeft (TopCat.Presheaf.imF U).op ((toAb O).map φ))) :=
    Functor.map_isIso _ _
  exact (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
    ((toAb O).map φ) ⟨x, hx⟩).mp hw

/-- **The stalk of `j_! (𝒪|_U)` at a point of `U` is free of rank one.** It is the stalk of `𝒪`
there, linearly over the stalk of the sheaf of rings, by `jShriekUnitToUnit` together with
`LocallyFreeRank.unitStalkLEquiv`. -/
def jShriekUnitStalkLEquiv (x : X) (hx : x ∈ U) :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((jShriek U O).obj (SheafOfModules.unit (resRing U O))).val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj x)]
      ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj x) :=
  have hbij : Function.Bijective (LocallyFreeRank.stalkLMap
      ((SheafOfModules.forget O).map (jShriekUnitToUnit U O)) x) :=
    (ConcreteCategory.isIso_iff_bijective _).mp (isIso_stalk_jShriekUnitToUnit U O x hx)
  (LinearEquiv.ofBijective _ hbij).trans (LocallyFreeRank.unitStalkLEquiv O.obj x)

end ExtensionByZeroModules

namespace AlgebraicGeometry.SheafOfModules

/-- Sheaves of abelian groups on the opens of `X` admit sheafification. -/
local instance (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the opens of `X`, a morphism of presheaves of abelian groups becomes an isomorphism
after sheafification exactly when it is locally bijective. -/
local instance (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- A module stalk that is free of rank one over the stalk of the underlying sheaf of rings is
flat over the stalk of the sheaf of commutative rings. The two sets of scalars are identified by
`SemilinearStalk.commStalkRingEquiv`, which is compatible with both actions by
`SemilinearStalk.comm_smul_eq`. -/
theorem flat_stalk_of_linearEquiv_ringCatStalk {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X)
    (M : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : X)
    (e : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
        ≃ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
            (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)]
        ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)) :
    Module.Flat (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)) := by
  let eR := SemilinearStalk.commStalkRingEquiv R x
  refine Module.Flat.of_linearEquiv
    { toFun := fun m => eR (e m)
      invFun := fun r => e.symm (eR.symm r)
      left_inv := fun m => by simp
      right_inv := fun r => by simp
      map_add' := fun m n => by simp
      map_smul' := ?_ }
  intro r m
  have hsmul : r • m = eR.symm r • m := by
    simpa only [eR, RingEquiv.apply_symm_apply] using
      SemilinearStalk.comm_smul_eq R x M (eR.symm r) m
  rw [hsmul, e.map_smul]
  simp [eR, smul_eq_mul]

/-- **Stacks 05NH.** The extension by zero of the structure sheaf of an open subset of a ringed
space is a flat sheaf of modules. -/
@[stacks 05NH]
theorem isFlat_jShriek_unit {X : TopCat.{u}} (U : Opens X)
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    IsFlat.{u, u, u, u} (O := O)
      ((ExtensionByZeroModules.jShriek U (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)).obj
        (_root_.SheafOfModules.unit
          (ExtensionByZeroModules.resRing U
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)))) := by
  set OX := Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O with hOX
  set F := (ExtensionByZeroModules.jShriek U OX).obj
    (_root_.SheafOfModules.unit (ExtensionByZeroModules.resRing U OX)) with hF
  rw [isFlat_iff_stalk_flat]
  intro x
  let _ : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) O.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) F.val.presheaf x) :=
    inferInstanceAs (Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) O.obj x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        ((id F.val : _root_.PresheafOfModules.{u}
          (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf) x))
  by_cases hx : x ∈ U
  · exact flat_stalk_of_linearEquiv_ringCatStalk O.obj
      (id F.val : _root_.PresheafOfModules.{u}
        (O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) x
      (ExtensionByZeroModules.jShriekUnitStalkLEquiv U OX x hx)
  · have hz : IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) F.val.presheaf x) :=
      ExtensionByZeroModules.isZero_stalk_jShriek U OX
        (_root_.SheafOfModules.unit (ExtensionByZeroModules.resRing U OX)) x hx
    have hsub : Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (X := X) F.val.presheaf x) := AddCommGrpCat.isZero_iff_subsingleton.mp hz
    rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ f hf a b hab
    exact Subsingleton.elim _ _

end AlgebraicGeometry.SheafOfModules

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules

/-- Sheaves of abelian groups on the opens of `X` admit sheafification. -/
local instance (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the opens of `X`, a morphism of presheaves of abelian groups becomes an isomorphism
after sheafification exactly when it is locally bijective. -/
local instance (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **Stacks 05NI, part (2).** Every sheaf of modules on a ringed space is a quotient of a flat
sheaf of modules: the explicit cover of part (1) is a direct sum of extensions by zero of
structure sheaves, each flat by Stacks 05NH, and a direct sum of flat sheaves is flat. -/
@[stacks 05NI "part (2)"]
theorem exists_epi_from_flat {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (F : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) :
    ∃ (P : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
        (f : P ⟶ F),
      IsFlat.{u, u, u, u} (O := O) P ∧ Epi f := by
  obtain ⟨I, U, f, hf⟩ :=
    exists_epi_from_coproduct_jShriek_unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) F
  exact ⟨_, f, FlatColimits.isFlat_coproduct (O := O) _ fun i => isFlat_jShriek_unit (U i) O, hf⟩

end Stacks.SheafOfModules
