module

public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TrivializationFromAGenerator

/-!
# The tensor product of two generator torsors

If `s` trivializes `L` over an open `U` and `t` trivializes `N` over `U`, then the section
`s ⊗ t` of `L ⊗ N` over `U` trivializes `L ⊗ N`.  This pairing of trivializing sections is
natural in `U` and equivariant for the action of units in each variable, so it is a pairing of
the generator torsors of `L` and `N` into the generator torsor of `L ⊗ N`.  Since the class of
a torsor carrying such a pairing is the sum of the classes of the two factors, this is what
makes the classification of invertible modules by first cohomology additive.

## Main definitions

* `Stacks.Cohomology.Generators.tensorGeneratorSections`: the trivializing section `s ⊗ t` of
  `L ⊗ N`.
* `Stacks.Cohomology.Generators.generatorTorsorTensorPairing`: the resulting pairing of
  generator torsors.

## Main results

* `Stacks.Cohomology.Generators.bijective_smul_toTensorSheafSection`: multiplication by
  `s ⊗ t` is bijective on sections over `U`, which is why `s ⊗ t` is a trivializing section.
* `Stacks.Cohomology.Generators.toTensorSheafSection_restrict`,
  `Stacks.Cohomology.Generators.toTensorSheafSection_smul_left` and
  `Stacks.Cohomology.Generators.toTensorSheafSection_smul_right`: the comparison map from the
  presheaf tensor product commutes with restriction and is bilinear on pure tensors.

## Implementation notes

The trivializing section is *defined* to be the image of the pure tensor `s ⊗ₜ t` under the
comparison map `toTensorSheafSection` into the tensor product sheaf, so the three laws of the
pairing are the three lemmas above.  What has to be proved is that it trivializes, and this is
done by identifying it with the image of `1` under an isomorphism `𝒪_U ≅ (L ⊗ N)|_U`.  That
isomorphism is assembled from the two trivializations of `L` and `N` over `U`, the left unit
constraint of the tensor product, and `AlgebraicGeometry.tensorRestrictionIso`, which says that
the tensor product commutes with restriction to an open.  Reading the composite on `1` uses
`AlgebraicGeometry.tensorRestrictionIso_inv_val_app_toSheafify` for the last factor and
`Stacks.Cohomology.Generators.tensorPresheafLeftUnitor_toSheafify_tmul` for the first.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TensorProduct TopologicalSpace

universe u

namespace Stacks.Cohomology.Generators

section LeftUnitor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{u})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The left unit constraint of the tensor product of presheaves of modules, written for the
presheaf tensor product of the structure sheaf with a sheaf of modules. -/
def tensorPresheafLeftUnitor
    (M : SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (PresheafOfModules.tensorObj (O := O) ((SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val) (M.val)) ⟶
      M.val := by
  let _ : MonoidalCategory (PresheafOfModules
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) := by
    change MonoidalCategory (PresheafOfModules
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    infer_instance
  change (SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val ⊗ M.val ⟶ M.val
  exact (MonoidalCategory.leftUnitor M.val).hom

/-- The left unit constraint of the tensor product of sheaves of modules is the sheafification
of the one on presheaves: composing it with the sheafification unit gives the latter back. -/
theorem toSheafify_tensorProductLeftUnitor
    (M : SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        ((PresheafOfModules.tensorObj (O := O) ((SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val) (M.val))) ≫
      (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor O hO M).hom.val =
        tensorPresheafLeftUnitor O hO M := by
  let P := PresheafOfModules.tensorObj (O := O)
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val M.val
  let adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO
  have hhom : (adj.homEquiv P M)
      (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor O hO M).hom =
        tensorPresheafLeftUnitor O hO M := by
    have hsource : (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor O hO M).hom =
        (adj.homEquiv P M).symm (tensorPresheafLeftUnitor O hO M) := by
      let _ : MonoidalCategory (PresheafOfModules
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) := by
        show MonoidalCategory (PresheafOfModules
          (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
        infer_instance
      dsimp [adj, Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor,
        tensorPresheafLeftUnitor]
      rfl
    rw [hsource]
    exact Equiv.apply_symm_apply _ _
  exact (Adjunction.homEquiv_unit adj P M _).symm.trans hhom

/-- The left unit constraint carries the sheafification of the pure tensor `r ⊗ s` of two
sections of the structure sheaf to their product. -/
theorem tensorPresheafLeftUnitor_toSheafify_tmul (U : C) (r s : O.obj (op U)) :
    ((Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor O hO
      (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).hom.val.app (op U)).hom
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
        ((PresheafOfModules.tensorObj (O := O) ((SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val)
          ((SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val)))).app
              (op U)).hom
        (r ⊗ₜ[O.obj (op U)] s)) = r * s := by
  let _ : CommRing (O.obj (op U)) := inferInstance
  let _ : MonoidalCategory (PresheafOfModules
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) := by
    show MonoidalCategory (PresheafOfModules
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    infer_instance
  let _ : Module (O.obj (op U)) (O.obj (op U)) := inferInstance
  have h := congrArg (fun f => (f.app (op U)).hom (r ⊗ₜ[O.obj (op U)] s))
    (toSheafify_tensorProductLeftUnitor O hO
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))
  have hmul : (tensorPresheafLeftUnitor O hO
      (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).app (op U)
      (r ⊗ₜ[O.obj (op U)] s) = r * s := by
    show (TensorProduct.lid (O.obj (op U)) (O.obj (op U)) (r ⊗ₜ[O.obj (op U)] s)) = r * s
    simp
  exact h.trans hmul

/-- The tensor product of two morphisms of presheaves of modules, read on a pure tensor of
sections. -/
theorem tensorPresheafHom_app_tmul
    {A A' B B' : PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}
    (f : A ⟶ A') (g : B ⟶ B') (W : Cᵒᵖ) (a : A.obj W) (b : B.obj W) :
    ((f ⊗ₘ g).app W).hom (a ⊗ₜ[O.obj W] b) =
      ((f.app W).hom a) ⊗ₜ[O.obj W] ((g.app W).hom b) := rfl

end LeftUnitor

section Tensor

variable (X : RingedSpace.{u, u})
  (L N : SheafOfModules.{u} (structureSheafRing X))

/-- The comparison map into the tensor product sheaf commutes with restriction. -/
theorem toTensorSheafSection_restrict {U V : Opens X.carrier} (h : V ≤ U)
    (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
        (N))).val.map (homOfLE h).op
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
          (s ⊗ₜ t)) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op V)
        ((L.val.map (homOfLE h).op).hom s ⊗ₜ (N.val.map (homOfLE h).op).hom t) := by
  let P := PresheafOfModules.tensorObj (O := X.presheaf) L.val N.val
  let η := Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X P
  have happ := congrArg (fun f => f.hom (s ⊗ₜ t)) (η.naturality (homOfLE h).op)
  change (η.app (op V)).hom ((P.map (homOfLE h).op).hom (s ⊗ₜ t)) =
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj L).obj N).val.map
      (homOfLE h).op).hom ((η.app (op U)).hom (s ⊗ₜ t)) at happ
  have hres : (P.map (homOfLE h).op).hom (s ⊗ₜ[X.presheaf.obj (op U)] t) =
      (L.val.map (homOfLE h).op).hom s ⊗ₜ[X.presheaf.obj (op V)]
        (N.val.map (homOfLE h).op).hom t :=
    ModuleCat.tensorRestrictMap_tmul (X.presheaf.map (homOfLE h).op).hom
      (L.val.restrictₛₗ (homOfLE h).op) (N.val.restrictₛₗ (homOfLE h).op) s t
  exact happ.symm.trans (congrArg (η.app (op V)).hom hres)

/-- The comparison map into the tensor product sheaf is linear in the first factor of a pure
tensor. -/
theorem toTensorSheafSection_smul_left (U : Opens X.carrier) (r : X.presheaf.obj (op U))
    (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
        ((r • s) ⊗ₜ[X.presheaf.obj (op U)] t) =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj (op U))
          _ _ r
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
          (s ⊗ₜ t)) := by
  rw [← TensorProduct.smul_tmul']
  exact map_smul ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) L.val N.val)).app (op U)).hom r
      (s ⊗ₜ[X.presheaf.obj (op U)] t)

/-- The comparison map into the tensor product sheaf is linear in the second factor of a pure
tensor. -/
theorem toTensorSheafSection_smul_right (U : Opens X.carrier) (r : X.presheaf.obj (op U))
    (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
        (s ⊗ₜ[X.presheaf.obj (op U)] (r • t)) =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj (op U))
          _ _ r
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
          (s ⊗ₜ t)) := by
  rw [TensorProduct.tmul_smul]
  exact map_smul ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
    (PresheafOfModules.tensorObj (O := X.presheaf) L.val N.val)).app (op U)).hom r
      (s ⊗ₜ[X.presheaf.obj (op U)] t)

/-- The `U`-restriction of the structure sheaf, as a sheaf of rings on the site over `U`. -/
abbrev structureSheafOver (U : Opens X.carrier) :
    Sheaf ((Opens.grothendieckTopology X.carrier).over U) RingCat.{u} :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf (X.sheaf.over U).obj
    ((Presheaf.isSheaf_iff_isSheaf_comp
      ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
      (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)

/-- The tensor product, as presheaves of modules on the site over `U`, of the trivializations
of `L` and of `N` determined by two trivializing sections. -/
def generatorTensorPresheafIso (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X N U) :
    (PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((SheafOfModules.unit
        (structureSheafOver X U)).val) ((SheafOfModules.unit (structureSheafOver X U)).val)) ≅
      (PresheafOfModules.tensorObj (O := (X.sheaf.over U).obj) ((L.over U).val) ((N.over U).val)) :=
  tensorIso ((SheafOfModules.forget (structureSheafOver X U)).mapIso
      (generatorSectionsUnitIso X L U s))
    ((SheafOfModules.forget (structureSheafOver X U)).mapIso (generatorSectionsUnitIso X N U t))

/-- The trivialization of `(L ⊗ N)|_U` assembled from trivializations of `L` and `N` over `U`:
tensor the two trivializations, cancel the resulting `𝒪_U ⊗ 𝒪_U`, and move the tensor product
past the restriction to `U`. -/
def tensorGeneratorUnitIso (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X N U) :
    SheafOfModules.unit (structureSheafOver X U) ≅
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
          (N))).over U :=
  (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor (X.sheaf.over U).obj
      ((Presheaf.isSheaf_iff_isSheaf_comp
        ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
        (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)
      (SheafOfModules.unit (structureSheafOver X U))).symm ≪≫
    (Stacks.SheafOfModules.TensorSheafification.sheafify (X.sheaf.over U).obj
        ((Presheaf.isSheaf_iff_isSheaf_comp
          ((Opens.grothendieckTopology X.carrier).over U) (X.sheaf.over U).obj
          (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property)).mapIso
      (generatorTensorPresheafIso X L N U s t) ≪≫
    (AlgebraicGeometry.tensorRestrictionIso X L N U).symm

/-- The trivialization of `(L ⊗ N)|_U` carries the unit section to the pure tensor of the two
trivializing sections it was built from. -/
theorem tensorGeneratorUnitIso_apply_one (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X N U) :
    ((tensorGeneratorUnitIso X L N U s t).hom.val.app (op (Over.mk (𝟙 U)))).hom
        (1 : (structureSheafOver X U).obj.obj (op (Over.mk (𝟙 U)))) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
        (s.val ⊗ₜ t.val) := by
  let O := (X.sheaf.over U).obj
  let hO := (Presheaf.isSheaf_iff_isSheaf_comp
    ((Opens.grothendieckTopology X.carrier).over U) O
    (forget₂ CommRingCat RingCat)).mp (X.sheaf.over U).property
  let R := structureSheafOver X U
  let top : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let _ : Module (O.obj top) ((SheafOfModules.unit R).val.obj top) :=
    ((SheafOfModules.unit R).val.obj top).isModule
  let _ : Module (O.obj top) ((L.over U).val.obj top) := (L.val.obj (op U)).isModule
  let _ : Module (O.obj top) ((N.over U).val.obj top) := (N.val.obj (op U)).isModule
  let _ : Module (O.obj top) (((SheafOfModules.forget R).obj (L.over U)).obj top) :=
    (L.val.obj (op U)).isModule
  let _ : Module (O.obj top) (((SheafOfModules.forget R).obj (N.over U)).obj top) :=
    (N.val.obj (op U)).isModule
  let fL := ((SheafOfModules.forget R).mapIso (generatorSectionsUnitIso X L U s)).hom
  let fN := ((SheafOfModules.forget R).mapIso (generatorSectionsUnitIso X N U t)).hom
  let unitIso : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (SheafOfModules.unit R)).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit R :=
    Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor O hO (SheafOfModules.unit R)
  let P₁ := PresheafOfModules.tensorObj (O := O) (SheafOfModules.unit R).val
    (SheafOfModules.unit R).val
  let P₂ := PresheafOfModules.tensorObj (O := O) (L.over U).val (N.over U).val
  let η₁ := Stacks.SheafOfModules.TensorSheafification.toSheafify O hO P₁
  let η₂ := Stacks.SheafOfModules.TensorSheafification.toSheafify O hO P₂
  let et : P₁ ≅ P₂ := generatorTensorPresheafIso X L N U s t
  let eTensor := (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso et
  let one : (SheafOfModules.unit R).val.obj top := (1 : R.obj.obj top)
  let p₁ : P₁.obj top := one ⊗ₜ[O.obj top] one
  let p₂ : P₂.obj top := s.val ⊗ₜ[O.obj top] t.val
  have hs : (fL.app top).hom one = s.val := generatorSectionsUnitIso_apply_one X L U s
  have ht : (fN.app top).hom one = t.val := generatorSectionsUnitIso_apply_one X N U t
  have hunit : (unitIso.inv.val.app top).hom one = (η₁.app top).hom p₁ := by
    have hf : Function.Injective (ConcreteCategory.hom (unitIso.hom.val.app top)) := by
      refine Function.LeftInverse.injective
        (g := ConcreteCategory.hom (unitIso.inv.val.app top)) fun a => ?_
      exact congrArg (fun f => (f.val.app top).hom a) unitIso.hom_inv_id
    refine hf ?_
    have hleft : (unitIso.hom.val.app top).hom ((unitIso.inv.val.app top).hom one) = one :=
      congrArg (fun f => (f.val.app top).hom one) unitIso.inv_hom_id
    have hright : (unitIso.hom.val.app top).hom ((η₁.app top).hom p₁) = one :=
      (tensorPresheafLeftUnitor_toSheafify_tmul O hO (Over.mk (𝟙 U)) one one).trans
        (mul_one (1 : R.obj.obj top))
    exact hleft.trans hright.symm
  have hEt : (et.hom.app top).hom p₁ = p₂ :=
    (tensorPresheafHom_app_tmul O fL fN top one one).trans
      (congrArg₂ (fun a b => a ⊗ₜ[O.obj top] b) hs ht)
  have hTensor : (eTensor.hom.val.app top).hom ((η₁.app top).hom p₁) =
      (η₂.app top).hom p₂ :=
    (congrArg (fun f => (f.app top).hom p₁)
      ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).unit.naturality
        et.hom)).symm.trans (congrArg (η₂.app top).hom hEt)
  have hgoal : ((tensorGeneratorUnitIso X L N U s t).hom.val.app top).hom one =
      ((AlgebraicGeometry.tensorRestrictionIso X L N U).inv.val.app top).hom
        ((eTensor.hom.val.app top).hom ((unitIso.inv.val.app top).hom one)) := rfl
  exact hgoal.trans <| (congrArg (fun z => ((AlgebraicGeometry.tensorRestrictionIso X L N
      U).inv.val.app top).hom ((eTensor.hom.val.app top).hom z)) hunit).trans <|
    (congrArg ((AlgebraicGeometry.tensorRestrictionIso X L N U).inv.val.app top).hom
      hTensor).trans
      (AlgebraicGeometry.tensorRestrictionIso_inv_val_app_toSheafify X L N U top p₂)

/-- Multiplication by the pure tensor of two trivializing sections is bijective on sections
over `U`. -/
theorem bijective_smul_toTensorSheafSection (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X N U) :
    Function.Bijective (fun r : X.presheaf.obj (op U) =>
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj (op U))
          _ _ r
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
          (s.val ⊗ₜ t.val))) := by
  let e := tensorGeneratorUnitIso X L N U s t
  have hiso : IsIso (e.hom.val.app (op (Over.mk (𝟙 U)))) :=
    ((_root_.SheafOfModules.evaluation (structureSheafOver X U)
      (op (Over.mk (𝟙 U)))).mapIso e).isIso_hom
  have hbij : Function.Bijective
      (ConcreteCategory.hom (e.hom.val.app (op (Over.mk (𝟙 U))))) :=
    ConcreteCategory.bijective_of_isIso _
  have hfun : (fun r : X.presheaf.obj (op U) =>
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj (op U))
          _ _ r
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
          (s.val ⊗ₜ t.val))) =
      fun r : X.presheaf.obj (op U) =>
        (e.hom.val.app (op (Over.mk (𝟙 U)))).hom r := by
    funext r
    rw [← tensorGeneratorUnitIso_apply_one X L N U s t]
    refine ((e.hom.val.app (op (Over.mk (𝟙 U)))).hom.map_smul r
      (1 : (structureSheafOver X U).obj.obj (op (Over.mk (𝟙 U))))).symm.trans ?_
    refine congrArg (e.hom.val.app (op (Over.mk (𝟙 U)))).hom ?_
    show r * 1 = r
    exact mul_one r
  rw [hfun]
  exact hbij

/-- The pure tensor of a trivializing section of `L` over `U` and one of `N` over `U`
trivializes `L ⊗ N` over `U`. -/
def tensorGeneratorSections (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X N U) :
    GeneratorSections X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N))) U := by
  refine ⟨Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
    (s.val ⊗ₜ t.val), fun V h => ?_⟩
  have hres : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      (L)).obj (N))).val.restrictₛₗ
        (homOfLE h).op
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
          (s.val ⊗ₜ t.val)) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op V)
        ((generatorSectionsRestrict X L h s).val ⊗ₜ (generatorSectionsRestrict X N h t).val) :=
    toTensorSheafSection_restrict X L N h s.val t.val
  have hbij := bijective_smul_toTensorSheafSection X L N V (generatorSectionsRestrict X L h s)
    (generatorSectionsRestrict X N h t)
  rwa [← hres] at hbij

/-- The trivializing section `s ⊗ t` is the image of the pure tensor under the comparison map
into the tensor product sheaf. -/
@[simp]
theorem tensorGeneratorSections_val (U : Opens X.carrier)
    (s : GeneratorSections X L U) (t : GeneratorSections X N U) :
    (tensorGeneratorSections X L N U s t).val =
      Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X L N (op U)
        (s.val ⊗ₜ t.val) := rfl

section Pairing

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
    (R := structureSheaf X.sheaf) L 1]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
    (R := structureSheaf X.sheaf) N 1]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
    (R := structureSheaf X.sheaf) ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N))) 1]

/-- The pairing of trivializing sections of `L` and of `N` into trivializing sections of
`L ⊗ N`, on the underlying sheaves of the generator torsors. -/
def tensorGeneratorTorsorApp (U : Opens X.carrier)
    (x : (generatorTorsor X L).toTorsor.F.obj U) (y : (generatorTorsor X N).toTorsor.F.obj U) :
    (generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).toTorsor.F.obj U :=
  ((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
      ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv U).symm
    (tensorGeneratorSections X L N U ((generatorTorsor X L).sectionsEquiv U x)
      ((generatorTorsor X N).sectionsEquiv U y))

/-- The pairing is the pure tensor of the two trivializing sections. -/
theorem tensorGeneratorTorsorApp_val (U : Opens X.carrier)
    (x : (generatorTorsor X L).toTorsor.F.obj U) (y : (generatorTorsor X N).toTorsor.F.obj U) :
    (((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv U)
      (tensorGeneratorTorsorApp X L N U x y)).val =
      toTensorSheafSection X L N (op U)
        (((generatorTorsor X L).sectionsEquiv U x).val ⊗ₜ
          ((generatorTorsor X N).sectionsEquiv U y).val) := by
  show (((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
      ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv U)
    (((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv U).symm
      (tensorGeneratorSections X L N U _ _))).val = _
  rw [Equiv.apply_symm_apply]
  exact tensorGeneratorSections_val X L N U _ _

/-- Restriction of the pairing. -/
theorem tensorGeneratorTorsorApp_res {U V : Opens X.carrier} (h : V ≤ U)
    (x : (generatorTorsor X L).toTorsor.F.obj U) (y : (generatorTorsor X N).toTorsor.F.obj U) :
    tensorGeneratorTorsorApp X L N V ((generatorTorsor X L).toTorsor.F.res h x)
        ((generatorTorsor X N).toTorsor.F.res h y) =
      (generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
          ((X)).IsSheaf⟩).obj (L)).obj (N)))).toTorsor.F.res h
        (tensorGeneratorTorsorApp X L N U x y) := by
  refine ((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
      ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv V).injective (Subtype.ext ?_)
  calc (((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
         ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv V)
          (tensorGeneratorTorsorApp X L N V ((generatorTorsor X L).toTorsor.F.res h x)
            ((generatorTorsor X N).toTorsor.F.res h y))).val
      = toTensorSheafSection X L N (op V)
          (((generatorTorsor X L).sectionsEquiv V
              ((generatorTorsor X L).toTorsor.F.res h x)).val ⊗ₜ
            ((generatorTorsor X N).sectionsEquiv V
              ((generatorTorsor X N).toTorsor.F.res h y)).val) :=
        tensorGeneratorTorsorApp_val X L N V _ _
    _ = toTensorSheafSection X L N (op V)
          (L.val.restrictₛₗ (homOfLE h).op
              ((generatorTorsor X L).sectionsEquiv U x).val ⊗ₜ
            N.val.restrictₛₗ (homOfLE h).op
              ((generatorTorsor X N).sectionsEquiv U y).val) :=
        congrArg₂ (fun a b => toTensorSheafSection X L N (op V) (a ⊗ₜ b))
          ((generatorTorsor X L).sectionsEquiv_restrict h x)
          ((generatorTorsor X N).sectionsEquiv_restrict h y)
    _ = ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
        (N))).val.restrictₛₗ (homOfLE h).op
          (toTensorSheafSection X L N (op U)
            (((generatorTorsor X L).sectionsEquiv U x).val ⊗ₜ
              ((generatorTorsor X N).sectionsEquiv U y).val)) :=
        (toTensorSheafSection_restrict X L N h _ _).symm
    _ = ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
        (N))).val.restrictₛₗ (homOfLE h).op
          (((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
              ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv U
            (tensorGeneratorTorsorApp X L N U x y)).val) :=
        congrArg (fun z => ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
            ((X)).IsSheaf⟩).obj (L)).obj (N))).val.restrictₛₗ (homOfLE h).op z)
          (tensorGeneratorTorsorApp_val X L N U x y).symm
    _ = (((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv V
          ((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
              ((X)).IsSheaf⟩).obj (L)).obj (N)))).toTorsor.F.res h
            (tensorGeneratorTorsorApp X L N U x y))).val) :=
        ((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
            ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv_restrict h
          (tensorGeneratorTorsorApp X L N U x y)).symm

/-- The pairing of `x'` and `y'` is the action of `g` on the pairing of `x` and `y` as soon as the
corresponding pure tensors differ by the unit `g`. -/
private theorem tensorGeneratorTorsorApp_eq_act (U : Opens X.carrier)
    (g : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj U)
    (x x' : (generatorTorsor X L).toTorsor.F.obj U)
    (y y' : (generatorTorsor X N).toTorsor.F.obj U)
    (h : toTensorSheafSection X L N (op U)
        (((generatorTorsor X L).sectionsEquiv U x').val ⊗ₜ
          ((generatorTorsor X N).sectionsEquiv U y').val) =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj.obj (op U))
        _ _ ((Additive.toMul (Multiplicative.toAdd g) : (X.presheaf.obj (op U))ˣ) :
          X.presheaf.obj (op U))
        (toTensorSheafSection X L N (op U)
          (((generatorTorsor X L).sectionsEquiv U x).val ⊗ₜ
            ((generatorTorsor X N).sectionsEquiv U y).val))) :
    tensorGeneratorTorsorApp X L N U x' y' =
      (generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).toTorsor.action.act g
        (tensorGeneratorTorsorApp X L N U x y) := by
  refine ((generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv U).injective (Subtype.ext ?_)
  have hK := (generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).sectionsEquiv_smul U
    (Additive.toMul (Multiplicative.toAdd g)) (tensorGeneratorTorsorApp X L N U x y)
  rw [tensorGeneratorTorsorApp_val, h, ← tensorGeneratorTorsorApp_val X L N U x y]
  exact hK.symm

/-- Equivariance of the pairing in the first variable. -/
theorem tensorGeneratorTorsorApp_act_left (U : Opens X.carrier)
    (g : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj U)
    (x : (generatorTorsor X L).toTorsor.F.obj U) (y : (generatorTorsor X N).toTorsor.F.obj U) :
    tensorGeneratorTorsorApp X L N U ((generatorTorsor X L).toTorsor.action.act g x) y =
      (generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).toTorsor.action.act g
        (tensorGeneratorTorsorApp X L N U x y) :=
  tensorGeneratorTorsorApp_eq_act X L N U g x _ y y
    ((congrArg (fun z => toTensorSheafSection X L N (op U)
      (z ⊗ₜ ((generatorTorsor X N).sectionsEquiv U y).val))
      ((generatorTorsor X L).sectionsEquiv_smul U (Additive.toMul (Multiplicative.toAdd g))
        x)).trans (toTensorSheafSection_smul_left X L N U _ _ _))

/-- Equivariance of the pairing in the second variable. -/
theorem tensorGeneratorTorsorApp_act_right (U : Opens X.carrier)
    (g : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj U)
    (x : (generatorTorsor X L).toTorsor.F.obj U) (y : (generatorTorsor X N).toTorsor.F.obj U) :
    tensorGeneratorTorsorApp X L N U x ((generatorTorsor X N).toTorsor.action.act g y) =
      (generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).toTorsor.action.act g
        (tensorGeneratorTorsorApp X L N U x y) :=
  tensorGeneratorTorsorApp_eq_act X L N U g x x y _
    ((congrArg (fun z => toTensorSheafSection X L N (op U)
      (((generatorTorsor X L).sectionsEquiv U x).val ⊗ₜ z))
      ((generatorTorsor X N).sectionsEquiv_smul U (Additive.toMul (Multiplicative.toAdd g))
        y)).trans (toTensorSheafSection_smul_right X L N U _ _ _))

/-- **The pairing of generator torsors.** Tensoring trivializing sections is natural in the
open and equivariant for the action of units in each variable, so it pairs the generator
torsors of `L` and `N` into the generator torsor of `L ⊗ N`. -/
def generatorTorsorTensorPairing :
    Stacks.Cohomology.SheafTorsor.TorsorPairing (generatorTorsor X L).toTorsor
      (generatorTorsor X N).toTorsor (generatorTorsor X ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj (N)))).toTorsor where
  app := tensorGeneratorTorsorApp X L N
  naturality h x y := tensorGeneratorTorsorApp_res X L N h x y
  map_act_left U g x y := tensorGeneratorTorsorApp_act_left X L N U g x y
  map_act_right U g x y := tensorGeneratorTorsorApp_act_right X L N U g x y

end Pairing

end Tensor

end Stacks.Cohomology.Generators

end
