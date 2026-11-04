module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitCorepresentable

/-!
# The inverse image of the structure sheaf, on the unit section

`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` — the identification
`1_{O_C} ≅ f^*1_{O_D}` of Stacks 03LU for a morphism of ringed topoi — is built by
corepresentability, so the only description of it available directly is the one its
corepresentability bijection gives
(`AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp`), which characterises it by its
composites and says nothing about a value on sections.

This file computes the one value that is needed: the transpose, across the Stacks 03D7
adjunction, of the comparison morphism `f^*1_{O_D} ⟶ 1_{O_C}`, evaluated on the unit section
`1`.  The computation is possible because the corepresentability bijection factors through the
preservation of global sections by a direct image
(`MorphismOfTopoi.pushforwardTerminalHomEquiv`), whose *inverse* is the easy
direction: it is transposition along the adjunction of the underlying topoi, i.e. the unit
followed by the direct image, and the unit appears only at the terminal sheaf, where it is
absorbed into a single morphism
`MorphismOfTopoi.pushforwardTerminalSection`.  So the transpose is the direct
image of the "constant `1`" morphism out of the terminal sheaf, composed with that morphism —
and *that* is a value a chart projection of the direct image can be applied to.

Everything here is stated for an arbitrary morphism of ringed topoi, at arbitrary universes; the
small étale ringed topoi of algebraic spaces are one instance.

## Main definitions

* `MorphismOfTopoi.pushforwardTerminalSection`: the canonical morphism from the
  terminal sheaf of the target to the direct image of the terminal sheaf of the source — the
  unit of the adjunction of topoi at the terminal sheaf, read through
  `MorphismOfTopoi.inverseImageTerminalIso`.

## Main results

* `MorphismOfTopoi.pushforwardTerminalHomEquiv_symm_apply`: the inverse of the
  global-sections bijection of a direct image is the direct image of the given global section,
  precomposed with that canonical morphism.
* `CategoryTheory.Sheaf.unitTerminalHomEquiv_symm_val_app_one`: a morphism out of the free
  sheaf of modules of rank one takes the unit section to the value at the unique section of the
  terminal sheaf of the corresponding morphism out of the terminal sheaf.
* `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_inv_adjunct_val_app_one`:
  **the value on the unit section of the transpose of the comparison morphism
  `f^*1_{O_D} ⟶ 1_{O_C}`.**  It is the direct image of the constant-`1` morphism out of the
  terminal sheaf, evaluated on the image of the unique section of the terminal sheaf under
  `MorphismOfTopoi.pushforwardTerminalSection`.

## Implementation notes

The composite bijections are unfolded by `rfl` wherever an `Equiv.trans` is involved — those are
definitional — and the two remaining rewrites of a bijection against its inverse are
`Equiv.symm_apply_eq` and `Equiv.eq_symm_apply`.  The identification of the sections of a sheaf
of modules with the sections of its underlying sheaf of sets is definitional but not visible at
reducible transparency, exactly as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposTerminalSections.lean`; the proofs therefore
compose `congrArg` and `Eq.trans` instead of rewriting.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite AlgebraicGeometry

universe w w' v u v' u'

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- **The canonical morphism from the terminal sheaf to the direct image of the terminal
sheaf**: the unit of the adjunction of topoi at the terminal sheaf of the target, followed by
the direct image of the identification
`MorphismOfTopoi.inverseImageTerminalIso` of the inverse image of that terminal
sheaf with the terminal sheaf of the source.

The direct image of the terminal sheaf is terminal, a direct image being a right adjoint, so
this is the unique such morphism; it is named because it is what the inverse of the
global-sections bijection
`MorphismOfTopoi.pushforwardTerminalHomEquiv` factors through. -/
noncomputable def pushforwardTerminalSection :
    ⊤_ (Sheaf K (Type w')) ⟶ g.pushforward.obj (⊤_ (Sheaf J (Type w))) :=
  g.adj.unit.app _ ≫ g.pushforward.map (inverseImageTerminalIso g).hom

/-- **The inverse of the global-sections bijection of a direct image.**  A global section
`t : 1 ⟶ E` of a sheaf on the source is carried to the direct image of `t` precomposed with
`MorphismOfTopoi.pushforwardTerminalSection`.

This is the *easy* direction of
`MorphismOfTopoi.pushforwardTerminalHomEquiv`: transposing against the
adjunction of topoi in this direction is composing the unit with a direct image, and the unit
occurs only at the terminal sheaf. -/
theorem pushforwardTerminalHomEquiv_symm_apply (E : Sheaf J (Type w))
    (t : ⊤_ (Sheaf J (Type w)) ⟶ E) :
    (pushforwardTerminalHomEquiv g E).symm t
      = pushforwardTerminalSection g ≫ g.pushforward.map t := by
  have h : (pushforwardTerminalHomEquiv g E).symm t
      = g.adj.homEquiv (⊤_ (Sheaf K (Type w'))) E ((inverseImageTerminalIso g).hom ≫ t) := rfl
  rw [h, Adjunction.homEquiv_unit, pushforwardTerminalSection, g.pushforward.map_comp,
    Category.assoc]
  rfl

end MorphismOfTopoi

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism out of the free sheaf of modules of rank one takes the unit section to the
corresponding global section.  This is `Mathlib.SheafOfModules.unitHomEquiv` read backwards. -/
theorem unitHomEquiv_symm_val_app_one
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) (s : M.sections) (W : Cᵒᵖ) :
    ((SheafOfModules.unitHomEquiv M).symm s).val.app W (1 : R.obj.obj W) = s.val W :=
  congrArg (fun z : M.sections ↦ z.val W) ((SheafOfModules.unitHomEquiv M).apply_symm_apply s)

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **The value on the unit section of a morphism out of the free sheaf of modules of rank
one**, read through `CategoryTheory.Sheaf.unitTerminalHomEquiv`: it is the value of the
corresponding morphism out of the terminal sheaf on the unique section of the terminal
sheaf. -/
theorem unitTerminalHomEquiv_symm_val_app_one (R : Sheaf J RingCat.{w})
    (M : SheafOfModules.{w} R) (b : ⊤_ (Sheaf J (Type w)) ⟶ moduleSheaf R M) (W : Cᵒᵖ) :
    ((unitTerminalHomEquiv R M).symm b).val.app W (1 : R.obj.obj W)
      = b.hom.app W (terminalSheafSection J W) :=
  unitHomEquiv_symm_val_app_one M (terminalHomEquivSections (moduleSheaf R M) b) W

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The morphism out of the terminal sheaf corresponding to the identity of the free sheaf of
modules of rank one is the constant unit section. -/
theorem unitTerminalHomEquiv_id_app_apply (R : Sheaf J RingCat.{w}) (W : Cᵒᵖ)
    (p : (⊤_ (Sheaf J (Type w))).obj.obj W) :
    (unitTerminalHomEquiv R (SheafOfModules.unit R) (𝟙 _)).hom.app W p
      = (1 : R.obj.obj W) :=
  rfl

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The value on the unit section of a morphism from `1_{O_D}` into a direct image**, read
through the bijection `Stacks.Sheaves.RingedToposModules.pushforwardModulesUnitHomEquiv` with
the global sections of the target: the direct image of the global section, evaluated on the
image of the unique section of the terminal sheaf. -/
theorem pushforwardModulesUnitHomEquiv_symm_val_app_one (f : RingedToposHom X Y)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (c : ⊤_ (Sheaf X.J (Type w)) ⟶ moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)
    (W : Y.Cᵒᵖ) :
    ((pushforwardModulesUnitHomEquiv f N).symm c).val.app W
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W)
      = (f.toToposHom.pushforward.map c).hom.app W
          ((MorphismOfTopoi.pushforwardTerminalSection f.toToposHom).hom.app W
            (terminalSheafSection Y.J W)) :=
  (unitTerminalHomEquiv_symm_val_app_one (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((pushforwardModules f).obj N)
      ((f.toToposHom.pushforwardTerminalHomEquiv
        (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)).symm c) W).trans
    (congrArg (fun m : ⊤_ (Sheaf Y.J (Type w')) ⟶
          f.toToposHom.pushforward.obj
            (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ↦
        m.hom.app W (terminalSheafSection Y.J W))
      (MorphismOfTopoi.pushforwardTerminalHomEquiv_symm_apply f.toToposHom _ c))

/-- **The transpose of the comparison `f^*1_{O_D} ⟶ 1_{O_C}`, on the unit section.**  The
morphism `1_{O_D} ⟶ f_*1_{O_C}` adjunct to the inverse of
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` takes the unit section to the
direct image of the constant unit section, evaluated on the image of the unique section of the
terminal sheaf under
`MorphismOfTopoi.pushforwardTerminalSection`.

This is the value that a chart projection of the direct image can be applied to, and it is the
only description of the comparison morphism on sections that corepresentability yields: the
comparison is pinned down by having corepresentability bijection the identity, and that
bijection's one hard factor — the preservation of global sections by a direct image — is read
in the direction where it is transposition along the adjunction of topoi. -/
theorem pullbackModulesObjUnitIso_inv_adjunct_val_app_one (f : RingedToposHom X Y)
    (W : Y.Cᵒᵖ) :
    ((pullbackAdjPushforwardModules f).homEquiv
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (pullbackModulesObjUnitIso f).inv).val.app W
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W)
      = (f.toToposHom.pushforward.map
            (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (𝟙 _))).hom.app W
          ((MorphismOfTopoi.pushforwardTerminalSection f.toToposHom).hom.app W
            (terminalSheafSection Y.J W)) := by
  have h1 : (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm
        ((pushforwardModulesUnitHomEquiv f
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          ((pullbackAdjPushforwardModules f).homEquiv _ _
            (pullbackModulesObjUnitIso f).inv))
      = 𝟙 (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    (pullbackModulesObjUnitIso_hom_comp f _ _).symm.trans (Iso.hom_inv_id _)
  have h2 := (Equiv.eq_symm_apply _).mpr ((Equiv.symm_apply_eq _).mp h1)
  exact (congrArg (fun m : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
        (pushforwardModules f).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ↦
      m.val.app W (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W)) h2).trans
    (pushforwardModulesUnitHomEquiv_symm_val_app_one f _ _ W)

end Stacks.Sheaves.RingedToposModules

end
