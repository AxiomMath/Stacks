module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul

/-!
# The pullback of multiplication by a global section of the structure sheaf

Let `(f, f♯) : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi and let `s` be a
global section of `𝒪_𝒟`. Its image `f♯(s)` is the global section of `𝒪_𝒞` obtained by taking
the inverse image `f⁻¹s` of `s`, a global section of `f⁻¹𝒪_𝒟`, and applying the structure map
`f♯ : f⁻¹𝒪_𝒟 ⟶ 𝒪_𝒞`. This file proves that the pullback `f^*` of sheaves of modules carries
multiplication by `s` on `𝒪_𝒟` to multiplication by `f♯(s)` on `𝒪_𝒞`, under the canonical
identification `ν : f^*𝒪_𝒟 ≅ 𝒪_𝒞`.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.pullbackTerminalSection`: the global section `f♯(s)` of
  `𝒪_𝒞`, for a global section `s` of `𝒪_𝒟` read as a morphism out of the terminal sheaf.

## Main results

* `CategoryTheory.Sheaf.moduleSheafFunctor_map_globalSectionToEnd_unit`: on underlying sheaves of
  sets, multiplication by a global section `s` on the structure sheaf is the composite of
  `(s, id)` with the multiplication of the structure sheaf.
* `Stacks.Sheaves.RingedToposModules.pullbackModules_map_globalSectionToEnd_unit`: the
  statement above, `ν ∘ f^*(s ·) = f♯(s) · ∘ ν`.

## Implementation notes

The identification `ν` is a morphism out of the extension of scalars `𝒪_𝒞 ⊗_{f⁻¹𝒪_𝒟} f⁻¹𝒪_𝒟`,
which has no description on sections. The proof therefore compares the two sides through their
transposes along the adjunction between extension and restriction of scalars along `f♯`: the
transpose of `ν` is `f♯` itself on underlying sheaves of sets
(`moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv`),
and the inverse image of sheaves of modules acts on underlying sheaves of sets by the inverse
image of sheaves of sets. What is left is the statement, on sections, that `f♯` is
multiplicative and that the inverse image of the multiplication of `𝒪_𝒟` is the multiplication
of `f⁻¹𝒪_𝒟`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u w v' u' w'

/-- Binary products of sheaves of sets, supplied directly: instance search for them otherwise
wanders through sheaves of rings and times out. -/
local instance (priority := high) hasBinaryProduct_sheafType {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (P Q : Sheaf J (Type w)) : HasBinaryProduct P Q :=
  instHasLimitOfHasLimitsOfShape _

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) [∀ U, IsMulCommutative (R.obj.obj U)]

/-- **Multiplication by a global section on the structure sheaf, on underlying sheaves of
sets**: it is `(s, id)` followed by the multiplication of the sheaf of rings. -/
theorem moduleSheafFunctor_map_globalSectionToEnd_unit
    (s : ⊤_ (Sheaf J (Type w)) ⟶ ringSheaf R) :
    (moduleSheafFunctor R).map
        ((Stacks.SheafOfModules.globalSectionToEnd R (terminalHomEquivSections _ s)).asHom.app
          (SheafOfModules.unit R)) =
      (prod.lift (terminal.from (ringSheaf R) ≫ s) (𝟙 _) ≫ ringMulHom R :
        ringSheaf R ⟶ ringSheaf R) :=
  hom_ext_sections fun X x => by
    let x' : (sectionsFunctor J X).obj (ringSheaf R) := x
    have h := Functor.map_lift_apply (P := sectionsFunctor J X)
      (terminal.from (ringSheaf R) ≫ s) (𝟙 _) x'
    refine Eq.trans ?_ (congrArg ((sectionsFunctor J X).map (ringMulHom R)) h).symm
    refine Eq.trans ?_ (sectionsFunctor_map_ringMulHom R X _ _).symm
    let y : R.obj.obj X := x
    let c₁ : R.obj.obj X := s.hom.app X (terminalSheafSection J X)
    let c₂ : R.obj.obj X := s.hom.app X ((terminal.from (ringSheaf R)).hom.app X x')
    have hc : c₁ = c₂ := congrArg (s.hom.app X)
      (eq_terminalSheafSection ((terminal.from (ringSheaf R)).hom.app X x')).symm
    change c₁ * y = c₂ * y
    rw [hc]

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

omit [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The rings of sections of the structure sheaf of a ringed topos are commutative. -/
local instance isMulCommutative_ringSheaf_obj (Z : RingedTopos.{v, u, w})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] (U : Z.Cᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj U) :=
  ⟨⟨fun a b => mul_comm (G := Z.O.obj.obj U) a b⟩⟩

/-- **The image `f♯(s)` of a global section `s` of `𝒪_𝒟`** under a morphism of ringed topoi: the
inverse image of `s`, read through the comparison `1 ≅ f⁻¹1`, followed by the structure map
`f♯ : f⁻¹𝒪_𝒟 ⟶ 𝒪_𝒞`. Global sections are morphisms out of the terminal sheaf of sets. -/
def pullbackTerminalSection
    (s : ⊤_ (Sheaf Y.J (Type w')) ⟶ Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ⊤_ (Sheaf X.J (Type w)) ⟶ Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  f.toToposHom.inverseImageTerminalIso.inv ≫ f.toToposHom.inverseImage.map s ≫
    (sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The pullback of multiplication by a global section.** Under the identification
`ν : f^*𝒪_𝒟 ≅ 𝒪_𝒞`, the pullback of multiplication by a global section `s` of `𝒪_𝒟` is
multiplication by its image `f♯(s)`. -/
theorem pullbackModules_map_globalSectionToEnd_unit
    (s : ⊤_ (Sheaf Y.J (Type w')) ⟶ Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f.pullbackModules.map
        ((Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (Sheaf.terminalHomEquivSections _ s)).asHom.app (SheafOfModules.unit _)) ≫
        (pullbackModulesObjUnitIso f).inv =
      (pullbackModulesObjUnitIso f).inv ≫
        (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (Sheaf.terminalHomEquivSections _ (pullbackTerminalSection f s))).asHom.app
            (SheafOfModules.unit _) := by
  apply ((fSharpAdjunction f).homEquiv _ _).injective
  refine ((fSharpAdjunction f).homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ ((fSharpAdjunction f).homEquiv_naturality_right _ _).symm
  refine hom_ext_moduleSheafFunctor ?_
  refine ((Sheaf.moduleSheafFunctor _).map_comp _ _).trans
    (Eq.trans ?_ ((Sheaf.moduleSheafFunctor _).map_comp _ _).symm)
  refine (congrArg (fun m => m ≫ _)
    (moduleSheafFunctor_map_inverseImageModules_map f.toToposHom _ _)).trans ?_
  refine (congrArg (fun m => _ ≫ m)
    (moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv f)).trans ?_
  refine Eq.trans ?_ (congrArg (fun m => m ≫ _)
    (moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv f)).symm
  refine (congrArg (fun m => f.toToposHom.inverseImage.map m ≫ _)
    (Sheaf.moduleSheafFunctor_map_globalSectionToEnd_unit _ s)).trans ?_
  refine Eq.trans ?_ (congrArg (fun m => _ ≫ m)
    (Sheaf.moduleSheafFunctor_map_globalSectionToEnd_unit _ (pullbackTerminalSection f s))).symm
  refine Sheaf.hom_ext_sections fun V y => ?_
  let P := f.toToposHom.inverseImage ⋙ Sheaf.sectionsFunctor X.J V
  let ψ := (f.fSharpInverseImage.hom.app V).hom
  change ψ (P.map (prod.lift
      (terminal.from (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫ s) (𝟙 _) ≫
      Sheaf.ringMulHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) y) =
    (Sheaf.sectionsFunctor X.J V).map (prod.lift
      (terminal.from (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
      pullbackTerminalSection f s) (𝟙 _) ≫
        Sheaf.ringMulHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ψ y)
  let y' : P.obj (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) := y
  have hP : P.map (prod.lift (terminal.from
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫ s) (𝟙 _) ≫
        Sheaf.ringMulHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) y' =
      Sheaf.ringMulObj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P
        (P.map s default) y' := by
    rw [Functor.map_comp, types_comp_apply, Functor.map_lift_apply, Functor.map_comp,
      types_comp_apply, Functor.map_terminalFrom_apply, P.map_id, types_id_apply]
    rfl
  let a : (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj V := P.map s default
  let b : (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj V := y
  have hmul : Sheaf.ringMulObj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P
      (P.map s default) y' = a * b := rfl
  have hX : ∀ z : (Sheaf.sectionsFunctor X.J V).obj
      (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      (Sheaf.sectionsFunctor X.J V).map (prod.lift (terminal.from
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
          pullbackTerminalSection f s) (𝟙 _) ≫
        Sheaf.ringMulHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) z =
      (ψ a * (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V from z) :
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V) := by
    intro z
    change (Sheaf.sectionsFunctor X.J V).map
      (Sheaf.ringMulHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((Sheaf.sectionsFunctor X.J V).map (prod.lift (terminal.from
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
          pullbackTerminalSection f s) (𝟙 _)) z) = _
    rw [Functor.map_lift_apply, Sheaf.sectionsFunctor_map_ringMulHom]
    congr 1
    change (Sheaf.sectionsFunctor X.J V).map (pullbackTerminalSection f s)
      ((Sheaf.sectionsFunctor X.J V).map (terminal.from
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) z) = _
    rw [Functor.map_terminalFrom_apply]
    change ψ (P.map s _) = ψ (P.map s default)
    congr 1
    exact congrArg (P.map s) (Subsingleton.elim _ _)
  exact (congrArg ψ (hP.trans hmul)).trans ((map_mul ψ a b).trans (hX (ψ b)).symm)

end Stacks.Sheaves.RingedToposModules

end
