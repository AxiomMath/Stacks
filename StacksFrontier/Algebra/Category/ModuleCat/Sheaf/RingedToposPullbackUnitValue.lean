module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposUnitStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafInverseImage

/-!
# The unit comparison `ν : f^*O_D ≅ O_C`, on sections

For a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` there are two
constructions of the identification `f^*O_D ≅ O_C` of Stacks 03LU:
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, by corepresentability, and
`Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso`, the identity
`f⁻¹1_{O_D} = 1_{f⁻¹O_D}` followed by the base-change unitor
`Stacks.SheafOfModules.ChangeOfRings.baseChangeUnitor`. They agree, and the transpose of the
comparison along the adjunction of Stacks 03CZ is, on underlying sheaves of sets, the structure
map `f♯ : f⁻¹O_D ⟶ O_C`.

## Main results

* `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso_eq`: the comparison built by
  corepresentability is the explicit one.
* `Stacks.Sheaves.RingedToposModules.fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv`:
  the transpose of `ν : f^*O_D ⟶ O_C` along the adjunction of Stacks 03CZ is
  `unitToRestrictScalarsUnit` at the inverse-image form of the structure map.
* `moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv`: the same on
  underlying sheaves of sets, where the right-hand side is `f♯ : f⁻¹O_D ⟶ O_C`.
* `CategoryTheory.Sheaf.unitTerminalHomEquiv_eq`: a morphism out of the free sheaf of modules of
  rank one, read as a global section, is the unit section `CategoryTheory.Sheaf.ringOneHom`
  followed by that morphism.
* `MorphismOfTopoi.pushforwardTerminalHomEquiv_ringOneHom_comp_homEquiv`: the global-sections
  bijection of a direct image on a unit section followed by a transpose.
* `MorphismOfTopoi.inverseImageTerminalIso_inv_comp_map_ringOneHom`: the unit section of an
  inverse-image sheaf of rings is the inverse image of the unit section.
* `AlgebraicGeometry.RingedToposHom.isIso_pullbackUnitStructureMap`: the canonical comparison
  `f^*O_D ⟶ O_C` of a morphism of ringed topoi is an isomorphism.
* `AlgebraicGeometry.RingedToposHom.pushforwardModulesUnitHomEquiv_pullbackUnitStructureMap`:
  the canonical comparison, read as a global section of `O_C`, is `1`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite CategoryTheory.Sheaf AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

namespace CategoryTheory.Sheaf

section OneSection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- A morphism out of the free sheaf of modules of rank one, read as a global section, is the
unit section followed by the underlying morphism of sheaves of sets. -/
lemma unitTerminalHomEquiv_eq (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R)
    (h : SheafOfModules.unit R ⟶ M) :
    unitTerminalHomEquiv R M h = ringOneHom R ≫ (moduleSheafFunctor R).map h :=
  hom_ext_sections fun _ _ ↦ rfl

/-- The global section corresponding to the identity of the free sheaf of modules of rank one is
the unit section. -/
lemma unitTerminalHomEquiv_id_eq (R : Sheaf J RingCat.{w}) :
    unitTerminalHomEquiv R (SheafOfModules.unit R) (𝟙 _) = ringOneHom R :=
  (unitTerminalHomEquiv_eq R _ (𝟙 _)).trans
    ((congrArg (fun m ↦ ringOneHom R ≫ m)
      ((moduleSheafFunctor R).map_id _)).trans (Category.comp_id _))

/-- Two morphisms out of the free sheaf of modules of rank one are equal if their underlying
morphisms of sheaves of sets agree on the unit section. -/
lemma hom_ext_ringOneHom {R : Sheaf J RingCat.{w}} {M : SheafOfModules.{w} R}
    {φ ψ : SheafOfModules.unit R ⟶ M}
    (h : ringOneHom R ≫ (moduleSheafFunctor R).map φ =
      ringOneHom R ≫ (moduleSheafFunctor R).map ψ) :
    φ = ψ :=
  (unitTerminalHomEquiv R M).injective
    ((unitTerminalHomEquiv_eq R M φ).trans (h.trans (unitTerminalHomEquiv_eq R M ψ).symm))

end OneSection

end CategoryTheory.Sheaf

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The unit section of an inverse-image sheaf of rings is the inverse image of the unit section,
read through the identification of the inverse image of the terminal sheaf with the terminal
sheaf. -/
lemma inverseImageTerminalIso_inv_comp_map_ringOneHom (O : Sheaf K RingCat.{w'}) :
    (inverseImageTerminalIso g).inv ≫ g.inverseImage.map (Sheaf.ringOneHom O) =
      Sheaf.ringOneHom (inverseImageRingSheaf g O) := by
  have := g.preservesFiniteLimits
  have ht : (inverseImageTerminalIso g).inv ≫
      terminal.from (g.inverseImage.obj (⊤_ (Sheaf K (Type w')))) = 𝟙 _ :=
    terminal.hom_ext _ _
  rw [← Stacks.Sheaves.LocalRingedness.terminalFrom_comp_ringOneHom_pullback J
      g.inverseImage O]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m ↦ m ≫ Sheaf.ringOneHom (pullbackRingSheaf J g.inverseImage O)) ht).trans
      (Category.id_comp _))

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The global-sections bijection of a direct image carries the unit section of `O` followed by
the transpose of `m` to the unit section of the inverse-image sheaf of rings followed by `m`. -/
lemma pushforwardTerminalHomEquiv_ringOneHom_comp_homEquiv (O : Sheaf K RingCat.{w'})
    {E : Sheaf J (Type w)} (m : g.inverseImage.obj (Sheaf.ringSheaf O) ⟶ E) :
    g.pushforwardTerminalHomEquiv E (Sheaf.ringOneHom O ≫ g.adj.homEquiv _ _ m) =
      (inverseImageTerminalIso g).inv ≫ g.inverseImage.map (Sheaf.ringOneHom O) ≫ m :=
  congrArg (fun z ↦ (inverseImageTerminalIso g).inv ≫ z)
    ((g.adj.homEquiv_naturality_left_symm (Sheaf.ringOneHom O) (g.adj.homEquiv _ _ m)).trans
      (congrArg (fun z ↦ g.inverseImage.map (Sheaf.ringOneHom O) ≫ z)
        ((g.adj.homEquiv _ E).symm_apply_apply m)))

end MorphismOfTopoi

namespace Stacks.Sheaves.RingedToposModules

section ToposLevel

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

/-- The bijection of the adjunction of Stacks 03D3 is `toposModulesHomEquiv`. -/
lemma inverseImageAdjDirectImageModules_homEquiv_eq
    (G : SheafOfModules.{w'} O) (F : SheafOfModules.{w} (inverseImageRingSheaf g O))
    (a : (inverseImageModules g O).obj G ⟶ F) :
    (inverseImageAdjDirectImageModules g O).homEquiv G F a = toposModulesHomEquiv g O G F a :=
  DFunLike.congr_fun (congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) G) F) a

/-- On underlying sheaves of sets, the transpose along the adjunction of Stacks 03D3 is the
transpose along the adjunction of the underlying topoi. -/
lemma moduleSheafFunctor_map_inverseImageAdjDirectImageModules_homEquiv
    {G : SheafOfModules.{w'} O} {F : SheafOfModules.{w} (inverseImageRingSheaf g O)}
    (a : (inverseImageModules g O).obj G ⟶ F) :
    (Sheaf.moduleSheafFunctor O).map ((inverseImageAdjDirectImageModules g O).homEquiv G F a) =
      g.adj.homEquiv _ _
        ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf g O)).map a) :=
  (congrArg (Sheaf.moduleSheafFunctor O).map
      (inverseImageAdjDirectImageModules_homEquiv_eq g O G F a)).trans
    (moduleSheafFunctor_map_toposModulesHomEquiv g O a)

end ToposLevel

end Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.RingedToposModules

open Stacks.SheafOfModules.ChangeOfRings Stacks.Sheaves.FinitePresentation

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- The adjunction of Stacks 03CZ along the inverse-image form of the structure map. -/
abbrev fSharpAdjunction :=
  f.extendRestrictScalarsFSharpAdjunction

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The transpose along Stacks 03CZ of the explicit comparison. -/
lemma fSharpAdjunction_homEquiv_pullbackModulesUnitIso_inv :
    (fSharpAdjunction f).homEquiv _ _ (pullbackModulesUnitIso f).inv =
      (inverseImageModulesUnitIso f).inv ≫
        unitToRestrictScalarsUnit f.fSharpInverseImage :=
  ((fSharpAdjunction f).homEquiv_naturality_left (inverseImageModulesUnitIso f).inv
      (extendScalarsFSharpUnitIso f).hom).trans
    (congrArg (fun m ↦ (inverseImageModulesUnitIso f).inv ≫ m)
      (homEquiv_unitComparison _ (fSharpAdjunction f)))

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The identification of the inverse image of `1_{O_D}` with `1_{f⁻¹O_D}` is the identity on
underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_inverseImageModulesUnitIso_inv :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        (inverseImageModulesUnitIso f).inv = 𝟙 _ :=
  (Sheaf.moduleSheafFunctor
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_id _

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- On underlying sheaves of sets, the transpose along Stacks 03CZ of the explicit comparison is
the inverse-image form of the structure map. -/
lemma moduleSheafFunctor_map_fSharpAdjunction_homEquiv :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((fSharpAdjunction f).homEquiv _ _ (pullbackModulesUnitIso f).inv) =
      (sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage :=
  (congrArg (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
      (fSharpAdjunction_homEquiv_pullbackModulesUnitIso_inv f)).trans
    (((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_comp _ _).trans
      ((congrArg (fun m ↦ m ≫ (Sheaf.moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            (unitToRestrictScalarsUnit f.fSharpInverseImage))
          (moduleSheafFunctor_map_inverseImageModulesUnitIso_inv f)).trans
        ((Category.id_comp _).trans
          (moduleSheafFunctor_map_unitToRestrictScalarsUnit f.fSharpInverseImage))))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The bijection of the adjunction of Stacks 03D7 is the bijection of Stacks 03CZ followed by
the bijection of Stacks 03D3. -/
lemma pullbackAdjPushforwardModules_homEquiv_eq
    (k : f.pullbackModules.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (pullbackAdjPushforwardModules f).homEquiv _ _ k =
      (inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv _ _
        ((fSharpAdjunction f).homEquiv _ _ k) :=
  DFunLike.congr_fun (congrFun (congrFun (Adjunction.comp_homEquiv
    (inverseImageAdjDirectImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (fSharpAdjunction f)) _) _) k

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- On underlying sheaves of sets, the transpose along Stacks 03D7 of the explicit comparison is
the transpose along the adjunction of the underlying topoi of the inverse-image form of the
structure map. -/
lemma moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).homEquiv _ _ (pullbackModulesUnitIso f).inv) =
      f.toToposHom.adj.homEquiv _ _
        ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage) :=
  (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (pullbackAdjPushforwardModules_homEquiv_eq f (pullbackModulesUnitIso f).inv)).trans
    ((moduleSheafFunctor_map_inverseImageAdjDirectImageModules_homEquiv f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _).trans
      (congrArg (f.toToposHom.adj.homEquiv _ _)
        (moduleSheafFunctor_map_fSharpAdjunction_homEquiv f)))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The explicit comparison, transposed along Stacks 03D7 and read as a global section of `O_C`,
is the unit section. -/
lemma pushforwardModulesUnitHomEquiv_pullbackModulesUnitIso_inv :
    pushforwardModulesUnitHomEquiv f
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((pullbackAdjPushforwardModules f).homEquiv _ _ (pullbackModulesUnitIso f).inv) =
      Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (congrArg (f.toToposHom.pushforwardTerminalHomEquiv
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      ((unitTerminalHomEquiv_eq (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _ _).trans
        (congrArg (fun z ↦ Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫ z)
          (moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv f)))).trans
    ((f.toToposHom.pushforwardTerminalHomEquiv_ringOneHom_comp_homEquiv
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z ↦ z ≫ (sheafCompose X.J (forget RingCat.{w})).map
              f.fSharpInverseImage)
            (f.toToposHom.inverseImageTerminalIso_inv_comp_map_ringOneHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).trans
          (Sheaf.ringOneHom_comp_ringSheafMap f.fSharpInverseImage))))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The comparison `f^*O_D ≅ O_C` built by corepresentability,
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, is the explicit one,
`Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso`. -/
theorem pullbackModulesObjUnitIso_eq :
    pullbackModulesObjUnitIso f = pullbackModulesUnitIso f := by
  have hco : (pullbackModulesObjUnitCorepresentableBy f).homEquiv
      ((pullbackModulesUnitIso f).inv) =
        𝟙 (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    (Equiv.symm_apply_eq _).mpr
      ((pushforwardModulesUnitHomEquiv_pullbackModulesUnitIso_inv f).trans
        (unitTerminalHomEquiv_id_eq (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).symm)
  exact Iso.ext (((Iso.comp_inv_eq _).mp
    ((pullbackModulesObjUnitIso_hom_comp f _ _).trans hco)).trans (Category.id_comp _))

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The transpose along Stacks 03CZ of the unit comparison `ν : f^*O_D ⟶ O_C` is the identity
`f⁻¹1_{O_D} = 1_{f⁻¹O_D}` followed by
`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit` at the inverse-image form of the
structure map. -/
theorem fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv :
    (fSharpAdjunction f).homEquiv _ _ (pullbackModulesObjUnitIso f).inv =
      (inverseImageModulesUnitIso f).inv ≫
        unitToRestrictScalarsUnit f.fSharpInverseImage :=
  (congrArg (fun e : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
        f.pullbackModules.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ↦
      (fSharpAdjunction f).homEquiv _ _ e.inv) (pullbackModulesObjUnitIso_eq f)).trans
    (fSharpAdjunction_homEquiv_pullbackModulesUnitIso_inv f)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- On underlying sheaves of sets, the transpose of the unit comparison `ν : f^*O_D ⟶ O_C` along
the adjunction of Stacks 03CZ is the inverse-image form `f♯ : f⁻¹O_D ⟶ O_C` of the structure
map. -/
theorem moduleSheafFunctor_map_fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((fSharpAdjunction f).homEquiv _ _ (pullbackModulesObjUnitIso f).inv) =
      (sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImage :=
  (congrArg (fun e : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
        f.pullbackModules.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ↦
      (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((fSharpAdjunction f).homEquiv _ _ e.inv)) (pullbackModulesObjUnitIso_eq f)).trans
    (moduleSheafFunctor_map_fSharpAdjunction_homEquiv f)

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.RingedToposModules (
  pullbackModulesObjUnitIso pullbackModulesObjUnitIso_hom_comp
  pullbackModulesObjUnitCorepresentableBy pushforwardModulesUnitHomEquiv
  fSharpAdjunction inverseImageAdjDirectImageModules inverseImageModules
  moduleSheafFunctor_map_inverseImageAdjDirectImageModules_homEquiv)

open Stacks.SheafOfModules.ChangeOfRings (unitToRestrictScalarsUnit
  moduleSheafFunctor_map_unitToRestrictScalarsUnit)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- The transpose of the canonical comparison `f^*O_D ⟶ O_C` along the adjunction
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` of Stacks 03D7 is the
unit-module structure map followed by the inverse of the comparison
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIsoApp` of the two direct images. -/
lemma modulesHomEquiv_pullbackUnitStructureMap :
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).homEquiv
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (pullbackUnitStructureMap f) =
      unitStructureMap f ≫
        (f.toModulesPushforwardIsoApp
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inv :=
  (Iso.eq_comp_inv _).mpr
    ((Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).symm.trans
      (homEquiv_pullbackUnitStructureMap f))

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Precomposing a morphism into a direct image with the comparison
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIsoApp` of the two direct images does not
change the global section it names. -/
lemma pushforwardModulesUnitHomEquiv_comp_toModulesPushforwardIsoApp_inv
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (b : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
      (pushforwardModules f).obj N) :
    pushforwardModulesUnitHomEquiv f.toModulesHom N
        (b ≫ (f.toModulesPushforwardIsoApp N).inv) =
      f.toToposHom.pushforwardTerminalHomEquiv
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)
        (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((pushforwardModules f).obj N) b) :=
  rfl

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The unit-module structure map `O_D ⟶ f_*O_C`, read as a global section of `f_*O_C`, is the
unit section of `O_D` followed by the adjunct of the inverse-image form of the structure map. -/
lemma unitTerminalHomEquiv_unitStructureMap :
    unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        ((pushforwardModules f).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
        (unitStructureMap f) =
      Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫
        f.toToposHom.adj.homEquiv _ _
          ((sheafCompose X.J (forget RingCat.{w})).map f.fSharpInverseImageRing) :=
  (unitTerminalHomEquiv_eq (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _
      (unitStructureMap f)).trans
    (congrArg (fun z ↦ Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫ z)
      ((moduleSheafFunctor_map_unitStructureMap f).trans (fSharpInverseImageRing_adjunct f)))

/-- The canonical comparison `f^*O_D ⟶ O_C`, transposed along Stacks 03D7 and read as a global
section of `O_C`, is the unit section. -/
lemma pushforwardModulesUnitHomEquiv_pullbackUnitStructureMap :
    pushforwardModulesUnitHomEquiv f.toModulesHom
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toModulesHom).homEquiv _ _ (pullbackUnitStructureMap f)) =
      Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (congrArg (pushforwardModulesUnitHomEquiv f.toModulesHom
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (modulesHomEquiv_pullbackUnitStructureMap f)).trans
    ((pushforwardModulesUnitHomEquiv_comp_toModulesPushforwardIsoApp_inv f _
          (unitStructureMap f)).trans
      ((congrArg (f.toToposHom.pushforwardTerminalHomEquiv
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
          (unitTerminalHomEquiv_unitStructureMap f)).trans
        ((f.toToposHom.pushforwardTerminalHomEquiv_ringOneHom_comp_homEquiv
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z ↦ z ≫ (sheafCompose X.J (forget RingCat.{w})).map
                  f.fSharpInverseImageRing)
                (f.toToposHom.inverseImageTerminalIso_inv_comp_map_ringOneHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).trans
              (Sheaf.ringOneHom_comp_ringSheafMap f.fSharpInverseImageRing))))))

/-- The comparison `f^*O_D ≅ O_C` built by corepresentability, followed by the canonical
comparison `f^*O_D ⟶ O_C`, is the identity. -/
lemma pullbackModulesObjUnitIso_hom_comp_pullbackUnitStructureMap :
    (pullbackModulesObjUnitIso f.toModulesHom).hom ≫ pullbackUnitStructureMap f =
      𝟙 (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (pullbackModulesObjUnitIso_hom_comp f.toModulesHom _ (pullbackUnitStructureMap f)).trans
    ((Equiv.symm_apply_eq _).mpr
      ((pushforwardModulesUnitHomEquiv_pullbackUnitStructureMap f).trans
        (unitTerminalHomEquiv_id_eq (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).symm))

/-- The canonical comparison `f^*O_D ⟶ O_C` attached to a morphism of ringed topoi is an
isomorphism. -/
instance isIso_pullbackUnitStructureMap : IsIso (pullbackUnitStructureMap f) :=
  have : IsIso ((pullbackModulesObjUnitIso f.toModulesHom).hom ≫
      pullbackUnitStructureMap f) :=
    (pullbackModulesObjUnitIso_hom_comp_pullbackUnitStructureMap f) ▸ inferInstance
  IsIso.of_isIso_comp_left (pullbackModulesObjUnitIso f.toModulesHom).hom
    (pullbackUnitStructureMap f)

/-! ### The transpose of `ν` along the extension of scalars alone -/

/-- The global section of `O_C` that the corepresentability bijection of Stacks 03LU attaches to
a morphism `q : f^*O_D ⟶ O_C` is the unit section of `f⁻¹O_D` followed by the underlying morphism
of sheaves of sets of the transpose of `q` along the adjunction of Stacks 03CZ. -/
lemma pushforwardModulesUnitHomEquiv_eq_ringOneHom_comp
    (q : f.toModulesHom.pullbackModules.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    pushforwardModulesUnitHomEquiv f.toModulesHom
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toModulesHom).homEquiv _ _ q) =
      Sheaf.ringOneHom
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((fSharpAdjunction f.toModulesHom).homEquiv _ _ q) :=
  (congrArg (fun b ↦ pushforwardModulesUnitHomEquiv f.toModulesHom
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) b)
      (Adjunction.comp_homEquiv_apply
        (inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (fSharpAdjunction f.toModulesHom) q)).trans
    ((congrArg (f.toToposHom.pushforwardTerminalHomEquiv
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        ((unitTerminalHomEquiv_eq (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _ _).trans
          (congrArg (fun z ↦ Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫ z)
            (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_homEquiv
              f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _)))).trans
      ((f.toToposHom.pushforwardTerminalHomEquiv_ringOneHom_comp_homEquiv
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((fSharpAdjunction f.toModulesHom).homEquiv _ _ q))
            (f.toToposHom.inverseImageTerminalIso_inv_comp_map_ringOneHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))))

/-- The identity `f⁻¹1_{O_D} = 1_{f⁻¹O_D}` of `Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`
followed by the transpose of the canonical comparison `ν : f^*O_D ⟶ O_C` along the adjunction of
Stacks 03CZ is `Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit` at the
inverse-image form of the structure map. -/
lemma pullbackModuleUnitIso_hom_comp_fSharpAdjunction_homEquiv :
    (pullbackModuleUnitIso X.J f.toToposHom.inverseImage
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom ≫
        (fSharpAdjunction f.toModulesHom).homEquiv
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (pullbackUnitStructureMap f) =
      unitToRestrictScalarsUnit f.fSharpInverseImageRing := by
  have hι : (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        (pullbackModuleUnitIso X.J f.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom =
      𝟙 _ :=
    (Sheaf.moduleSheafFunctor
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_id _
  have hone : Sheaf.ringOneHom
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          (pullbackModuleUnitIso X.J f.toToposHom.inverseImage
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom =
      Sheaf.ringOneHom
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
    (congrArg (fun m ↦ Sheaf.ringOneHom
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫ m)
      hι).trans
      (Category.comp_id _)
  have hL : Sheaf.ringOneHom
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((pullbackModuleUnitIso X.J f.toToposHom.inverseImage
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).hom ≫
            (fSharpAdjunction f.toModulesHom).homEquiv _ _ (pullbackUnitStructureMap f)) =
      Sheaf.ringOneHom
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((fSharpAdjunction f.toModulesHom).homEquiv _ _ (pullbackUnitStructureMap f)) :=
    (congrArg (fun m ↦ Sheaf.ringOneHom
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫ m)
        ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_comp _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun m ↦ m ≫ (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((fSharpAdjunction f.toModulesHom).homEquiv _ _ (pullbackUnitStructureMap f))) hone))
  have hR : Sheaf.ringOneHom
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        (Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          (unitToRestrictScalarsUnit f.fSharpInverseImageRing) =
      Sheaf.ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    (congrArg (fun m ↦ Sheaf.ringOneHom
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫ m)
        (moduleSheafFunctor_map_unitToRestrictScalarsUnit f.fSharpInverseImageRing)).trans
      (Sheaf.ringOneHom_comp_ringSheafMap f.fSharpInverseImageRing)
  exact Sheaf.hom_ext_ringOneHom (hL.trans (((pushforwardModulesUnitHomEquiv_eq_ringOneHom_comp f
      (pullbackUnitStructureMap f)).symm.trans
    (pushforwardModulesUnitHomEquiv_pullbackUnitStructureMap f)).trans hR.symm))

/-- The transpose of the canonical comparison `ν : f^*O_D ⟶ O_C` along the adjunction of
Stacks 03CZ is the identity `f⁻¹1_{O_D} = 1_{f⁻¹O_D}` followed by
`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit` at the inverse-image form of the
structure map. -/
lemma fSharpAdjunction_homEquiv_pullbackUnitStructureMap :
    (fSharpAdjunction f.toModulesHom).homEquiv
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (pullbackUnitStructureMap f) =
      (pullbackModuleUnitIso X.J f.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).inv ≫
        unitToRestrictScalarsUnit f.fSharpInverseImageRing :=
  (Iso.eq_inv_comp _).mpr (pullbackModuleUnitIso_hom_comp_fSharpAdjunction_homEquiv f)

end AlgebraicGeometry.RingedToposHom

end
