module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue

/-!
# The inverse image of an algebra sheaf, on underlying sheaves of sets

Let `g : Y ⟶ X` be a morphism of algebraic spaces and `A` a sheaf of `𝒪_X`-algebras.  The module
underlying the algebra pullback `g^*A = 𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹A` is identified with the module
pullback `g^*(A_mod)` by
`AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso`. This file computes the
transpose of that identification along the extension-of-scalars adjunction of Stacks 03CZ on
underlying sheaves of sets: it is the inverse image of `A` followed by the first inclusion
`g⁻¹A ⟶ g^*A` of the pushout, i.e. the ring-level map `AlgebraicGeometry.Space.algebraPullbackMap`.
This is the module-level half of the identification, on chart sections, of the module-level and
ring-level canonical sections of `g^*A` used for the base-change clause of Stacks 081V.

## Main results

* `moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_eq`, in
  `Stacks.Sheaves.RingedToposModules`: on underlying sheaves of sets, the transpose along the
  pullback/pushforward adjunction of Stacks 03D7 is the transpose along the adjunction of the
  topoi of the transpose along Stacks 03CZ.
* `Stacks.SheafOfModules.AlgebraPushout.moduleSheafFunctor_map_pullbackComparison_comp`: on
  sheaves of sets, the three factors of the identification compose to the first inclusion of
  the pushout.
* `moduleSheafFunctor_map_extendScalarsAdjunction_homEquiv_underlyingModuleIso`, in
  `AlgebraicGeometry.Space`: the transpose of the identification along Stacks 03CZ is, on
  sheaves of sets, the inverse image of `A` followed by
  `AlgebraicGeometry.Space.algebraPullbackMap`.

## Implementation notes

The statements name the object of `Stacks.FlatChangeOfRings.extendScalarsAdjunction` exactly as
the factors of the identification produce it (the source of
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`), and the
codomain of the transposed map as the inverse image of the underlying sheaf of sets of `A`.
Other spellings of the same objects are definitionally equal, but checking that inside larger
terms is expensive for both the elaborator and the kernel.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u u' u'' v v' w w'


/-- The transpose of a composite `L e ≫ eqToHom ≫ k` along an adjunction `L ⊣ R`, after a
functor `F`: it is `F e ≫ eqToHom ≫ F m` once the transpose of `k` is known to be `m`. -/
theorem _root_.CategoryTheory.Adjunction.map_homEquiv_mapIso_trans_eqToIso_trans_hom_of_eq
    {C D E : Type*} [Category C] [Category D] [Category E] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (F : C ⥤ E) {a a' b : C}
    (e : a ≅ a') (h : a' = b) {c : D} (k : L.obj b ≅ c) {m : b ⟶ R.obj c}
    (hk : adj.homEquiv _ _ k.hom = m) :
    F.map (adj.homEquiv _ _ ((L.mapIso e ≪≫ eqToIso (congrArg L.obj h) ≪≫ k).hom)) =
      F.map e.hom ≫ eqToHom (congrArg F.obj h) ≫ F.map m := by
  subst h hk
  simp [Adjunction.homEquiv_naturality_left]

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u', w}} {Y : RingedTopos.{v', u'', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- **On underlying sheaves of sets the transpose along Stacks 03D7 is the transpose along the
adjunction of the underlying topoi of the transpose along Stacks 03CZ.** -/
lemma moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_eq
    {G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (k : f.pullbackModules.obj G ⟶ F) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).homEquiv G F k) =
      f.toToposHom.adj.homEquiv _ _
        ((Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((fSharpAdjunction f).homEquiv _ _ k)) :=
  (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (DFunLike.congr_fun (congrFun (congrFun (Adjunction.comp_homEquiv
        (inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (fSharpAdjunction f)) G) F) k)).trans
    (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_homEquiv f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _)

end Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules.AlgebraPushout

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
  Stacks.Sheaves.RingedToposModules

section PullbackComparison

universe uC vC uD vD ww

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [HasWeakSheafify J AddCommGrpCat.{ww}] [J.WEqualsLocallyBijective AddCommGrpCat.{ww}]
  [HasWeakSheafify J CommRingCat.{ww}] [J.WEqualsLocallyBijective CommRingCat.{ww}]
  [HasPushouts (Sheaf J CommRingCat.{ww})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww)))

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J CommRingCat] [J.WEqualsLocallyBijective CommRingCat] in
/-- On underlying sheaves of sets, the interchange of inverse image and restriction of scalars,
the comparison `underlyingModule_inverseImage…`, and the first inclusion of the pushout of
`f⁻¹a` along `φ`, read as a map of modules, compose to that first inclusion. -/
theorem moduleSheafFunctor_map_pullbackComparison_comp
    {O Rt : Sheaf K CommRingCat.{ww}} (a : O ⟶ Rt) {R' : Sheaf J CommRingCat.{ww}}
    (φ : (inverseImageCommRingFunctor f).obj O ⟶ R')
    (h : (_root_.SheafOfModules.restrictScalars
          (pullbackRingSheafMap J f.inverseImage (Stacks.FlatChangeOfRings.ringSheafMap a))).obj
        (pullbackModuleObj J f.inverseImage (Stacks.SheafOfModules.Tensor.ringSheaf Rt)
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rt))) =
      underlyingModule_anySite (Under.mk ((inverseImageCommRingFunctor f).map a))) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        ((inverseImageCommRingFunctor f).obj O))).map
        (pullbackModuleObjRestrictScalarsIso J f.inverseImage
          (Stacks.FlatChangeOfRings.ringSheafMap a)
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rt))).symm.hom ≫
      eqToHom (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        ((inverseImageCommRingFunctor f).obj O))).obj h) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        ((inverseImageCommRingFunctor f).obj O))).map
        (pushoutInlModuleMap_anySite φ (Under.mk ((inverseImageCommRingFunctor f).map a))) =
      (sheafCompose J (forget CommRingCat.{ww})).map
        (pushout.inl ((inverseImageCommRingFunctor f).map a) φ) :=
  CategoryTheory.Sheaf.hom_ext_sections fun _ _ ↦ rfl

end PullbackComparison

end Stacks.SheafOfModules.AlgebraPushout

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The identification of the module underlying `g^*A` with `g^*(A_mod)`, unfolded into its three
factors. -/
theorem underlyingModuleAlgebraPullbackModulePullbackIso_eq (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A =
      (Stacks.FlatChangeOfRings.extendScalars (structurePullbackMap B S hS g)).mapIso
        ((Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso
          (SmallEtale.topology B S hS Y.1)
          ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
          (Stacks.FlatChangeOfRings.ringSheafMap
            (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))).symm) ≪≫
      eqToIso (congrArg (Stacks.FlatChangeOfRings.extendScalars
          (structurePullbackMap B S hS g)).obj
        (underlyingModule_inverseImageAlgebra B S hS g A).symm) ≪≫
      (underlyingModuleAlgebraPullbackIso B S hS g A).symm :=
  rfl

/-- The forward map of the identification of the module underlying `g^*A` with `g^*(A_mod)`,
unfolded into its three factors. -/
theorem underlyingModuleAlgebraPullbackModulePullbackIso_hom_eq (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom =
      ((Stacks.FlatChangeOfRings.extendScalars (structurePullbackMap B S hS g)).mapIso
            (Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso
          (SmallEtale.topology B S hS Y.1)
          ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
          (Stacks.FlatChangeOfRings.ringSheafMap
            (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))).symm ≪≫
          eqToIso (congrArg (Stacks.FlatChangeOfRings.extendScalars
            (structurePullbackMap B S hS g)).obj
              (underlyingModule_inverseImageAlgebra B S hS g A).symm) ≪≫
          (underlyingModuleAlgebraPullbackIso B S hS g A).symm).hom :=
  rfl

/-- **The transpose along Stacks 03CZ of the identification of the module underlying `g^*A`
with `g^*(A_mod)` is, on sheaves of sets, the first inclusion `g⁻¹A ⟶ g^*A` of the pushout.**
The map transposed is the forward map of
`AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso`, in the unfolded form
`AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso_hom_eq`. -/
theorem moduleSheafFunctor_map_extendScalarsAdjunction_homEquiv_underlyingModuleIso
    (g : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) :
    ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2)))).map
      ((Stacks.FlatChangeOfRings.extendScalarsAdjunction (structurePullbackMap B S hS g)).homEquiv
        _
        ((algebraPullback B S hS g).obj A).underlyingModule
        ((Stacks.FlatChangeOfRings.extendScalars (structurePullbackMap B S hS g)).mapIso
            (Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso
          (SmallEtale.topology B S hS Y.1)
          ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
          (Stacks.FlatChangeOfRings.ringSheafMap
            (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))).symm ≪≫
          eqToIso (congrArg (Stacks.FlatChangeOfRings.extendScalars
            (structurePullbackMap B S hS g)).obj
              (underlyingModule_inverseImageAlgebra B S hS g A).symm) ≪≫
          (underlyingModuleAlgebraPullbackIso B S hS g A).symm).hom) :
          (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.obj
              ((sheafCompose (smallEtaleRingedTopos B S hS X).J (forget CommRingCat.{u})).obj
          (AlgebraSheaf.forget.obj A)) ⟶
            (sheafCompose (smallEtaleRingedTopos B S hS Y).J (forget CommRingCat.{u})).obj
              ((algebraPullback B S hS g ⋙ AlgebraSheaf.forget).obj A)) =
      (sheafCompose (smallEtaleRingedTopos B S hS Y).J (forget CommRingCat.{u})).map
        ((algebraPullbackMap B S hS g).app A) := by
  refine (Adjunction.map_homEquiv_mapIso_trans_eqToIso_trans_hom_of_eq
      (Stacks.FlatChangeOfRings.extendScalarsAdjunction (structurePullbackMap B S hS g))
      (Sheaf.moduleSheafFunctor.{u, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2))))
      (Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso
          (SmallEtale.topology B S hS Y.1)
          ((smallEtaleRingedToposHom B S hS g).toToposHom).inverseImage
          (Stacks.FlatChangeOfRings.ringSheafMap
            (O₁ := structureSheaf B S hS X.1 X.2) (O₂ := A.right) A.hom)
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.right))).symm
      (underlyingModule_inverseImageAlgebra B S hS g A).symm
      (underlyingModuleAlgebraPullbackIso B S hS g A).symm
      (Stacks.SheafOfModules.AlgebraPushout.homEquiv_extendScalarsComparison_anySite
        (structurePullbackMap B S hS g) (inverseImageAlgebra B S hS g A))).trans ?_
  exact Stacks.SheafOfModules.AlgebraPushout.moduleSheafFunctor_map_pullbackComparison_comp
    (smallEtaleRingedToposHom B S hS g).toToposHom A.hom (structurePullbackMap B S hS g)
    (underlyingModule_inverseImageAlgebra B S hS g A).symm

/-- `moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_eq` (in
`Stacks.Sheaves.RingedToposModules`) for a morphism of algebraic spaces, with the
extension-of-scalars adjunction spelled as
`Stacks.FlatChangeOfRings.extendScalarsAdjunction` along `structurePullbackMap`. -/
theorem moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_flat (g : Y ⟶ X)
    {G : Modules.{u, u} B S hS X.1 X.2} {F : Modules.{u, u} B S hS Y.1 Y.2}
    (k : (modulePullback B S hS g).obj G ⟶ F) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS X)).map
        ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).homEquiv
          G F k) =
      (smallEtaleRingedToposHom B S hS g).toToposHom.adj.homEquiv _ _
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
            ((ringSheafPullback B S hS g).obj (structureSheaf B S hS X.1 X.2)))).map
          ((Stacks.FlatChangeOfRings.extendScalarsAdjunction
            (structurePullbackMap B S hS g)).homEquiv _ _ k)) :=
  moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_eq
    (smallEtaleRingedToposModulesHom B S hS g) k

end AlgebraicGeometry.Space

end
