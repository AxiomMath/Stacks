module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.Deformation.ToposThickening.BaseThickeningInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearRingVariable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearSourceNaturality
public import StacksFrontier.Deformation.ToposThickening.Helpers.ExtDescentAlongThickening
public import StacksFrontier.Deformation.ToposThickening.Helpers.PushforwardBilinearPairing
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundaryPushout
public import StacksFrontier.Deformation.ToposThickening.TrivializedThickeningComparison

/-!
# Pushing extensions forward along a morphism of the targets of two thickenings

Let `i₁ : X ⟶ Y₁` and `i₂ : X ⟶ Y₂` be two first order thickenings of the same ringed topos and
let `j : Y₂ ⟶ Y₁` be a morphism of ringed topoi whose underlying morphism of topoi is an
equivalence (for instance a first order thickening), together with a map
`ρ : i₁_*O_X ⟶ j_*i₂_*O_X` of the two bases making the square of structure maps commute. This is
the situation of Stacks 0CYD with the two thickenings presented on their own sites, as in the
proof of Stacks 0CYF for a surjection `A'₁ ⟶ A'₂` of thickenings of `A`, where
`Y₂ = X_{A'₂} ⊂ Y₁ = X_{A'₁}`.

The direct image `j_*` carries an extension of `F` by `K` over the second thickening to one of
`ρ^*j_*F` by `ρ^*j_*K` over the first, and its action map is computed here: it is the direct image
of the action map, precomposed with the canonical map `ℐ₁ ⊗ ρ^*j_*F ⟶ ρ^*j_*(ℐ₂ ⊗ F)` built from
the map `ℐ₁ ⟶ j_*ℐ₂` of square-zero ideals induced by `j^♯`.

## Main definitions

* `Deformation.ToposThickening.ThickeningTargetMorphism`: the data `j`, `ρ` and the commuting
  square.
* `Deformation.ToposThickening.ThickeningTargetMorphism.basePushforward`: `Ψ₀ = ρ^*j_*` on modules
  over the bases.
* `Deformation.ToposThickening.ThickeningTargetMorphism.restrictIso`: `j_*` of a module read over
  the second thickening is `Ψ₀` of it read over the first.

## References

* [Stacks Project, Tag 0CYD](https://stacks.math.columbia.edu/tag/0CYD)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor
  pushforwardRingSheaf)
open Stacks.Sheaves.ToposPullback (pullbackModuleFunctor pullbackRingSheafMap
  pullbackRestrictScalarsIso)

universe v u v₁ u₁ v₂ u₂ w

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **A morphism of the targets of two thickenings of the same ringed topos.** For
`i₁ : X ⟶ Y₁` and `i₂ : X ⟶ Y₂`, a morphism of ringed topoi `j : Y₂ ⟶ Y₁` together with a map
`ρ : i₁_*O_X ⟶ j_*i₂_*O_X` of sheaves of rings on `Y₁` such that the two composites
`O_{Y₁} ⟶ j_*i₂_*O_X` agree. -/
structure ThickeningTargetMorphism (i₁ : RingedToposHom X Y₁) (i₂ : RingedToposHom X Y₂) where
  /-- The morphism of the thickened ringed topoi. -/
  j : RingedToposHom Y₂ Y₁
  /-- The comparison of the two bases. -/
  ρ : baseRing i₁ ⟶ (pushforwardCommRingFunctor j.toToposHom).obj (baseRing i₂)
  /-- The square of structure maps commutes. -/
  comm : i₁.fSharp ≫ ρ = j.fSharp ≫ (pushforwardCommRingFunctor j.toToposHom).map i₂.fSharp

namespace ThickeningTargetMorphism

variable {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)

/-- The morphism of ringed topoi `(Y₂, i₂_*O_X) ⟶ (Y₁, i₁_*O_X)` of the two bases. -/
noncomputable abbrev baseHom :
    RingedToposHom (reshape Y₂ (baseRing i₂)) (reshape Y₁ (baseRing i₁)) where
  toToposHom := D.j.toToposHom
  fSharp := D.ρ

/-- **The direct image on modules over the bases**, `Ψ₀ = ρ^*j_*`. -/
noncomputable abbrev basePushforward :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂)) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)) :=
  D.baseHom.pushforwardModules

/-- The two composite ring maps `O_{Y₁} ⟶ j_*i₂_*O_X` agree, on underlying sheaves of rings. -/
theorem ringMap_comm :
    D.j.structureRingMap ≫ pullbackRingSheafMap Y₁.J D.j.toToposHom.pushforward
        (structureRingMap i₂) =
      structureRingMap i₁ ≫ D.baseHom.structureRingMap := by
  have h1 := Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap Y₁.J
    D.j.toToposHom.pushforward i₂.fSharp
  have h2 : (Stacks.forgetCommRingSheaf Y₁.J).map
      (D.j.fSharp ≫ (pushforwardCommRingFunctor D.j.toToposHom).map i₂.fSharp) =
      (Stacks.forgetCommRingSheaf Y₁.J).map (i₁.fSharp ≫ D.ρ) := congrArg _ D.comm.symm
  rw [Functor.map_comp, Functor.map_comp] at h2
  exact (congrArg (fun m => (Stacks.forgetCommRingSheaf Y₁.J).map D.j.fSharp ≫ m) h1.symm).trans h2

variable [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **`j_*` of a module read over the second thickening is `Ψ₀` of it read over the first**: the
identity of the underlying sheaf of sets `j_*F`, assembled from the comparison of Stacks 03D2 with
restriction of scalars. -/
noncomputable def restrictIso
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))) :
    D.j.pushforwardModules.obj ((structureRestrict i₂).obj M) ≅
      (structureRestrict i₁).obj (D.basePushforward.obj M) :=
  (SheafOfModules.restrictScalars D.j.structureRingMap).mapIso
      ((pullbackRestrictScalarsIso D.j.toToposHom.pushforward (structureRingMap i₂)).app M) ≪≫
    (Stacks.SheafOfModules.restrictScalarsCompIso (structureRingMap i₁)
      D.baseHom.structureRingMap _ D.ringMap_comm
      ((pushforwardModuleFunctor D.j.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))).obj M))

/-- On sections, the comparison `restrictIso` is the identity. -/
theorem restrictIso_hom_val_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))) (U : Y₁.Cᵒᵖ)
    (y : (D.j.pushforwardModules.obj ((structureRestrict i₂).obj M)).val.obj U) :
    (D.restrictIso M).hom.val.app U y = y := rfl

/-- On sections, the inverse of the comparison `restrictIso` is the identity. -/
theorem restrictIso_inv_val_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))) (U : Y₁.Cᵒᵖ)
    (y : ((structureRestrict i₁).obj (D.basePushforward.obj M)).val.obj U) :
    (D.restrictIso M).inv.val.app U y = y :=
  congrArg (fun φ => φ.val.app U y) (D.restrictIso M).hom_inv_id

/-- The comparison `restrictIso` is natural. -/
theorem restrictIso_hom_naturality
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))} (ψ : M ⟶ N) :
    D.j.pushforwardModules.map ((structureRestrict i₂).map ψ) ≫ (D.restrictIso N).hom =
      (D.restrictIso M).hom ≫ (structureRestrict i₁).map (D.basePushforward.map ψ) := by
  ext U y
  rfl

/-- The inverse of the comparison `restrictIso` is natural. -/
theorem restrictIso_inv_naturality
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))} (ψ : M ⟶ N) :
    (structureRestrict i₁).map (D.basePushforward.map ψ) ≫ (D.restrictIso N).inv =
      (D.restrictIso M).inv ≫ D.j.pushforwardModules.map ((structureRestrict i₂).map ψ) := by
  rw [Iso.comp_inv_eq, Category.assoc, restrictIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- The direct image of sheaves of sets along `j` is left exact, being a right adjoint. -/
noncomputable instance preservesFiniteLimits_pushforward :
    PreservesFiniteLimits D.j.toToposHom.pushforward :=
  letI : PreservesLimitsOfSize.{0, 0} D.j.toToposHom.pushforward :=
    D.j.toToposHom.adj.rightAdjoint_preservesLimits
  inferInstance

/-! ### The map of square-zero ideals -/

variable (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂)

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The image under `j^♯` of a section of `ℐ₁` is killed by `j_*` of the structure map of the
second thickening: it is the image under `ρ` of the image of that section in `i₁_*O_X`, which
vanishes. -/
theorem jSharp_incl_mem_kernel (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U) :
    (Sheaf.sectionsFunctor Y₁.J U).map ((sheafCompose Y₁.J (forget RingCat.{w})).map
        (pullbackRingSheafMap Y₁.J D.j.toToposHom.pushforward (structureRingMap i₂)))
      (D.j.structureRingMap.hom.app U (hi₁.incl.val.app U a)) = 0 := by
  refine (congrArg (fun φ => φ.hom.app U (hi₁.incl.val.app U a)) D.ringMap_comm).trans ?_
  change (D.baseHom.structureRingMap.hom.app U)
    ((structureRingMap i₁).hom.app U (hi₁.incl.val.app U a)) = 0
  have h0 : (structureRingMap i₁).hom.app U (hi₁.incl.val.app U a) = 0 :=
    (hi₁.kernel U _).2 ⟨a, rfl⟩
  rw [h0, map_zero]

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The section of `j_*ℐ₂` cut out by a section of `ℐ₁`**: the unique section of `j_*ℐ₂` whose
image in `j_*O_{Y₂}` is the image of the given section under `j^♯`. It exists because `j_*` is left
exact, so carries the kernel square of the second thickening to a kernel square. -/
theorem existsUnique_idealSection (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U) :
    ∃! m : (Sheaf.sectionsFunctor Y₁.J U).obj (D.j.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)
          ((structureRestrict i₂).obj hi₂.I))),
      (Sheaf.sectionsFunctor Y₁.J U).map (D.j.toToposHom.pushforward.map hi₂.inclSheafSets) m =
        D.j.structureRingMap.hom.app U (hi₁.incl.val.app U a) :=
  Stacks.Sheaves.ToposPullback.existsUnique_sections_of_isPullback Y₁.J
    D.j.toToposHom.pushforward (structureRingMap i₂) hi₂.inclSheafSets hi₂.isPullback_incl U _
    (D.jSharp_incl_mem_kernel hi₁ U a)

/-- The section of `j_*ℐ₂` cut out by a section of `ℐ₁`. -/
noncomputable def idealSection (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U) :
    (D.j.pushforwardModules.obj ((structureRestrict i₂).obj hi₂.I)).val.obj U :=
  (D.existsUnique_idealSection hi₁ hi₂ U a).exists.choose

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The image of `idealSection` in `j_*O_{Y₂}` is the image of the given section of `ℐ₁` under
`j^♯`. -/
theorem idealSection_spec (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U) :
    (Sheaf.sectionsFunctor Y₁.J U).map (D.j.toToposHom.pushforward.map hi₂.inclSheafSets)
        (D.idealSection hi₁ hi₂ U a) =
      D.j.structureRingMap.hom.app U (hi₁.incl.val.app U a) :=
  (D.existsUnique_idealSection hi₁ hi₂ U a).exists.choose_spec

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- A section of `j_*ℐ₂` whose image in `j_*O_{Y₂}` is the image of a section of `ℐ₁` under `j^♯`
is `idealSection` of that section. -/
theorem idealSection_eq (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U)
    (m : (Sheaf.sectionsFunctor Y₁.J U).obj (D.j.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)
        ((structureRestrict i₂).obj hi₂.I))))
    (hm : (Sheaf.sectionsFunctor Y₁.J U).map (D.j.toToposHom.pushforward.map hi₂.inclSheafSets) m =
      D.j.structureRingMap.hom.app U (hi₁.incl.val.app U a)) :
    D.idealSection hi₁ hi₂ U a = m :=
  (D.existsUnique_idealSection hi₁ hi₂ U a).unique (D.idealSection_spec hi₁ hi₂ U a) hm

/-- The structure map `j^♯ : O_{Y₁} ⟶ j_*O_{Y₂}`, as a map of `O_{Y₁}`-modules. -/
noncomputable abbrev jSharpUnit :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O) ⟶
      D.j.pushforwardModules.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)) :=
  SheafOfModules.unitToRestrictScalarsObjUnit D.j.structureRingMap

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The defining property of `idealSection`, read on the direct image of modules. -/
theorem pushforwardModules_map_incl_idealSection (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U) :
    (D.j.pushforwardModules.map hi₂.incl).val.app U (D.idealSection hi₁ hi₂ U a) =
      D.jSharpUnit.val.app U (hi₁.incl.val.app U a) :=
  D.idealSection_spec hi₁ hi₂ U a

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- `idealSection` is the only section with its defining property, read on the direct image of
modules. -/
theorem idealSection_eq_of_pushforwardModules (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U)
    (m : (D.j.pushforwardModules.obj ((structureRestrict i₂).obj hi₂.I)).val.obj U)
    (hm : (D.j.pushforwardModules.map hi₂.incl).val.app U m =
      D.jSharpUnit.val.app U (hi₁.incl.val.app U a)) :
    D.idealSection hi₁ hi₂ U a = m :=
  D.idealSection_eq hi₁ hi₂ U a m hm

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The sections `idealSection` are compatible with restriction. -/
theorem idealSection_naturality {U V : Y₁.Cᵒᵖ} (g : U ⟶ V) (a : hi₁.I.val.obj U) :
    (D.j.pushforwardModules.obj ((structureRestrict i₂).obj hi₂.I)).val.map g
        (D.idealSection hi₁ hi₂ U a) =
      D.idealSection hi₁ hi₂ V (hi₁.I.val.map g a) := by
  refine (D.idealSection_eq_of_pushforwardModules hi₁ hi₂ V _ _ ?_).symm
  exact ((PresheafOfModules.naturality_apply (D.j.pushforwardModules.map hi₂.incl).val g
    (D.idealSection hi₁ hi₂ U a)).trans
      (congrArg _ (D.pushforwardModules_map_incl_idealSection hi₁ hi₂ U a))).trans
    ((PresheafOfModules.naturality_apply D.jSharpUnit.val g _).symm.trans
      (congrArg (D.jSharpUnit.val.app V)
        (PresheafOfModules.naturality_apply hi₁.incl.val g a).symm))

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- `idealSection` is additive. -/
theorem idealSection_add (U : Y₁.Cᵒᵖ) (a b : hi₁.I.val.obj U) :
    D.idealSection hi₁ hi₂ U (a + b) =
      D.idealSection hi₁ hi₂ U a + D.idealSection hi₁ hi₂ U b := by
  refine D.idealSection_eq_of_pushforwardModules hi₁ hi₂ U _ _ ?_
  rw [map_add, D.pushforwardModules_map_incl_idealSection hi₁ hi₂ U a,
    D.pushforwardModules_map_incl_idealSection hi₁ hi₂ U b, ← map_add]
  exact congrArg (D.jSharpUnit.val.app U) (map_add (hi₁.incl.val.app U).hom a b).symm

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- `idealSection` is linear over `O_{Y₁}`. -/
theorem idealSection_smul (U : Y₁.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O).obj.obj U)
    (a : hi₁.I.val.obj U) :
    D.idealSection hi₁ hi₂ U
        (show ((structureRestrict i₁).obj hi₁.I).val.obj U from
          r • (show ((structureRestrict i₁).obj hi₁.I).val.obj U from a)) =
      r • D.idealSection hi₁ hi₂ U a := by
  refine D.idealSection_eq_of_pushforwardModules hi₁ hi₂ U _ _ ?_
  rw [map_smul, D.pushforwardModules_map_incl_idealSection hi₁ hi₂ U a, ← map_smul]
  exact congrArg (D.jSharpUnit.val.app U) (map_smul (hi₁.incl.val.app U).hom r _).symm

/-- The map of square-zero ideals induced by `j^♯`, on underlying sheaves of sets. -/
noncomputable def idealSheafHom :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O)
        ((structureRestrict i₁).obj hi₁.I) ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O)
        (D.j.pushforwardModules.obj ((structureRestrict i₂).obj hi₂.I)) :=
  Sheaf.unaryOpHom (fun U a => D.idealSection hi₁ hi₂ U a)
    (fun g a => D.idealSection_naturality hi₁ hi₂ g a)

/-- **The map `ℐ₁ ⟶ j_*ℐ₂` of square-zero ideals induced by `j^♯`**, as a map of
`O_{Y₁}`-modules. -/
noncomputable def idealMapOver :
    (structureRestrict i₁).obj hi₁.I ⟶
      D.j.pushforwardModules.obj ((structureRestrict i₂).obj hi₂.I) :=
  Stacks.Sheaves.RingedToposModules.ofSheafHom (D.idealSheafHom hi₁ hi₂)
    (fun U a b => D.idealSection_add hi₁ hi₂ U a b)
    (fun U r a => D.idealSection_smul hi₁ hi₂ U r a)

/-- On sections, `idealMapOver` sends a section of `ℐ₁` to its `idealSection`. -/
theorem idealMapOver_val_app (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U) :
    (D.idealMapOver hi₁ hi₂).val.app U a = D.idealSection hi₁ hi₂ U a :=
  rfl

/-- **The map `ℐ₁ ⟶ Ψ₀ℐ₂` of square-zero ideals induced by `j^♯`**, as a map of modules over
the base `i₁_*O_X`. -/
noncomputable def idealMap : hi₁.I ⟶ D.basePushforward.obj hi₂.I :=
  hi₁.restrictScalarsFullyFaithful.preimage (D.idealMapOver hi₁ hi₂ ≫ (D.restrictIso hi₂.I).hom)

/-- Read over the first thickening, `idealMap` is `idealMapOver` followed by `restrictIso`. -/
theorem restrictScalars_map_idealMap :
    (structureRestrict i₁).map (D.idealMap hi₁ hi₂) =
      D.idealMapOver hi₁ hi₂ ≫ (D.restrictIso hi₂.I).hom :=
  hi₁.restrictScalarsFullyFaithful.map_preimage _

/-- On sections, `idealMap` sends a section of `ℐ₁` to its `idealSection`. -/
theorem idealMap_val_app (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U) :
    (D.idealMap hi₁ hi₂).val.app U a = D.idealSection hi₁ hi₂ U a :=
  congrArg (fun φ => φ.val.app U a) (D.restrictScalars_map_idealMap hi₁ hi₂)

/-! ### The comparison `ℐ₁ ⊗ Ψ₀F ⟶ Ψ₀(ℐ₂ ⊗ F)` -/

section Tensor

variable [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂)))

/-- The pairing `ℐ₁ × Ψ₀F ⟶ Ψ₀(ℐ₂ ⊗ F)`: the map of ideals on the first factor, followed by `j_*`
of the universal pairing `ℐ₂ × F ⟶ ℐ₂ ⊗ F`. -/
noncomputable def idealTensorPairing :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)) hi₁.I ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))
          (D.basePushforward.obj F) ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))
        (D.basePushforward.obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).obj hi₂.I).obj F)) :=
  prod.map ((Sheaf.moduleSheafFunctor _).map (D.idealMap hi₁ hi₂))
      ((Sheaf.moduleSheafFunctor _).map (𝟙 (D.basePushforward.obj F))) ≫
    Stacks.SheafOfModules.pushPairing Y₁.J D.j.toToposHom.pushforward
      (Stacks.SheafOfModules.tensorSectionPairing hi₂.I F)

omit [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] in
/-- The pairing `idealTensorPairing` is bilinear over the base `i₁_*O_X`. -/
theorem isBilinearPairing_idealTensorPairing :
    Stacks.SheafOfModules.IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))
      (D.idealTensorPairing hi₁ hi₂ F) :=
  Stacks.SheafOfModules.IsBilinearPairing.precomp
    (Stacks.SheafOfModules.IsBilinearPairing.restrictScalars D.baseHom.structureRingMap
      (Stacks.SheafOfModules.isBilinearPairing_pushPairing Y₁.J D.j.toToposHom.pushforward
        (Stacks.SheafOfModules.isBilinearPairing_tensorSectionPairing hi₂.I F)))
    (D.idealMap hi₁ hi₂) (𝟙 _)

/-- **The comparison `θ_F : ℐ₁ ⊗ Ψ₀F ⟶ Ψ₀(ℐ₂ ⊗ F)`**, the morphism out of the tensor product
determined by `idealTensorPairing`. -/
noncomputable def idealTensorMap :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).obj
        (D.basePushforward.obj F) ⟶
      D.basePushforward.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).obj hi₂.I).obj F) :=
  Stacks.SheafOfModules.bilinearEquivTensorHom
    ⟨D.idealTensorPairing hi₁ hi₂ F, D.isBilinearPairing_idealTensorPairing hi₁ hi₂ F⟩

/-- **The comparison on a pure tensor**: `a ⊗ y ↦ j_*(λ(a) ⊗ y)`, with `λ(a)` the section of
`j_*ℐ₂` cut out by `a`. -/
theorem idealTensorMap_val_app_unit (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U)
    (y : (D.basePushforward.obj F).val.obj U) :
    (D.idealTensorMap hi₁ hi₂ F).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)).obj)).unit.app
            (PresheafOfModules.tensorObj hi₁.I.val (D.basePushforward.obj F).val)).app U
          (a ⊗ₜ[(baseRing i₁).obj.obj U] y)) =
      (D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y₁.J U).map
        (Stacks.SheafOfModules.tensorSectionPairing hi₂.I F)
        (Functor.prodObjMk (P := D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor Y₁.J U)
          (A := Sheaf.moduleSheaf _ hi₂.I) (B := Sheaf.moduleSheaf _ F)
          (D.idealSection hi₁ hi₂ U a) y) := by
  refine (congrArg (fun t => t.app U (a ⊗ₜ[(baseRing i₁).obj.obj U] y))
    ((Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom (A := hi₁.I)
      (B := D.basePushforward.obj F)).apply_symm_apply
        (Stacks.SheafOfModules.tensorHomOfPairing
          (D.isBilinearPairing_idealTensorPairing hi₁ hi₂ F)))).trans ?_
  refine (Stacks.SheafOfModules.pairingApp_prodMap_comp
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)) (A := hi₁.I)
    (B := D.basePushforward.obj F) (A' := D.basePushforward.obj hi₂.I)
    (B' := D.basePushforward.obj F)
    (N := D.basePushforward.obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).obj hi₂.I).obj F))
    (Stacks.SheafOfModules.pushPairing Y₁.J D.j.toToposHom.pushforward
      (Stacks.SheafOfModules.tensorSectionPairing hi₂.I F))
    (D.idealMap hi₁ hi₂) (𝟙 (D.basePushforward.obj F)) U a y).trans ?_
  refine (Stacks.SheafOfModules.pairingApp_pushPairing Y₁.J D.j.toToposHom.pushforward
    _ U _ _).trans ?_
  have ha : (Sheaf.sectionsFunctor Y₁.J U).map
      ((Sheaf.moduleSheafFunctor _).map (D.idealMap hi₁ hi₂)) a =
      D.idealSection hi₁ hi₂ U a := D.idealMap_val_app hi₁ hi₂ U a
  have hy : (Sheaf.sectionsFunctor Y₁.J U).map
      ((Sheaf.moduleSheafFunctor _).map (𝟙 (D.basePushforward.obj F))) y = y :=
    (congrArg (fun φ => (Sheaf.sectionsFunctor Y₁.J U).map φ y)
      ((Sheaf.moduleSheafFunctor _).map_id _)).trans
        ((Sheaf.sectionsFunctor Y₁.J U).map_id_apply _ y)
  rw [ha, hy]

end Tensor

/-! ### Pushing an extension forward along `j` -/

section Extension

variable [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  [HasSheafify Y₁.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}]
  (hj : FirstOrderThickening D.j)

omit [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}] in
include hj in
/-- `j_*` on modules over the thickened structure sheaf is exact: it is an equivalence followed
by restriction of scalars. -/
theorem pushforwardModules_exact :
    PreservesFiniteLimits D.j.pushforwardModules ∧
      PreservesFiniteColimits D.j.pushforwardModules := by
  have := isEquivalence_pushforwardModuleFunctor_of_firstOrderThickening hj
  have := (restrictScalars_exact D.j.structureRingMap).1
  have := (restrictScalars_exact D.j.structureRingMap).2
  exact ⟨inferInstanceAs (PreservesFiniteLimits (pushforwardModuleFunctor D.j.toToposHom _ ⋙
      SheafOfModules.restrictScalars D.j.structureRingMap)),
    inferInstanceAs (PreservesFiniteColimits (pushforwardModuleFunctor D.j.toToposHom _ ⋙
      SheafOfModules.restrictScalars D.j.structureRingMap))⟩

variable {F K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))}
  (E : Abelian.YonedaExtension ((structureRestrict i₂).obj F) ((structureRestrict i₂).obj K) 0)

omit [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] [HasSheafify Y₁.J AddCommGrpCat.{w}] in
/-- The two maps of the pushed extension compose to zero. -/
theorem pushedShortComplex_zero :
    ((D.restrictIso K).inv ≫ D.j.pushforwardModules.map E.f) ≫
      (D.j.pushforwardModules.map E.g ≫ (D.restrictIso F).hom) = 0 := by
  rw [Category.assoc, ← Category.assoc (D.j.pushforwardModules.map E.f), ← Functor.map_comp,
    yonedaExtension_comp_zero E, Functor.map_zero, zero_comp, comp_zero]

/-- **An extension over the second thickening, pushed forward along `j`**: an extension of
`Ψ₀F` by `Ψ₀K` over the first thickening, with middle term `j_*` of the given one. -/
noncomputable def pushedExtension :
    Abelian.YonedaExtension ((structureRestrict i₁).obj (D.basePushforward.obj F))
      ((structureRestrict i₁).obj (D.basePushforward.obj K)) 0 :=
  letI := (D.pushforwardModules_exact hj).1
  letI := (D.pushforwardModules_exact hj).2
  letI hSE : (ShortComplex.mk _ _ (D.pushedShortComplex_zero E)).ShortExact := by
    refine ShortComplex.shortExact_of_iso ?_
      ((yonedaExtension_shortExact E).map_of_exact D.j.pushforwardModules)
    refine ShortComplex.isoMk (D.restrictIso K) (Iso.refl _) (D.restrictIso F) ?_ ?_
    · exact (Iso.hom_inv_id_assoc (D.restrictIso K) (D.j.pushforwardModules.map E.f)).trans
        (Category.comp_id _).symm
    · exact Category.id_comp _
  Abelian.shortExactYonedaExtension hSE

omit [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- The first map of the pushed extension is the inverse of `restrictIso` followed by `j_*` of the
first map of `E`. -/
theorem pushedExtension_f : (D.pushedExtension hj E).f =
    (D.restrictIso K).inv ≫ D.j.pushforwardModules.map E.f := rfl

omit [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- The second map of the pushed extension is `j_*` of the second map of `E` followed by
`restrictIso`. -/
theorem pushedExtension_g : (D.pushedExtension hj E).g =
    D.j.pushforwardModules.map E.g ≫ (D.restrictIso F).hom := rfl

omit [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- On sections, the first map of the pushed extension is `j_*` of the first map of `E`. -/
theorem pushedExtension_f_val_app (U : Y₁.Cᵒᵖ)
    (y : ((structureRestrict i₁).obj (D.basePushforward.obj K)).val.obj U) :
    (D.pushedExtension hj E).f.val.app U y = (D.j.pushforwardModules.map E.f).val.app U y :=
  congrArg ((D.j.pushforwardModules.map E.f).val.app U) (D.restrictIso_inv_val_app K U y)

omit [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- On sections, the second map of the pushed extension is `j_*` of the second map of `E`. -/
theorem pushedExtension_g_val_app (U : Y₁.Cᵒᵖ) (x : (D.pushedExtension hj E).Z.left.val.obj U) :
    (D.pushedExtension hj E).g.val.app U x = (D.j.pushforwardModules.map E.g).val.app U x := rfl

omit hj in
/-- The action map of an extension over the second thickening, as an identity of morphisms of
sheaves of sets: `a · x` is the image in the middle term of `c(a ⊗ x̄)`. -/
theorem actionMap_sheafSets :
    (prod.map (𝟙 (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)
        ((structureRestrict i₂).obj hi₂.I)))
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)).map E.g) ≫
        Stacks.SheafOfModules.tensorSectionPairing hi₂.I F ≫
          (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))).map
            (extensionActionMap hi₂ E).1 ≫
            (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)).map E.f :
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)
          ((structureRestrict i₂).obj hi₂.I) ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) E.Z.left ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) E.Z.left) =
      prod.map hi₂.inclSheafSets
          (𝟙 (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) E.Z.left)) ≫
        Sheaf.moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) E.Z.left := by
  refine Sheaf.hom_ext_sections fun U z => ?_
  rw [← Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor.{w} Y₂.J U) z]
  refine (Functor.map_prodMap_comp_prodObjMk (Sheaf.sectionsFunctor.{w} Y₂.J U) _ _ _ _ _).trans ?_
  refine Eq.trans ?_
    (Functor.map_prodMap_comp_prodObjMk (Sheaf.sectionsFunctor.{w} Y₂.J U) _ _ _ _ _).symm
  refine Eq.trans ?_ (((extensionActionMap hi₂ E).2 U _ _).trans
    (Sheaf.sectionsFunctor_map_moduleSMulHom _ _ U _ _).symm)
  exact ((Sheaf.sectionsFunctor.{w} Y₂.J U).map_comp_apply _ _ _).trans
    (((Sheaf.sectionsFunctor.{w} Y₂.J U).map_comp_apply _ _ _).trans
      (congrArg (fun t => (E.f.val.app U) ((extensionActionMap hi₂ E).1.val.app U t))
        (Stacks.SheafOfModules.pairingApp_tensorSectionPairing hi₂.I F U _ _)))

omit [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- **A comparison of the kind a presentation carries, pushed forward along `j`.** If `cmp`
exhibits the restriction of an extension `D'` of `F` by `C` over the base as the pushout of `E`
along `proj`, then `j_*cmp` does so for `Ψ₀D'` and the pushed extension. -/
theorem pushedExtension_comparison
    {C : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))}
    (proj : K ⟶ C) (D' : Abelian.YonedaExtension F C 0)
    (cmp : E.Z.left ⟶ (structureRestrict i₂).obj D'.Z.left)
    (hcmp₁ : E.f ≫ cmp = (structureRestrict i₂).map proj ≫ (structureRestrict i₂).map D'.f)
    (hcmp₂ : cmp ≫ (structureRestrict i₂).map D'.g = E.g) :
    (D.pushedExtension hj E).f ≫ (D.j.pushforwardModules.map cmp ≫ (D.restrictIso D'.Z.left).hom) =
        (structureRestrict i₁).map (D.basePushforward.map proj) ≫
          (structureRestrict i₁).map (D.basePushforward.map D'.f) ∧
      (D.j.pushforwardModules.map cmp ≫ (D.restrictIso D'.Z.left).hom) ≫
          (structureRestrict i₁).map (D.basePushforward.map D'.g) =
        (D.pushedExtension hj E).g := by
  have h₁ : ((D.restrictIso K).inv ≫ D.j.pushforwardModules.map E.f) ≫
      (D.j.pushforwardModules.map cmp ≫ (D.restrictIso D'.Z.left).hom) =
        (structureRestrict i₁).map (D.basePushforward.map proj) ≫
          (structureRestrict i₁).map (D.basePushforward.map D'.f) := by
    rw [Category.assoc, ← Category.assoc (D.j.pushforwardModules.map E.f),
      ← Functor.map_comp, hcmp₁, Functor.map_comp]
    simp only [Category.assoc]
    rw [restrictIso_hom_naturality, ← Category.assoc (D.j.pushforwardModules.map _),
      restrictIso_hom_naturality]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h₂ : (D.j.pushforwardModules.map cmp ≫ (D.restrictIso D'.Z.left).hom) ≫
        (structureRestrict i₁).map (D.basePushforward.map D'.g) =
      D.j.pushforwardModules.map E.g ≫ (D.restrictIso F).hom := by
    rw [Category.assoc, ← restrictIso_hom_naturality, ← Category.assoc, ← Functor.map_comp, hcmp₂]
  exact ⟨h₁, h₂⟩

/-- **The action map of a pushed extension**: for an extension `E` of `F` by `K` over the second
thickening, the action map of `j_*E` over the first thickening is the comparison
`ℐ₁ ⊗ Ψ₀F ⟶ Ψ₀(ℐ₂ ⊗ F)` followed by `Ψ₀` of the action map of `E`. -/
theorem pushedExtension_actionMap :
    (extensionActionMap hi₁ (D.pushedExtension hj E)).1 =
      D.idealTensorMap hi₁ hi₂ F ≫ D.basePushforward.map (extensionActionMap hi₂ E).1 := by
  refine extensionActionMap_unique hi₁ (D.pushedExtension hj E) _ fun U a x => ?_
  let P := D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor.{w} Y₁.J U
  have hθ := D.idealTensorMap_val_app_unit hi₁ hi₂ F U a
    ((D.j.pushforwardModules.map E.g).val.app U x)
  have hS := congrArg (fun m => P.map m
    (Functor.prodObjMk (P := P) (A := Sheaf.moduleSheaf _ ((structureRestrict i₂).obj hi₂.I))
      (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) E.Z.left)
      (D.idealSection hi₁ hi₂ U a) x)) (actionMap_sheafSets hi₂ E)
  refine (D.pushedExtension_f_val_app hj E U _).trans ?_
  let G := fun t => P.map ((Sheaf.moduleSheafFunctor _).map E.f)
    (P.map ((Sheaf.moduleSheafFunctor _).map (extensionActionMap hi₂ E).1) t)
  refine (congrArg G hθ).trans ?_
  refine Eq.trans ?_ (hS.trans ?_)
  · refine Eq.trans ?_ (Functor.map_prodMap_comp_prodObjMk P _ _ _ _ _).symm
    refine Eq.trans ?_ ((P.map_comp_apply _ _ _).trans (P.map_comp_apply _ _ _)).symm
    exact congrArg (fun t => G (P.map (Stacks.SheafOfModules.tensorSectionPairing hi₂.I F)
      (Functor.prodObjMk (P := P) (A := Sheaf.moduleSheaf _ hi₂.I) (B := Sheaf.moduleSheaf _ F)
        t _))) (P.map_id_apply _ _).symm
  · refine (Functor.map_prodMap_comp_prodObjMk P _ _ _ _ _).trans ?_
    refine (congrArg₂ (fun t t' => P.map (Sheaf.moduleSMulHom _ E.Z.left)
      (Functor.prodObjMk (P := P) (A := Sheaf.ringSheaf _)
        (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) E.Z.left) t t'))
      (D.idealSection_spec hi₁ hi₂ U a) (P.map_id_apply _ _)).trans ?_
    exact (Stacks.SheafOfModules.smul_eq_map_moduleSMulHom (J := Y₁.J)
      (Φ := D.j.toToposHom.pushforward) U _ _).symm

end Extension

end ThickeningTargetMorphism

end Deformation.ToposThickening

end
