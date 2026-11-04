module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraAdjunctionEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The unit of the graded pullback-pushforward adjunction, at unrelated universes

The unit of the graded pullback-pushforward adjunction, for ringed topoi whose objects, morphisms
and sections of the structure sheaf live in three unrelated universes, such as a
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`; the site of the target is assumed
`CategoryTheory.EssentiallySmall.{w}`.

## Main definitions

* `pullbackScalarUnit` is the change-of-rings half of the unit, as a morphism of sheaves of
  sets: a local section `x` of an inverse image goes to the pure tensor `1 ⊗ x` in the
  extension of scalars.
* `unitApp` is the unit as a homomorphism of sheaves of graded algebras.

## Main results

* `moduleSheafFunctor_map_pullbackUnit`: the unit of the pullback adjunction for sheaves of
  modules is, on underlying sheaves of sets, the transpose of `pullbackScalarUnit` across the
  adjunction of the underlying topoi.
* `pullbackScalarUnit_mul`: the change-of-rings half of the unit preserves products of
  homogeneous local sections.
* `scalarExtension_submodule_eq_top`: a submodule of an extension of scalars containing every
  pure tensor `1 ⊗ x` is the whole thing.

## Implementation notes

Local sections of a sheaf of sets are identified with morphisms out of a sheafified
representable by `Stacks.Sites.SheafSection.sectionEquivSmall`, which allows the objects and the
morphisms of the site to live in different universes.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry TensorProduct Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraExtendScalars
open Stacks.Sheaves.GradedAlgebraInverseImage
open Stacks.Sheaves.GradedAlgebraPullback
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe w w' v u u₁ v' u'

variable {X Y : RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C]


/-- The transposed description of a local section of a sheaf of sets takes a pair of sections to
the morphism pairing their transposes. -/
public theorem sectionEquivSmall_prodObjMk
    {C : Type u₁} [Category.{v} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C)
    (U : Cᵒᵖ) (M N : Sheaf J (Type w))
    (x : (sectionsFunctor J U).obj M) (y : (sectionsFunctor J U).obj N) :
    sectionEquivSmall J U (M ⨯ N) (Functor.prodObjMk x y) =
      Limits.prod.lift (sectionEquivSmall J U M x) (sectionEquivSmall J U N y) :=
  Limits.prod.hom_ext
    (((sectionEquivSmall_comp J U (Limits.prod.fst : M ⨯ N ⟶ M)
          (Functor.prodObjMk x y)).symm.trans
        (congrArg (sectionEquivSmall J U M) (Functor.map_fst_prodObjMk x y))).trans
      (Limits.prod.lift_fst _ _).symm)
    (((sectionEquivSmall_comp J U (Limits.prod.snd : M ⨯ N ⟶ N)
          (Functor.prodObjMk x y)).symm.trans
        (congrArg (sectionEquivSmall J U N) (Functor.map_snd_prodObjMk x y))).trans
      (Limits.prod.lift_snd _ _).symm)

/-- A section of a composite of morphisms of sheaves of sets. -/
public theorem sheafHom_comp_app_apply
    {C : Type u₁} [Category.{v} C] (J : GrothendieckTopology C)
    {M N P : Sheaf J (Type w)} (g : M ⟶ N) (h : N ⟶ P) (V : Cᵒᵖ) (z : M.obj.obj V) :
    (g ≫ h).hom.app V z = h.hom.app V (g.hom.app V z) := rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
omit [X.J.HasSheafCompose (forget RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The multiplication of a sheaf of graded algebras, read as a morphism of sheaves of sets, is
multiplication of local sections. -/
public theorem sections_multiplicationSheafMap
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (i j : ℤ) (U : X.Cᵒᵖ)
    (x : (sectionsFunctor X.J U).obj (underlyingPiece A i))
    (y : (sectionsFunctor X.J U).obj (underlyingPiece A j)) :
    (sectionsFunctor X.J U).map (multiplicationSheafMap A i j) (Functor.prodObjMk x y) =
      (A.mul i j).app U x y :=
  congrArg₂ (fun a b => (A.mul i j).app U a b)
    (Functor.map_fst_prodObjMk x y) (Functor.map_snd_prodObjMk x y)

/-! ### The two constructions of the direct image agree on underlying sheaves of sets -/

section Comparison

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {S R : Sheaf K RingCat.{w'}} (α : S ⟶ R)

/-- The comparison between the inverse image of a restriction of scalars and the restriction of
scalars of an inverse image, whiskered by a further restriction of scalars, is the identity on
underlying sheaves of sets. -/
public theorem moduleSheafFunctor_map_pullbackRestrictScalarsIso_hom_app
    {T : Sheaf J RingCat.{w}} (β : T ⟶ pullbackRingSheaf J Φ S)
    (M : SheafOfModules.{w'} R) :
    (Sheaf.moduleSheafFunctor T).map
        ((CategoryTheory.Functor.isoWhiskerRight (pullbackRestrictScalarsIso Φ α)
          (SheafOfModules.restrictScalars β)).hom.app M) =
      CategoryTheory.CategoryStruct.id (Φ.obj (Sheaf.moduleSheaf R M)) := rfl

end Comparison

/-! ### The change-of-rings half of the unit -/

section ScalarUnit

variable (f : AlgebraicGeometry.RingedToposHom X Y)

/-- The extension-of-scalars half of the pullback adjunction for sheaves of modules: extension
of scalars along the inverse-image form of the structure map is left adjoint to restriction of
scalars along it. -/
public noncomputable abbrev scalarAdjunction :
    extendScalarsFSharp f.toRingedToposModulesHom ⊣
      SheafOfModules.restrictScalars (commRingSheafMap X.J
        (fSharpCommRing f.toRingedToposModulesHom)
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) :=
  extendRestrictScalarsAdjunction X.J (fSharpCommRing f.toRingedToposModulesHom)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property

/-- **The change-of-rings half of the unit of the pullback adjunction**, as a morphism of sheaves
of sets: the inverse image of a sheaf of modules maps to its extension of scalars, which is the
pullback, by `x ↦ 1 ⊗ x`. -/
public noncomputable def pullbackScalarUnit
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f.toToposHom.inverseImage.obj (Stacks.underlyingModuleSheaf Y.J M) ⟶
      Stacks.underlyingModuleSheaf X.J
        ((f.toRingedToposModulesHom.pullbackModules).obj M) :=
  (Sheaf.moduleSheafFunctor
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
    ((scalarAdjunction f).unit.app
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))

omit [EssentiallySmall.{w} Y.C] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The unit of the Stacks 03D3 adjunction for sheaves of modules has the unit of the underlying
adjunction of topoi as its underlying morphism of sheaves of sets. -/
public theorem moduleSheafFunctor_map_inverseImageUnit
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).unit.app M) =
      f.toToposHom.adj.unit.app (Stacks.underlyingModuleSheaf Y.J M) := by
  have hunit : (inverseImageAdjDirectImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).unit.app M =
      toposModulesHomEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)
        (𝟙 _) := rfl
  refine Eq.trans
    (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map hunit) ?_
  refine Eq.trans (moduleSheafFunctor_map_toposModulesHomEquiv f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (𝟙 _)) ?_
  refine Eq.trans (congrArg (f.toToposHom.adj.homEquiv _ _)
    ((Sheaf.moduleSheafFunctor
      (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_id _)) ?_
  exact f.toToposHom.adj.homEquiv_id _

omit [EssentiallySmall.{w} Y.C] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison between the two spellings of the direct image of sheaves of modules splits
into the whiskered comparison of inverse images and the transport along the equality of
functors. -/
public theorem pushforwardModulesIso_hom_app_eq
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    f.pushforwardModulesIso.hom.app N =
      (CategoryTheory.Functor.isoWhiskerRight
          (pullbackRestrictScalarsIso f.toToposHom.pushforward f.ringFsharpInverseImage)
          (SheafOfModules.restrictScalars
            (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom.app N ≫
        (eqToIso f.pushforwardModules_eq).hom.app N :=
  NatTrans.comp_app _ _ N

omit [EssentiallySmall.{w} Y.C] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The whiskered comparison of inverse images is the identity on underlying sheaves of sets. -/
public theorem moduleSheafFunctor_map_whiskered_comparison
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((CategoryTheory.Functor.isoWhiskerRight
            (pullbackRestrictScalarsIso f.toToposHom.pushforward f.ringFsharpInverseImage)
            (SheafOfModules.restrictScalars
              (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).hom.app N) =
      CategoryTheory.CategoryStruct.id
        (f.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :=
  moduleSheafFunctor_map_pullbackRestrictScalarsIso_hom_app f.toToposHom.pushforward
    f.ringFsharpInverseImage (ringUnit f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) N

omit [EssentiallySmall.{w} Y.C] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The transport along the equality of the two direct-image functors is the identity on
underlying sheaves of sets. -/
public theorem moduleSheafFunctor_map_eqToIso_pushforwardModules_eq
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((eqToIso f.pushforwardModules_eq).hom.app N) =
      CategoryTheory.CategoryStruct.id
        (f.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) := by
  rw [eqToIso.hom, CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map]
  exact eqToHom_refl _ _

omit [EssentiallySmall.{w} Y.C] in
omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The comparison between the two spellings of the direct image of sheaves of modules is the
identity on underlying sheaves of sets.** -/
public theorem moduleSheafFunctor_map_pushforwardModulesIso_hom_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.pushforwardModulesIso.hom.app N) =
      CategoryTheory.CategoryStruct.id
        (f.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :=
  (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (pushforwardModulesIso_hom_app_eq f N)).trans
    (((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _).trans
      ((congrArg₂ (fun p q => p ≫ q) (moduleSheafFunctor_map_whiskered_comparison f N)
          (moduleSheafFunctor_map_eqToIso_pushforwardModules_eq f N)).trans
        (Category.id_comp (CategoryTheory.CategoryStruct.id
          (f.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))))))

omit [EssentiallySmall.{w} Y.C] in
/-- The unit of the Stacks 03D7 adjunction of the modules development, as a morphism of sheaves
of sets, is the transpose of the change-of-rings half. -/
public theorem moduleSheafFunctor_map_modulesPullbackUnit
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposModulesHom).unit.app M) =
      f.toToposHom.adj.homEquiv _ _ (pullbackScalarUnit f M) := by
  refine Eq.trans
    (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
    (Adjunction.comp_unit_app
      (inverseImageAdjDirectImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (scalarAdjunction f) M)) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun k => k ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((scalarAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))))
    (moduleSheafFunctor_map_inverseImageUnit f M)) ?_
  refine Eq.trans (congrArg (fun k => f.toToposHom.adj.unit.app
      (Stacks.underlyingModuleSheaf Y.J M) ≫ k)
    (moduleSheafFunctor_map_directImageModules_map f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      ((scalarAdjunction f).unit.app
        ((inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)))) ?_
  exact (f.toToposHom.adj.homEquiv_unit _ _ _).symm

omit [EssentiallySmall.{w} Y.C] in
/-- **The unit of the pullback adjunction for sheaves of modules, as a morphism of sheaves of
sets, is the transpose of the change-of-rings half.** -/
public theorem moduleSheafFunctor_map_pullbackUnit
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.pullbackAdjPushforwardModulesViaComparison.unit.app M) =
      f.toToposHom.adj.homEquiv _ _ (pullbackScalarUnit f M) := by
  have hiso : f.pullbackAdjPushforwardModulesViaComparison.unit.app M =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposModulesHom).unit.app M ≫
        f.pushforwardModulesIso.hom.app _ := rfl
  refine Eq.trans
    (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map hiso) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun k =>
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toRingedToposModulesHom).unit.app M) ≫ k)
    (moduleSheafFunctor_map_pushforwardModulesIso_hom_app f _)) ?_
  refine Eq.trans (Category.comp_id _) ?_
  exact moduleSheafFunctor_map_modulesPullbackUnit f M

omit [EssentiallySmall.{w} Y.C] in
/-- **The change-of-rings half of the unit sends a local section `x` to the pure tensor
`1 ⊗ x`**, read in the sheafification that the extension of scalars is. -/
public theorem pullbackScalarUnit_app
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (V : X.Cᵒᵖ)
    (w : ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M).val.obj V) :
    letI := ((fSharpCommRing f.toRingedToposModulesHom).app V).hom.toAlgebra
    (pullbackScalarUnit f M).hom.app V w =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
          ((changeOfRings (fSharpCommRing f.toRingedToposModulesHom)).obj
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M).val)) V
        ((1 : X.O.obj.obj V) ⊗ₜ[(inverseImageStructureCommRing
          f.toRingedToposModulesHom).obj V] w) := by
  let := ((fSharpCommRing f.toRingedToposModulesHom).app V).hom.toAlgebra
  have hforget := congrArg (fun φ => PresheafOfModules.Hom.app φ V w)
    (forget_map_extendRestrictScalarsAdjunction_unit_app X.J
      (fSharpCommRing f.toRingedToposModulesHom)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))
  refine Eq.trans hforget ?_
  exact congrArg
    (fun t => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        ((changeOfRings (fSharpCommRing f.toRingedToposModulesHom)).obj
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M).val)) V t)
    (changeOfRingsAdjunction_unit_app_apply (fSharpCommRing f.toRingedToposModulesHom)
      ((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M).val V w)

omit [EssentiallySmall.{w} Y.C] in
/-- **The change-of-rings half of the unit preserves products of homogeneous local sections.** -/
public theorem pullbackScalarUnit_mul
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (i j : ℤ) (V : X.Cᵒᵖ)
    (u : ((inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece i).val.obj V)
    (v : ((inverseImageGradedAlgebra f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece j).val.obj V) :
    (pullbackScalarUnit f (B.piece (i + j))).hom.app V
        (((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app V
          u v) =
      ((toposPullbackGradedAlgebra f.toRingedToposModulesHom B).mul i j).app V
        ((pullbackScalarUnit f (B.piece i)).hom.app V u)
        ((pullbackScalarUnit f (B.piece j)).hom.app V v) := by
  let := ((fSharpCommRing f.toRingedToposModulesHom).app V).hom.toAlgebra
  have hmul := extendScalarsGradedAlgebra_mul_unit
    (fSharpCommRing f.toRingedToposModulesHom) X.J
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    (inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) i j V
    (1 : X.O.obj.obj V) (1 : X.O.obj.obj V) u v
  refine Eq.trans (pullbackScalarUnit_app f (B.piece (i + j)) V _) ?_
  refine Eq.trans ?_ hmul.symm
  refine Eq.trans ?_ (congrArg
    (fun r => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        ((changeOfRings (fSharpCommRing f.toRingedToposModulesHom)).obj
          ((inverseImageGradedAlgebra f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).piece (i + j)).val)) V
      (r ⊗ₜ[(inverseImageStructureCommRing f.toRingedToposModulesHom).obj V]
        (((inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app V
          u v)))
    (one_mul (1 : X.O.obj.obj V)).symm)
  rfl

/-- **A local section of the direct image of a pullback coming from the unit**, read through
the transposed description of local sections of a direct image: it is the inverse image of the
transposed section, followed by the change-of-rings half of the unit. -/
public theorem pushedSectionEquiv_unit
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (U : Y.Cᵒᵖ) (b : M.val.obj U) :
    pushedSectionEquiv f
        ((f.toRingedToposModulesHom.pullbackModules).obj M) U
        ((f.pullbackAdjPushforwardModulesViaComparison.unit.app M).val.app U b) =
      f.toToposHom.inverseImage.map
          (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J M) b) ≫
        pullbackScalarUnit f M := by
  refine Eq.trans (congrArg (f.toToposHom.adj.homEquiv _ _).symm
    (sectionEquivSmall_comp Y.J U
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.pullbackAdjPushforwardModulesViaComparison.unit.app M)) b)) ?_
  refine Eq.trans (f.toToposHom.adj.homEquiv_naturality_left_symm _ _) ?_
  exact congrArg
    (fun k => f.toToposHom.inverseImage.map
      (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J M) b) ≫ k)
    ((congrArg (f.toToposHom.adj.homEquiv _ _).symm
      (moduleSheafFunctor_map_pullbackUnit f M)).trans (Equiv.symm_apply_apply _ _))

/-! ### Local generation of an extension of scalars by pure tensors -/

/-- The restriction of scalars along the inverse-image form of the structure map: the right
adjoint of the change-of-rings half of the pullback of sheaves of modules. -/
public noncomputable abbrev scalarRestrict :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w}
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  SheafOfModules.restrictScalars (commRingSheafMap X.J
    (fSharpCommRing f.toRingedToposModulesHom)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
omit [EssentiallySmall.{w} Y.C] in
/-- **An extension of scalars is generated locally by the pure tensors `1 ⊗ x`**: a submodule of
it containing all of them is the whole thing. -/
public theorem scalarExtension_submodule_eq_top
    (M : SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (N : ((extendScalarsFSharp f.toRingedToposModulesHom).obj M).Submodule)
    (contains : ∀ (U : X.Cᵒᵖ) (x : M.val.obj U),
      ((scalarAdjunction f).unit.app M).val.app U x ∈ N.toSubmodule.obj U)
    (U : X.Cᵒᵖ)
    (x : ((extendScalarsFSharp f.toRingedToposModulesHom).obj M).val.obj U) :
    x ∈ N.toSubmodule.obj U := by
  let unitLift : M ⟶ (scalarRestrict f).obj N.toSheafOfModules :=
    ⟨{ app := fun V => ModuleCat.ofHom
         (X := M.val.obj V) (Y := ((scalarRestrict f).obj N.toSheafOfModules).val.obj V)
         { toFun := fun z => ⟨((scalarAdjunction f).unit.app M).val.app V z, contains V z⟩
           map_add' := fun z w =>
             Subtype.ext ((((scalarAdjunction f).unit.app M).val.app V).hom.map_add z w)
           map_smul' := fun r z =>
             Subtype.ext ((((scalarAdjunction f).unit.app M).val.app V).hom.map_smul r z) }
       naturality := fun {V _} g => ModuleCat.hom_ext (LinearMap.ext fun z =>
         Subtype.ext
           ((PresheafOfModules.naturality_apply
               ((scalarAdjunction f).unit.app M).val g z).trans
             (PresheafOfModules.Submodule.toPresheafOfModules_map_apply N.toSubmodule g
               ⟨((scalarAdjunction f).unit.app M).val.app V z, contains V z⟩).symm)) }⟩
  have hunit : unitLift ≫ (scalarRestrict f).map N.ι = (scalarAdjunction f).unit.app M :=
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
      ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))
  have lift_comp :
      ((scalarAdjunction f).homEquiv M N.toSheafOfModules).symm unitLift ≫ N.ι =
        CategoryTheory.CategoryStruct.id _ := by
    apply ((scalarAdjunction f).homEquiv M _).injective
    refine Eq.trans ((scalarAdjunction f).homEquiv_naturality_right _ _) ?_
    refine Eq.trans (congrArg (fun k => k ≫ (scalarRestrict f).map N.ι)
      (Equiv.apply_symm_apply ((scalarAdjunction f).homEquiv M N.toSheafOfModules) unitLift)) ?_
    exact Eq.trans hunit ((scalarAdjunction f).homEquiv_id _).symm
  have equation :
      ((((scalarAdjunction f).homEquiv M N.toSheafOfModules).symm unitLift).val.app U x).val =
        x :=
    congrArg (fun arrow => arrow.val.app U x) lift_comp
  exact Eq.mp (congrArg (fun t => t ∈ N.toSubmodule.obj U) equation)
    ((((scalarAdjunction f).homEquiv M N.toSheafOfModules).symm unitLift).val.app U x).property

end ScalarUnit



/-! ### The unit as a homomorphism of sheaves of graded algebras -/

section Unit

variable (f : AlgebraicGeometry.RingedToposHom X Y)

/-- The transposed description of a section obtained by applying a morphism out of a binary
product to a pair of sections. -/
public theorem sectionEquivSmall_map_prodObjMk
    {C : Type u₁} [Category.{v} C] [EssentiallySmall.{w} C] (J : GrothendieckTopology C) (U : Cᵒᵖ)
    {M N P : Sheaf J (Type w)} (m : M ⨯ N ⟶ P)
    (x : (sectionsFunctor J U).obj M) (y : (sectionsFunctor J U).obj N) :
    sectionEquivSmall J U P ((sectionsFunctor J U).map m (Functor.prodObjMk x y)) =
      Limits.prod.lift (sectionEquivSmall J U M x) (sectionEquivSmall J U N y) ≫ m :=
  (sectionEquivSmall_comp J U m (Functor.prodObjMk x y)).trans
    (congrArg (fun k => k ≫ m) (sectionEquivSmall_prodObjMk J U M N x y))

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
omit [Y.J.HasSheafCompose (forget RingCat.{w})] in
/-- The transposed description of a product of homogeneous local sections: it is the pairing of
the transposed sections followed by the multiplication read on the underlying sheaves of
sets. -/
public theorem sectionEquivSmall_mul
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (x : (B.piece i).val.obj U) (y : (B.piece j).val.obj U) :
    sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece (i + j)))
        ((B.mul i j).app U x y) =
      Limits.prod.lift
          (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece i)) x)
          (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece j)) y) ≫
        mulSheafHom B i j :=
  (congrArg (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece (i + j))))
      (sections_mulSheafHom B i j U x y).symm).trans
    (sectionEquivSmall_map_prodObjMk Y.J U (mulSheafHom B i j) x y)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse image of the transposed description of a product is the product of the inverse
images, read in the inverse image of the sheaf of graded algebras. -/
public theorem transportSections_sectionEquivSmall_mul
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (x : (B.piece i).val.obj U) (y : (B.piece j).val.obj U) (V : X.Cᵒᵖ)
    (s : (transportSections X.J f.toToposHom.inverseImage V).obj
      ((presheafToSheaf Y.J (Type w)).obj (smallYoneda.{w} U.unop))) :
    (transportSections X.J f.toToposHom.inverseImage V).map
        (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece (i + j)))
          ((B.mul i j).app U x y)) s =
      ((inverseImageGradedAlgebra f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app V
        ((transportSections X.J f.toToposHom.inverseImage V).map
          (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece i)) x) s)
        ((transportSections X.J f.toToposHom.inverseImage V).map
          (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece j)) y) s) := by
  refine Eq.trans (congrArg
    (fun k => (transportSections X.J f.toToposHom.inverseImage V).map k s)
    (sectionEquivSmall_mul B i j U x y)) ?_
  refine Eq.trans
    ((transportSections X.J f.toToposHom.inverseImage V).map_comp_apply _ _ s) ?_
  exact congrArg
    ((transportSections X.J f.toToposHom.inverseImage V).map (mulSheafHom B i j))
    (Functor.map_lift_apply _ _ s)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse image of the transposed description of a product, read on a single section. -/
public theorem inverseImageSection_mul
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (x : (B.piece i).val.obj U) (y : (B.piece j).val.obj U) (V : X.Cᵒᵖ)
    (s : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w)).obj (smallYoneda.{w} U.unop))).obj.obj V) :
    (f.toToposHom.inverseImage.map
        (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece (i + j)))
          ((B.mul i j).app U x y))).hom.app V s =
      ((inverseImageGradedAlgebra f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app V
        ((f.toToposHom.inverseImage.map
          (sectionEquivSmall Y.J U
            (Stacks.underlyingModuleSheaf Y.J (B.piece i)) x)).hom.app V s)
        ((f.toToposHom.inverseImage.map
          (sectionEquivSmall Y.J U
            (Stacks.underlyingModuleSheaf Y.J (B.piece j)) y)).hom.app V s) :=
  transportSections_sectionEquivSmall_mul f B i j U x y V s

/-- The transposed description of the unit on a product of homogeneous local sections is the
product of the transposed descriptions, read in the pullback. -/
public theorem transposedUnit_mul
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (x : (B.piece i).val.obj U) (y : (B.piece j).val.obj U) (V : X.Cᵒᵖ)
    (s : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w)).obj (smallYoneda.{w} U.unop))).obj.obj V) :
    (pullbackScalarUnit f (B.piece (i + j))).hom.app V
        ((f.toToposHom.inverseImage.map
          (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece (i + j)))
            ((B.mul i j).app U x y))).hom.app V s) =
      ((toposPullbackGradedAlgebra f.toRingedToposModulesHom B).mul i j).app V
        ((pullbackScalarUnit f (B.piece i)).hom.app V
          ((f.toToposHom.inverseImage.map
            (sectionEquivSmall Y.J U
              (Stacks.underlyingModuleSheaf Y.J (B.piece i)) x)).hom.app V s))
        ((pullbackScalarUnit f (B.piece j)).hom.app V
          ((f.toToposHom.inverseImage.map
            (sectionEquivSmall Y.J U
              (Stacks.underlyingModuleSheaf Y.J (B.piece j)) y)).hom.app V s)) :=
  (congrArg ((pullbackScalarUnit f (B.piece (i + j))).hom.app V)
      (inverseImageSection_mul f B i j U x y V s)).trans
    (pullbackScalarUnit_mul f B i j V _ _)

/-- **The unit of the Stacks 03D7 adjunction as a homomorphism of sheaves of graded algebras.**
Its degreewise components are the degreewise units. -/
public noncomputable def unitApp
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    B ⟶ (pushFunctor f).obj ((pullFunctor f).obj B) where
  app n := f.pullbackAdjPushforwardModulesViaComparison.unit.app (B.piece n)
  map_mul i j U x y := by
    apply (pushedSectionEquiv f
      ((toposPullbackGradedAlgebra f.toRingedToposModulesHom B).piece (i + j)) U).injective
    refine Eq.trans (pushedSectionEquiv_unit f (B.piece (i + j)) U
      ((B.mul i j).app U x y)) ?_
    refine Sheaf.hom_ext_sections fun V s => ?_
    refine Eq.trans (Sheaf.sectionsFunctor_map_apply _ s) ?_
    refine Eq.trans (sheafHom_comp_app_apply X.J
      (f.toToposHom.inverseImage.map
        (sectionEquivSmall Y.J U (Stacks.underlyingModuleSheaf Y.J (B.piece (i + j)))
          ((B.mul i j).app U x y)))
      (pullbackScalarUnit f (B.piece (i + j))) V s) ?_
    refine Eq.trans (transposedUnit_mul f B i j U x y V s) ?_
    refine Eq.trans ?_ (Sheaf.sectionsFunctor_map_apply
      (pushedSectionEquiv f
          ((toposPullbackGradedAlgebra f.toRingedToposModulesHom B).piece (i + j)) U
        (transposedMultiplicationAt f
          (toposPullbackGradedAlgebra f.toRingedToposModulesHom B) i j U
          ((f.pullbackAdjPushforwardModulesViaComparison.unit.app (B.piece i)).val.app U x)
          ((f.pullbackAdjPushforwardModulesViaComparison.unit.app (B.piece j)).val.app U y)))
        s).symm
    refine Eq.trans ?_ (transposedMultiplicationAt_apply f
      (toposPullbackGradedAlgebra f.toRingedToposModulesHom B) i j U
      ((f.pullbackAdjPushforwardModulesViaComparison.unit.app (B.piece i)).val.app U x)
      ((f.pullbackAdjPushforwardModulesViaComparison.unit.app (B.piece j)).val.app U y) V s).symm
    exact congrArg₂ (fun a b =>
        ((toposPullbackGradedAlgebra f.toRingedToposModulesHom B).mul i j).app V a b)
      ((congrArg (fun k => k.hom.app V s)
          (pushedSectionEquiv_unit f (B.piece i) U x)).trans
        (sheafHom_comp_app_apply X.J _ (pullbackScalarUnit f (B.piece i)) V s)).symm
      ((congrArg (fun k => k.hom.app V s)
          (pushedSectionEquiv_unit f (B.piece j) U y)).trans
        (sheafHom_comp_app_apply X.J _ (pullbackScalarUnit f (B.piece j)) V s)).symm

end Unit

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
