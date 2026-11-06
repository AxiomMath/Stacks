module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties
public import StacksFrontier.Homology.Injectives.Size.BoundedSizeObjects
public import StacksFrontier.Homology.Injectives.KInjective.Enlargement
public import StacksFrontier.Homology.Injectives.KInjective.Criterion
public import StacksFrontier.Homology.Injectives.KInjective.SmallAcyclicComplexes
import StacksCore.Tactic.StacksAttribute

/-!
# Functorial K-injective resolutions in Grothendieck abelian categories

Every cochain complex in a Grothendieck abelian category embeds termwise and
quasi-isomorphically into a complex of injective objects which is K-injective. These
resolutions may be chosen functorially.

## Main definitions

* `Stacks.Injectives.FunctorialKInjectiveResolution` packages a functorial K-injective
  resolution.
* `Stacks.Injectives.kInjectiveResolutionFunctor` is the chosen resolution functor.
* `Stacks.Injectives.kInjectiveResolutionInclusion` is its natural inclusion.

## Main results

* `Stacks.Injectives.exists_functorial_quasiIso_isKInjective` gives the functorial
  K-injective resolution.

The instances on `Stacks.Injectives.kInjectiveResolutionInclusion` expose its four
properties separately.

## Implementation notes

The source's existential functorial construction is exposed as a chosen
endofunctor and natural transformation. The instances
`kInjectiveResolutionInclusion_quasiIso`,
`kInjectiveResolutionInclusion_f_mono`,
`kInjectiveResolutionFunctor_obj_X_injective`, and
`kInjectiveResolutionFunctor_obj_isKInjective` respectively state the
quasi-isomorphism, termwise monomorphism, injective-term, and K-injectivity
parts of the source.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe w v u

namespace Stacks.Injectives

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A functorial K-injective resolution consists of an endofunctor on cochain
complexes and a natural inclusion into it, with the properties of Tag 079P. -/
structure FunctorialKInjectiveResolution where
  /-- The K-injective resolution endofunctor. -/
  functor : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The natural inclusion into the resolution. -/
  inclusion : Functor.id (CochainComplex C ℤ) ⟶ functor
  quasiIso (M : CochainComplex C ℤ) : QuasiIso (inclusion.app M)
  mono_f (M : CochainComplex C ℤ) (n : ℤ) : Mono ((inclusion.app M).f n)
  injective (M : CochainComplex C ℤ) (n : ℤ) : Injective ((functor.obj M).X n)
  isKInjective (M : CochainComplex C ℤ) : (functor.obj M).IsKInjective

/-- A functorial successor step can be iterated transfinitely in any category with
the required ordinal colimits. This packages the generic small-object iteration
used in the construction below. -/
noncomputable def iterateFunctorialStep
    {D : Type*} [Category D] [CategoryTheory.Limits.HasColimitsOfSize.{w, w} D]
    (F : D ⥤ D) (η : 𝟭 D ⟶ F) (κ : Cardinal.{w})
    [OrderBot κ.ord.ToType] : D ⥤ D :=
  (CategoryTheory.SmallObject.SuccStruct.ofNatTrans η).iteration κ.ord.ToType

/-- The canonical natural inclusion into the transfinite iterate. -/
noncomputable def iterateFunctorialStepInclusion
    {D : Type*} [Category D] [CategoryTheory.Limits.HasColimitsOfSize.{w, w} D]
    (F : D ⥤ D) (η : 𝟭 D ⟶ F) (κ : Cardinal.{w})
    [OrderBot κ.ord.ToType] : 𝟭 D ⟶ iterateFunctorialStep F η κ :=
  (CategoryTheory.SmallObject.SuccStruct.ofNatTrans η).ιIteration κ.ord.ToType

/-- The two natural inclusions from the published successor step combine into a
single endofunctorial inclusion. -/
def composeFunctorialInclusions
    {D : Type*} [Category D] (M N : D ⥤ D)
    (ηM : 𝟭 D ⟶ M) (ηN : 𝟭 D ⟶ N) : 𝟭 D ⟶ M ⋙ N :=
  ηM ≫ Functor.whiskerLeft M ηN

/-- The combined successor inclusion is componentwise monic whenever both
successor inclusions are componentwise monic. -/
theorem composeFunctorialInclusions_mono
    {D : Type*} [Category D] (M N : D ⥤ D)
    (ηM : 𝟭 D ⟶ M) (ηN : 𝟭 D ⟶ N)
    (hM : ∀ X, Mono (ηM.app X)) (hN : ∀ X, Mono (ηN.app X)) (X : D) :
    Mono ((composeFunctorialInclusions M N ηM ηN).app X) := by
  change Mono (ηM.app X ≫ ηN.app (M.obj X))
  exact mono_comp' (hM X) (hN (M.obj X))

/-- The combined successor inclusion is a quasi-isomorphism if the two
functorial inclusions are quasi-isomorphisms. -/
theorem composeFunctorialInclusions_quasiIso
    (M N : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (ηM : 𝟭 (CochainComplex C ℤ) ⟶ M)
    (ηN : 𝟭 (CochainComplex C ℤ) ⟶ N)
    (hM : ∀ X, QuasiIso (ηM.app X)) (hN : ∀ X, QuasiIso (ηN.app X))
    (X : CochainComplex C ℤ) :
    QuasiIso ((composeFunctorialInclusions M N ηM ηN).app X) := by
  change QuasiIso (ηM.app X ≫ ηN.app (M.obj X))
  let : QuasiIso (ηM.app X) := hM X
  let : QuasiIso (ηN.app (M.obj X)) := hN (M.obj X)
  infer_instance

/-- Iterate the successor operation (M mapsto N(M(-))) through an ordinal. -/
noncomputable def iterateCompositeFunctor
    {D : Type*} [Category D] [CategoryTheory.Limits.HasColimitsOfSize.{w, w} D]
    (M N : D ⥤ D) (ηM : 𝟭 D ⟶ M) (ηN : 𝟭 D ⟶ N)
    (κ : Cardinal.{w}) [OrderBot κ.ord.ToType] : D ⥤ D :=
  iterateFunctorialStep (M ⋙ N) (composeFunctorialInclusions M N ηM ηN) κ

/-- The natural map into the transfinite composite successor iteration. -/
noncomputable def iterateCompositeFunctorInclusion
    {D : Type*} [Category D] [CategoryTheory.Limits.HasColimitsOfSize.{w, w} D]
    (M N : D ⥤ D) (ηM : 𝟭 D ⟶ M) (ηN : 𝟭 D ⟶ N)
    (κ : Cardinal.{w}) [OrderBot κ.ord.ToType] :
    𝟭 D ⟶ iterateCompositeFunctor M N ηM ηN κ :=
  iterateFunctorialStepInclusion (M ⋙ N) (composeFunctorialInclusions M N ηM ηN) κ

/-- The morphisms of the successor structure of a natural transformation from the identity
satisfy a property after evaluation, provided every component of the transformation does. -/
private theorem ofNatTrans_prop_le_inverseImage {D : Type*} [Category D] {F : D ⥤ D}
    (η : 𝟭 D ⟶ F) (P : MorphismProperty D) (Y : D) (hη : ∀ Z, P (η.app Z)) :
    (CategoryTheory.SmallObject.SuccStruct.ofNatTrans η).prop ≤
      P.inverseImage ((CategoryTheory.evaluation D D).obj Y) := by
  change MorphismProperty.ofHoms (fun G : D ⥤ D => Functor.whiskerLeft G η) ≤ _
  rw [MorphismProperty.ofHoms_le_iff]
  exact fun G => hη (G.obj Y)

/-- A transfinite iterate of a functorial monomorphism is still monic at each
object. This is the colimit-stage bridge used by the resolution tower. -/
theorem iterateFunctorialStepInclusion_mono
    {D : Type*} [Category D] [Abelian D] [IsGrothendieckAbelian.{w} D]
    [CategoryTheory.Limits.HasColimitsOfSize.{w, w} D]
    (F : D ⥤ D) (η : 𝟭 D ⟶ F) (hη : ∀ X, Mono (η.app X))
    (κ : Cardinal.{w}) [OrderBot κ.ord.ToType] (X : D) :
    Mono ((iterateFunctorialStepInclusion F η κ).app X) := by
  let E := (CategoryTheory.evaluation D D).obj X
  let S := CategoryTheory.SmallObject.SuccStruct.ofNatTrans η
  have hstep : S.prop ≤ (MorphismProperty.monomorphisms D).inverseImage E :=
    ofNatTrans_prop_le_inverseImage η _ X hη
  have hcomp := (S.transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE hstep
  have hmono : MorphismProperty.monomorphisms D
      (E.map (S.ιIteration κ.ord.ToType)) := by
    exact MorphismProperty.transfiniteCompositionsOfShape_le _ _ _ hcomp.map.mem
  change Mono ((iterateFunctorialStepInclusion F η κ).app X)
  simpa [iterateFunctorialStepInclusion, iterateFunctorialStep, E, S,
    CategoryTheory.SmallObject.SuccStruct.ofNatTrans] using hmono

/-- Every transition map of the transfinite iteration of a functorial monomorphism is
again componentwise monic. -/
theorem iterateFunctorialStepMap_mono
    {D : Type*} [Category D] [Abelian D] [IsGrothendieckAbelian.{w} D]
    [CategoryTheory.Limits.HasColimitsOfSize.{w, w} D]
    (F : D ⥤ D) (η : 𝟭 D ⟶ F) (hη : ∀ X, Mono (η.app X))
    (κ : Cardinal.{w}) [OrderBot κ.ord.ToType]
    (i j : κ.ord.ToType) (f : i ⟶ j) (X : D) :
    Mono ((((CategoryTheory.SmallObject.SuccStruct.ofNatTrans η).iterationFunctor
      κ.ord.ToType).map f).app X) := by
  let E := (CategoryTheory.evaluation D D).obj X
  let S := CategoryTheory.SmallObject.SuccStruct.ofNatTrans η
  have hstep : S.prop ≤ (MorphismProperty.monomorphisms D).inverseImage E :=
    ofNatTrans_prop_le_inverseImage η _ X hη
  let hcomp := (S.transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE hstep
  let hcompD := hcomp.map
  have hmono := hcompD.mem_map f
  change Mono (E.map ((S.iterationFunctor κ.ord.ToType).map f)) at hmono
  simpa [E] using hmono

/-- A map out of an object with fewer than `κ` subobjects into the transfinite iterate
factors through one of the stages, by presentability in a Grothendieck abelian
category. -/
theorem factor_through_iterateFunctorialStep
    {D : Type*} [Category D] [Abelian D] [IsGrothendieckAbelian.{w} D]
    [CategoryTheory.Limits.HasColimitsOfSize.{w, w} D]
    (F : D ⥤ D) (η : 𝟭 D ⟶ F) (hη : ∀ X, Mono (η.app X))
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [IsCardinalFiltered κ.ord.ToType κ] (X Y : D)
    (hX : HasCardinalLT (Subobject X) κ)
    (f : X ⟶ (iterateFunctorialStep F η κ).obj Y) :
    ∃ (i : κ.ord.ToType) (g : X ⟶
      (((CategoryTheory.SmallObject.SuccStruct.ofNatTrans η).iterationFunctor
        κ.ord.ToType).obj i).obj Y),
      f = g ≫ (((CategoryTheory.SmallObject.SuccStruct.ofNatTrans η).iterationCocone
        κ.ord.ToType).ι.app i).app Y := by
  let S := CategoryTheory.SmallObject.SuccStruct.ofNatTrans η
  let E := (CategoryTheory.evaluation D D).obj Y
  let T := S.iterationFunctor κ.ord.ToType ⋙ E
  let c : Cocone T := E.mapCocone (S.iterationCocone κ.ord.ToType)
  have hc : IsColimit c := isColimitOfPreserves E (S.isColimitIterationCocone κ.ord.ToType)
  have hmono : ∀ (i j : κ.ord.ToType) (u : i ⟶ j), Mono (T.map u) := by
    intro i j u
    dsimp [T, E]
    exact iterateFunctorialStepMap_mono F η hη κ i j u Y
  have hF : ∀ (i j : κ.ord.ToType) (u : i ⟶ j), Mono (T.map u) := hmono
  let : ∀ (i j : κ.ord.ToType) (u : i ⟶ j), Mono (T.map u) := hF
  let : IsGrothendieckAbelian.{w} D := inferInstance
  have hfactor :=
    CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity hc hX f
  simpa [T, E, c, S, iterateFunctorialStep] using hfactor

/-- The factorization through a stage, specialized to the composite successor operation
on cochain complexes. -/
theorem factor_through_iterateCompositeFunctor
    [IsGrothendieckAbelian.{w} (CochainComplex C ℤ)]
    [CategoryTheory.Limits.HasColimitsOfSize.{w, w} (CochainComplex C ℤ)]
    (M N : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (ηM : 𝟭 (CochainComplex C ℤ) ⟶ M)
    (ηN : 𝟭 (CochainComplex C ℤ) ⟶ N)
    (hηM : ∀ X, Mono (ηM.app X)) (hηN : ∀ X, Mono (ηN.app X))
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [IsCardinalFiltered κ.ord.ToType κ]
    (X Y : CochainComplex C ℤ) (hX : HasCardinalLT (Subobject X) κ)
    (f : X ⟶ (iterateCompositeFunctor M N ηM ηN κ).obj Y) :
    ∃ (i : κ.ord.ToType) (g : X ⟶
      (((CategoryTheory.SmallObject.SuccStruct.ofNatTrans
        (composeFunctorialInclusions M N ηM ηN)).iterationFunctor
        κ.ord.ToType).obj i).obj Y),
      f = g ≫ (((CategoryTheory.SmallObject.SuccStruct.ofNatTrans
        (composeFunctorialInclusions M N ηM ηN)).iterationCocone
        κ.ord.ToType).ι.app i).app Y := by
  exact factor_through_iterateFunctorialStep
    (F := M ⋙ N) (η := composeFunctorialInclusions M N ηM ηN)
    (hη := fun Z => composeFunctorialInclusions_mono M N ηM ηN hηM hηN Z)
    (κ := κ) X Y hX f

/-- The inclusion into the transfinite iterate of the composite successor operation is
componentwise monic. -/
theorem iterateCompositeFunctorInclusion_mono
    {D : Type*} [Category D] [Abelian D] [IsGrothendieckAbelian.{w} D]
    [CategoryTheory.Limits.HasColimitsOfSize.{w, w} D]
    (M N : D ⥤ D) (ηM : 𝟭 D ⟶ M) (ηN : 𝟭 D ⟶ N)
    (hM : ∀ X, Mono (ηM.app X)) (hN : ∀ X, Mono (ηN.app X))
    (κ : Cardinal.{w}) [OrderBot κ.ord.ToType] (X : D) :
    Mono ((iterateCompositeFunctorInclusion M N ηM ηN κ).app X) := by
  apply iterateFunctorialStepInclusion_mono
  intro Y
  exact composeFunctorialInclusions_mono M N ηM ηN hM hN Y

/-- The inclusion of a complex into the cone on its identity is a monomorphism. -/
private theorem mappingConeInr_id_mono (K : CochainComplex C ℤ) :
    Mono (CochainComplex.mappingCone.inr (𝟙 K)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro j
  have hs : IsSplitMono ((CochainComplex.mappingCone.inr (𝟙 K)).f j) := IsSplitMono.mk' ⟨
    (CochainComplex.mappingCone.snd (𝟙 K)).v j j (add_zero j), by simp⟩
  infer_instance

variable [IsGrothendieckAbelian.{w} C]

/-- A diagram of cochain complexes, read as a cochain complex of diagrams: the complex in
`J ⥤ C` whose term in degree `n` is the evaluation of the diagram in degree `n`. -/
noncomputable def complexDiagram
    {J : Type*} [SmallCategory J]
    (A : J ⥤ HomologicalComplex C (ComplexShape.up ℤ)) :
    CochainComplex (J ⥤ C) ℤ where
  X n := A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n
  d n m := {
    app := fun j => (A.obj j).d n m
    naturality := by
      intro i j f
      dsimp
      rw [← HomologicalComplex.Hom.comm (A.map f) n m] }
  shape := by
    intro n m h
    ext j
    exact (A.obj j).shape n m h

/-- The functoriality of `complexDiagram` on morphisms of diagrams. -/
noncomputable def complexDiagramMap
    {J : Type*} [SmallCategory J]
    {A B : J ⥤ HomologicalComplex C (ComplexShape.up ℤ)} (α : A ⟶ B) :
    complexDiagram C A ⟶ complexDiagram C B where
  f n := {
    app := fun j => (α.app j).f n
    naturality := by
      intro i j f
      exact congrArg (fun g => (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map g)
        (α.naturality f) }
  comm' := by
    intro n m h
    ext j
    exact (α.app j).comm n m

/-- The cocone on a diagram of complexes whose vertex is the degreewise colimit, formed
by applying `colim` termwise to `complexDiagram`. -/
noncomputable abbrev complexDiagramCocone
    {J : Type*} [SmallCategory J] [HasColimitsOfShape J C]
    (A : J ⥤ HomologicalComplex C (ComplexShape.up ℤ)) : Cocone A where
  pt := ((colim (J := J) (C := C)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (complexDiagram C A)
  ι := {
    app := fun j => {
      f := fun n => colimit.ι (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) j
      comm' := by
        intro n m h
        let δ : (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) ⟶
            (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) m) :=
          { app := fun j => (A.obj j).d n m
            naturality := by
              intro i j f
              simp }
        change colimit.ι (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) j ≫
          (colim (J := J) (C := C)).map δ =
          (A.obj j).d n m ≫ colimit.ι (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) m) j
        simp [δ] }
    naturality := by
      intro i j f
      ext n
      simpa [Functor.comp_map, HomologicalComplex.eval_map, complexDiagram] using
        (colimit.w (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) f) }

/-- The degreewise colimit cocone is a colimit, since colimits of complexes are computed
degreewise. -/
noncomputable def complexDiagramCoconeColim
    {J : Type*} [SmallCategory J] [HasColimitsOfShape J C]
    (A : J ⥤ HomologicalComplex C (ComplexShape.up ℤ)) :
    IsColimit (complexDiagramCocone C A) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact colimit.isColimit (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n)

/-- The degreewise colimit agrees with the colimit of the diagram of complexes. -/
noncomputable def complexDiagramCoconeIso
    {J : Type*} [SmallCategory J] [HasColimitsOfShape J C]
    (A : J ⥤ HomologicalComplex C (ComplexShape.up ℤ)) :
    ((colim (J := J) (C := C)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexDiagram C A) ≅ colimit A :=
  IsColimit.coconePointUniqueUpToIso (complexDiagramCoconeColim C A) (colimit.isColimit A)

omit [IsGrothendieckAbelian.{w} C] in
/-- Filtered colimits in a Grothendieck abelian category preserve
quasi-isomorphisms of diagrams of complexes. -/
theorem quasiIso_colimMap
    {J : Type*} [SmallCategory J] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C]
    (A B : J ⥤ HomologicalComplex C (ComplexShape.up ℤ)) (α : A ⟶ B)
    (hα : ∀ j, QuasiIso (α.app j)) : QuasiIso (colim.map α) := by
  let G : (J ⥤ C) ⥤ C := colim
  let ψ := complexDiagramMap C α
  have hψ : QuasiIso ψ := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro j
    change QuasiIso (α.app j)
    exact hα j
  let : QuasiIso ψ := hψ
  have hmap : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) := by
    let : G.Additive := ⟨by
      intro X Y f g
      apply colimit.hom_ext
      intro j
      change colimit.ι X j ≫ colim.map (f + g) =
        colimit.ι X j ≫ (colim.map f + colim.map g)
      rw [colimit.ι_map, Preadditive.comp_add, colimit.ι_map, colimit.ι_map]
      simp⟩
    let : G.PreservesHomology := by infer_instance
    exact HomologicalComplex.quasiIso_map_of_preservesHomology ψ G
  let eA := complexDiagramCoconeIso C A
  let eB := complexDiagramCoconeIso C B
  have hcomm : eA.hom ≫ colim.map α =
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) ≫ eB.hom := by
    apply (complexDiagramCoconeColim C A).hom_ext
    intro j
    dsimp [complexDiagramCocone]
    have hlegA : (complexDiagramCocone C A).ι.app j ≫ eA.hom = colimit.ι A j := by
      simpa [eA, complexDiagramCoconeIso] using
        (complexDiagramCoconeColim C A).comp_coconePointUniqueUpToIso_hom
          (colimit.isColimit A) j
    have hlegB : (complexDiagramCocone C B).ι.app j ≫ eB.hom = colimit.ι B j := by
      simpa [eB, complexDiagramCoconeIso] using
        (complexDiagramCoconeColim C B).comp_coconePointUniqueUpToIso_hom
          (colimit.isColimit B) j
    have hnat : (complexDiagramCocone C A).ι.app j ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ =
        α.app j ≫ (complexDiagramCocone C B).ι.app j := by
      ext n
      let αn : (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) ⟶
          (B ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) :=
        { app := fun j => (α.app j).f n
          naturality := by
            intro i j f
            exact congrArg (fun φ => φ.f n) (α.naturality f) }
      change colimit.ι (A ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) j ≫
          colim.map αn = αn.app j ≫
          colimit.ι (B ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) j
      exact colimit.ι_map _ _
    calc
      (complexDiagramCocone C A).ι.app j ≫ eA.hom ≫ colim.map α =
          colimit.ι A j ≫ colim.map α := by
            calc
              (complexDiagramCocone C A).ι.app j ≫ (eA.hom ≫ colim.map α) =
                  ((complexDiagramCocone C A).ι.app j ≫ eA.hom) ≫ colim.map α :=
                    (Category.assoc _ _ _).symm
              _ = _ := congrArg (fun t => t ≫ colim.map α) hlegA
      _ = α.app j ≫ colimit.ι B j := colimit.ι_map _ _
      _ = (complexDiagramCocone C A).ι.app j ≫
            (G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫ eB.hom := by
            calc
              α.app j ≫ colimit.ι B j =
                  α.app j ≫ ((complexDiagramCocone C B).ι.app j ≫ eB.hom) :=
                congrArg (fun t => α.app j ≫ t) hlegB.symm
              _ = (α.app j ≫ (complexDiagramCocone C B).ι.app j) ≫ eB.hom :=
                (Category.assoc _ _ _).symm
              _ = ((complexDiagramCocone C A).ι.app j ≫
                  (G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) ≫ eB.hom :=
                congrArg (fun t => t ≫ eB.hom) hnat.symm
              _ = _ := Category.assoc _ _ _
  let he : Arrow.mk ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) ≅
      Arrow.mk (colim.map α) := Arrow.isoMk eA eB hcomm
  let : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) := hmap
  exact quasiIso_of_arrow_mk_iso _ _ he

omit [IsGrothendieckAbelian.{w} C] in
/-- A coproduct of quasi-isomorphisms is a quasi-isomorphism, when coproducts of the
given shape are exact. -/
theorem quasiIso_sigmaMap {J : Type*}
    (A B : J → CochainComplex C ℤ) (f : ∀ j, A j ⟶ B j)
    (hf : ∀ j, QuasiIso (f j))
    [HasColimitsOfShape (Discrete J) (CochainComplex C ℤ)]
    [HasColimitsOfShape (Discrete J) C]
    [HasExactColimitsOfShape (Discrete J) C] :
    QuasiIso (Limits.Sigma.map f) := by
  let A' : Discrete J ⥤ CochainComplex C ℤ := Discrete.functor A
  let B' : Discrete J ⥤ CochainComplex C ℤ := Discrete.functor B
  let α : A' ⟶ B' := Discrete.natTrans fun j => f j.as
  have hmap : QuasiIso (colim.map α) :=
    quasiIso_colimMap C A' B' α (fun j => hf j.as)
  have hEq : colim.map α = Limits.Sigma.map f := by
    rfl
  rw [← hEq]
  exact hmap

/-- Quasi-isomorphisms of cochain complexes are stable under filtered colimits; this is
the AB5 input to the limit stages of the resolution tower. -/
instance quasiIso_isStableUnderFilteredColimits :
    MorphismProperty.IsStableUnderFilteredColimits.{w, w}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) where
  isStableUnderColimitsOfShape J _ hJ := by
    constructor
    intro A B cA cB hcA hcB f hf φ hφ
    have hcolim : QuasiIso (colim.map f) := quasiIso_colimMap C A B f hf
    let eA := (colimit.isColimit A).coconePointUniqueUpToIso hcA
    let eB := (colimit.isColimit B).coconePointUniqueUpToIso hcB
    have hcomm : eA.hom ≫ φ = colim.map f ≫ eB.hom := by
      apply (colimit.isColimit A).hom_ext
      intro j
      have hlegA : colimit.ι A j ≫ eA.hom = cA.ι.app j :=
        IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit A) hcA j
      have hlegB : colimit.ι B j ≫ eB.hom = cB.ι.app j :=
        IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit B) hcB j
      calc
        colimit.ι A j ≫ (eA.hom ≫ φ) =
            (colimit.ι A j ≫ eA.hom) ≫ φ := (Category.assoc _ _ _).symm
        _ = cA.ι.app j ≫ φ := congrArg (fun t => t ≫ φ) hlegA
        _ = f.app j ≫ cB.ι.app j := hφ j
        _ = f.app j ≫ (colimit.ι B j ≫ eB.hom) :=
          congrArg (fun t => f.app j ≫ t) hlegB.symm
        _ = (f.app j ≫ colimit.ι B j) ≫ eB.hom := (Category.assoc _ _ _).symm
        _ = (colimit.ι A j ≫ colim.map f) ≫ eB.hom :=
          congrArg (fun t => t ≫ eB.hom) (colimit.ι_map f j).symm
        _ = colimit.ι A j ≫ (colim.map f ≫ eB.hom) := Category.assoc _ _ _
    let e : Arrow.mk (colim.map f) ≅ Arrow.mk φ := Arrow.isoMk eA eB hcomm
    let : QuasiIso (colim.map f) := hcolim
    exact quasiIso_of_arrow_mk_iso _ _ e

open MorphismProperty in
/-- The inclusion into the transfinite iterate of the composite successor operation is a
quasi-isomorphism, by stability of quasi-isomorphisms under transfinite composition. -/
theorem iterateCompositeFunctorInclusion_quasiIso
    [IsGrothendieckAbelian.{w} (CochainComplex C ℤ)]
    [CategoryTheory.Limits.HasColimitsOfSize.{w, w} (CochainComplex C ℤ)]
    (M N : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (ηM : 𝟭 (CochainComplex C ℤ) ⟶ M)
    (ηN : 𝟭 (CochainComplex C ℤ) ⟶ N)
    (hM : ∀ X, QuasiIso (ηM.app X)) (hN : ∀ X, QuasiIso (ηN.app X))
    (κ : Cardinal.{w}) [OrderBot κ.ord.ToType] (X : CochainComplex C ℤ) :
    QuasiIso ((iterateCompositeFunctorInclusion M N ηM ηN κ).app X) := by
  let D := CochainComplex C ℤ
  let η := composeFunctorialInclusions M N ηM ηN
  let S := CategoryTheory.SmallObject.SuccStruct.ofNatTrans η
  let Q := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let E := (CategoryTheory.evaluation D D).obj X
  have hstep : S.prop ≤ Q.inverseImage E :=
    ofNatTrans_prop_le_inverseImage η Q X
      (composeFunctorialInclusions_quasiIso C M N ηM ηN hM hN)
  let hcomp := (S.transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE hstep
  let : Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    apply IsStableUnderTransfiniteCompositionOfShape.of_isStableUnderColimitsOfShape
    intro J _ _ _ _
    let : Category.{w} J := inferInstance
    let : IsFiltered J := inferInstance
    let : HasColimitsOfShape J D := HasColimitsOfShape.of_small.{w, w} D J
    infer_instance
  have hfinal : Q (E.map (S.ιIteration κ.ord.ToType)) := by
    exact MorphismProperty.transfiniteCompositionsOfShape_le
      Q κ.ord.ToType _ hcomp.map.mem
  change QuasiIso ((iterateCompositeFunctorInclusion M N ηM ηN κ).app X)
  change QuasiIso ((S.ιIteration κ.ord.ToType).app X) at hfinal
  simpa [iterateCompositeFunctorInclusion, iterateFunctorialStepInclusion,
    iterateCompositeFunctor, iterateFunctorialStep, S, η,
    CategoryTheory.SmallObject.SuccStruct.ofNatTrans] using hfinal

/-- The functorial injective enlargement from Tag 079N, used as the second
successor operation in the K-injective construction. -/
private noncomputable def functorialInjectiveStep :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  (exists_functorialInjectiveResolution C).some.functor

/-- The natural map into the functorial injective enlargement. -/
private noncomputable def functorialInjectiveStepInclusion :
    𝟭 (CochainComplex C ℤ) ⟶ functorialInjectiveStep C :=
  (exists_functorialInjectiveResolution C).some.inclusion

private theorem functorialInjectiveStepInclusion_mono
    (M : CochainComplex C ℤ) (n : ℤ) :
    Mono (((functorialInjectiveStepInclusion C).app M).f n) :=
  (exists_functorialInjectiveResolution C).some.mono_f M n

private theorem functorialInjectiveStepInclusion_quasiIso
    (M : CochainComplex C ℤ) :
    QuasiIso ((functorialInjectiveStepInclusion C).app M) :=
  (exists_functorialInjectiveResolution C).some.quasiIso M

private theorem functorialInjectiveStepInclusion_mono_complex
    (M : CochainComplex C ℤ) : Mono ((functorialInjectiveStepInclusion C).app M) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact functorialInjectiveStepInclusion_mono C M n

/-- Cochain complexes over a Grothendieck abelian category are locally small. -/
instance complexLocallySmall : LocallySmall.{w} (CochainComplex C ℤ) := inferInstance

/-- A map from an object with fewer than `κ` subobjects into a `κ`-filtered
colimit of monomorphisms factors through one of the stages. This is the
presentability bridge used at limit stages of the resolution tower. -/
noncomputable def evalComplexSubobject (K : CochainComplex C ℤ) (n : ℤ)
    (S : Subobject K) : Subobject (K.X n) :=
  Subobject.mk ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map S.arrow)

/-- A subobject of a complex is determined by the subobjects induced in all
degrees. -/
theorem evalComplexSubobject_injective (K : CochainComplex C ℤ) :
    Function.Injective (fun S : Subobject K =>
      fun n => equivShrink.{w} (Subobject (K.X n)) (evalComplexSubobject C K n S)) := by
  intro S T h
  have hdeg (n : ℤ) : evalComplexSubobject C K n S = evalComplexSubobject C K n T :=
    (equivShrink.{w} (Subobject (K.X n))).injective (congrFun h n)
  have hdegEq (n : ℤ) : Subobject.mk (S.arrow.f n) = Subobject.mk (T.arrow.f n) := by
    simpa [evalComplexSubobject, HomologicalComplex.eval_map] using hdeg n
  let e (n : ℤ) : (S : CochainComplex C ℤ).X n ≅ (T : CochainComplex C ℤ).X n :=
    Subobject.isoOfMkEqMk (S.arrow.f n) (T.arrow.f n) (hdegEq n)
  have he (n : ℤ) : (e n).hom ≫ (T.arrow).f n = (S.arrow).f n := by
    dsimp [e]
    rw [Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp]
  have hcomm (n : ℤ) : (e n).hom ≫ (T : CochainComplex C ℤ).d n (n + 1) =
      (S : CochainComplex C ℤ).d n (n + 1) ≫ (e (n + 1)).hom := by
    apply (cancel_mono ((T.arrow).f (n + 1))).1
    calc
      ((e n).hom ≫ (T : CochainComplex C ℤ).d n (n + 1)) ≫ (T.arrow).f (n + 1) =
          (e n).hom ≫ ((T : CochainComplex C ℤ).d n (n + 1) ≫ (T.arrow).f (n + 1)) :=
            Category.assoc _ _ _
      _ = (e n).hom ≫ ((T.arrow).f n ≫ K.d n (n + 1)) := by
            rw [HomologicalComplex.Hom.comm (T.arrow) n (n + 1)]
      _ = (S.arrow).f n ≫ K.d n (n + 1) := by
            rw [← Category.assoc, he n]
      _ = (S : CochainComplex C ℤ).d n (n + 1) ≫ (S.arrow).f (n + 1) := by
            rw [HomologicalComplex.Hom.comm S.arrow n (n + 1)]
      _ = (S : CochainComplex C ℤ).d n (n + 1) ≫ (e (n + 1)).hom ≫
            (T.arrow).f (n + 1) :=
              congrArg (fun f => (S : CochainComplex C ℤ).d n (n + 1) ≫ f)
                (he (n + 1)).symm
      _ = ((S : CochainComplex C ℤ).d n (n + 1) ≫ (e (n + 1)).hom) ≫
            (T.arrow).f (n + 1) := by
              rw [Category.assoc]
  let isoST : (S : CochainComplex C ℤ) ≅ (T : CochainComplex C ℤ) := {
    hom :=
      { f := fun n => (e n).hom
        comm' := by
          intro i j hij
          simp only [ComplexShape.up_Rel] at hij
          subst j
          exact hcomm i }
    inv :=
      { f := fun n => (e n).inv
        comm' := by
          intro i j hij
          simp only [ComplexShape.up_Rel] at hij
          subst j
          have := congrArg (fun f => (e i).inv ≫ f ≫ (e (i + 1)).inv) (hcomm i).symm
          simpa [Category.assoc] using this }
    hom_inv_id := by ext n; simp
    inv_hom_id := by ext n; simp }
  exact Subobject.eq_of_comm isoST (by
    ext n
    exact he n)

/-- A degreewise bound on subobjects gives a bound on subcomplexes, since a
subcomplex is determined by its terms. -/
theorem complexSubobject_cardinality_le (K : CochainComplex C ℤ)
    (κ : Cardinal.{w})
    (hK : ∀ n : ℤ, Cardinal.mk (Shrink.{w} (Subobject (K.X n))) ≤ κ) :
    Cardinal.mk (Shrink.{w} (Subobject K)) ≤
      Cardinal.prod (fun _ : ℤ => κ) := by
  have hinj : Function.Injective (fun S : Shrink.{w} (Subobject K) =>
      fun n : ℤ => equivShrink.{w} (Subobject (K.X n))
        (evalComplexSubobject C K n ((equivShrink.{w} (Subobject K)).symm S))) := by
    intro S T h
    apply (equivShrink.{w} (Subobject K)).symm.injective
    apply evalComplexSubobject_injective C K
    funext n
    change equivShrink.{w} (Subobject (K.X n))
      (evalComplexSubobject C K n ((equivShrink.{w} (Subobject K)).symm S)) =
      equivShrink.{w} (Subobject (K.X n))
        (evalComplexSubobject C K n ((equivShrink.{w} (Subobject K)).symm T))
    exact congrFun h n
  calc
    Cardinal.mk (Shrink.{w} (Subobject K)) ≤
        Cardinal.mk (∀ n : ℤ, Shrink.{w} (Subobject (K.X n))) :=
      Cardinal.mk_le_of_injective hinj
    _ = Cardinal.prod (fun n : ℤ =>
        Cardinal.mk (Shrink.{w} (Subobject (K.X n)))) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod (fun _ : ℤ => κ) :=
      Cardinal.prod_le_prod _ _ hK

/-- Objects of the category of complexes with a fixed bound on their subobjects
have a set of representatives. -/
theorem exists_small_complex_representatives (lam : Cardinal.{w}) :
    ∃ (I : Type w) (R : I → CochainComplex C ℤ),
      (∀ i, Cardinal.lift.{w} (Cardinal.mk (Subobject (R i))) ≤
        Cardinal.lift.{max u v} lam) ∧
      ∀ (K : CochainComplex C ℤ),
        Cardinal.lift.{w} (Cardinal.mk (Subobject K)) ≤
          Cardinal.lift.{max u v} lam →
        ∃ i, Nonempty (R i ≅ K) := by
  let P : ObjectProperty (CochainComplex C ℤ) := fun K =>
    Cardinal.lift.{w} (Cardinal.mk (Subobject K)) ≤ Cardinal.lift.{max u v} lam
  let : IsGrothendieckAbelian.{w} (CochainComplex C ℤ) := inferInstance
  have hP : ObjectProperty.EssentiallySmall.{w} P :=
    essentiallySmall_subobject_cardinality_le lam
  obtain ⟨Q, hQ, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  let I : Type w := Shrink.{w} (Subtype Q)
  let R : I → CochainComplex C ℤ := fun i => ((equivShrink.{w} (Subtype Q)).symm i).1
  refine ⟨I, R, ?_, ?_⟩
  · intro i
    exact hQP _ ((equivShrink.{w} (Subtype Q)).symm i).2
  · intro K hK
    obtain ⟨q, hq, ⟨e⟩⟩ := hPQ K hK
    refine ⟨equivShrink.{w} (Subtype Q) ⟨q, hq⟩, ?_⟩
    simpa [R, I] using (show Nonempty (q ≅ K) from ⟨e.symm⟩)

/-- A set of bounded-above acyclic representatives suffices for all acyclic
complexes with the prescribed degreewise size bound. -/
theorem exists_small_boundedAbove_acyclic_representatives
    (κ : Cardinal.{w}) :
    ∃ (lam : Cardinal.{w}) (I : Type w) (K : I → CochainComplex C ℤ),
      (∀ i, (K i).Acyclic ∧
        Cardinal.lift.{w} (Cardinal.mk (Subobject (K i))) ≤
          Cardinal.lift.{max u v} lam) ∧
      ∀ (M : CochainComplex C ℤ), M.Acyclic →
        (∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (M.X n)) →
        (∀ n : ℤ, Cardinal.mk (Shrink.{w} (Subobject (M.X n))) ≤ κ) →
        ∃ i, Nonempty (K i ≅ M) := by
  let lam : Cardinal.{w} := Cardinal.prod (fun _ : ℤ => κ)
  obtain ⟨I₀, R, hR, hcover⟩ := exists_small_complex_representatives C lam
  let I := {i : I₀ // (R i).Acyclic}
  let K : I → CochainComplex C ℤ := fun i => R i.1
  refine ⟨lam, I, K, ?_, ?_⟩
  · intro i
    exact ⟨i.2, hR i.1⟩
  · intro M hM hMtop hMsize
    have hsub := complexSubobject_cardinality_le C M κ hMsize
    have hMcard : Cardinal.lift.{w} (Cardinal.mk (Subobject M)) ≤
        Cardinal.lift.{max u v} lam := by
      rw [← Cardinal.lift_mk_shrink.{max u v, w, 0} (Subobject M)]
      exact Cardinal.lift_le.2 hsub
    obtain ⟨i, ⟨e⟩⟩ := hcover M hMcard
    have hRi : (R i).Acyclic := by
      intro n
      exact (hM n).of_iso e.symm
    refine ⟨⟨i, hRi⟩, ?_⟩
    exact ⟨e⟩

/-- A type whose `Shrink` has cardinality below `κ` has fewer than `κ` elements. -/
private theorem hasCardinalLT_of_mk_shrink_lt {X : Type*} [Small.{w} X] (κ : Cardinal.{w})
    (h : Cardinal.mk (Shrink.{w} X) < κ) : HasCardinalLT X κ :=
  (hasCardinalLT_iff_of_equiv (equivShrink.{w} X) κ).2 ((hasCardinalLT_iff_cardinal_mk_lt _ _).2 h)

/-- An object whose set of subobjects has cardinality at most `lam < κ` has fewer than
`κ` subobjects, in the sense of `HasCardinalLT`. -/
theorem subobject_hasCardinalLT_of_bounded_cardinality
    (X : CochainComplex C ℤ) (κ lam : Cardinal.{w})
    (hX : Cardinal.lift.{w} (Cardinal.mk (Subobject X)) ≤
      Cardinal.lift.{max u v} lam) (hlam : lam < κ) :
    HasCardinalLT (Subobject X) κ := by
  have hShrink : Cardinal.mk (Shrink.{w} (Subobject X)) ≤ lam := by
    have h' : Cardinal.lift.{max u v} (Cardinal.mk (Shrink.{w} (Subobject X))) ≤
        Cardinal.lift.{max u v} lam := by
      rw [Cardinal.lift_mk_shrink.{max u v, w, 0} (Subobject X)]
      exact hX
    exact Cardinal.lift_le.1 h'
  exact hasCardinalLT_of_mk_shrink_lt κ (hShrink.trans_lt hlam)

omit [IsGrothendieckAbelian.{w} C] in
/-- A complex whose identity is null-homotopic is acyclic. -/
theorem acyclic_of_homotopy_id_zero (K : CochainComplex C ℤ)
    (h : Homotopy (𝟙 K) 0) : K.Acyclic := by
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K).1
  rw [HomotopyCategory.mem_subcategoryAcyclic_iff]
  intro n
  have hzero : IsZero ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) :=
    (HomotopyCategory.isZero_quotient_obj_iff K).2 ⟨h⟩
  exact (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map_isZero hzero

omit [IsGrothendieckAbelian.{w} C] in
/-- Any map between acyclic complexes is a quasi-isomorphism. -/
theorem quasiIso_of_acyclics {K L : CochainComplex C ℤ}
    (hK : K.Acyclic) (hL : L.Acyclic) (f : K ⟶ L) : QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact IsZero.isIso (hK n |>.isZero_homology) (hL n |>.isZero_homology)
    (HomologicalComplex.homologyMap f n)

omit [IsGrothendieckAbelian.{w} C] in
/-- A monomorphism with acyclic cokernel is a quasi-isomorphism. -/
theorem quasiIso_of_mono_of_acyclic_cokernel {K L : CochainComplex C ℤ}
    (f : K ⟶ L) [Mono f] (h : (cokernel f).Acyclic) : QuasiIso f :=
  quasiIso_of_shortExact_of_acyclic_X₃
    (S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
    { exact := ShortComplex.exact_cokernel f } h

omit [IsGrothendieckAbelian.{w} C] in
/-- The cokernel of a monomorphism which is a quasi-isomorphism is acyclic. -/
theorem acyclic_cokernel_of_mono_quasiIso {K L : CochainComplex C ℤ}
    (f : K ⟶ L) [Mono f] (hf : QuasiIso f) : (cokernel f).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let S : ShortComplex (CochainComplex C ℤ) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hfi (j : ℤ) : IsIso (HomologicalComplex.homologyMap f j) := by
    let : QuasiIso f := hf
    infer_instance
  have hπ : HomologicalComplex.homologyMap (cokernel.π f) n = 0 := by
    apply (hS.homology_exact₂ n).epi_f_iff.mp
    let : IsIso (HomologicalComplex.homologyMap f n) := hfi n
    infer_instance
  have hδ : hS.δ n (n + 1) (by simp) = 0 := by
    apply (hS.homology_exact₁ n (n + 1) (by simp)).mono_g_iff.mp
    let : IsIso (HomologicalComplex.homologyMap f (n + 1)) := hfi (n + 1)
    infer_instance
  have hz : IsZero ((cokernel f).homology n) := by
    exact (hS.homology_exact₃ n (n + 1) (by simp)).isZero_X₂ hπ hδ
  exact hz

/-- The cokernel of one leg of a pushout square agrees with the cokernel of the opposite
side: `cokernel (pushout.inl f g) ≅ cokernel g`. -/
noncomputable def cokernelPushoutInlIso {A X B : CochainComplex C ℤ}
    (f : A ⟶ X) (g : A ⟶ B) :
    cokernel (pushout.inl f g) ≅ cokernel g := by
  let p := pushout.inl f g
  let q := pushout.inr f g
  let ψ : pushout f g ⟶ cokernel g :=
    pushout.desc 0 (cokernel.π g) (by simp)
  have hψ : p ≫ ψ = 0 := by
    change pushout.inl f g ≫ pushout.desc 0 (cokernel.π g) _ = 0
    rw [pushout.inl_desc]
  let α : cokernel p ⟶ cokernel g := cokernel.desc p ψ hψ
  let β : cokernel g ⟶ cokernel p :=
    cokernel.desc g (q ≫ cokernel.π p) (by
      calc
        g ≫ q ≫ cokernel.π p = f ≫ p ≫ cokernel.π p := by
          simpa [p, q, Category.assoc] using
            congrArg (fun t => t ≫ cokernel.π p) pushout.condition.symm
        _ = 0 := by simp)
  have hqψ : q ≫ ψ = cokernel.π g := by
    change pushout.inr f g ≫ pushout.desc 0 (cokernel.π g) _ = _
    rw [pushout.inr_desc]
  have hπα : cokernel.π p ≫ α = ψ := by
    dsimp [α]
    exact cokernel.π_desc _ _ _
  have hπβ : cokernel.π g ≫ β = q ≫ cokernel.π p := by
    dsimp [β]
    exact cokernel.π_desc _ _ _
  have hψβ : ψ ≫ β = cokernel.π p := by
    apply pushout.hom_ext
    · calc
        p ≫ ψ ≫ β = (p ≫ ψ) ≫ β := (Category.assoc _ _ _).symm
        _ = 0 := by rw [hψ, zero_comp]
        _ = p ≫ cokernel.π p := by simp [cokernel.condition]
    · calc
        q ≫ ψ ≫ β = cokernel.π g ≫ β := (reassoc_of% hqψ) β
        _ = q ≫ cokernel.π p := hπβ
  refine ⟨α, β, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π p)).1
    calc
      cokernel.π p ≫ α ≫ β = ψ ≫ β := (reassoc_of% hπα) β
      _ = cokernel.π p := hψβ
      _ = cokernel.π p ≫ 𝟙 _ := by simp
  · apply (cancel_epi (cokernel.π g)).1
    calc
      cokernel.π g ≫ β ≫ α = q ≫ cokernel.π p ≫ α := (reassoc_of% hπβ) α
      _ = q ≫ ψ := congrArg (fun t => q ≫ t) hπα
      _ = cokernel.π g := hqψ
      _ = cokernel.π g ≫ 𝟙 _ := by simp

omit [IsGrothendieckAbelian.{w} C] in
/-- For an acyclic complex `K`, the inclusion of `K` into the cone on its identity is a
quasi-isomorphism, both complexes being acyclic. -/
theorem mappingConeInr_quasiIso_of_acyclic (K : CochainComplex C ℤ)
    (hK : K.Acyclic) :
    QuasiIso (CochainComplex.mappingCone.inr (𝟙 K)) :=
  quasiIso_of_acyclics C (K := K) (L := CochainComplex.mappingCone (𝟙 K)) hK
    (acyclic_of_homotopy_id_zero C _
      (CochainComplex.mappingCone.homotopyToZeroOfId K))
    (CochainComplex.mappingCone.inr (𝟙 K))

/-- A regular cardinal exceeding a given cardinal, the cardinality of a given index type,
and the size of a given object: the successor of their maximum with `ℵ₀`. -/
theorem exists_large_regular_cardinal (lam : Cardinal.{w}) (I : Type w)
    (U : C) :
    ∃ κ : Cardinal.{w}, κ.IsRegular ∧ lam < κ ∧ Cardinal.mk I < κ ∧
      Cardinal.mk (Shrink.{w} (Subobject U)) < κ := by
  let β := max Cardinal.aleph0 (max lam
    (max (Cardinal.mk I) (Cardinal.mk (Shrink.{w} (Subobject U)))))
  let κ := Order.succ β
  have hAleph : Cardinal.aleph0 ≤ β := le_max_left _ _
  have hLam : lam ≤ β :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hI : Cardinal.mk I ≤ β := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hU : Cardinal.mk (Shrink.{w} (Subobject U)) ≤ β := by
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨κ, Cardinal.isRegular_succ hAleph, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt hLam (Order.lt_succ β)
  · exact lt_of_le_of_lt hI (Order.lt_succ β)
  · exact lt_of_le_of_lt hU (Order.lt_succ β)

/-- The functor sending a complex `X` to the arrow `X ⟶ 0`, used to feed the small-object
construction, which operates on arrows. -/
noncomputable def complexToZeroArrow :
    CochainComplex C ℤ ⥤ Arrow (CochainComplex C ℤ) where
  obj X := Arrow.mk (0 : X ⟶ (0 : CochainComplex C ℤ))
  map f := Arrow.homMk f (𝟙 (0 : CochainComplex C ℤ)) (by simp)
  map_id X := by ext <;> simp
  map_comp f g := by ext <;> simp

/-- The first successor operation: the small-object construction applied to the cells
`K i ⟶ Cone(𝟙 (K i))`, which attaches to a complex enough cones to kill, up to homotopy,
every map out of the complexes `K i`. -/
noncomputable def killMapsObjectFunctor (I : Type w)
    (K : I → CochainComplex C ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ := by
  let cell (i : I) : K i ⟶ CochainComplex.mappingCone (𝟙 (K i)) :=
    CochainComplex.mappingCone.inr (𝟙 (K i))
  letI : ∀ {X S : CochainComplex C ℤ} (πX : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex cell πX))
        (CochainComplex C ℤ) := by
    intro X S πX
    apply HasColimitsOfShape.of_small
  exact complexToZeroArrow C ⋙ SmallObject.functor cell ⋙ Arrow.leftFunc

/-- The natural inclusion of a complex into the result of attaching the cells. -/
noncomputable def killMapsObjectInclusion (I : Type w)
    (K : I → CochainComplex C ℤ) :
    𝟭 (CochainComplex C ℤ) ⟶ killMapsObjectFunctor C I K := by
  let cell (i : I) : K i ⟶ CochainComplex.mappingCone (𝟙 (K i)) :=
    CochainComplex.mappingCone.inr (𝟙 (K i))
  letI : ∀ {X S : CochainComplex C ℤ} (πX : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex cell πX))
        (CochainComplex C ℤ) := by
    intro X S πX
    apply HasColimitsOfShape.of_small
  let G := SmallObject.functor cell
  let ε := SmallObject.ε cell
  refine
    { app := fun X => (ε.app ((complexToZeroArrow C).obj X)).left
      naturality := ?_ }
  intro X Y f
  have h := ε.naturality ((complexToZeroArrow C).map f)
  change f ≫ (ε.app ((complexToZeroArrow C).obj Y)).left =
    (ε.app ((complexToZeroArrow C).obj X)).left ≫
      (G.map ((complexToZeroArrow C).map f)).left
  have hleft := congrArg Arrow.Hom.left h
  change f ≫ (ε.app ((complexToZeroArrow C).obj Y)).left =
    (ε.app ((complexToZeroArrow C).obj X)).left ≫
      (G.map ((complexToZeroArrow C).map f)).left at hleft
  exact hleft

/-- Coproducts indexed by a `w`-small type are exact in a Grothendieck abelian category. -/
private theorem hasExactColimitsOfShape_discrete_of_small {D : Type*} [Category D] [Abelian D]
    [IsGrothendieckAbelian.{w} D] (α : Type*) [Small.{w} α] [HasColimitsOfShape (Discrete α) D] :
    HasExactColimitsOfShape (Discrete α) D := by
  have : HasExactColimitsOfShape (Discrete (Shrink.{w} α)) D := AB4OfSize.ofShape (C := D) _
  exact HasExactColimitsOfShape.of_domain_equivalence (C := D)
    (Discrete.equivalence (equivShrink.{w} α)).symm

/-- The inclusion into the cell attachment is a monomorphism in every degree. -/
lemma killMapsObjectInclusion_mono (I : Type w)
    (K : I → CochainComplex C ℤ) (X : CochainComplex C ℤ) (n : ℤ) :
    Mono (((killMapsObjectInclusion C I K).app X).f n) := by
  let cell (i : I) : K i ⟶ CochainComplex.mappingCone (𝟙 (K i)) :=
    CochainComplex.mappingCone.inr (𝟙 (K i))
  let : ∀ {A S : CochainComplex C ℤ} (πA : A ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex cell πA))
        (CochainComplex C ℤ) := by
    intro A S πA
    apply HasColimitsOfShape.of_small
  have hcell (i : I) : Mono (cell i) := mappingConeInr_id_mono C (K i)
  let (i : I) : Mono (cell i) := hcell i
  let : IsGrothendieckAbelian.{w} (CochainComplex C ℤ) := by infer_instance
  have hleft : Mono (SmallObject.functorObjLeft cell
      (0 : X ⟶ (0 : CochainComplex C ℤ))) := by
    let : ∀ j : SmallObject.FunctorObjIndex cell
        (0 : X ⟶ (0 : CochainComplex C ℤ)),
        Mono (cell j.i) := fun j => hcell j.i
    let idx := SmallObject.FunctorObjIndex cell
      (0 : X ⟶ (0 : CochainComplex C ℤ))
    let : HasColimitsOfShape (Discrete idx) (CochainComplex C ℤ) := by
      apply HasColimitsOfShape.of_small
    let := hasExactColimitsOfShape_discrete_of_small.{w} (D := CochainComplex C ℤ) idx
    infer_instance
  let : Mono (SmallObject.functorObjLeft cell
      (0 : X ⟶ (0 : CochainComplex C ℤ))) := hleft
  have hι : Mono (SmallObject.ιFunctorObj cell
      (0 : X ⟶ (0 : CochainComplex C ℤ))) := by
    dsimp [SmallObject.ιFunctorObj]
    exact Abelian.mono_pushout_of_mono_g _ _
  have hη : Mono ((killMapsObjectInclusion C I K).app X) := by
    change Mono (SmallObject.ιFunctorObj cell
      (0 : X ⟶ (0 : CochainComplex C ℤ)))
    exact hι
  have hEval : Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
      ((killMapsObjectInclusion C I K).app X)) :=
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_mono _
  exact hEval

/-- The inclusion into the cell attachment is a monomorphism of complexes. -/
lemma killMapsObjectInclusion_mono_complex (I : Type w)
    (K : I → CochainComplex C ℤ) (X : CochainComplex C ℤ) :
    Mono ((killMapsObjectInclusion C I K).app X) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact killMapsObjectInclusion_mono C I K X n

private theorem iterateCompositeFunctor_term_injective
    [IsGrothendieckAbelian.{w} (CochainComplex C ℤ)]
    [CategoryTheory.Limits.HasColimitsOfSize.{w, w} (CochainComplex C ℤ)]
    (M : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (ηM : 𝟭 (CochainComplex C ℤ) ⟶ M)
    (hM : ∀ X, Mono (ηM.app X))
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [NoMaxOrder κ.ord.ToType] [IsCardinalFiltered κ.ord.ToType κ]
    (G : C) (hG : IsSeparator G)
    (hGcard : Cardinal.mk (Shrink.{w} (Subobject G)) < κ)
    (Base : CochainComplex C ℤ) (n : ℤ) :
    Injective (((iterateCompositeFunctor M (functorialInjectiveStep C) ηM
      (functorialInjectiveStepInclusion C) κ).obj Base).X n) := by
  let D := CochainComplex C ℤ
  let NR := (exists_functorialInjectiveResolution C).some
  let N := NR.functor
  let ηN := NR.inclusion
  let η := composeFunctorialInclusions M N ηM ηN
  let S := CategoryTheory.SmallObject.SuccStruct.ofNatTrans η
  let T := S.iterationFunctor κ.ord.ToType
  let E := (CategoryTheory.evaluation D D).obj Base ⋙
    HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let F := T ⋙ E
  let c : Cocone F := E.mapCocone (S.iterationCocone κ.ord.ToType)
  have hc : IsColimit c :=
    isColimitOfPreserves E (S.isColimitIterationCocone κ.ord.ToType)
  have htransition : ∀ (i j : κ.ord.ToType) (f : i ⟶ j), Mono (F.map f) := by
    intro i j f
    dsimp [F, E, T]
    have hmono : Mono (((S.iterationFunctor κ.ord.ToType).map f).app Base) :=
      iterateFunctorialStepMap_mono (M ⋙ N) η
        (fun Z => composeFunctorialInclusions_mono M N ηM ηN hM
          (fun Z => functorialInjectiveStepInclusion_mono_complex C Z) Z)
        κ i j f Base
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
      (((S.iterationFunctor κ.ord.ToType).map f).app Base))
    exact (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_mono _
  let : ∀ (i j : κ.ord.ToType) (f : i ⟶ j), Mono (F.map f) := htransition
  have hGsmall : HasCardinalLT (Subobject G) κ := hasCardinalLT_of_mk_shrink_lt κ hGcard
  have hgen : (IsGrothendieckAbelian.generatingMonomorphisms G).rlp
      (0 : (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n) ⟶ 0) := by
    change ∀ ⦃A B : C⦄ (i : A ⟶ B),
      IsGrothendieckAbelian.generatingMonomorphisms G i →
        HasLiftingProperty i (0 : (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n) ⟶ 0)
    intro A B i hi
    change MorphismProperty.ofHoms (fun S : Subobject G => S.arrow) i at hi
    rcases hi with ⟨ASub⟩
    have hSsmall : HasCardinalLT (Subobject (ASub : C)) κ := by
      apply hGsmall.of_injective
      exact Subobject.map_obj_injective ASub.arrow
    have hstage : ∀ (f : (ASub : C) ⟶ (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n)),
        ∃ (j : κ.ord.ToType) (g : (ASub : C) ⟶ ((T.obj j).obj Base).X n),
          f = g ≫ c.ι.app j := by
      intro f
      exact CategoryTheory.IsGrothendieckAbelian.IsPresentable.surjectivity
        hc hSsmall f
    have hSextend : ∀ (f : (ASub : C) ⟶ (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n)),
        ∃ (g : G ⟶ (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n)),
          ASub.arrow ≫ g = f := by
      intro f
      obtain ⟨j, g, rfl⟩ := hstage f
      let Z := (T.obj j).obj Base
      obtain ⟨I, hI, toI, into, hinto, hfactor⟩ :=
        NR.factors_through_injective_subobject (M.obj Z) n
      change toI ≫ into = (ηN.app (M.obj Z)).f n at hfactor
      let : Injective I := hI
      let u := homOfLE (Order.le_succ j : j ≤ Order.succ j)
      have hj : ¬ IsMax j := by
        obtain ⟨k, hk⟩ := exists_gt j
        exact not_isMax_of_lt hk
      let e := S.iterationFunctorObjSuccIso j hj
      let α := Functor.associator (T.obj j) M N
      let leg := (α.hom.app Base).f n ≫ (e.inv.app Base).f n ≫
        c.ι.app (Order.succ j)
      let a := Injective.factorThru (g ≫ (ηM.app Z).f n ≫ toI) ASub.arrow
      refine ⟨a ≫ into ≫ leg, ?_⟩
      have ha : ASub.arrow ≫ a = g ≫ (ηM.app Z).f n ≫ toI := by
        simp [a]
      have hmap : ((T.map u).app Base).f n =
          (η.app Z).f n ≫ (e.inv.app Base).f n := by
        have hh := congrArg (fun q => (q.app Base).f n)
          (S.iterationFunctor_map_succ j hj)
        change ((T.map u).app Base).f n =
          (((T.obj j).whiskerLeft η).app Base).f n ≫
            (e.inv.app Base).f n at hh
        simpa only [Functor.whiskerLeft_app, Z] using hh
      have hcocone : ((T.map u).app Base).f n ≫ c.ι.app (Order.succ j) = c.ι.app j := by
        simpa [F, E, T, u] using (c.w u)
      calc
        ASub.arrow ≫ (a ≫ into ≫ leg) =
            (g ≫ (ηM.app Z).f n ≫ toI) ≫ into ≫ leg := by
              simpa only [Category.assoc] using
                congrArg (fun t => t ≫ into ≫ leg) ha
        _ = g ≫ (η.app Z).f n ≫ (e.inv.app Base).f n ≫ c.ι.app (Order.succ j) := by
              calc
                _ = g ≫ (ηM.app Z).f n ≫ (toI ≫ into) ≫
                    (α.hom.app Base).f n ≫ (e.inv.app Base).f n ≫
                    c.ι.app (Order.succ j) := by
                      simp only [leg, Category.assoc]
                _ = g ≫ (ηM.app Z).f n ≫ (ηN.app (M.obj Z)).f n ≫
                    (α.hom.app Base).f n ≫ (e.inv.app Base).f n ≫
                    c.ι.app (Order.succ j) := by
                      rw [hfactor]
                _ = g ≫ (η.app Z).f n ≫ (e.inv.app Base).f n ≫
                    c.ι.app (Order.succ j) := by
                      have hη : (ηM.app Z).f n ≫ (ηN.app (M.obj Z)).f n ≫
                          (α.hom.app Base).f n = (η.app Z).f n := by
                        dsimp [η, ηN, N, Z, composeFunctorialInclusions, α,
                          Functor.associator]
                        simpa only [Category.assoc] using Category.comp_id
                          ((ηM.app ((T.obj j).obj Base)).f n ≫
                            (NR.inclusion.app (M.obj ((T.obj j).obj Base))).f n)
                      calc
                        _ = g ≫ ((ηM.app Z).f n ≫ (ηN.app (M.obj Z)).f n ≫
                            (α.hom.app Base).f n) ≫ (e.inv.app Base).f n ≫
                            c.ι.app (Order.succ j) := by simp only [Category.assoc]
                        _ = _ := by rw [hη]
        _ = g ≫ ((T.map u).app Base).f n ≫ c.ι.app (Order.succ j) := by
              calc
                _ = g ≫ ((η.app Z).f n ≫ (e.inv.app Base).f n) ≫
                    c.ι.app (Order.succ j) := by
                      exact congrArg (fun t => g ≫ t)
                        (Category.assoc ((η.app Z).f n) ((e.inv.app Base).f n)
                          (c.ι.app (Order.succ j))).symm
                _ = _ := congrArg (fun t => g ≫ t ≫ c.ι.app (Order.succ j)) hmap.symm
        _ = g ≫ c.ι.app j := by rw [hcocone]
    have hlp : HasLiftingProperty ASub.arrow
        (0 : (((iterateCompositeFunctor M N ηM ηN κ).obj Base).X n) ⟶ 0) := by
      constructor
      intro f g sq
      obtain ⟨l, hl⟩ := hSextend f
      refine CommSq.HasLift.mk' ⟨l, hl, ?_⟩
      exact (isZero_zero C).eq_of_tgt _ _
    exact hlp
  apply (injective_iff_rlp_monomorphisms_zero _).2
  rw [← IsGrothendieckAbelian.generatingMonomorphisms_rlp hG]
  exact hgen

/-- Every map out of one of the complexes `K i` becomes null-homotopic after composing
with the inclusion into the cell attachment: this is what the cells are for. -/
lemma killMapsObjectInclusion_kills_map (I : Type w)
    (K : I → CochainComplex C ℤ) (X : CochainComplex C ℤ)
    (i : I) (f : K i ⟶ X) :
    homotopic C (ComplexShape.up ℤ)
      (f ≫ (killMapsObjectInclusion C I K).app X) 0 := by
  let cell (j : I) : K j ⟶ CochainComplex.mappingCone (𝟙 (K j)) :=
    CochainComplex.mappingCone.inr (𝟙 (K j))
  let : ∀ {X S : CochainComplex C ℤ} (πX : X ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex cell πX))
        (CochainComplex C ℤ) := by
    intro X S πX
    apply HasColimitsOfShape.of_small
  let G := SmallObject.functor cell
  obtain ⟨l, hl, _⟩ := SmallObject.ιFunctorObj_extension cell
    (πX := (0 : X ⟶ (0 : CochainComplex C ℤ))) (t := f)
    (b := (0 : CochainComplex.mappingCone (𝟙 (K i)) ⟶ 0)) ⟨by simp⟩
  have hcone : Homotopy (cell i ≫ l) 0 := by
    simpa [cell] using
      (((CochainComplex.mappingCone.homotopyToZeroOfId (K i)).compLeft (cell i)).compRight l)
  have hfac : cell i ≫ l = f ≫ (killMapsObjectInclusion C I K).app X := by
    change cell i ≫ l = f ≫ SmallObject.ιFunctorObj cell
      (0 : X ⟶ (0 : CochainComplex C ℤ))
    exact hl
  exact ⟨(Homotopy.ofEq hfac.symm).trans hcone⟩

/-- When all the `K i` are acyclic, the inclusion into the cell attachment is a
quasi-isomorphism: the cells are attached along quasi-isomorphisms, and a coproduct of
those is a quasi-isomorphism with acyclic cokernel, which the pushout inherits. -/
theorem killMapsObjectInclusion_quasiIso (I : Type w)
    (K : I → CochainComplex C ℤ) (hK : ∀ i, (K i).Acyclic)
    (X : CochainComplex C ℤ) :
    QuasiIso ((killMapsObjectInclusion C I K).app X) := by
  let cell (i : I) : K i ⟶ CochainComplex.mappingCone (𝟙 (K i)) :=
    CochainComplex.mappingCone.inr (𝟙 (K i))
  let : ∀ {A S : CochainComplex C ℤ} (πA : A ⟶ S),
      HasColimitsOfShape (Discrete (SmallObject.FunctorObjIndex cell πA))
        (CochainComplex C ℤ) := by
    intro A S πA
    apply HasColimitsOfShape.of_small
  let πX : X ⟶ (0 : CochainComplex C ℤ) := 0
  let idx := SmallObject.FunctorObjIndex cell πX
  let : HasColimitsOfShape (Discrete idx) (CochainComplex C ℤ) := by
    apply HasColimitsOfShape.of_small
  let : HasColimitsOfShape (Discrete idx) C := by
    apply HasColimitsOfShape.of_small
  let := hasExactColimitsOfShape_discrete_of_small.{w} (D := C) idx
  let src : idx → CochainComplex C ℤ := fun j => K j.i
  let tgt : idx → CochainComplex C ℤ := fun j =>
    CochainComplex.mappingCone (𝟙 (K j.i))
  have hcell (j : idx) : QuasiIso (cell j.i) :=
    mappingConeInr_quasiIso_of_acyclic C (K j.i) (hK j.i)
  have hcop : QuasiIso (SmallObject.functorObjLeft cell πX) := by
    change QuasiIso (Limits.Sigma.map (fun j : idx => cell j.i))
    exact quasiIso_sigmaMap C src tgt (fun j => cell j.i) hcell
  have hcellmono (i : I) : Mono (cell i) := mappingConeInr_id_mono C (K i)
  let := hasExactColimitsOfShape_discrete_of_small.{w} (D := CochainComplex C ℤ) idx
  let D := CochainComplex C ℤ
  let A' : Discrete idx ⥤ D := Discrete.functor src
  let B' : Discrete idx ⥤ D := Discrete.functor tgt
  let α : A' ⟶ B' := Discrete.natTrans fun j => cell j.as.i
  have hα : Mono α := (NatTrans.mono_iff_mono_app α).2
    (fun j => hcellmono j.as.i)
  let G : (Discrete idx ⥤ D) ⥤ D := colim
  have hmapMono : Mono (G.map α) := by
    let : G.PreservesMonomorphisms := by infer_instance
    exact G.map_mono α
  have hcolimEq : G.map α = Limits.Sigma.map (fun j : idx => cell j.i) := by
    rfl
  have hcopmono : Mono (SmallObject.functorObjLeft cell πX) := by
    change Mono (Limits.Sigma.map (fun j : idx => cell j.i))
    rw [← hcolimEq]
    exact hmapMono
  let : Mono (SmallObject.functorObjLeft cell πX) := hcopmono
  have hcopcoker : (cokernel (SmallObject.functorObjLeft cell πX)).Acyclic :=
    acyclic_cokernel_of_mono_quasiIso C _ hcop
  let : Mono (SmallObject.ιFunctorObj cell πX) := by
    change Mono ((killMapsObjectInclusion C I K).app X)
    exact killMapsObjectInclusion_mono_complex C I K X
  have hpushCoker : (cokernel (SmallObject.ιFunctorObj cell πX)).Acyclic := by
    intro n
    exact (hcopcoker n).of_iso (cokernelPushoutInlIso C
      (SmallObject.functorObjTop cell πX)
      (SmallObject.functorObjLeft cell πX)).symm
  have hqi : QuasiIso (SmallObject.ιFunctorObj cell πX) :=
    quasiIso_of_mono_of_acyclic_cokernel C _ hpushCoker
  change QuasiIso ((killMapsObjectInclusion C I K).app X)
  exact hqi

/-- Functorial K-injective resolutions exist in a Grothendieck abelian category. -/
@[stacks 079P "existence and functoriality"]
theorem exists_functorial_quasiIso_isKInjective :
    Nonempty (FunctorialKInjectiveResolution C) := by
  let κ₀ := acyclicComplexSizeBound (C := C)
  obtain ⟨lam, I, K, hK, hcover⟩ :=
    exists_small_boundedAbove_acyclic_representatives (C := C) κ₀
  let U := separator C
  have hU : IsSeparator U := isSeparator_separator C
  obtain ⟨κ, hκreg, hlam, hI, hUcard⟩ := exists_large_regular_cardinal
    (C := C) lam I U
  let F := killMapsObjectFunctor C I K
  let ηF := killMapsObjectInclusion C I K
  let N := functorialInjectiveStep C
  let ηN := functorialInjectiveStepInclusion C
  let : Fact κ.IsRegular := ⟨hκreg⟩
  have hκne : Nonempty κ.ord.ToType := by simpa using hκreg.ne_zero
  let : Nonempty κ.ord.ToType := hκne
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  let : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder hκreg.aleph0_le
  let : IsCardinalFiltered κ.ord.ToType κ := inferInstance
  let T := iterateCompositeFunctor F N ηF ηN κ
  let ηT := iterateCompositeFunctorInclusion F N ηF ηN κ
  have hFmono (X : CochainComplex C ℤ) : Mono ((ηF.app X)) := by
    exact killMapsObjectInclusion_mono_complex C I K X
  have hNmono (X : CochainComplex C ℤ) : Mono ((ηN.app X)) :=
    functorialInjectiveStepInclusion_mono_complex C X
  have hNqi (X : CochainComplex C ℤ) : QuasiIso ((ηN.app X)) :=
    functorialInjectiveStepInclusion_quasiIso C X
  have hFqi (X : CochainComplex C ℤ) : QuasiIso ((ηF.app X)) := by
    exact killMapsObjectInclusion_quasiIso C I K (fun i => (hK i).1) X
  have hTqi (X : CochainComplex C ℤ) : QuasiIso ((ηT.app X)) := by
    simpa [ηT] using iterateCompositeFunctorInclusion_quasiIso C F N ηF ηN hFqi hNqi κ X
  have hTmono (X : CochainComplex C ℤ) : Mono ((ηT.app X)) := by
    simpa [ηT] using iterateCompositeFunctorInclusion_mono F N ηF ηN hFmono hNmono κ X
  have hterm (X : CochainComplex C ℤ) (n : ℤ) : Injective ((T.obj X).X n) := by
    exact iterateCompositeFunctor_term_injective C F ηF hFmono κ U hU hUcard X n
  have hvanish (X : CochainComplex C ℤ) :
      ∀ (M : CochainComplex C ℤ), M.Acyclic →
        (∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (M.X n)) →
        (∀ n : ℤ, Cardinal.mk (Shrink.{w} (Subobject (M.X n))) ≤ κ₀) →
        ∀ f : M ⟶ T.obj X, Nonempty (Homotopy f 0) := by
    intro M hM hMtop hMsize f
    obtain ⟨i, ⟨e⟩⟩ := hcover M hM hMtop hMsize
    let g : K i ⟶ T.obj X := e.hom ≫ f
    have hKi : HasCardinalLT (Subobject (K i)) κ :=
      subobject_hasCardinalLT_of_bounded_cardinality C (K i) κ lam (hK i).2 hlam
    obtain ⟨j, g₀, hg₀⟩ := factor_through_iterateCompositeFunctor C F N ηF ηN
      (fun Y => hFmono Y) (fun Y => hNmono Y) κ (K i) X hKi g
    let S := CategoryTheory.SmallObject.SuccStruct.ofNatTrans
      (composeFunctorialInclusions F N ηF ηN)
    let Tj := S.iterationFunctor κ.ord.ToType
    let u : j ⟶ Order.succ j := homOfLE (Order.le_succ j)
    have hj : ¬ IsMax j := by
      obtain ⟨j', hj'⟩ := exists_gt j
      exact not_isMax_of_lt hj'
    let eSucc := S.iterationFunctorObjSuccIso j hj
    let leg := ((S.iterationCocone κ.ord.ToType).ι.app j).app X
    have hmap : (Tj.map u).app X =
        ((Tj.obj j).whiskerLeft (composeFunctorialInclusions F N ηF ηN)).app X ≫
          (eSucc.inv.app X) := by
      have hh := congrArg (fun q => q.app X) (S.iterationFunctor_map_succ j hj)
      change (Tj.map u).app X =
        ((Tj.obj j).whiskerLeft (composeFunctorialInclusions F N ηF ηN)).app X ≫
          (eSucc.inv.app X) at hh
      exact hh
    have hkill : homotopic C (ComplexShape.up ℤ)
        (g₀ ≫ (ηF.app ((Tj.obj j).obj X))) 0 :=
      killMapsObjectInclusion_kills_map C I K ((Tj.obj j).obj X) i g₀
    obtain ⟨hkill⟩ := hkill
    have hkill' : homotopic C (ComplexShape.up ℤ) (g₀ ≫ leg) 0 := by
      have hpost := hkill.compRight ((ηN.app (F.obj ((Tj.obj j).obj X))) ≫
        (eSucc.inv.app X) ≫
        ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X)
      have hcocone : (Tj.map u).app X ≫
          ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X =
            ((S.iterationCocone κ.ord.ToType).ι.app j).app X :=
        congrArg (fun q => q.app X) ((S.iterationCocone κ.ord.ToType).w u)
      have heta : (composeFunctorialInclusions F N ηF ηN).app ((Tj.obj j).obj X) =
          (ηF.app ((Tj.obj j).obj X)) ≫ (ηN.app (F.obj ((Tj.obj j).obj X))) := rfl
      have hwhisk : ((Tj.obj j).whiskerLeft
          (composeFunctorialInclusions F N ηF ηN)).app X =
        ηF.app ((Tj.obj j).obj X) ≫
          ηN.app (F.obj ((Tj.obj j).obj X)) := by
        simpa only [Functor.whiskerLeft_app] using heta
      have heq : g₀ ≫ leg =
          (((g₀ ≫ ηF.app ((Tj.obj j).obj X)) ≫
            ηN.app (F.obj ((Tj.obj j).obj X))) ≫
            eSucc.inv.app X) ≫
            ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X := by
        calc
          g₀ ≫ leg = g₀ ≫ ((Tj.map u).app X ≫
              ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X) := by
                dsimp [leg]
                exact congrArg (fun q => g₀ ≫ q) hcocone.symm
          _ = g₀ ≫ (((Tj.obj j).whiskerLeft
              (composeFunctorialInclusions F N ηF ηN)).app X ≫
              eSucc.inv.app X) ≫
                ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X := by
                exact congrArg (fun q => g₀ ≫ (q ≫
                  ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X)) hmap
          _ = g₀ ≫ (((ηF.app ((Tj.obj j).obj X) ≫
              ηN.app (F.obj ((Tj.obj j).obj X))) ≫ eSucc.inv.app X) ≫
                ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X) := by
                exact congrArg (fun q => g₀ ≫ ((q ≫ eSucc.inv.app X) ≫
                  ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X)) hwhisk
          _ = (((g₀ ≫ ηF.app ((Tj.obj j).obj X)) ≫
              ηN.app (F.obj ((Tj.obj j).obj X))) ≫ eSucc.inv.app X) ≫
                ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X := by
                let a := ηF.app ((Tj.obj j).obj X)
                let b := ηN.app (F.obj ((Tj.obj j).obj X))
                let c := eSucc.inv.app X
                let d := ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X
                change g₀ ≫ (((a ≫ b) ≫ c) ≫ d) =
                  (((g₀ ≫ a) ≫ b) ≫ c) ≫ d
                calc
                  g₀ ≫ (((a ≫ b) ≫ c) ≫ d) =
                      (g₀ ≫ ((a ≫ b) ≫ c)) ≫ d :=
                    (Category.assoc _ _ _).symm
                  _ = ((g₀ ≫ (a ≫ b)) ≫ c) ≫ d :=
                    congrArg (fun q => q ≫ d) (Category.assoc _ _ _).symm
                  _ = (((g₀ ≫ a) ≫ b) ≫ c) ≫ d :=
                    congrArg (fun q => (q ≫ c) ≫ d) (Category.assoc _ _ _).symm
      have hpost0 : Homotopy
          (((g₀ ≫ ηF.app ((Tj.obj j).obj X)) ≫
            ηN.app (F.obj ((Tj.obj j).obj X))) ≫ eSucc.inv.app X ≫
              ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X) 0 := by
        simpa only [Category.assoc, zero_comp] using hpost
      have hpost' : Homotopy
          ((((g₀ ≫ ηF.app ((Tj.obj j).obj X)) ≫
            ηN.app (F.obj ((Tj.obj j).obj X))) ≫ eSucc.inv.app X) ≫
              ((S.iterationCocone κ.ord.ToType).ι.app (Order.succ j)).app X) 0 := by
        exact (Homotopy.ofEq (Category.assoc _ _ _)).trans hpost0
      exact ⟨(Homotopy.ofEq heq).trans hpost'⟩
    have hfactor : g = g₀ ≫ leg := by
      change g = g₀ ≫
        ((S.iterationCocone κ.ord.ToType).ι.app j).app X
      exact hg₀
    have hgfzero : homotopic C (ComplexShape.up ℤ) g 0 := by
      rw [hfactor]
      exact hkill'
    have he : f = e.inv ≫ g := by simp [g]
    rw [he]
    obtain ⟨hgfzero⟩ := hgfzero
    exact ⟨by simpa [Category.assoc] using hgfzero.compLeft e.inv⟩
  refine ⟨{
    functor := T
    inclusion := ηT
    quasiIso := hTqi
    mono_f := ?_
    injective := hterm
    isKInjective := ?_ }⟩
  · intro X n
    let := hTmono X
    infer_instance
  · intro X
    exact isKInjective_of_small_boundedAbove_acyclic (T.obj X)
      (fun n => hterm X n) (hvanish X)

/-- The chosen functorial K-injective resolution in a Grothendieck abelian category. -/
noncomputable def functorialKInjectiveResolution :
    FunctorialKInjectiveResolution C :=
  exists_functorial_quasiIso_isKInjective C |>.some

/-- The functor sending a complex to its chosen K-injective resolution. -/
noncomputable def kInjectiveResolutionFunctor :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  (functorialKInjectiveResolution C).functor

/-- The natural inclusion into the chosen K-injective resolution. -/
noncomputable def kInjectiveResolutionInclusion :
    Functor.id (CochainComplex C ℤ) ⟶ kInjectiveResolutionFunctor C :=
  (functorialKInjectiveResolution C).inclusion

/-- The inclusion into the chosen K-injective resolution is a quasi-isomorphism. -/
@[stacks 079P "quasi-isomorphism"]
noncomputable instance kInjectiveResolutionInclusion_quasiIso
    (M : CochainComplex C ℤ) :
    QuasiIso ((kInjectiveResolutionInclusion C).app M) :=
  (functorialKInjectiveResolution C).quasiIso M

/-- The inclusion into the chosen K-injective resolution is termwise monic. -/
@[stacks 079P "termwise monomorphism"]
noncomputable instance kInjectiveResolutionInclusion_f_mono
    (M : CochainComplex C ℤ) (n : ℤ) :
    Mono (((kInjectiveResolutionInclusion C).app M).f n) :=
  (functorialKInjectiveResolution C).mono_f M n

/-- Every term of the chosen resolution is an injective object. -/
@[stacks 079P "injective terms"]
noncomputable instance kInjectiveResolutionFunctor_obj_X_injective
    (M : CochainComplex C ℤ) (n : ℤ) :
    Injective (((kInjectiveResolutionFunctor C).obj M).X n) :=
  (functorialKInjectiveResolution C).injective M n

/-- The chosen resolution is K-injective. -/
@[stacks 079P "K-injective target"]
noncomputable instance kInjectiveResolutionFunctor_obj_isKInjective
    (M : CochainComplex C ℤ) :
    ((kInjectiveResolutionFunctor C).obj M).IsKInjective :=
  (functorialKInjectiveResolution C).isKInjective M

/-- **Every cochain complex in a Grothendieck abelian category admits a quasi-isomorphism into a
K-injective complex.**  This is the existential form of the chosen functorial resolution, which
is what a consumer that only needs *some* resolution asks for. -/
theorem exists_quasiIso_isKInjective_of_isGrothendieckAbelian (K : CochainComplex C ℤ) :
    ∃ (I : CochainComplex C ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  ⟨(kInjectiveResolutionFunctor C).obj K, (kInjectiveResolutionInclusion C).app K,
    inferInstance, inferInstance⟩

end Stacks.Injectives
