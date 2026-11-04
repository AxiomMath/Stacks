module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaerDifference
public import StacksFrontier.Deformation.ToposThickening.SquareZeroIdealAction
public import StacksFrontier.Deformation.ToposThickening.SquareZeroLiftModels

/-!
# Two lifts differ by a class of `Ext¹(K₀, K₀ ⊗^L I)`

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings with a square-zero ideal
sequence `0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0`, and let `(K, α)` and `(K', α')` be two lifts of
`K₀ ∈ D⁻(O₀)`. Choose cellular models `P` of `K` and `P'` of `K'` joined by a morphism
`a₀ : P'₀ ⟶ P₀` of their reductions over `K₀` (Tag 0DIX). The reduction sequences of `P` and `P'`
are two extensions, of `P₀|_O` by `(P₀ ⊗ I₀)|_O` and of `P'₀|_O` by `(P'₀ ⊗ I₀)|_O`; pulling the
first back along `a₀` and pushing the second out along `a₀ ⊗ I₀`, their difference `E` is an
extension of `P'₀|_O` by `(P₀ ⊗ I₀)|_O` on whose middle term the ideal acts by zero, because it
acts on both extensions through the same map. So `E` is an extension of complexes of
`O₀`-modules, its connecting morphism is restricted from `D(O₀)`, and the connecting classes of
the two lifts differ by the restriction of a class of `Ext¹(K₀, K₀ ⊗^L I)`.

This is the input `hdiff` of `Deformation.ComplexLift.exists_addTorsor_liftClasses`, and it is
what the source's proof of Stacks 0DIZ (2) uses when it calls the map from lifts to obstruction
classes injective.

## Main results

* `Deformation.ComplexLift.idealActionComplex_app_baerCokernel`: the ideal acts by zero on the
  difference of the two reduction sequences.
* `Deformation.ComplexLift.connectingClass_sub_flatReduction`: the connecting classes of two
  lifts differ by a restricted class.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe d d₀ v' u u'

namespace Deformation.ComplexLift

attribute [-instance] CategoryTheory.catToReflQuiver

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀}
variable {I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
  (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)

/-- Restriction of scalars along `f`, on complexes. -/
abbrev restrictComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ :=
  (SheafOfModules.restrictScalars (ringSheafMapOf J f)).mapHomologicalComplex (ComplexShape.up ℤ)

section Difference

variable {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
  (a₀ : (extensionOfScalarsCochainComplex J f).obj P' ⟶
    (extensionOfScalarsCochainComplex J f).obj P)

/-- The map of quotient terms of the two reduction sequences: `a₀`, restricted. -/
abbrev quotientMap :
    (reductionSequence ι hι P').X₃ ⟶ (reductionSequence ι hι P).X₃ :=
  (restrictComplex (f := f)).map a₀

/-- The map of kernel terms of the two reduction sequences: `a₀ ⊗ I₀`, restricted. -/
abbrev kernelMap :
    (reductionSequence ι hι P').X₁ ⟶ (reductionSequence ι hι P).X₁ :=
  (restrictComplex (f := f)).map (((tensorRight O₀ I₀).mapHomologicalComplex
    (ComplexShape.up ℤ)).map a₀)

/-- On the fibre product of the two middle terms over the quotients, the two projections have
reductions related by `a₀`. -/
theorem extensionOfScalars_map_snd :
    (extensionOfScalarsCochainComplex J f).map
        (pullback.snd ((reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
          (reductionSequence ι hι P).g) =
      (extensionOfScalarsCochainComplex J f).map
          (pullback.fst ((reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
            (reductionSequence ι hι P).g) ≫ a₀ := by
  have hc := pullback.condition (f := (reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
    (g := (reductionSequence ι hι P).g)
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  have hcn := congrArg (fun φ ↦ HomologicalComplex.Hom.f φ n) hc
  dsimp only [HomologicalComplex.comp_f] at hcn
  show (extensionOfScalars f).map ((pullback.snd ((reductionSequence ι hι P').g ≫
      quotientMap ι hι a₀) (reductionSequence ι hι P).g).f n) =
    (extensionOfScalars f).map ((pullback.fst ((reductionSequence ι hι P').g ≫
      quotientMap ι hι a₀) (reductionSequence ι hι P).g).f n) ≫ a₀.f n
  refine ((extendRestrictAdjunction f).homEquiv _ _).injective
    ((Adjunction.homEquiv_unit _ _ _ _).trans (Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm))
  have n₁ := (extendRestrictAdjunction f).unit.naturality
    ((pullback.snd ((reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
      (reductionSequence ι hι P).g).f n)
  have n₂ := (extendRestrictAdjunction f).unit.naturality
    ((pullback.fst ((reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
      (reductionSequence ι hι P).g).f n)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at n₁ n₂
  rw [← n₁]
  have hm := (SheafOfModules.restrictScalars (ringSheafMapOf J f)).map_comp
    ((extensionOfScalars f).map ((pullback.fst ((reductionSequence ι hι P').g ≫
      quotientMap ι hι a₀) (reductionSequence ι hι P).g).f n)) (a₀.f n)
  refine Eq.trans ?_ (congrArg (fun k ↦ (extendRestrictAdjunction f).unit.app _ ≫ k) hm).symm
  rw [← Category.assoc, ← n₂, Category.assoc]
  exact hcn.symm

/-- **The ideal acts on the fibre product through the graph of `a₀ ⊗ I₀`**. -/
theorem idealActionComplex_app_baerPullback :
    (idealActionComplex ι).app (CochainComplex.baerPullback (S₁ := reductionSequence ι hι P)
        (S₂ := reductionSequence ι hι P') (quotientMap ι hι a₀)) =
      (idealTensorRightIsoComplex (f := f) (I₀ := I₀)).hom.app _ ≫
        ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (pullback.fst ((reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
            (reductionSequence ι hι P).g) ≫
        CochainComplex.baerGraph (quotientMap ι hι a₀) (kernelMap ι hι a₀) := by
  have key : ∀ {Y} (p : pullback ((reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
        (reductionSequence ι hι P).g ⟶ Y),
      (idealActionComplex ι).app (CochainComplex.baerPullback
          (S₁ := reductionSequence ι hι P) (S₂ := reductionSequence ι hι P')
          (quotientMap ι hι a₀)) ≫ p =
        (idealTensorRightIsoComplex (f := f) (I₀ := I₀)).hom.app _ ≫
          ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map p ≫
            idealPartInclComplex ι Y := fun p ↦ by
    refine ((idealActionComplex ι).naturality p).symm.trans ?_
    rw [idealActionComplex_app_eq, ← Category.assoc,
      (idealTensorRightIsoComplex (f := f) (I₀ := I₀)).hom.naturality p, Category.assoc]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, key]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, key]
    have hk : ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (pullback.snd ((reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
          (reductionSequence ι hι P).g) =
        ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (pullback.fst ((reductionSequence ι hι P').g ≫ quotientMap ι hι a₀)
            (reductionSequence ι hι P).g) ≫ kernelMap ι hι a₀ := by
      show (restrictComplex (f := f)).map (((tensorRight O₀ I₀).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map _)) =
        (restrictComplex (f := f)).map (((tensorRight O₀ I₀).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((extensionOfScalarsCochainComplex J f).map _)) ≫
          (restrictComplex (f := f)).map (((tensorRight O₀ I₀).mapHomologicalComplex
            (ComplexShape.up ℤ)).map a₀)
      rw [extensionOfScalars_map_snd ι hι a₀, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp]
    rw [hk, Category.assoc]

omit hι in
/-- If the ideal acts through the kernel of an epimorphism, it acts by zero on its target. -/
theorem idealActionComplex_app_eq_zero_of_epi
    {X E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (π : X ⟶ E) [hπ : Epi π] (h : (idealActionComplex ι).app X ≫ π = 0) :
    (idealActionComplex ι).app E = 0 := by
  have hπ' : Epi (((tensorRight O (restrictIdeal f I₀)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map π) :=
    HomologicalComplex.epi_of_epi_f _ fun n ↦ by
      have hen : Epi (π.f n) := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_epi π
      exact (tensorRight O (restrictIdeal f I₀)).map_epi (π.f n)
  rw [← cancel_epi (((tensorRight O (restrictIdeal f I₀)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map π), comp_zero]
  have hn : ((tensorRight O (restrictIdeal f I₀)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map π ≫ (idealActionComplex ι).app E =
      (idealActionComplex ι).app X ≫ π := (idealActionComplex ι).naturality π
  rw [hn, h]

/-- **The ideal acts by zero on the difference of the two reduction sequences.** -/
theorem idealActionComplex_app_baerCokernel :
    (idealActionComplex ι).app (cokernel (CochainComplex.baerGraph
      (S₁ := reductionSequence ι hι P) (S₂ := reductionSequence ι hι P')
      (quotientMap ι hι a₀) (kernelMap ι hι a₀))) = 0 :=
  idealActionComplex_app_eq_zero_of_epi ι (cokernel.π _) (by
    rw [idealActionComplex_app_baerPullback, Category.assoc, Category.assoc, cokernel.condition,
      comp_zero, comp_zero])

end Difference

/-- Cancelling an isomorphism inserted between two morphisms, with the objects abstract. -/
theorem comp_hom_inv_comp_eq_zero' {D : Type*} [Category D] [Preadditive D] {X Y Y' Z : D}
    (a : X ⟶ Y) (u : Y ⟶ Y') (hu : IsIso u) (b : Y ⟶ Z) (h : a ≫ b = 0) :
    (a ≫ u) ≫ (inv u ≫ b) = 0 := by simp [h]

/-- A morphism of short exact sequences over identities, read on connecting morphisms, with the
objects abstract. -/
theorem eq_of_comp_shift_map_id' {A D : Type*} [Category A] [Category D] [HasShift D ℤ]
    (G : A ⥤ D) {X Y : A} (x y : G.obj Y ⟶ (G.obj X)⟦(1 : ℤ)⟧)
    (h : x ≫ (G.map (𝟙 X))⟦(1 : ℤ)⟧' = G.map (𝟙 Y) ≫ y) : x = y := by simpa using h

/-- Cancelling three isomorphisms around a morphism, with the objects abstract. -/
theorem cancel_three_isos' {D : Type*} [Category D] {X X' Y Y' Y'' : D} (i : X' ≅ X) (d : X ⟶ Y)
    (j : Y' ≅ Y) (k : Y'' ≅ Y') :
    i.inv ≫ (i.hom ≫ d ≫ j.inv ≫ k.inv) ≫ k.hom ≫ j.hom = d := by simp

/-- A commutative square with an identity isomorphism on the left and `asIso u` on the right. -/
theorem iso_refl_square₁' {D : Type*} [Category D] {X Y Y' : D} (x : X ⟶ Y) (u : Y ⟶ Y')
    (hu : IsIso u) (y : X ⟶ Y') (h : y = x ≫ u) :
    (Iso.refl X).hom ≫ y = x ≫ (@asIso _ _ _ _ u hu).hom := by simp [h]

/-- A commutative square with `asIso u` on the left and an identity isomorphism on the right. -/
theorem iso_refl_square₂' {D : Type*} [Category D] {Y Y' Z : D} (u : Y ⟶ Y') (hu : IsIso u)
    (x : Y ⟶ Z) (y : Y' ⟶ Z) (h : y = @inv _ _ _ _ u hu ≫ x) :
    (@asIso _ _ _ _ u hu).hom ≫ y = x ≫ (Iso.refl Z).hom := by simp [h]

section Descent

variable (hf : Presheaf.IsLocallySurjective J (ringSheafMapOf J f).hom)

/-- Restriction of scalars along a locally surjective map is fully faithful. -/
def restrictScalarsFullyFaithful :
    (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).FullyFaithful where
  preimage g := Deformation.ToposThickening.moduleHomEquivOfLocallySurjective _ hf g
  map_preimage g :=
    (Deformation.ToposThickening.moduleHomEquivOfLocallySurjective _ hf).symm_apply_apply g
  preimage_map g :=
    (Deformation.ToposThickening.moduleHomEquivOfLocallySurjective _ hf).apply_symm_apply g

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
include hf in
/-- Restriction of scalars on cochain complexes along a locally surjective map of sheaves of rings
is full. -/
theorem restrictComplex_full : (restrictComplex (f := f)).Full := by
  have := (restrictScalarsFullyFaithful hf).full
  have := (restrictScalarsFullyFaithful hf).faithful
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
include hf in
/-- Restriction of scalars on cochain complexes along a locally surjective map of sheaves of rings
is faithful. -/
theorem restrictComplex_faithful : (restrictComplex (f := f)).Faithful := by
  have := (restrictScalarsFullyFaithful hf).faithful
  infer_instance

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The restriction of the connecting morphism of a short exact sequence of complexes of
`O₀`-modules is the connecting morphism of the restricted sequence. -/
theorem restrict_triangleOfSESδ
    {S : ShortComplex (CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ)} (hS : S.ShortExact) :
    (restrictionOnDerived.{d, d₀} f).map (DerivedCategory.triangleOfSESδ hS) =
      (restrictionFactors.{d, d₀} f).hom.app S.X₃ ≫
        DerivedCategory.triangleOfSESδ (hS.map_of_exact (restrictComplex (f := f))) ≫
        ((restrictionFactors.{d, d₀} f).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
        ((restrictionOnDerived.{d, d₀} f).commShiftIso (1 : ℤ)).inv.app _ :=
  DerivedCategory.map_triangleOfSESδ (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)) hS

variable (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
  {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
  (hP : ∀ n, flatObjects O (P.X n)) (hP' : ∀ n, flatObjects O (P'.X n))
  (a₀ : (extensionOfScalarsCochainComplex J f).obj P' ⟶
    (extensionOfScalarsCochainComplex J f).obj P)

include hf hS hP hP' in
/-- **The difference of the two reduction sequences is restricted from `O₀`**: its connecting
morphism is the restriction of a morphism `Q(P'₀) ⟶ Q(P₀ ⊗ I₀)⟦1⟧` of `D(O₀)`. -/
theorem exists_triangleOfSESδ_baerDifference_eq_restrict :
    ∃ δ₀ : DerivedCategory.Q.obj ((extensionOfScalarsCochainComplex J f).obj P') ⟶
        (DerivedCategory.Q.obj (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((extensionOfScalarsCochainComplex J f).obj P)))⟦(1 : ℤ)⟧,
      DerivedCategory.triangleOfSESδ (CochainComplex.shortExact_baerDifference
          (shortExact_reductionSequence ι hι hS P hP) (shortExact_reductionSequence ι hι hS P' hP')
          (quotientMap ι hι a₀) (kernelMap ι hι a₀)) =
        (restrictionFactors.{d, d₀} f).inv.app ((extensionOfScalarsCochainComplex J f).obj P') ≫
          (restrictionOnDerived.{d, d₀} f).map δ₀ ≫
          ((restrictionOnDerived.{d, d₀} f).commShiftIso (1 : ℤ)).hom.app _ ≫
          ((restrictionFactors.{d, d₀} f).hom.app (((tensorRight O₀ I₀).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              ((extensionOfScalarsCochainComplex J f).obj P)))⟦(1 : ℤ)⟧' := by
  have := restrictComplex_full hf
  have := restrictComplex_faithful hf
  let SE := CochainComplex.baerDifference (S₁ := reductionSequence ι hι P)
    (S₂ := reductionSequence ι hι P') (quotientMap ι hι a₀) (kernelMap ι hι a₀)
  have hSE : SE.ShortExact := CochainComplex.shortExact_baerDifference
    (shortExact_reductionSequence ι hι hS P hP) (shortExact_reductionSequence ι hι hS P' hP')
    (quotientMap ι hι a₀) (kernelMap ι hι a₀)
  have hu : IsIso (reductionMapComplex (f := f) SE.X₂) :=
    isIso_reductionMapComplex_of_idealActionComplex ι hι hS _
      (idealActionComplex_app_baerCokernel ι hι a₀)
  let f₀ : ((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((extensionOfScalarsCochainComplex J f).obj P) ⟶
      (extensionOfScalarsCochainComplex J f).obj SE.X₂ :=
    (restrictComplex (f := f)).preimage (SE.f ≫ reductionMapComplex (f := f) SE.X₂)
  let g₀ : (extensionOfScalarsCochainComplex J f).obj SE.X₂ ⟶
      (extensionOfScalarsCochainComplex J f).obj P' :=
    (restrictComplex (f := f)).preimage
      (@inv _ _ _ _ (reductionMapComplex (f := f) SE.X₂) hu ≫ SE.g)
  have hf₀ : (restrictComplex (f := f)).map f₀ = SE.f ≫ reductionMapComplex (f := f) SE.X₂ :=
    (restrictComplex (f := f)).map_preimage _
  have hg₀ : (restrictComplex (f := f)).map g₀ =
      @inv _ _ _ _ (reductionMapComplex (f := f) SE.X₂) hu ≫ SE.g :=
    (restrictComplex (f := f)).map_preimage _
  have hz : f₀ ≫ g₀ = 0 := (restrictComplex (f := f)).map_injective (by
    rw [CategoryTheory.Functor.map_comp, hf₀, hg₀, CategoryTheory.Functor.map_zero]
    exact comp_hom_inv_comp_eq_zero' _ _ hu _ SE.zero)
  let S₀ := ShortComplex.mk f₀ g₀ hz
  let e : SE ≅ S₀.map (restrictComplex (f := f)) :=
    ShortComplex.isoMk (Iso.refl _) (@asIso _ _ _ _ (reductionMapComplex (f := f) SE.X₂) hu)
      (Iso.refl _)
      (iso_refl_square₁' _ _ hu _ hf₀) (iso_refl_square₂' _ hu _ _ hg₀)
  have hS₀ : S₀.ShortExact := Deformation.ToposThickening.shortExact_of_fullyFaithful_map _
    (Functor.FullyFaithful.ofFullyFaithful _) S₀ (ShortComplex.shortExact_of_iso e hSE)
  refine ⟨DerivedCategory.triangleOfSESδ hS₀, ?_⟩
  have hn := DerivedCategory.triangleOfSESδ_naturality hSE (hS₀.map_of_exact _) e.hom
  have hn' := eq_of_comp_shift_map_id' DerivedCategory.Q _ _ hn
  rw [restrict_triangleOfSESδ]
  exact (hn'.trans (cancel_three_isos' ((restrictionFactors.{d, d₀} f).app _) _
    ((shiftFunctor _ (1 : ℤ)).mapIso ((restrictionFactors.{d, d₀} f).app _))
    (((restrictionOnDerived.{d, d₀} f).commShiftIso (1 : ℤ)).app _)).symm)

variable
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The algebra of the difference of two transported connecting morphisms, with the objects
abstract: if the two connecting morphisms are related through the Baer difference, whose
connecting morphism is restricted, the difference of the transported morphisms is restricted. -/
theorem sub_eq_shiftedRestriction' {D₀ D : Type*} [Category D₀] [Category D] [Preadditive D₀]
    [Preadditive D] [HasShift D₀ ℤ] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    (r : D₀ ⥤ D) [r.CommShift ℤ] [r.Additive]
    {K₁ X₀ X₀' Y₀ Y₀' K₂ : D₀} {X X' Y Y' : D}
    (Mi : K₁ ⟶ X₀) (Mi' : K₁ ⟶ X₀') (qa : X₀' ⟶ X₀) (hM : Mi' ≫ qa = Mi)
    (Nh : Y₀ ⟶ K₂) (Nh' : Y₀' ⟶ K₂) (qφ : Y₀' ⟶ Y₀) (hN : qφ ≫ Nh = Nh')
    (a : r.obj X₀ ≅ X) (a' : r.obj X₀' ≅ X') (b : Y ≅ r.obj Y₀) (b' : Y' ≅ r.obj Y₀')
    (ea : X' ⟶ X) (ha : r.map qa ≫ a.hom = a'.hom ≫ ea)
    (φ : Y' ⟶ Y) (hb : b'.hom ≫ r.map qφ = φ ≫ b.hom)
    (δ : X ⟶ Y⟦(1 : ℤ)⟧) (δ' : X' ⟶ Y'⟦(1 : ℤ)⟧) (δE : X' ⟶ Y⟦(1 : ℤ)⟧)
    (hE : δE = ea ≫ δ - δ' ≫ φ⟦(1 : ℤ)⟧')
    (δ₀ : X₀' ⟶ Y₀⟦(1 : ℤ)⟧)
    (hE' : δE = a'.inv ≫ r.map δ₀ ≫ (r.commShiftIso (1 : ℤ)).hom.app _ ≫ b.inv⟦(1 : ℤ)⟧') :
    (r.map Mi ≫ a.hom ≫ δ ≫ (b.hom ≫ r.map Nh)⟦(1 : ℤ)⟧') -
        (r.map Mi' ≫ a'.hom ≫ δ' ≫ (b'.hom ≫ r.map Nh')⟦(1 : ℤ)⟧') =
      r.map (Mi' ≫ δ₀ ≫ Nh⟦(1 : ℤ)⟧') ≫ (r.commShiftIso (1 : ℤ)).hom.app _ := by
  subst hM hN
  have hY : (b'.hom ≫ r.map (qφ ≫ Nh))⟦(1 : ℤ)⟧' = φ⟦(1 : ℤ)⟧' ≫ (b.hom ≫ r.map Nh)⟦(1 : ℤ)⟧' := by
    rw [← Functor.map_comp, r.map_comp, reassoc_of% hb]
  have hX : r.map (Mi' ≫ qa) ≫ a.hom = r.map Mi' ≫ a'.hom ≫ ea := by
    rw [r.map_comp, Category.assoc, ha]
  have key : a'.hom ≫ δE = r.map δ₀ ≫ (r.commShiftIso (1 : ℤ)).hom.app _ ≫ b.inv⟦(1 : ℤ)⟧' := by
    rw [hE']; simp
  rw [hE] at key
  have hfin : r.map Mi' ≫ (a'.hom ≫ (ea ≫ δ - δ' ≫ φ⟦(1 : ℤ)⟧')) ≫
      (b.hom ≫ r.map Nh)⟦(1 : ℤ)⟧' =
      r.map (Mi' ≫ δ₀ ≫ Nh⟦(1 : ℤ)⟧') ≫ (r.commShiftIso (1 : ℤ)).hom.app _ := by
    rw [key]
    simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality]
    simp
  rw [← hfin, ← Category.assoc (r.map (Mi' ≫ qa)), hX, hY]
  simp only [Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp]

include hf in
/-- **The connecting classes of two lifts differ by a restricted class**: for lifts `L` and `L'`
of `K₀` there is `ξ ∈ Ext¹(K₀, K₀ ⊗^L I)` whose restriction is the difference of their connecting
classes. -/
theorem connectingClass_sub_flatReduction
    (L L' : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀) :
    ∃ ξ, connectingClass (flatReduction.{d, d₀} f ι hι hS) L -
        connectingClass (flatReduction.{d, d₀} f ι hι hS) L' =
      shiftedRestriction (flatReduction.{d, d₀} f ι hι hS) ξ := by
  obtain ⟨P, P', hP, hP', w, w', a₀, ha₀⟩ := exists_models_hom.{d, d₀} f L L'
  have hP₁ := flatObjects_X_of_isFlatCellular hP
  have hP₁' := flatObjects_X_of_isFlatCellular hP'
  obtain ⟨δ₀, hδ₀⟩ :=
    exists_triangleOfSESδ_baerDifference_eq_restrict.{d, d₀} ι hι hf hS hP₁ hP₁' a₀
  have hBaer := CochainComplex.triangleOfSESδ_baerDifference
    (shortExact_reductionSequence ι hι hS P hP₁) (shortExact_reductionSequence ι hι hS P' hP₁')
    (quotientMap ι hι a₀) (kernelMap ι hι a₀)
  refine ⟨(liftModelIso.{d, d₀} f L' hP' w').inv ≫ δ₀ ≫
    ((liftModelIdealIso.{d, d₀} f I₀ L hP w).hom)⟦(1 : ℤ)⟧', ?_⟩
  rw [connectingClass_flatReduction_eq.{d, d₀} f ι hι hS L hP w,
    connectingClass_flatReduction_eq.{d, d₀} f ι hι hS L' hP' w', shiftedRestriction_apply]
  have hM : (liftModelIso.{d, d₀} f L' hP' w').inv ≫ DerivedCategory.Q.map a₀ =
      (liftModelIso.{d, d₀} f L hP w).inv := by
    rw [Iso.inv_comp_eq, ← ha₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hN : DerivedCategory.Q.map (((tensorRight O₀ I₀).mapHomologicalComplex
      (ComplexShape.up ℤ)).map a₀) ≫ (liftModelIdealIso.{d, d₀} f I₀ L hP w).hom =
      (liftModelIdealIso.{d, d₀} f I₀ L' hP' w').hom := by
    have h₁ := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hP
    have h₂ := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P' hP'
    have hn := (derivedTensorRightCounit.{d₀} I₀).naturality a₀
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [liftModelIdealIso_hom, liftModelIdealIso_hom, ← ha₀, CategoryTheory.Functor.map_comp,
      IsIso.eq_inv_comp, ← Category.assoc, ← Category.assoc, ← hn]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact sub_eq_shiftedRestriction' (restrictionOnDerived.{d, d₀} f) _ _ _ hM _ _ _ hN
    ((restrictionFactors.{d, d₀} f).app _) ((restrictionFactors.{d, d₀} f).app _)
    ((restrictionFactors.{d, d₀} f).symm.app _) ((restrictionFactors.{d, d₀} f).symm.app _)
    _ ((restrictionFactors.{d, d₀} f).hom.naturality a₀)
    _ ((restrictionFactors.{d, d₀} f).inv.naturality _).symm _ _ _ hBaer δ₀ hδ₀

end Descent

end Deformation.ComplexLift

end
