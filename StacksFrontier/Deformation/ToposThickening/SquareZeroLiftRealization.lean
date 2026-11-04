module

public import StacksFrontier.Deformation.ToposThickening.SquareZeroLiftDifference
public import StacksFrontier.Deformation.ToposThickening.FlatTensorAmplitude
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass

/-!
# Every class of `Ext¹(K₀, K₀ ⊗^L I)` is the difference of two lifts

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings with square-zero kernel, given
by its ideal sequence `0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0`, let `(K, α)` be a lift of `K₀ ∈ D⁻(O₀)` and
let `ξ : K₀ ⟶ (K₀ ⊗^L I)[1]`. This file constructs, following the proof of Stacks 0DIZ (2), a
lift `(K', α')` whose connecting class differs from that of `(K, α)` by the restriction of `ξ`.

Represent `K` by a bounded above complex `P` of flat `O`-modules with reduction `P₀`, and `ξ` by
a fraction `t ∘ s⁻¹` with `s : G₀ ⟶ P₀` a quasi-isomorphism and `t : G₀ ⟶ (P₀ ⊗ I₀)[1]`. The
twist of `P₀ ⊗ I₀` by `G₀` along `t` is an extension of `G₀` by `P₀ ⊗ I₀` with connecting
morphism `t`; the difference of the reduction sequence of `P`, pulled back along `s`, and this
extension is an extension `0 ⟶ (P₀ ⊗ I₀)|_O ⟶ H ⟶ G₀|_O ⟶ 0` of complexes of `O`-modules (the
complex `H` of the source). A bounded above flat resolution `P' ⟶ H` reduces to a map
`δ' : P'₀ ⟶ G₀`, which is a quasi-isomorphism by the descending induction of the source, using
Stacks 0DIV; so `P'` is a lift of `K₀`, and its connecting class is read off the connecting
morphism of `H`, which is that of `P` minus `t`.

## Main results

* `Deformation.ComplexLift.exists_connectingClass_sub_flatReduction_eq`: the realization.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DIW](https://stacks.math.columbia.edu/tag/0DIW)
* [Stacks Project, Tag 0DIV](https://stacks.math.columbia.edu/tag/0DIV)
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

/-! ### The counit of extension and restriction of scalars on complexes -/

/-- The counit `(O₀ ⊗_O X|_O) ⟶ X` of extension and restriction of scalars, degreewise. -/
def extensionCounitComplex
    (X : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (extensionOfScalarsCochainComplex J f).obj ((restrictComplex (f := f)).obj X) ⟶ X where
  f n := (extendRestrictAdjunction f).counit.app (X.X n)
  comm' i j _ := ((extendRestrictAdjunction f).counit.naturality (X.d i j)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The transpose of a map `x : P ⟶ X|_O`, followed by the structure map of the reduction,
recovers `x`. -/
theorem reductionMapComplex_comp_restrict_counit
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    {X : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ}
    (x : P ⟶ (restrictComplex (f := f)).obj X) :
    reductionMapComplex (f := f) P ≫ (restrictComplex (f := f)).map
      ((extensionOfScalarsCochainComplex J f).map x ≫ extensionCounitComplex X) = x := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  have h := ((extendRestrictAdjunction f).homEquiv _ _).apply_symm_apply (x.f n)
  exact ((congrArg (fun k ↦ (extendRestrictAdjunction f).unit.app (P.X n) ≫
      (SheafOfModules.restrictScalars (ringSheafMapOf J f)).map k)
    ((extendRestrictAdjunction f).homEquiv_counit _ _ _).symm).trans
      ((extendRestrictAdjunction f).homEquiv_unit _ _ _).symm).trans h

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- A map out of the reduction of a complex is determined by its transpose. -/
theorem extensionOfScalars_hom_ext
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    {X : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ}
    (a b : (extensionOfScalarsCochainComplex J f).obj P ⟶ X)
    (h : reductionMapComplex (f := f) P ≫ (restrictComplex (f := f)).map a =
      reductionMapComplex (f := f) P ≫ (restrictComplex (f := f)).map b) : a = b := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  have hn := congrArg (fun φ ↦ HomologicalComplex.Hom.f φ n) h
  refine ((extendRestrictAdjunction f).homEquiv _ _).injective ?_
  exact ((extendRestrictAdjunction f).homEquiv_unit _ _ _).trans
    (hn.trans ((extendRestrictAdjunction f).homEquiv_unit _ _ _).symm)

/-- The extension of scalars of a map `y` is the map whose transpose is `y` followed by the
structure map. -/
theorem extensionOfScalars_map_eq
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (y : P' ⟶ P) (c : (extensionOfScalarsCochainComplex J f).obj P' ⟶
      (extensionOfScalarsCochainComplex J f).obj P)
    (h : reductionMapComplex (f := f) P' ≫ (restrictComplex (f := f)).map c =
      y ≫ reductionMapComplex (f := f) P) :
    (extensionOfScalarsCochainComplex J f).map y = c := by
  refine extensionOfScalars_hom_ext _ _ ?_
  rw [h, reductionMapComplex_naturality]
  rfl

/-! ### Cohomology and an exact faithful functor -/

section Exact

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B] (F : A ⥤ B) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]
  {X Y : CochainComplex A ℤ} (g : X ⟶ Y) (i : ℤ)

omit [F.Faithful] in
/-- An exact functor commutes with cohomology. -/
theorem homologyMap_map_comp_mapHomologyIso :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) i ≫
        ((Y.sc i).mapHomologyIso F).hom =
      ((X.sc i).mapHomologyIso F).hom ≫ F.map (HomologicalComplex.homologyMap g i) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i).map g) F

/-- An exact faithful functor preserves and reflects surjectivity on cohomology. -/
theorem epi_homologyMap_map_iff :
    Epi (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) i) ↔
      Epi (HomologicalComplex.homologyMap g i) := by
  rw [← F.epi_map_iff_epi, ← MorphismProperty.epimorphisms.iff,
    ← MorphismProperty.epimorphisms.iff]
  exact (MorphismProperty.epimorphisms B).arrow_mk_iso_iff
    (Arrow.isoMk ((X.sc i).mapHomologyIso F) ((Y.sc i).mapHomologyIso F)
      (homologyMap_map_comp_mapHomologyIso F g i).symm)

/-- An exact faithful functor preserves and reflects injectivity on cohomology. -/
theorem mono_homologyMap_map_iff :
    Mono (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) i) ↔
      Mono (HomologicalComplex.homologyMap g i) := by
  rw [← F.mono_map_iff_mono, ← MorphismProperty.monomorphisms.iff,
    ← MorphismProperty.monomorphisms.iff]
  exact (MorphismProperty.monomorphisms B).arrow_mk_iso_iff
    (Arrow.isoMk ((X.sc i).mapHomologyIso F) ((Y.sc i).mapHomologyIso F)
      (homologyMap_map_comp_mapHomologyIso F g i).symm)

end Exact

/-! ### The difference of the reduction sequence and a twisted extension -/

section Twist

variable (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
  {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
  {G₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ}
  (s : G₀ ⟶ (extensionOfScalarsCochainComplex J f).obj P)
  (t : G₀ ⟶ (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((extensionOfScalarsCochainComplex J f).obj P))⟦(1 : ℤ)⟧)

/-- The twisted extension `0 ⟶ P₀ ⊗ I₀ ⟶ twist t ⟶ G₀ ⟶ 0`, restricted to `O`. -/
abbrev twistSequence :
    ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :=
  (CochainComplex.twistShortComplex t).map (restrictComplex (f := f))

/-- The comparison of the quotients: `s`, restricted. -/
abbrev twistQuotientMap : (twistSequence t).X₃ ⟶ (reductionSequence ι hι P).X₃ :=
  (restrictComplex (f := f)).map s

/-- The comparison of the kernels: the identity of `(P₀ ⊗ I₀)|_O`. -/
abbrev twistKernelMap : (twistSequence t).X₁ ⟶ (reductionSequence ι hι P).X₁ := 𝟙 _

/-- **The difference sequence** `0 ⟶ (P₀ ⊗ I₀)|_O ⟶ H ⟶ G₀|_O ⟶ 0`: the reduction sequence of
`P`, pulled back along `s`, minus the twisted extension. -/
abbrev realizationSequence :
    ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :=
  CochainComplex.baerDifference (twistQuotientMap ι hι s t) (twistKernelMap ι hι t)

/-- The projection of the fibre product onto `H`. -/
abbrev realizationπ :
    CochainComplex.baerPullback (twistQuotientMap ι hι s t) ⟶ (realizationSequence ι hι s t).X₂ :=
  cokernel.π (CochainComplex.baerGraph (twistQuotientMap ι hι s t) (twistKernelMap ι hι t))

/-- The map `H₀ ⟶ P₀` through which the ideal acts on `H`: the transpose of the projection
`H ⟶ G₀|_O`, followed by `s`. -/
abbrev realizationReduction :
    (extensionOfScalarsCochainComplex J f).obj (realizationSequence ι hι s t).X₂ ⟶
      (extensionOfScalarsCochainComplex J f).obj P :=
  (extensionOfScalarsCochainComplex J f).map (realizationSequence ι hι s t).g ≫
    extensionCounitComplex G₀ ≫ s

omit hι in
/-- The ideal acts by zero on a complex restricted from `O₀`: the inclusion of its ideal part
vanishes. -/
theorem idealPartInclComplex_restrict (hι' : ι ≫
      Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
    (Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    idealPartInclComplex ι ((restrictComplex (f := f)).obj Y) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  change (idealPartIncl f ι).app ((SheafOfModules.restrictScalars (ringSheafMapOf J f)).obj
    (Y.X n)) = 0
  rw [idealPartIncl_eq, NatTrans.comp_app, idealAction_app_restrict ι hι', comp_zero]

omit hι [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The twisted extension is short exact: it is split in each degree. -/
theorem shortExact_twistSequence : (twistSequence t).ShortExact :=
  (HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (CochainComplex.twistSplitting t n).shortExact).map_of_exact _

/-- The difference sequence is short exact. -/
theorem shortExact_realizationSequence (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
    (hP : ∀ n, flatObjects O (P.X n)) : (realizationSequence ι hι s t).ShortExact :=
  CochainComplex.shortExact_baerDifference (shortExact_reductionSequence ι hι hS P hP)
    (shortExact_twistSequence t) _ _

/-- On the fibre product of `P` and `twist t` over `G₀`, the reduction of the projection to `P`
is the transpose of the projection to `G₀` followed by `s`. -/
theorem extensionOfScalars_map_baerSnd :
    (extensionOfScalarsCochainComplex J f).map
        (pullback.snd ((twistSequence t).g ≫ twistQuotientMap ι hι s t)
          (reductionSequence ι hι P).g) =
      (extensionOfScalarsCochainComplex J f).map
          (pullback.fst ((twistSequence t).g ≫ twistQuotientMap ι hι s t)
            (reductionSequence ι hι P).g ≫ (twistSequence t).g) ≫
        extensionCounitComplex G₀ ≫ s := by
  refine extensionOfScalars_map_eq _ _ ?_
  have h := reductionMapComplex_comp_restrict_counit (pullback.fst
    ((twistSequence t).g ≫ twistQuotientMap ι hι s t) (reductionSequence ι hι P).g ≫
      (twistSequence t).g)
  rw [← Category.assoc ((extensionOfScalarsCochainComplex J f).map _),
    CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ twistQuotientMap ι hι s t) h).trans
    ((Category.assoc _ _ _).trans pullback.condition))

/-- The map `(H₀ ⊗ I₀)|_O ⟶ (P₀ ⊗ I₀)|_O` induced by `realizationReduction`. -/
abbrev realizationIdealMap :
    ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (realizationSequence ι hι s t).X₂ ⟶ (realizationSequence ι hι s t).X₁ :=
  (restrictComplex (f := f)).map (((tensorRight O₀ I₀).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (realizationReduction ι hι s t))

/-- A map `x : A ⟶ H` whose reduction is `z` followed by `realizationReduction` induces `z ⊗ I₀`
on the ideal parts. -/
private theorem idealPart_map_comp_realizationIdealMap
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (x : A ⟶ (realizationSequence ι hι s t).X₂)
    (z : (extensionOfScalarsCochainComplex J f).obj A ⟶
      (extensionOfScalarsCochainComplex J f).obj P)
    (hz : (extensionOfScalarsCochainComplex J f).map x ≫ realizationReduction ι hι s t = z) :
    ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map x ≫
        realizationIdealMap ι hι s t =
      (restrictComplex (f := f)).map (((tensorRight O₀ I₀).mapHomologicalComplex
        (ComplexShape.up ℤ)).map z) := by
  subst hz
  conv_rhs => rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- **The ideal acts on `H` through `H₀ ⟶ P₀`**: the inclusion of the ideal part of `H` is the
map induced by `realizationReduction`, followed by the inclusion of `(P₀ ⊗ I₀)|_O`. -/
theorem idealPartInclComplex_realization :
    idealPartInclComplex ι (realizationSequence ι hι s t).X₂ =
      realizationIdealMap ι hι s t ≫ (realizationSequence ι hι s t).f := by
  let π := realizationπ ι hι s t
  have hπ : Epi (((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map π) :=
    HomologicalComplex.epi_of_epi_f _ fun n ↦ by
      have : Epi (π.f n) := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_epi π
      exact (idealPart f I₀).map_epi (π.f n)
  refine (cancel_epi (((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map π)).1 ?_
  have hg : π ≫ (realizationSequence ι hι s t).g =
      pullback.fst ((twistSequence t).g ≫ twistQuotientMap ι hι s t)
        (reductionSequence ι hι P).g ≫ (twistSequence t).g := cokernel.π_desc _ _ _
  have hred : (extensionOfScalarsCochainComplex J f).map π ≫ realizationReduction ι hι s t =
      (extensionOfScalarsCochainComplex J f).map (pullback.snd
        ((twistSequence t).g ≫ twistQuotientMap ι hι s t) (reductionSequence ι hι P).g) := by
    rw [extensionOfScalars_map_baerSnd, realizationReduction, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, hg]
  have hR := idealPart_map_comp_realizationIdealMap ι hι s t π _ hred
  change _ = ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map (pullback.snd
    ((twistSequence t).g ≫ twistQuotientMap ι hι s t) (reductionSequence ι hι P).g) at hR
  have hf : (realizationSequence ι hι s t).f =
      pullback.lift (f := (twistSequence t).g ≫ twistQuotientMap ι hι s t)
        (g := (reductionSequence ι hι P).g) 0 (reductionSequence ι hι P).f
        (by rw [zero_comp, (reductionSequence ι hι P).zero]) ≫ π := rfl
  have hX : idealPartInclComplex ι (CochainComplex.baerPullback (twistQuotientMap ι hι s t)) =
      ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map (pullback.snd
        ((twistSequence t).g ≫ twistQuotientMap ι hι s t) (reductionSequence ι hι P).g) ≫
      pullback.lift (f := (twistSequence t).g ≫ twistQuotientMap ι hι s t)
        (g := (reductionSequence ι hι P).g) 0 (reductionSequence ι hι P).f
        (by rw [zero_comp, (reductionSequence ι hι P).zero]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, comp_zero, ← idealPartInclComplex_naturality]
      change _ ≫ idealPartInclComplex ι ((restrictComplex (f := f)).obj
        (CochainComplex.twist t)) = 0
      rw [idealPartInclComplex_restrict ι hι, comp_zero]
    · rw [Category.assoc, pullback.lift_snd, ← idealPartInclComplex_naturality]
  rw [idealPartInclComplex_naturality, ← Category.assoc, hR, hf, hX, Category.assoc]

end Twist

/-- The reduction of a bounded above complex of `O`-modules is bounded above. -/
private instance isStrictlyLE_extensionOfScalars_obj
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (b : ℤ) [P.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE ((extensionOfScalarsCochainComplex J f).obj P) b :=
  isStrictlyLE_map_extensionOfScalars f b P inferInstance

/-! ### A resolution of `H` and its reduction -/

section Lift

variable (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
  {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
  {G₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ}
  (s : G₀ ⟶ (extensionOfScalarsCochainComplex J f).obj P)
  (t : G₀ ⟶ (((tensorRight O₀ I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((extensionOfScalarsCochainComplex J f).obj P))⟦(1 : ℤ)⟧)
  {P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
  (γ : P' ⟶ (realizationSequence ι hι s t).X₂)

/-- The reduction `P'₀ ⟶ G₀` of a map `γ : P' ⟶ H`: the transpose of `γ` followed by the
projection `H ⟶ G₀|_O`. -/
abbrev realizationTranspose : (extensionOfScalarsCochainComplex J f).obj P' ⟶ G₀ :=
  (extensionOfScalarsCochainComplex J f).map (γ ≫ (realizationSequence ι hι s t).g) ≫
    extensionCounitComplex G₀

/-- The map of kernels `(P'₀ ⊗ I₀)|_O ⟶ (P₀ ⊗ I₀)|_O` induced by `γ`. -/
abbrev realizationKernelMap :
    (reductionSequence ι hι P').X₁ ⟶ (realizationSequence ι hι s t).X₁ :=
  (restrictComplex (f := f)).map (((tensorRight O₀ I₀).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (realizationTranspose ι hι s t γ ≫ s))

/-- The map of quotients `P'₀|_O ⟶ G₀|_O` induced by `γ`. -/
abbrev realizationQuotientMap :
    (reductionSequence ι hι P').X₃ ⟶ (realizationSequence ι hι s t).X₃ :=
  (restrictComplex (f := f)).map (realizationTranspose ι hι s t γ)

/-- The square formed by `γ`, the two quotient maps and `realizationQuotientMap` commutes. -/
theorem realization_comm₂₃ :
    γ ≫ (realizationSequence ι hι s t).g =
      (reductionSequence ι hι P').g ≫ realizationQuotientMap ι hι s t γ :=
  (reductionMapComplex_comp_restrict_counit _).symm

/-- The square formed by `realizationKernelMap`, the two kernel inclusions and `γ` commutes. -/
theorem realization_comm₁₂ :
    realizationKernelMap ι hι s t γ ≫ (realizationSequence ι hι s t).f =
      (reductionSequence ι hι P').f ≫ γ := by
  have key : realizationKernelMap ι hι s t γ =
      ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map γ ≫
        realizationIdealMap ι hι s t := by
    refine (idealPart_map_comp_realizationIdealMap ι hι s t γ _ ?_).symm
    simp only [realizationTranspose, realizationReduction, CategoryTheory.Functor.map_comp,
      Category.assoc]
  rw [key, Category.assoc, ← idealPartInclComplex_realization]
  exact idealPartInclComplex_naturality ι γ

/-- **The reduction sequence of `P'` maps to `0 ⟶ (P₀ ⊗ I₀)|_O ⟶ H ⟶ G₀|_O ⟶ 0`**, by
`(δ' ≫ s) ⊗ I₀`, `γ` and `δ'`. -/
def realizationMap : reductionSequence ι hι P' ⟶ realizationSequence ι hι s t where
  τ₁ := realizationKernelMap ι hι s t γ
  τ₂ := γ
  τ₃ := realizationQuotientMap ι hι s t γ
  comm₁₂ := realization_comm₁₂ ι hι s t γ
  comm₂₃ := realization_comm₂₃ ι hι s t γ

/-! ### The reduction of a resolution of `H` is a quasi-isomorphism -/

section QuasiIso

variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
  (hf : Presheaf.IsLocallySurjective J (ringSheafMapOf J f).hom)
  (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
  (hP : ∀ n, flatObjects O (P.X n)) (hP' : ∀ n, flatObjects O (P'.X n))
  (b : ℤ) [P.IsStrictlyLE b] [P'.IsStrictlyLE b] [QuasiIso s] [QuasiIso γ]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Every morphism between zero objects is an isomorphism. -/
theorem isIso_of_isZero' {D : Type*} [Category D] [HasZeroMorphisms D] {X Y : D} (g : X ⟶ Y)
    (hX : IsZero X) (hY : IsZero Y) : IsIso g :=
  ⟨⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A cochain complex strictly concentrated in degrees `≤ a` has zero homology in each degree
`i > a`. -/
theorem isZero_homology_of_isStrictlyLE' {D : Type*} [Category D] [Abelian D]
    (X : CochainComplex D ℤ) (a : ℤ) [X.IsStrictlyLE a] (i : ℤ) (hi : a < i) :
    IsZero (X.homology i) :=
  ((HomologicalComplex.exactAt_iff _ i).2
    (ShortComplex.exact_of_isZero_X₂ _ (X.isZero_of_isStrictlyLE a i hi))).isZero_homology

include hf hS hP hP' b in
/-- **The inductive step of the source**: if `δ' ≫ s` is an isomorphism on cohomology in
degrees `≥ n`, it is one in degree `n - 1`. -/
theorem isIso_homologyMap_realization_step (n : ℤ)
    (h : ∀ i, n ≤ i → IsIso (HomologicalComplex.homologyMap
      (realizationTranspose ι hι s t γ ≫ s) i)) :
    IsIso (HomologicalComplex.homologyMap (realizationTranspose ι hι s t γ ≫ s) (n - 1)) := by
  have := (restrictScalarsFullyFaithful hf).faithful
  have hflX : ∀ i, flatObjects O₀ (((extensionOfScalarsCochainComplex J f).obj P').X i) :=
    fun i ↦ flatObjects_extensionOfScalars f (hP' i)
  have hflY : ∀ i, flatObjects O₀ (((extensionOfScalarsCochainComplex J f).obj P).X i) :=
    fun i ↦ flatObjects_extensionOfScalars f (hP i)
  have hSE' := shortExact_reductionSequence ι hι hS P' hP'
  have hE := shortExact_realizationSequence ι hι s t hS hP
  have T := homologyMap_tensorRight_of_isStrictlyLE.{d₀} O₀ I₀
    (realizationTranspose ι hι s t γ ≫ s) b hflX hflY n (fun i hi ↦ h i hi.le)
    (fun i hi ↦ by have := h i hi; infer_instance)
  have h₁ : Epi (HomologicalComplex.homologyMap (realizationQuotientMap ι hι s t γ) (n - 1)) := by
    refine HomologicalComplex.HomologySequence.epi_homologyMap_τ₃
      (realizationMap ι hι s t γ) hSE' hE (n - 1) (by dsimp [realizationMap]; infer_instance)
      (fun j hj ↦ ?_) (fun j hj ↦ by dsimp [realizationMap]; infer_instance)
    have hj' : j = n - 1 + 1 := hj.symm
    exact (epi_homologyMap_map_iff (SheafOfModules.restrictScalars (ringSheafMapOf J f)) _ j).2
      (T.2 j (by omega))
  have h₂ : Epi (HomologicalComplex.homologyMap (realizationTranspose ι hι s t γ) (n - 1)) :=
    (epi_homologyMap_map_iff (SheafOfModules.restrictScalars (ringSheafMapOf J f)) _ _).1 h₁
  have h₃ : Epi (HomologicalComplex.homologyMap (realizationTranspose ι hι s t γ ≫ s) (n - 1)) := by
    rw [HomologicalComplex.homologyMap_comp]; exact epi_comp _ _
  have T' := homologyMap_tensorRight_of_isStrictlyLE.{d₀} O₀ I₀
    (realizationTranspose ι hι s t γ ≫ s) b hflX hflY (n - 1) (fun i hi ↦ h i (by omega))
    (fun i hi ↦ by
      by_cases hin : i = n - 1
      · subst hin; exact h₃
      · have := h i (by omega); infer_instance)
  have h₄ : Mono (HomologicalComplex.homologyMap (realizationQuotientMap ι hι s t γ) (n - 1)) :=
    HomologicalComplex.HomologySequence.mono_homologyMap_τ₃
      (realizationMap ι hι s t γ) hSE' hE (n - 1)
      ((epi_homologyMap_map_iff (SheafOfModules.restrictScalars (ringSheafMapOf J f)) _ _).2
        (T'.2 (n - 1) le_rfl))
      (by dsimp [realizationMap]; infer_instance)
      (fun j hj ↦ (mono_homologyMap_map_iff (SheafOfModules.restrictScalars (ringSheafMapOf J f))
        _ j).2 (by have := T'.1 j (by have hj' : n - 1 + 1 = j := hj; omega); infer_instance))
  have h₅ : Mono (HomologicalComplex.homologyMap (realizationTranspose ι hι s t γ) (n - 1)) :=
    (mono_homologyMap_map_iff (SheafOfModules.restrictScalars (ringSheafMapOf J f)) _ _).1 h₄
  have : IsIso (HomologicalComplex.homologyMap (realizationTranspose ι hι s t γ) (n - 1)) :=
    isIso_of_mono_of_epi _
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

include hf hS hP hP' b in
/-- **The reduction `δ' : P'₀ ⟶ G₀` of a resolution of `H` is a quasi-isomorphism**, by
descending induction on the degree, starting above the common bound `b`. -/
theorem quasiIso_realizationTranspose : QuasiIso (realizationTranspose ι hι s t γ) := by
  have key : ∀ k : ℕ, ∀ i, b + 1 - k ≤ i → IsIso (HomologicalComplex.homologyMap
      (realizationTranspose ι hι s t γ ≫ s) i) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      exact isIso_of_isZero' _ (isZero_homology_of_isStrictlyLE' _ b i (by omega))
        (isZero_homology_of_isStrictlyLE' _ b i (by omega))
    | succ k ih =>
      intro i hi
      by_cases hik : b + 1 - k ≤ i
      · exact ih i hik
      · have hi' : i = b + 1 - k - 1 := by omega
        subst hi'
        exact isIso_homologyMap_realization_step ι hι s t γ hf hS hP hP' b (b + 1 - k) ih
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hu := key (b + 1 - i).toNat i (by omega)
  have hs : IsIso (HomologicalComplex.homologyMap s i) := inferInstance
  rw [HomologicalComplex.homologyMap_comp] at hu
  exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap s i)

end QuasiIso

end Lift

/-! ### The realization -/

section Realization

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The middle term of a short exact sequence of complexes whose outer terms vanish above `a`
vanishes above `a`. -/
theorem isStrictlyLE_X₂_of_shortExact {D : Type*} [Category D] [Abelian D]
    {S : ShortComplex (CochainComplex D ℤ)} (hS : S.ShortExact) (a : ℤ) [S.X₁.IsStrictlyLE a]
    [S.X₃.IsStrictlyLE a] : S.X₂.IsStrictlyLE a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have h := hS.map_of_exact (HomologicalComplex.eval D (ComplexShape.up ℤ) i)
  exact h.exact.isZero_X₂ ((S.X₁.isZero_of_isStrictlyLE a i hi).eq_of_src _ _)
    ((S.X₃.isZero_of_isStrictlyLE a i hi).eq_of_tgt _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A functor preserving zero morphisms keeps a complex vanishing above `a`. -/
theorem isStrictlyLE_mapHomologicalComplex' {D D' : Type*} [Category D] [Category D']
    [HasZeroMorphisms D] [HasZeroMorphisms D'] (F : D ⥤ D') [F.PreservesZeroMorphisms]
    (K : CochainComplex D ℤ) (a : ℤ) [K.IsStrictlyLE a] :
    CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact F.map_isZero (K.isZero_of_isStrictlyLE a i hi)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The algebra of the realization**, with the objects abstract: the connecting classes of the
two lifts, transported along their models, differ by the restriction of `ξ`. -/
theorem realization_sub_eq' {D₀ D : Type*} [Category D₀] [Category D] [Preadditive D₀]
    [Preadditive D] [HasShift D₀ ℤ] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    (r : D₀ ⥤ D) [r.CommShift ℤ] [r.Additive]
    {K₁ X₀ X₀' Z₀ Y₀ Y₀' K₂ : D₀} {X X' Z Y Y' : D}
    (M : X₀ ≅ K₁) (M' : X₀' ≅ K₁) (N : Y₀ ≅ K₂) (N' : Y₀' ≅ K₂)
    (qδ : X₀' ⟶ Z₀) (qs : Z₀ ⟶ X₀) (hM : qδ ≫ qs ≫ M.hom = M'.hom)
    (qφ : Y₀' ⟶ Y₀) (hN : qφ ≫ N.hom = N'.hom)
    (a : r.obj X₀ ≅ X) (a' : r.obj X₀' ≅ X') (aZ : r.obj Z₀ ≅ Z)
    (b : Y ≅ r.obj Y₀) (b' : Y' ≅ r.obj Y₀')
    (eδ : X' ⟶ Z) (es : Z ⟶ X) (hδ : r.map qδ ≫ aZ.hom = a'.hom ≫ eδ)
    (hs : r.map qs ≫ a.hom = aZ.hom ≫ es)
    (φ : Y' ⟶ Y) (hb : b'.hom ≫ r.map qφ = φ ≫ b.hom)
    (δ : X ⟶ Y⟦(1 : ℤ)⟧) (δ' : X' ⟶ Y'⟦(1 : ℤ)⟧) (δE δT : Z ⟶ Y⟦(1 : ℤ)⟧)
    (hnat : eδ ≫ δE = δ' ≫ φ⟦(1 : ℤ)⟧') (ι1 : Y ⟶ Y) (hι1 : ι1 = 𝟙 Y)
    (hBaer : δE = es ≫ δ - δT ≫ ι1⟦(1 : ℤ)⟧')
    (θ : Z₀ ⟶ Y₀⟦(1 : ℤ)⟧)
    (hT : r.map θ = aZ.hom ≫ δT ≫ b.hom⟦(1 : ℤ)⟧' ≫ (r.commShiftIso (1 : ℤ)).inv.app Y₀)
    (ξ : K₁ ⟶ K₂⟦(1 : ℤ)⟧) (hξ : qs ≫ M.hom ≫ ξ ≫ N.inv⟦(1 : ℤ)⟧' = θ) :
    (r.map M.inv ≫ a.hom ≫ δ ≫ (b.hom ≫ r.map N.hom)⟦(1 : ℤ)⟧') -
        (r.map M'.inv ≫ a'.hom ≫ δ' ≫ (b'.hom ≫ r.map N'.hom)⟦(1 : ℤ)⟧') =
      r.map ξ ≫ (r.commShiftIso (1 : ℤ)).hom.app K₂ := by
  subst hι1
  have hM' : M'.inv ≫ qδ ≫ qs = M.inv := by
    rw [← cancel_mono M.hom, Category.assoc, Category.assoc, hM, Iso.inv_hom_id, Iso.inv_hom_id]
  have ha : r.map (qδ ≫ qs) ≫ a.hom = a'.hom ≫ eδ ≫ es := by
    rw [r.map_comp, Category.assoc, hs, reassoc_of% hδ]
  have hE' : (eδ ≫ es) ≫ δ - δ' ≫ φ⟦(1 : ℤ)⟧' =
      a'.inv ≫ r.map (qδ ≫ θ) ≫ (r.commShiftIso (1 : ℤ)).hom.app _ ≫ b.inv⟦(1 : ℤ)⟧' := by
    have h₁ : (eδ ≫ es) ≫ δ - δ' ≫ φ⟦(1 : ℤ)⟧' = eδ ≫ δT := by
      rw [← hnat, hBaer]
      simp
    rw [h₁, r.map_comp, hT]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rw [reassoc_of% hδ, Iso.inv_hom_id_assoc]
  have key := sub_eq_shiftedRestriction' r M.inv M'.inv (qδ ≫ qs) hM' N.hom N'.hom qφ hN a a' b b'
    (eδ ≫ es) ha φ hb δ δ' _ rfl (qδ ≫ θ) hE'
  rw [key]
  congr 2
  rw [← hξ]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [reassoc_of% hM, Iso.inv_hom_id_assoc]

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}
  (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)
  (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
  (hf : Presheaf.IsLocallySurjective J (ringSheafMapOf J f).hom)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The connecting morphism of the twisted extension is `t`. -/
theorem triangleOfSESδ_twist
    {A G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ}
    (t : G ⟶ A⟦(1 : ℤ)⟧) (ht : (CochainComplex.twistShortComplex t).ShortExact) :
    DerivedCategory.triangleOfSESδ ht =
      DerivedCategory.Q.map t ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app A := by
  rw [Deformation.Artin.triangleOfSESδ_eq_homOfDegreewiseSplit _
    (CochainComplex.twistSplitting t) ht, CochainComplex.homOfDegreewiseSplit_twistSplitting]

include hf in
/-- **Every class of `Ext¹(K₀, K₀ ⊗^L I)` is realized** (the surjectivity half of Stacks 0DIZ
(2)): for a lift `L` of `K₀` and `ξ`, there is a lift `L'` whose connecting class differs from
that of `L` by the restriction of `ξ`. -/
theorem exists_connectingClass_sub_flatReduction_eq
    (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀)
    (ξ : K₀.obj ⟶ ((derivedTensorRight.{d₀} I₀).obj K₀.obj)⟦(1 : ℤ)⟧) :
    ∃ L' : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀,
      connectingClass (flatReduction.{d, d₀} f ι hι hS) L -
          connectingClass (flatReduction.{d, d₀} f ι hι hS) L' =
        shiftedRestriction (flatReduction.{d, d₀} f ι hι hS) ξ := by
  -- a bounded above flat model `P` of `L`
  obtain ⟨n, hn⟩ := L.K.property
  have : L.K.obj.IsLE n := hn
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE L.K.obj n
  obtain ⟨P, p, -, hp, hPf, hPle⟩ : ∃ (P : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) (p : P ⟶ K) (_ : ∀ i, Epi (p.f i))
      (_ : QuasiIso p) (_ : ∀ i, flatObjects O (P.X i)), P.IsStrictlyLE n :=
    exists_isFlat_quasiIso_isStrictlyLE O n K
  have hPc := isFlatCellular_of_isStrictlyLE O P n hPf
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := p)).2 hp
  let w : DerivedCategory.Q.obj P ≅ L.K.obj := asIso (DerivedCategory.Q.map p) ≪≫ e.symm
  let M := liftModelIso.{d, d₀} f L hPc w
  let N := liftModelIdealIso.{d, d₀} f I₀ L hPc w
  -- the fraction `t ∘ s⁻¹` representing `ξ`
  obtain ⟨G₀, hG₀, s, hs, t, hst⟩ := DerivedCategory.right_fac_of_isStrictlyLE
    (M.hom ≫ ξ ≫ N.inv⟦(1 : ℤ)⟧' ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app _) n
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).1 hs
  -- the complex `H` and a bounded above flat resolution `P'` of it
  have hE := shortExact_realizationSequence ι hι s t hS hPf
  have : CochainComplex.IsStrictlyLE (realizationSequence ι hι s t).X₁ n :=
    isStrictlyLE_mapHomologicalComplex' (idealPart f I₀) P n
  have : CochainComplex.IsStrictlyLE (realizationSequence ι hι s t).X₃ n :=
    isStrictlyLE_mapHomologicalComplex' (SheafOfModules.restrictScalars (ringSheafMapOf J f)) G₀ n
  have := isStrictlyLE_X₂_of_shortExact hE n
  obtain ⟨P', γ, -, hγ, hP'f, hP'le⟩ : ∃ (P' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) (γ : P' ⟶ (realizationSequence ι hι s t).X₂)
      (_ : ∀ i, Epi (γ.f i)) (_ : QuasiIso γ) (_ : ∀ i, flatObjects O (P'.X i)),
      P'.IsStrictlyLE n :=
    exists_isFlat_quasiIso_isStrictlyLE O n _
  have hP'c := isFlatCellular_of_isStrictlyLE O P' n hP'f
  have hδ := quasiIso_realizationTranspose.{d₀} ι hι s t γ hf hS hPf hP'f n
  have : IsIso (DerivedCategory.Q.map (realizationTranspose ι hι s t γ ≫ s)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  -- the new lift
  let K' : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    ⟨DerivedCategory.Q.obj P', ⟨n, (inferInstance : (DerivedCategory.Q.obj P').IsLE n)⟩⟩
  let L' : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀ :=
    { K := K'
      identification := (baseModelIso.{d, d₀} f hP'c (Iso.refl (DerivedCategory.Q.obj P'))).symm ≪≫
        asIso (DerivedCategory.Q.map (realizationTranspose ι hι s t γ ≫ s)) ≪≫ M }
  refine ⟨L', ?_⟩
  let M' := liftModelIso.{d, d₀} f L' hP'c (Iso.refl _)
  let N' := liftModelIdealIso.{d, d₀} f I₀ L' hP'c (Iso.refl _)
  have hM : DerivedCategory.Q.map (realizationTranspose ι hι s t γ) ≫ DerivedCategory.Q.map s ≫
      M.hom = M'.hom := by
    change _ = (baseModelIso.{d, d₀} f hP'c (Iso.refl (DerivedCategory.Q.obj P'))).hom ≫
      ((baseModelIso.{d, d₀} f hP'c (Iso.refl (DerivedCategory.Q.obj P'))).inv ≫
        DerivedCategory.Q.map (realizationTranspose ι hι s t γ ≫ s) ≫ M.hom)
    rw [Iso.hom_inv_id_assoc, DerivedCategory.Q.map_comp (realizationTranspose ι hι s t γ) s,
      Category.assoc]
  have hN : DerivedCategory.Q.map (((tensorRight O₀ I₀).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (realizationTranspose ι hι s t γ ≫ s)) ≫ N.hom = N'.hom := by
    have h₁ := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P hPc
    have h₂ := isIso_derivedTensorRightCounit_app_extensionOfScalars.{d, d₀} f I₀ P' hP'c
    have hn := (derivedTensorRightCounit.{d₀} I₀).naturality
      (realizationTranspose ι hι s t γ ≫ s)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    have hn' : DerivedCategory.Q.map (((tensorRight O₀ I₀).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (realizationTranspose ι hι s t γ ≫ s)) ≫
        inv ((derivedTensorRightCounit.{d₀} I₀).app
          ((extensionOfScalarsCochainComplex J f).obj P)) =
        inv ((derivedTensorRightCounit.{d₀} I₀).app
          ((extensionOfScalarsCochainComplex J f).obj P')) ≫
          (derivedTensorRight.{d₀} I₀).map
            (DerivedCategory.Q.map (realizationTranspose ι hι s t γ ≫ s)) := by
      rw [IsIso.comp_inv_eq]
      exact (((congrArg (inv ((derivedTensorRightCounit.{d₀} I₀).app
        ((extensionOfScalarsCochainComplex J f).obj P')) ≫ ·) hn).trans
          (IsIso.inv_hom_id_assoc _ _)).symm).trans (Category.assoc _ _ _).symm
    rw [liftModelIdealIso_hom, liftModelIdealIso_hom, ← hM, ← Category.assoc, hn', Category.assoc,
      ← CategoryTheory.Functor.map_comp,
      DerivedCategory.Q.map_comp (realizationTranspose ι hι s t γ) s, Category.assoc]
  have hT := restrict_triangleOfSESδ.{d, d₀} (f := f)
    (HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦
      (CochainComplex.twistSplitting t i).shortExact)
  rw [triangleOfSESδ_twist] at hT
  have hξ : DerivedCategory.Q.map s ≫ M.hom ≫ ξ ≫ N.inv⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map t ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app _ := by
    have h2 : DerivedCategory.Q.map s ≫ (M.hom ≫ ξ ≫ N.inv⟦(1 : ℤ)⟧' ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app _) = DerivedCategory.Q.map t := by
      rw [hst, IsIso.hom_inv_id_assoc]
    rw [← h2]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  have hBaer := CochainComplex.triangleOfSESδ_baerDifference
    (shortExact_reductionSequence ι hι hS P (flatObjects_X_of_isFlatCellular hPc))
    (shortExact_twistSequence t) (twistQuotientMap ι hι s t) (twistKernelMap ι hι t)
  have hnat := DerivedCategory.triangleOfSESδ_naturality
    (shortExact_reductionSequence ι hι hS P' (flatObjects_X_of_isFlatCellular hP'c)) hE
    (realizationMap ι hι s t γ)
  rw [connectingClass_flatReduction_eq.{d, d₀} f ι hι hS L hPc w,
    connectingClass_flatReduction_eq.{d, d₀} f ι hι hS L' hP'c (Iso.refl _),
    shiftedRestriction_apply]
  exact realization_sub_eq' (restrictionOnDerived.{d, d₀} f) M M' N N'
    (DerivedCategory.Q.map (realizationTranspose ι hι s t γ)) (DerivedCategory.Q.map s) hM
    _ hN ((restrictionFactors.{d, d₀} f).app _) ((restrictionFactors.{d, d₀} f).app _)
    ((restrictionFactors.{d, d₀} f).app G₀)
    ((restrictionFactors.{d, d₀} f).symm.app _) ((restrictionFactors.{d, d₀} f).symm.app _)
    _ _ ((restrictionFactors.{d, d₀} f).hom.naturality _)
    ((restrictionFactors.{d, d₀} f).hom.naturality s)
    _ ((restrictionFactors.{d, d₀} f).inv.naturality _).symm
    _ _ _ _ hnat.symm _ (DerivedCategory.Q.map_id _) hBaer _ hT ξ hξ

end Realization

end Deformation.ComplexLift

end
