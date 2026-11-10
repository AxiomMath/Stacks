module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartTensorFinite
public import StacksFrontier.Homology.DoubleExtend
import StacksCore.Tactic.StacksAttribute

/-!
# The naive cotangent complex of a morphism locally of finite presentation, étale locally

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite presentation.  Stacks 0D0Z asserts that the naive cotangent complex `NL_{X/Y}`
of Stacks 0D0V is, étale locally on `X`, quasi-isomorphic to a complex
`… → 0 → 𝓕⁻¹ → 𝓕⁰ → 0 → …` of quasi-coherent `𝒪_X`-modules with `𝓕⁰` of finite presentation and
`𝓕⁻¹` of finite type.  This file proves it, as
`AlgebraicGeometry.Space.exists_quasiIso_naiveCotangentComplex_of_isLocallyOfFinitePresentation`.

## The proof

The charts `V = Spec A` of `X` carrying an affine chart diagram `V → W = Spec R` over `f` cover
`X` (`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`), so it suffices to work on
the small étale site of `X` localized at such a `V`.  There:

* `A` is a finitely presented `R`-algebra
  (`AlgebraicGeometry.Space.algebraFinitePresentation_chartDiagram`), so it has a presentation
  `P` with finitely many variables and relations, and `NL(P)` has a finite free degree `0` term
  and a finitely generated degree `-1` term `I/I²`;
* the comparison `NL(P) ⟶ NL_{A/R}` of Stacks 00S1 is a homotopy equivalence, hence stays a
  quasi-isomorphism after applying the additive functor `N ↦ N ⊗_A 𝒪`
  (`Stacks.NaiveCotangentFinitePresentation.quasiIso_nlDoubleMap`);
* the canonical chain map `(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V`
  (`AlgebraicGeometry.Space.chartCanonicalNaiveCotangentMap`) is a quasi-isomorphism: on the
  kernels of the differentials it is the identification of `H⁻¹(NL_{X/Y})|_V` with
  `H₁(L_{A/R}) ⊗_A 𝒪` (`AlgebraicGeometry.Space.isIso_chartKernelMap`, which uses that
  `- ⊗_A 𝒪` is exact, the stalks being ind-étale and so flat over `A`), and on the cokernels it is
  the identification of `Ω_{X/Y}|_V` with `Ω_{A/R} ⊗_A 𝒪`
  (`AlgebraicGeometry.Space.isIso_chartCokernelMap`, Stacks 0D08 in degree `0` at the geometric
  points together with Stacks 08TP);
* `N ⊗_A 𝒪` is quasi-coherent, of finite presentation for `N` finitely presented and of finite
  type for `N` finite (`AlgebraicGeometry.Space.isFinitePresentationOnSite_chartTensorFunctor_obj`,
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_chartTensorFunctor_obj`).

This is the source's proof read on a site: the source reduces to schemes by Stacks 0D0W and 0D0X
and then quotes Stacks 0D0K; here the reduction and the scheme case are carried out together on
the affine charts of the small étale site.

## Main results

* `AlgebraicGeometry.Space.quasiIso_chartCanonicalNaiveCotangentMap`
* `AlgebraicGeometry.Space.exists_chart_quasiIso_naiveCotangentComplex`: the statement on one
  affine chart.
* `AlgebraicGeometry.Space.exists_quasiIso_naiveCotangentComplex_of_isLocallyOfFinitePresentation`:
  **Stacks 0D0Z**.

## References

* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
* [Stacks Project, Tag 0D0K](https://stacks.math.columbia.edu/tag/0D0K)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 0D08](https://stacks.math.columbia.edu/tag/0D08)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
  HomologicalComplex Stacks.NaiveCotangentFinitePresentation

universe u

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace CategoryTheory.Functor

/-- A commutative square survives conjugating its right-hand edge by isomorphisms inside a
functor. -/
theorem map_conj_comm {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X₀ X₁ Y₀ Y₁ : C}
    {P Q : D} (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁) (g : Y₀ ⟶ Y₁) (a : P ⟶ F.obj Y₀) (b : Q ⟶ F.obj Y₁)
    (t : P ⟶ Q) (h : a ≫ F.map g = t ≫ b) :
    (a ≫ F.map e₀.inv) ≫ F.map (e₀.hom ≫ g ≫ e₁.inv) = t ≫ b ≫ F.map e₁.inv := by
  rw [F.map_comp, F.map_comp, Category.assoc, ← Category.assoc (F.map e₀.inv), ← F.map_comp,
    e₀.inv_hom_id, F.map_id, Category.id_comp, ← Category.assoc, h, Category.assoc]

/-- A morphism followed by the image of a zero morphism under a functor preserving zero morphisms
is zero. -/
theorem comp_map_eq_zero {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {Y Z : C} {P : D}
    {g : Y ⟶ Z} (hg : g = 0) (a : P ⟶ F.obj Y) : a ≫ F.map g = 0 := by
  rw [hg, F.map_zero, comp_zero]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

attribute [local instance] chartDiagramAlgebraInst

/-- **The complex `(NL_{A/R}) ⊗_A 𝒪`** on the slice at `V`. -/
abbrev chartCanonicalDouble :
    CochainComplex (_root_.SheafOfModules.{u + 1} (chartSliceRingSheaf B S hS f d)) ℤ :=
  double ((chartTensorFunctor B S hS f d).map (nlModD (chartCanonicalGenerators B S hS f d)))
    ComplexShape.upIntRelNegOneZero

/-- **The canonical chain map `(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V`**, made of the two components
`AlgebraicGeometry.Space.chartConormalTensorHom` and `AlgebraicGeometry.Space.chartTensorTensorHom`
read in the terms of `NL_{X/Y}`. -/
def chartCanonicalNaiveCotangentMap :
    chartCanonicalDouble B S hS f d ⟶ chartNaiveCotangentSlice B S hS f d :=
  mkHomFromDouble ComplexShape.upIntRelNegOneZero (by decide)
    (chartConormalTensorHom B S hS f d ≫ (_root_.SheafOfModules.overFunctor.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
      (doubleXIso₀ (chartCS B S hS f).f ComplexShape.upIntRelNegOneZero).inv)
    (chartTensorTensorHom B S hS f d ≫ (_root_.SheafOfModules.overFunctor.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
      (doubleXIso₁ (chartCS B S hS f).f ComplexShape.upIntRelNegOneZero (by decide)).inv)
    (by
      change _ ≫ (_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
        ((naiveCotangentComplex B S hS f).d (-1) 0) = _
      have hd : (naiveCotangentComplex B S hS f).d (-1) 0 =
          (doubleXIso₀ (chartCS B S hS f).f ComplexShape.upIntRelNegOneZero).hom ≫
            (chartCS B S hS f).f ≫
            (doubleXIso₁ (chartCS B S hS f).f ComplexShape.upIntRelNegOneZero (by decide)).inv :=
        double_d _ _ (by decide)
      rw [hd]
      exact Functor.map_conj_comm _ _ _ _ _ _ _ (chartTensorHom_comm B S hS f d).symm)
    (by
      intro k _
      change _ ≫ (_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
        ((naiveCotangentComplex B S hS f).d 0 k) = 0
      exact Functor.comp_map_eq_zero (_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U)
        (double_d_eq_zero₀ (chartCS B S hS f).f ComplexShape.upIntRelNegOneZero 0 k (by decide)) _)

/-- **The canonical chain map is a quasi-isomorphism as soon as it is one on the kernels and on
the cokernels of the two differentials**, read in the terms of the components. -/
theorem quasiIso_chartCanonicalNaiveCotangentMap_of
    (hK : IsIso (kernel.map ((chartTensorFunctor B S hS f d).map
      (nlModD (chartCanonicalGenerators B S hS f d)))
      ((_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
            (chartCS B S hS f).f)
      (chartConormalTensorHom B S hS f d) (chartTensorTensorHom B S hS f d)
      (chartTensorHom_comm B S hS f d)))
    (hC : IsIso (cokernel.map ((chartTensorFunctor B S hS f d).map
      (nlModD (chartCanonicalGenerators B S hS f d)))
      ((_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
            (chartCS B S hS f).f)
      (chartConormalTensorHom B S hS f d) (chartTensorTensorHom B S hS f d)
      (chartTensorHom_comm B S hS f d))) :
    QuasiIso (chartCanonicalNaiveCotangentMap B S hS f d) := by
  have h01 : (-1 : ℤ) ≠ 0 := by decide
  have hX₁ : (chartCanonicalDouble B S hS f d).X (-1) =
      (chartTensorFunctor B S hS f d).obj (nlMod₁ (chartCanonicalGenerators B S hS f d)) :=
    dite_eq_left rfl
  have hX₀ : (chartCanonicalDouble B S hS f d).X 0 =
      (chartTensorFunctor B S hS f d).obj (nlMod₀ (chartCanonicalGenerators B S hS f d)) := by
    dsimp only [chartCanonicalDouble, double]
    rw [ite_eq_right h01.symm, ite_eq_left rfl]
  have hN₁ : (naiveCotangentComplex B S hS f).X (-1) = (chartCS B S hS f).X₁ :=
    dite_eq_left rfl
  have hN₀ : (naiveCotangentComplex B S hS f).X 0 = (chartCS B S hS f).X₂ :=
    Stacks.SheafOfModules.naiveCotangentComplex_X_zero.{u, u + 1, u, u}
      (SmallEtale.topology B S hS X.1) (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
  have hL₁ : (chartNaiveCotangentSlice B S hS f d).X (-1) = chartSliceModule B S hS f d
      (chartCS B S hS f).X₁ := congrArg (_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).obj hN₁
  have hL₀ : (chartNaiveCotangentSlice B S hS f d).X 0 = chartSliceModule B S hS f d
      (chartCS B S hS f).X₂ := congrArg (_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).obj hN₀
  have hdK : (chartCanonicalDouble B S hS f d).d (-1) 0 = eqToHom hX₁ ≫
      (chartTensorFunctor B S hS f d).map (nlModD (chartCanonicalGenerators B S hS f d)) ≫
        eqToHom hX₀.symm := double_d _ _ h01
  have hdN : (naiveCotangentComplex B S hS f).d (-1) 0 = eqToHom hN₁ ≫
      (chartCS B S hS f).f ≫ eqToHom hN₀.symm :=
    double_d (chartCS B S hS f).f ComplexShape.upIntRelNegOneZero h01
  have hdL : (chartNaiveCotangentSlice B S hS f d).d (-1) 0 = eqToHom hL₁ ≫
      (_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
            (chartCS B S hS f).f ≫ eqToHom hL₀.symm := by
    change (_root_.SheafOfModules.overFunctor.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
      ((naiveCotangentComplex B S hS f).d (-1) 0) = _
    rw [hdN, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    rfl
  have hpc : (chartCanonicalNaiveCotangentMap B S hS f d).f (-1) = eqToHom hX₁ ≫
      chartConormalTensorHom B S hS f d ≫ eqToHom hL₁.symm := by
    refine (mkHomFromDouble_f₀ _ _ _ _ _ _).trans ?_
    change eqToHom hX₁ ≫ chartConormalTensorHom B S hS f d ≫
      (_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
            (eqToHom hN₁.symm) = _
    rw [eqToHom_map]
    rfl
  have hpt : (chartCanonicalNaiveCotangentMap B S hS f d).f 0 = eqToHom hX₀ ≫
      chartTensorTensorHom B S hS f d ≫ eqToHom hL₀.symm := by
    refine (mkHomFromDouble_f₁ _ _ _ _ _ _).trans ?_
    change eqToHom hX₀ ≫ chartTensorTensorHom B S hS f d ≫
      (_root_.SheafOfModules.overFunctor.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
            (eqToHom hN₀.symm) = _
    rw [eqToHom_map]
    rfl
  refine CochainComplex.quasiIso_of_isZero_X_of_isIso_kernel_cokernel _
    (fun i h₁ h₂ => isZero_double_X _ _ i h₁ h₂) (fun i h₁ h₂ => ?_) ?_ ?_
  · exact Functor.map_isZero (_root_.SheafOfModules.overFunctor.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U)
      (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u + 1, u, u}
        (SmallEtale.topology B S hS X.1) (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) i h₁ h₂)
  · exact isIso_kernel_map_of_eqToHom hX₁ hX₀ hL₁ hL₀ hdK hdL hpc hpt _
      (chartTensorHom_comm B S hS f d) hK
  · exact isIso_cokernel_map_of_eqToHom hX₁ hX₀ hL₁ hL₀ hdK hdL hpc hpt _
      (chartTensorHom_comm B S hS f d) hC

variable (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
  (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))

include hU hW in
/-- **The canonical chain map `(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V` is a quasi-isomorphism** on an
affine chart diagram. -/
theorem quasiIso_chartCanonicalNaiveCotangentMap :
    QuasiIso (chartCanonicalNaiveCotangentMap B S hS f d) :=
  quasiIso_chartCanonicalNaiveCotangentMap_of B S hS f d (isIso_chartKernelMap B S hS f d hU hW)
    (isIso_chartCokernelMap B S hS f d hU hW)

include hU hW in
/-- **Stacks 0D0Z on one affine chart.**  If `f` is locally of finite presentation then on the
slice of the small étale site of `X` at an affine chart `V = Spec A` carrying an affine chart
diagram over `f`, `NL_{X/Y}|_V` receives a quasi-isomorphism from a complex
`0 → 𝓕⁻¹ → 𝓕⁰ → 0` of quasi-coherent modules with `𝓕⁰` of finite presentation and `𝓕⁻¹` of
finite type: `NL(P) ⊗_A 𝒪` for a presentation `P` of `A` with finitely many variables and
relations. -/
theorem exists_chart_quasiIso_naiveCotangentComplex
    (hf : IsLocallyOfFinitePresentation B S hS f.hom) :
    ∃ (F : CochainComplex (_root_.SheafOfModules.{u + 1} (chartSliceRingSheaf B S hS f d)) ℤ)
      (φ : F ⟶ chartNaiveCotangentSlice B S hS f d),
      (∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (F.X i)) ∧ QuasiIso φ ∧
        (F.X 0).IsQuasicoherentOnSite ∧ (F.X 0).IsFinitePresentationOnSite ∧
        (F.X (-1)).IsQuasicoherentOnSite ∧ (F.X (-1)).IsFiniteTypeOnSite := by
  have : Algebra.FinitePresentation (chartTargetRing B S hS f d) (chartSourceRing B S hS f d) :=
    algebraFinitePresentation_chartDiagram B S hS f hf d hU hW
  let P : Algebra.Presentation (chartTargetRing B S hS f d) (chartSourceRing B S hS f d)
      (ULift.{u} (Fin (Algebra.Presentation.ofFinitePresentationVars (chartTargetRing B S hS f d)
        (chartSourceRing B S hS f d))))
      (ULift.{u} (Fin (Algebra.Presentation.ofFinitePresentationRels (chartTargetRing B S hS f d)
        (chartSourceRing B S hS f d)))) :=
    (Algebra.Presentation.ofFinitePresentation (chartTargetRing B S hS f d)
      (chartSourceRing B S hS f d)).reindex Equiv.ulift Equiv.ulift
  have : Module.FinitePresentation (chartSourceRing B S hS f d) (nlMod₀ P.toGenerators) :=
    finitePresentation_cotangentSpace P.toGenerators
  have : Module.Finite (chartSourceRing B S hS f d) (nlMod₁ P.toGenerators) := finite_cotangent P
  let Fa := chartTensorFunctor B S hS f d
  have hX₁ : (double (Fa.map (nlModD P.toGenerators)) ComplexShape.upIntRelNegOneZero).X (-1) =
      Fa.obj (nlMod₁ P.toGenerators) := dite_eq_left rfl
  have hX₀ : (double (Fa.map (nlModD P.toGenerators)) ComplexShape.upIntRelNegOneZero).X 0 =
      Fa.obj (nlMod₀ P.toGenerators) := by
    dsimp only [double]
    rw [ite_eq_right (by decide), ite_eq_left rfl]
  refine ⟨double (Fa.map (nlModD P.toGenerators)) ComplexShape.upIntRelNegOneZero,
    nlDoubleMap P.toGenerators Fa ComplexShape.upIntRelNegOneZero ≫
      chartCanonicalNaiveCotangentMap B S hS f d,
    fun i h₁ h₂ => isZero_double_X _ _ i h₁ h₂, ?_, ?_, ?_, ?_, ?_⟩
  · have := quasiIso_nlDoubleMap P.toGenerators Fa ComplexShape.upIntRelNegOneZero
    have := quasiIso_chartCanonicalNaiveCotangentMap B S hS f d hU hW
    infer_instance
  · rw [hX₀]
    exact isQuasicoherentOnSite_chartTensorFunctor_obj B S hS f d _
  · rw [hX₀]
    exact isFinitePresentationOnSite_chartTensorFunctor_obj B S hS f d _
  · rw [hX₁]
    exact isQuasicoherentOnSite_chartTensorFunctor_obj B S hS f d _
  · rw [hX₁]
    exact isFiniteTypeOnSite_chartTensorFunctor_obj B S hS f d _

/-- **Stacks 0D0Z.**  Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is locally of finite presentation.  Then `NL_{X/Y}` is étale locally on `X`
quasi-isomorphic to a complex `… → 0 → 𝓕⁻¹ → 𝓕⁰ → 0 → …` of quasi-coherent `𝒪_X`-modules with
`𝓕⁰` of finite presentation and `𝓕⁻¹` of finite type.

"Étale locally on `X`" is read as on the small étale site of `X`: every étale scheme chart `U` of
`X` has an étale covering `{Wᵢ ⟶ U}` such that the restriction of `NL_{X/Y}` to the small étale
site of `X` localized at each `Wᵢ` receives a quasi-isomorphism `φ` from a complex `F` of sheaves
of modules over the restricted structure sheaf which vanishes outside degrees `-1` and `0`, whose
degree `0` term is quasi-coherent and of finite presentation and whose degree `-1` term is
quasi-coherent and of finite type.  `NL_{X/Y}` is `AlgebraicGeometry.Space.naiveCotangentComplex`
(Stacks 0D0V) and the restriction is `SheafOfModules.overFunctor` applied termwise. -/
@[stacks 0D0Z "the whole statement.  `etale locally on X` is read on the small etale site of `X`: \
every etale chart `U` of `X` has an etale covering `{W_i -> U}` (a covering sieve of \
`SmallEtale.topology`) such that `NL_{X/Y}` restricted to the slice at each `W_i` receives a \
quasi-isomorphism from a complex `F` concentrated in degrees -1 and 0 with `F^0` quasi-coherent \
and of finite presentation and `F^{-1}` quasi-coherent and of finite type -- the two degrees \
carrying DIFFERENT finiteness conditions, exactly as the tag states.  The source's `NL_{X/Y} is \
quasi-isomorphic to F` is realized by a quasi-isomorphism FROM `F`, which is the same content.  \
The only hypothesis is the source's: `f` locally of finite presentation \
(`IsLocallyOfFinitePresentation`, Stacks 03XP).  Nothing is assumed: the covering is by the \
affine chart diagrams, on which `F = NL(P) (x)_A O` for a finite presentation `P` of the chart \
ring `A` over `R`, the comparison with `(NL_{A/R}) (x)_A O` is the Stacks 00S1 homotopy \
equivalence, and `(NL_{A/R}) (x)_A O -> NL_{X/Y}|_V` is proved to be a quasi-isomorphism on \
kernels (H^{-1} = H_1(L_{A/R}) (x)_A O, using flatness of the etale stalks) and on cokernels \
(Omega_{X/Y}|_V = Omega_{A/R} (x)_A O, Stacks 0D08 in degree 0 and Stacks 08TP)"]
theorem exists_quasiIso_naiveCotangentComplex_of_isLocallyOfFinitePresentation
    (hf : IsLocallyOfFinitePresentation B S hS f.hom) (U : SmallEtale B S hS X.1) :
    ∃ (I : Type (u + 1)) (W : I → SmallEtale B S hS X.1) (g : ∀ i, W i ⟶ U),
      Sieve.ofArrows W g ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ i, ∃ (F : CochainComplex (_root_.SheafOfModules.{u + 1}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).over
            (W i))) ℤ)
        (φ : F ⟶ ((_root_.SheafOfModules.overFunctor.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
              (W i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (naiveCotangentComplex B S hS f)),
        (∀ j : ℤ, j ≠ -1 → j ≠ 0 → IsZero (F.X j)) ∧ QuasiIso φ ∧
          (F.X 0).IsQuasicoherentOnSite ∧ (F.X 0).IsFinitePresentationOnSite ∧
          (F.X (-1)).IsQuasicoherentOnSite ∧ (F.X (-1)).IsFiniteTypeOnSite := by
  refine ⟨Σ W : {W : SmallEtale B S hS X.1 // HasAffineChartDiagram B S hS f W}, W.1 ⟶ U,
    fun i => i.1.1, fun i => i.2, ?_, fun i => ?_⟩
  · exact mem_topology_of_hasAffineChartDiagram B S hS f U _
      fun {W} a hW => Sieve.ofArrows_mk _ _ (⟨⟨W, hW⟩, a⟩ : Σ W : {W : SmallEtale B S hS X.1 //
        HasAffineChartDiagram B S hS f W}, W.1 ⟶ U)
  · exact exists_chart_quasiIso_naiveCotangentComplex B S hS f
      (chartDiagramOfHasAffineChartDiagram B S hS f i.1.2) i.1.2.1
      i.1.2.2.choose_spec.choose_spec.2 hf

end AlgebraicGeometry.Space

end
