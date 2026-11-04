module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Invertible
public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Charts

/-!
# The determinant of the naive cotangent complex of a syntomic morphism

Let `f : Y ⟶ X` be a syntomic morphism of schemes. Then `NL_{Y/X}` is a perfect object of
`D(𝒪_Y)` of Tor amplitude in `[-1, 0]`, and its determinant `det(NL_{Y/X})` is the invertible
`𝒪_Y`-module which on every pair of affine opens `U ⊆ X`, `V ⊆ Y` with `f(V) ⊆ U` is the
determinant `det(NL_{Γ(V)/Γ(U)})` of More on Algebra, Section 0FJI (Derived Categories of
Schemes, Lemma 0FJX, and Discriminants, Section 0FKB). This file constructs it by gluing these
determinants along the charts `(U, V)` of `f`, the transition maps being the base change maps
`det(NL_{Γ(V)/Γ(U)}) → det(NL_{Γ(V')/Γ(U')})` of the squares of restriction maps of nested
charts (`NaiveCotangent.detNLMap`), which identify `det(NL_{Γ(V')/Γ(U')})` with the base change
`Γ(V') ⊗_{Γ(V)} det(NL_{Γ(V)/Γ(U)})`. When `f` is moreover locally quasi-finite, `NL_{Y/X}` has
rank zero and the canonical elements `δ(NL_{Γ(V)/Γ(U)})` glue to the global section
`δ(NL_{Y/X})`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.detNL f hf`: the invertible `𝒪_Y`-module `det(NL_{Y/X})`.
* `AlgebraicGeometry.Scheme.Hom.detNLSectionsEquiv`: its sections over the source open of a
  chart `(U, V)` are `det(NL_{Γ(V)/Γ(U)})`.
* `AlgebraicGeometry.Scheme.Hom.deltaNL f hf`: the global section `δ(NL_{Y/X})`, for `f` locally
  quasi-finite and syntomic.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isInvertibleModule_detNL`: `det(NL_{Y/X})` is invertible.
* `AlgebraicGeometry.Scheme.Hom.detNLSectionsEquiv_deltaNL`: on every chart, `δ(NL_{Y/X})` is
  `δ(NL_{Γ(V)/Γ(U)})`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Syntomic f)

/-- The chart index of `f`: pairs of affine opens `U ⊆ X`, `V ⊆ Y` with `f(V) ⊆ U`. -/
abbrev chartIndex : Y.AffineChartIndex :=
  Scheme.AffineChartIndex.ofHom f

/-- The module `det(NL_{Γ(V)/Γ(U)})` on a chart `(U, V)` of a syntomic morphism. -/
abbrev detNLChart (c : f.chartIndex.ι) : ModuleCat.{u} Γ(Y, c.1.2.1) :=
  letI := f.chartAlgebra c.2
  haveI := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  NaiveCotangent.detNL Γ(X, c.1.1.1) Γ(Y, c.1.2.1)

/-- The base change map `det(NL_{Γ(V)/Γ(U)}) → det(NL_{Γ(V')/Γ(U')})` along a refinement of
charts. -/
def detNLChartRestrict {c' c : f.chartIndex.ι} (h : f.chartIndex.Refines c' c) :
    f.detNLChart hf c →ₛₗ[(Y.presheaf.map (homOfLE h.2.le).op).hom] f.detNLChart hf c' :=
  letI := f.chartAlgebra c.2
  letI := f.chartAlgebra c'.2
  letI := X.restrictAlgebra h.1.le
  letI := Y.restrictAlgebra h.2.le
  letI := f.chartAlgebra (h.2.le.trans c.2)
  haveI := f.isScalarTower_chartAlgebra_restrict c.2 c'.2 h.1.le h.2.le
  haveI := f.isScalarTower_restrict_chartAlgebra c.2 h.2.le
  haveI := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  haveI := f.syntomic_chartAlgebra hf c'.1.1 c'.1.2 c'.2
  NaiveCotangent.detNLMap (f.isGoodSquare_of_isBasicOpenOf c.2 c'.2 h.1 h.2)

/-- The restriction maps of `det(NL)` compose along refinements. -/
theorem detNLChartRestrict_detNLChartRestrict {c'' c' c : f.chartIndex.ι}
    (h' : f.chartIndex.Refines c'' c') (h : f.chartIndex.Refines c' c) (x : f.detNLChart hf c) :
    f.detNLChartRestrict hf h' (f.detNLChartRestrict hf h x) =
      f.detNLChartRestrict hf (f.chartIndex.refines_trans h' h) x := by
  let := f.chartAlgebra c.2
  let := f.chartAlgebra c'.2
  let := f.chartAlgebra c''.2
  let := X.restrictAlgebra h.1.le
  let := Y.restrictAlgebra h.2.le
  let := X.restrictAlgebra h'.1.le
  let := Y.restrictAlgebra h'.2.le
  let := X.restrictAlgebra (h'.1.le.trans h.1.le)
  let := Y.restrictAlgebra (h'.2.le.trans h.2.le)
  let := f.chartAlgebra (h.2.le.trans c.2)
  let := f.chartAlgebra (h'.2.le.trans c'.2)
  let := f.chartAlgebra ((h'.2.le.trans h.2.le).trans c.2)
  have := X.isScalarTower_restrictAlgebra h.1.le h'.1.le
  have := Y.isScalarTower_restrictAlgebra h.2.le h'.2.le
  have := f.isScalarTower_chartAlgebra_restrict c.2 c'.2 h.1.le h.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.2 h.2.le
  have := f.isScalarTower_chartAlgebra_restrict c'.2 c''.2 h'.1.le h'.2.le
  have := f.isScalarTower_restrict_chartAlgebra c'.2 h'.2.le
  have := f.isScalarTower_chartAlgebra_restrict c.2 c''.2 (h'.1.le.trans h.1.le)
    (h'.2.le.trans h.2.le)
  have := f.isScalarTower_restrict_chartAlgebra c.2 (h'.2.le.trans h.2.le)
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f.syntomic_chartAlgebra hf c'.1.1 c'.1.2 c'.2
  have := f.syntomic_chartAlgebra hf c''.1.1 c''.1.2 c''.2
  exact NaiveCotangent.detNLMap_detNLMap (f.isGoodSquare_of_isBasicOpenOf c.2 c'.2 h.1 h.2)
    (f.isGoodSquare_of_isBasicOpenOf c'.2 c''.2 h'.1 h'.2)
    (f.isGoodSquare_of_isBasicOpenOf c.2 c''.2 (f.chartIndex.refines_trans h' h).1
      (f.chartIndex.refines_trans h' h).2) x

/-- The restriction maps of `det(NL)` are injective along a refinement of a chart by itself. -/
theorem detNLChartRestrict_injective (c : f.chartIndex.ι) :
    Function.Injective (f.detNLChartRestrict hf (f.chartIndex.refines_refl c)) := by
  let := f.chartAlgebra c.2
  let := X.restrictAlgebra (le_refl c.1.1.1)
  let := Y.restrictAlgebra (le_refl c.1.2.1)
  let := f.chartAlgebra ((le_refl c.1.2.1).trans c.2)
  have := f.isScalarTower_chartAlgebra_restrict c.2 c.2 (le_refl c.1.1.1) (le_refl c.1.2.1)
  have := f.isScalarTower_restrict_chartAlgebra c.2 (le_refl c.1.2.1)
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  exact NaiveCotangent.detNLMap_injective _ (Y.bijective_restrict_self c.1.2.1 le_rfl)

/-- The restriction map of `det(NL)` along the refinement of a chart by itself is the
identity. -/
theorem detNLChartRestrict_refl (c : f.chartIndex.ι) (x : f.detNLChart hf c) :
    f.detNLChartRestrict hf (f.chartIndex.refines_refl c) x = x :=
  f.detNLChartRestrict_injective hf c
    (f.detNLChartRestrict_detNLChartRestrict hf _ _ x)

/-- The restriction maps of `det(NL)` exhibit the module on a refinement as a base change. -/
theorem isBaseChangeAlong_detNLChartRestrict {c' c : f.chartIndex.ι}
    (h : f.chartIndex.Refines c' c) : (f.detNLChartRestrict hf h).IsBaseChangeAlong := by
  let := f.chartAlgebra c.2
  let := f.chartAlgebra c'.2
  let := X.restrictAlgebra h.1.le
  let := Y.restrictAlgebra h.2.le
  let := f.chartAlgebra (h.2.le.trans c.2)
  have := f.isScalarTower_chartAlgebra_restrict c.2 c'.2 h.1.le h.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.2 h.2.le
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f.syntomic_chartAlgebra hf c'.1.1 c'.1.2 c'.2
  let : Module Γ(Y, c.1.2.1) (f.detNLChart hf c') :=
    Module.compHom _ (Y.presheaf.map (homOfLE h.2.le).op).hom
  have : IsScalarTower Γ(Y, c.1.2.1) Γ(Y, c'.1.2.1) (f.detNLChart hf c') :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact IsBaseChange.of_equiv
    (NaiveCotangent.detNLBaseChangeLinearEquiv (f.isGoodSquare_of_isBasicOpenOf c.2 c'.2 h.1 h.2))
    (NaiveCotangent.detNLBaseChangeLinearEquiv_one_tmul _)

/-- The system of modules `det(NL_{Γ(V)/Γ(U)})` on the charts of a syntomic morphism, with the
base change maps along refinements. -/
def detNLSystem : ChartModuleSystem f.chartIndex where
  M c := f.detNLChart hf c
  addCommGroup c := (f.detNLChart hf c).isAddCommGroup
  module c := (f.detNLChart hf c).isModule
  ρ h := f.detNLChartRestrict hf h
  ρ_refl c x := f.detNLChartRestrict_refl hf c x
  ρ_ρ h' h x := f.detNLChartRestrict_detNLChartRestrict hf h' h x
  isBaseChangeAlong_ρ h := f.isBaseChangeAlong_detNLChartRestrict hf h

/-- **The determinant `det(NL_{Y/X})` of the naive cotangent complex of a syntomic morphism**
`f : Y ⟶ X`: the `𝒪_Y`-module which on every chart `(U, V)` of `f` is
`det(NL_{Γ(V)/Γ(U)})` (Derived Categories of Schemes, Lemma 0FJX; Discriminants,
Section 0FKB). -/
def detNL : Y.Modules :=
  (f.detNLSystem hf).sheaf

/-- `det(NL_{Y/X})` is an invertible `𝒪_Y`-module. -/
theorem isInvertibleModule_detNL : Stacks.Ample.IsInvertibleModule Y (f.detNL hf) :=
  have : ∀ c, Module.Invertible Γ(Y, (f.chartIndex.V c).1) ((f.detNLSystem hf).M c) :=
    fun c => by
      let := f.chartAlgebra c.2
      have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
      exact (inferInstance : Module.Invertible Γ(Y, c.1.2.1)
        (NaiveCotangent.detNL Γ(X, c.1.1.1) Γ(Y, c.1.2.1)))
  (f.detNLSystem hf).isInvertibleModule_sheaf_of_invertible

/-- `det(NL_{Y/X})` is a quasi-coherent `𝒪_Y`-module. -/
instance isQuasicoherent_detNL : (f.detNL hf).IsQuasicoherent :=
  ChartModuleSystem.isQuasicoherent_sheaf _

/-- **The sections of `det(NL_{Y/X})` over the source open `V` of a chart `(U, V)`** are
`det(NL_{Γ(V)/Γ(U)})`. -/
def detNLSectionsEquiv (c : f.chartIndex.ι) :
    Γ(f.detNL hf, c.1.2.1) ≃ₗ[Γ(Y, c.1.2.1)] f.detNLChart hf c :=
  (f.detNLSystem hf).sectionsEquiv c

/-- The identification of sections over charts is compatible with restriction to a refinement:
restriction of sections is the base change map of determinants. -/
theorem detNLSectionsEquiv_restrict {c' c : f.chartIndex.ι} (h : f.chartIndex.Refines c' c)
    (s : Γ(f.detNL hf, c.1.2.1)) :
    f.detNLSectionsEquiv hf c' ((f.detNL hf).presheaf.map
        (homOfLE (f.chartIndex.le_of_refines h)).op s) =
      f.detNLChartRestrict hf h (f.detNLSectionsEquiv hf c s) :=
  (f.detNLSystem hf).sectionsEquiv_restrict c h s

/-! ### The canonical global section -/

section Delta

variable [LocallyQuasiFinite f]

/-- The canonical element `δ(NL_{Γ(V)/Γ(U)})` on a chart of a locally quasi-finite syntomic
morphism. -/
abbrev deltaNLChart (c : f.chartIndex.ι) : f.detNLChart hf c :=
  letI := f.chartAlgebra c.2
  haveI := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  haveI := f.quasiFinite_chartAlgebra inferInstance c.1.1 c.1.2 c.2
  NaiveCotangent.deltaNL Γ(X, c.1.1.1) Γ(Y, c.1.2.1)

/-- The canonical elements on the charts are compatible with the restriction maps. -/
theorem detNLChartRestrict_deltaNLChart {c' c : f.chartIndex.ι}
    (h : f.chartIndex.Refines c' c) :
    f.detNLChartRestrict hf h (f.deltaNLChart hf c) = f.deltaNLChart hf c' := by
  let := f.chartAlgebra c.2
  let := f.chartAlgebra c'.2
  let := X.restrictAlgebra h.1.le
  let := Y.restrictAlgebra h.2.le
  let := f.chartAlgebra (h.2.le.trans c.2)
  have := f.isScalarTower_chartAlgebra_restrict c.2 c'.2 h.1.le h.2.le
  have := f.isScalarTower_restrict_chartAlgebra c.2 h.2.le
  have := f.syntomic_chartAlgebra hf c.1.1 c.1.2 c.2
  have := f.syntomic_chartAlgebra hf c'.1.1 c'.1.2 c'.2
  have := f.quasiFinite_chartAlgebra inferInstance c.1.1 c.1.2 c.2
  have := f.quasiFinite_chartAlgebra inferInstance c'.1.1 c'.1.2 c'.2
  exact NaiveCotangent.detNLMap_deltaNL _

/-- **The canonical global section `δ(NL_{Y/X})`** of `det(NL_{Y/X})` for a locally quasi-finite
syntomic morphism: on every chart `(U, V)` it is the canonical element `δ(NL_{Γ(V)/Γ(U)})` of
More on Algebra, Section 0FJI (Derived Categories of Schemes, Lemma 0FJX; Discriminants,
Section 0FKB). -/
def deltaNL : Γ(f.detNL hf, ⊤) :=
  (f.detNLSystem hf).globalSectionOfCompatible (f.deltaNLChart hf)
    fun _ _ h => f.detNLChartRestrict_deltaNLChart hf h

/-- On every chart `(U, V)`, `δ(NL_{Y/X})` is `δ(NL_{Γ(V)/Γ(U)})`. -/
theorem detNLSectionsEquiv_deltaNL (c : f.chartIndex.ι) :
    f.detNLSectionsEquiv hf c ((f.detNL hf).presheaf.map (homOfLE le_top).op (f.deltaNL hf)) =
      f.deltaNLChart hf c :=
  (f.detNLSystem hf).sectionsEquiv_globalSectionOfCompatible _ _ c

end Delta

end AlgebraicGeometry.Scheme.Hom

end
