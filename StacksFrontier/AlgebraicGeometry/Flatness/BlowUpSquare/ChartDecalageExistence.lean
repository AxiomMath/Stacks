module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaAffineSheafComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBasis
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Homology.Eta.Complex
public import StacksFrontier.Homology.Eta.RestrictScalars

/-!
# The derived décalage of a triple on an affine chart

Let `(X, D, M)` be a triple as in Situation 0F8S, let `I ⊆ 𝒪_X` be the ideal sheaf of `D` and
let `(U, A, f, M^•)` be an affine chart: `U ⊆ X` is affine with coordinate ring `A = Γ(X, U)`,
`f ∈ A` is a nonzerodivisor cutting out `D ∩ U`, and `M^•` is a bounded complex of finite free
`A`-modules representing `M|_U`.  The restriction of `Lη_I M` to `U` is then the complex of
`𝒪_U`-modules associated with the algebraic décalage `η_f M^•`:

`(Lη_I M)|_U ≅ (η_f M^•)^~`   in `D(𝒪_U)`.

This is the second assertion of Stacks tag 0GTV read at the object `M|_U`: since `M^•` consists
of `f`-torsion-free modules, `η_f M^•` computes `Lη_f M^•`.  With it, the perfectness of
`Lη_I M` for a good triple (Stacks tag 0GTW) and the perfectness of `Lη_{I'} Lb^*M` on the
modification `b : X' ⟶ X` of Stacks tag 0GTY (Stacks tag 0F8U) hold with no further hypothesis.

The comparison is assembled in four steps, all on `Spec A`, which `U` is identified with.

1. Represent `M` by a complex `F^•` of `I`-torsion-free modules, so that `Lη_I M` is the
   chain-level décalage `η_I F^•`.  Pullback along the flat morphism `Spec A ⟶ X` commutes with
   the chain-level décalage (the flat case of Stacks tag 0F9X).
2. On `Spec A` the pullback of `F^•` and the complex of sheaves `M̃^•` of the chart are two
   representatives of the same object, and both consist of torsion-free modules for the
   pulled-back divisor; so their décalages agree in the derived category.
3. The décalage of `M̃^•` is the complex of sheaves of the décalage of its complex of global
   sections, by Stacks tag 0F8M; that complex of sections is `M^•`.
4. Restriction to `U` is pullback to `Spec A` followed by the direct image along
   `Spec A ≅ U`.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.etaObjSpecTildeComplexIso`: the
  décalage of the complex of sheaves `M̃^•` of a chart is `(η_f M^•)^~`.

## Main results

* `nonempty_restrictModules_derivedEta_iso`, in the namespace
  `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart`:
  `(Lη_I M)|_U ≅ (η_f M^•)^~` on every affine chart.
* `AlgebraicGeometry.ComplexAndDivisorSituation.chartDecalage_of_derivedEta`: the comparison
  `AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage`, for every triple and every
  derived décalage of its divisor.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodTriple.isPerfect_derivedEta_obj`:
  **Stacks tag 0GTW**, for every derived décalage `Lη_I` of the divisor.  Stacks tag 0F8U, its
  case for the pulled-back triple of a good morphism, is
  `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_etaDerivedPullbackObject_goodBlowup`.

## Implementation notes

The ring `Γ(Spec A, ⊤)` over which the décalage of a sheaf on `Spec A` is computed is not `A`
but isomorphic to it, and the chart's décalage `η_f M^•` is formed over `A`.  The two are
compared by `EtaComplex.etaObjectRestrictScalarsIso`, applied to `Γ(Spec A, ⊤)` regarded as an
`A`-algebra through the isomorphism `A ≅ Γ(Spec A, ⊤)`.

The derived décalage is an arbitrary `Stacks.Divisors.Eta.DerivedEta` at the model of `D(𝒪_X)`
that the triple carries; only its two characterizing properties are used.  The derived
décalage on `Spec A` is `Stacks.Divisors.Eta.derivedEtaData`.  The triple's own model of
`D(𝒪_X)` is pinned above the standard model, which is pinned above the locally small models the
imports make available, so that each derived category below is formed at the model its
neighbours expect.

## References

* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F8M](https://stacks.math.columbia.edu/tag/0F8M)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open StrictlyPerfect
open Stacks.Divisors.Eta (idealSheaf idealSheafι)

universe u d

attribute [local instance] AlgebraicGeometry.ComplexAndDivisorSituation.isEffectiveCartierDivisor

namespace AlgebraicGeometry.ComplexAndDivisorSituation

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-! ### The chart on its spectrum -/

/-- The pullback of the divisor along `Spec Γ(X, U) ⟶ X` is defined: an open immersion is
flat. -/
theorem isPullbackDefined_fromSpec (C : AffineChart S) :
    Stacks.Divisors.IsPullbackDefined C.U.2.fromSpec S.D :=
  have := IsAffineOpen.isOpenImmersion_fromSpec C.U.2
  Stacks.Divisors.isPullbackDefined_of_flat _ _ S.isEffectiveCartierDivisor

/-- The pullback of the divisor to the spectrum of an affine chart is an effective Cartier
divisor. -/
instance isEffectiveCartierDivisor_comap_fromSpec (C : AffineChart S) :
    Stacks.Divisors.IsEffectiveCartierDivisor (S.D.comap C.U.2.fromSpec) :=
  C.isPullbackDefined_fromSpec

/-- The whole of `Spec Γ(X, U)` lies in the preimage of `U` under `Spec Γ(X, U) ⟶ X`. -/
theorem top_le_fromSpec_preimage (C : AffineChart S) :
    ((⟨⊤, isAffineOpen_top _⟩ : (Spec Γ(S.X, C.U)).affineOpens) : (Spec Γ(S.X, C.U)).Opens) ≤
      C.U.2.fromSpec ⁻¹ᵁ (C.U : S.X.Opens) :=
  (IsAffineOpen.fromSpec_preimage_self C.U.2).ge

/-- The equation of an affine chart, carried to the global sections of `Spec Γ(X, U)`, comes from
a section of the ideal sheaf of the pulled-back divisor which generates it on all of
`Spec Γ(X, U)`. -/
theorem exists_generatesIdealOn_fromSpec (C : AffineChart S) :
    ∃ g : (idealSheaf (S.D.comap C.U.2.fromSpec)).val.obj (op ⊤),
      Stacks.IdealTorsion.GeneratesIdealOn (Spec Γ(S.X, C.U)).toRingedSpace ⊤ g ∧
        Stacks.IdealTorsion.Eta.generatorSection (Spec Γ(S.X, C.U)).toRingedSpace
          (idealSheafι (S.D.comap C.U.2.fromSpec)) ⊤ g =
            (Scheme.ΓSpecIso Γ(S.X, C.U)).inv.hom C.f := by
  have hspan := C.comap_ideal_eq_span C.U.2.fromSpec ⟨⊤, isAffineOpen_top _⟩
    C.top_le_fromSpec_preimage
  have hreg := C.isRegular_pullbackRingHom_f C.U.2.fromSpec C.isPullbackDefined_fromSpec
    ⟨⊤, isAffineOpen_top _⟩ C.top_le_fromSpec_preimage
  rw [pullbackRingHom, AlgebraicGeometry.fromSpec_appLE_top C.U.2] at hspan hreg
  exact Stacks.Divisors.Eta.exists_generatesIdealOn_of_ideal_eq_span _ ⟨⊤, isAffineOpen_top _⟩
    hspan hreg.mem_nonZeroDivisors

/-- The complex of quasi-coherent `𝒪_{Spec Γ(X, U)}`-modules `M̃^•` of the bounded complex of
an affine chart. -/
abbrev specTildeComplex (C : AffineChart S) : CochainComplex (Spec Γ(S.X, C.U)).Modules ℤ :=
  ((tilde.functor Γ(S.X, C.U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    C.complex.toCochainComplex

/-- The terms of the complex of sheaves of an affine chart have no torsion for the pulled-back
divisor: they are finite free. -/
theorem isIdealTorsionFree_specTildeComplex (C : AffineChart S) (n : ℤ) :
    Stacks.IdealTorsion.IsIdealTorsionFree (Spec Γ(S.X, C.U)).toRingedSpace
      (idealSheafι (S.D.comap C.U.2.fromSpec)) (C.specTildeComplex.X n) :=
  Stacks.BlowUpComplexes.isIdealTorsionFree_of_isFiniteLocallyFree _
    C.isPullbackDefined_fromSpec _
    ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr
      ((Stacks.Modules.tilde_isFiniteLocallyFree_iff_module Γ(S.X, C.U)
        (Fin (C.complex.rank n) → Γ(S.X, C.U))).mpr
        ((Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr
          ⟨inferInstance, inferInstance⟩)))

/-- The global sections of the complex of sheaves of an affine chart are the chart's
complex. -/
def gammaSpecTildeComplexIso (C : AffineChart S) :
    ((moduleSpecΓFunctor (R := Γ(S.X, C.U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        C.specTildeComplex ≅ C.complex.toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (tilde.toTildeΓNatIso.app (C.complex.toCochainComplex.X n)).symm)
    (fun i j _ => (tilde.toTildeΓNatIso.inv.naturality (C.complex.toCochainComplex.d i j)).symm)

/-- **The décalage of the complex of sheaves of an affine chart is the complex of sheaves of the
algebraic décalage.**  On `Spec A`, `A = Γ(X, U)`, the décalage `η_I(M̃^•)` along the pulled-back
divisor is `(η_f M^•)^~`.  This is Stacks tag 0F8M in the form
`Stacks.Divisors.Eta.etaObjTildeIso`, computed over `Γ(Spec A, ⊤)`, and carried to `A` by
`EtaComplex.etaObjectRestrictScalarsIso`. -/
def etaObjSpecTildeComplexIso (C : AffineChart S) :
    Stacks.IdealTorsion.Eta.etaObj (Spec Γ(S.X, C.U)).toRingedSpace
        (idealSheaf (S.D.comap C.U.2.fromSpec)) (idealSheafι (S.D.comap C.U.2.fromSpec))
        C.specTildeComplex C.isIdealTorsionFree_specTildeComplex ≅
      ((tilde.functor Γ(S.X, C.U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        C.etaComplex :=
  let g := C.exists_generatesIdealOn_fromSpec.choose
  have hg := C.exists_generatesIdealOn_fromSpec.choose_spec
  Stacks.Divisors.Eta.etaObjTildeIso Γ(S.X, C.U) (S.D.comap C.U.2.fromSpec) C.specTildeComplex
      (fun n => (inferInstance : ((tilde.functor Γ(S.X, C.U)).obj
        (C.complex.toCochainComplex.X n)).IsQuasicoherent))
      C.isIdealTorsionFree_specTildeComplex g hg.1 ≪≫
    ((tilde.functor Γ(S.X, C.U)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (((ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(S.X, C.U)).inv.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso
          (eqToIso (congrArg (fun a => EtaComplex.etaObject a
            (Stacks.IdealTorsion.Eta.sectionsComplex (Spec Γ(S.X, C.U)).toRingedSpace
              C.specTildeComplex ⊤)) hg.2)) ≪≫
        (letI := (Scheme.ΓSpecIso Γ(S.X, C.U)).inv.hom.toAlgebra;
          (EtaComplex.etaObjectRestrictScalarsIso (A := Γ(S.X, C.U)) C.f
            (Stacks.IdealTorsion.Eta.sectionsComplex (Spec Γ(S.X, C.U)).toRingedSpace
              C.specTildeComplex ⊤)).symm) ≪≫
        Stacks.BlowUpComplexes.etaObjectIso C.f C.gammaSpecTildeComplexIso)

/-- The open immersion `Spec Γ(X, U) ⟶ X` of an affine chart is flat, at the level of the
underlying morphism of ringed spaces. -/
theorem isFlat_fromSpec (C : AffineChart S) :
    AlgebraicGeometry.IsFlat C.U.2.fromSpec.toLRSHom.toShHom :=
  have := IsAffineOpen.isOpenImmersion_fromSpec C.U.2
  fun x => AlgebraicGeometry.Flat.stalkMap C.U.2.fromSpec x

/-- Pulling back the ideal-sheaf inclusion of `D` along the flat map `Spec Γ(X, U) ⟶ X` keeps it
a monomorphism. -/
theorem mono_pullbackIdealIncl_fromSpec (C : AffineChart S) :
    Mono (Stacks.IdealTorsion.Eta.pullbackIdealIncl
      C.U.2.fromSpec.toLRSHom.toShHom (idealSheaf S.D) (idealSheafι S.D)) :=
  @Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl _ _ C.U.2.fromSpec.toLRSHom.toShHom
    C.isFlat_fromSpec (idealSheaf S.D) (idealSheafι S.D)
    (Stacks.Divisors.Eta.mono_idealSheafι S.D)

/-- The termwise pullback, along `Spec Γ(X, U) ⟶ X`, of a complex of `I_D`-torsion-free modules
is a complex of torsion-free modules for the pulled-back divisor. -/
theorem isIdealTorsionFree_pullbackComplex_fromSpec (C : AffineChart S)
    (F : CochainComplex S.X.Modules ℤ)
    (htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree S.X.toRingedSpace
      (idealSheafι S.D) (F.X n)) (n : ℤ) :
    Stacks.IdealTorsion.IsIdealTorsionFree (Spec Γ(S.X, C.U)).toRingedSpace
      (idealSheafι (S.D.comap C.U.2.fromSpec))
      ((Stacks.IdealTorsion.Eta.pullbackComplex C.U.2.fromSpec.toLRSHom.toShHom F).X n) :=
  Stacks.IdealTorsion.Eta.isIdealTorsionFree_of_pullbackIdealIncl
    C.U.2.fromSpec.toLRSHom.toShHom (idealSheaf S.D) (idealSheafι S.D)
    (idealSheaf (S.D.comap C.U.2.fromSpec)) (idealSheafι (S.D.comap C.U.2.fromSpec))
    (Stacks.Divisors.pullbackIdealSheafComapIso C.U.2.fromSpec S.D C.isPullbackDefined_fromSpec)
    (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι C.U.2.fromSpec S.D
      C.isPullbackDefined_fromSpec) _
    (@Stacks.IdealTorsion.Eta.isIdealTorsionFree_pullbackComplex_of_isFlat _ _
      C.U.2.fromSpec.toLRSHom.toShHom (idealSheaf S.D) (idealSheafι S.D)
      (Stacks.Divisors.Eta.mono_idealSheafι S.D) C.isFlat_fromSpec
      (Stacks.Divisors.Eta.isInvertible_idealSheaf S.D) C.mono_pullbackIdealIncl_fromSpec _ _ F
      htf n)

/-- **The décalage commutes with pullback along `Spec Γ(X, U) ⟶ X`**, at the level of
complexes: the comparison of `Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap`, the open immersion
being flat, followed by the identification of the pulled-back ideal with the ideal of the
pulled-back divisor. -/
def pullbackEtaObjFromSpecIso (C : AffineChart S) (F : CochainComplex S.X.Modules ℤ)
    (htf : ∀ n : ℤ, Stacks.IdealTorsion.IsIdealTorsionFree S.X.toRingedSpace
      (idealSheafι S.D) (F.X n)) :
    Stacks.IdealTorsion.Eta.pullbackComplex C.U.2.fromSpec.toLRSHom.toShHom
        (Stacks.IdealTorsion.Eta.etaObj S.X.toRingedSpace (idealSheaf S.D) (idealSheafι S.D)
          F htf) ≅
      Stacks.IdealTorsion.Eta.etaObj (Spec Γ(S.X, C.U)).toRingedSpace
        (idealSheaf (S.D.comap C.U.2.fromSpec)) (idealSheafι (S.D.comap C.U.2.fromSpec))
        (Stacks.IdealTorsion.Eta.pullbackComplex C.U.2.fromSpec.toLRSHom.toShHom F)
        (C.isIdealTorsionFree_pullbackComplex_fromSpec F htf) :=
  have hmono := C.mono_pullbackIdealIncl_fromSpec
  have hF' := @Stacks.IdealTorsion.Eta.isIdealTorsionFree_pullbackComplex_of_isFlat _ _
    C.U.2.fromSpec.toLRSHom.toShHom (idealSheaf S.D) (idealSheafι S.D)
    (Stacks.Divisors.Eta.mono_idealSheafι S.D) C.isFlat_fromSpec
    (Stacks.Divisors.Eta.isInvertible_idealSheaf S.D) hmono _ _ F htf
  haveI := @Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap _ _ C.U.2.fromSpec.toLRSHom.toShHom
    (idealSheaf S.D) (idealSheafι S.D) (Stacks.Divisors.Eta.mono_idealSheafι S.D)
    (Stacks.Divisors.Eta.isInvertible_idealSheaf S.D) hmono F htf hF' C.isFlat_fromSpec
  asIso (@Stacks.IdealTorsion.Eta.pullbackEtaMap _ _ C.U.2.fromSpec.toLRSHom.toShHom
      (idealSheaf S.D) (idealSheafι S.D) (Stacks.Divisors.Eta.mono_idealSheafι S.D)
      (Stacks.Divisors.Eta.isInvertible_idealSheaf S.D) hmono F htf hF') ≪≫
    @Stacks.IdealTorsion.Eta.IdealCongr.etaIso (Spec Γ(S.X, C.U)).toRingedSpace _
      (idealSheaf (S.D.comap C.U.2.fromSpec))
      (Stacks.IdealTorsion.Eta.isInvertible_pullbackIdeal C.U.2.fromSpec.toLRSHom.toShHom
        (idealSheaf S.D)) _ _ (idealSheafι (S.D.comap C.U.2.fromSpec))
      (Stacks.Divisors.pullbackIdealSheafComapIso C.U.2.fromSpec S.D C.isPullbackDefined_fromSpec)
      (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι C.U.2.fromSpec S.D
        C.isPullbackDefined_fromSpec) _ hmono _ hF'
      (C.isIdealTorsionFree_pullbackComplex_fromSpec F htf)

/-- Restriction to the domain of an affine chart is pullback along `Spec Γ(X, U) ⟶ X` followed by
the direct image along `Spec Γ(X, U) ≅ U`. -/
def restrictModulesIsoPullbackFromSpec (C : AffineChart S) :
    RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace C.U.1 ≅
      Stacks.RingedSpace.pullbackFunctor C.U.2.fromSpec.toLRSHom.toShHom ⋙
        (RingedSpace.PseudoCoherence.moduleEquivOfIso C.specIso).functor :=
  haveI := IsAffineOpen.isOpenImmersion_fromSpec C.U.2
  RingedSpace.restrictModulesIsoRestrictFunctor S.X C.U.1 ≪≫
    Scheme.Modules.restrictFunctorCongr (IsAffineOpen.isoSpec_hom_fromSpec C.U.2).symm ≪≫
    Scheme.Modules.restrictFunctorComp C.U.2.isoSpec.hom C.U.2.fromSpec ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback C.U.2.fromSpec) _ ≪≫
    Functor.isoWhiskerLeft _ (Stacks.Morphisms.pushforwardIsoRestrictInv C.U.2.isoSpec.symm).symm

/-! ### The comparison in the derived category -/

section Derived

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 100001] ComplexAndDivisorSituation.hasDerivedCategory
attribute [local instance 100000] modulesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesHomology

/-- **The representation clause of an affine chart, read on `Spec Γ(X, U)`.**  If a complex `F`
of `𝒪_X`-modules represents `M`, its restriction along `Spec Γ(X, U) ⟶ X` is isomorphic, in the
derived category, to the complex of sheaves `M̃^•` of the chart. -/
theorem nonempty_restrictFromSpec_iso_specTildeComplex (C : AffineChart S)
    (F : CochainComplex S.X.Modules ℤ)
    (eF : (@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj F ≅ S.M) :
    haveI := IsAffineOpen.isOpenImmersion_fromSpec C.U.2
    Nonempty (DerivedCategory.Q.obj
      (((Scheme.Modules.restrictFunctor C.U.2.fromSpec).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj F) ≅ DerivedCategory.Q.obj C.specTildeComplex) := by
  have := IsAffineOpen.isOpenImmersion_fromSpec C.U.2
  obtain ⟨E₀, ⟨e₀⟩, ⟨r⟩⟩ := C.represents
  let ρ := Scheme.Modules.restrictFunctor C.U.2.isoSpec.inv
  refine ⟨((Scheme.Modules.restrictFunctor C.U.2.fromSpec).mapDerivedCategoryFactors.app F).symm ≪≫
    (Scheme.Modules.restrictFunctor C.U.2.fromSpec).mapDerivedCategory.mapIso (eF ≪≫ e₀.symm) ≪≫
    (Scheme.Modules.restrictFunctor C.U.2.fromSpec).mapDerivedCategoryFactors.app E₀ ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex C.U.2.restrictCompIso.symm (ComplexShape.up ℤ)).app E₀) ≪≫
    (ρ.mapDerivedCategoryFactors.app (((Scheme.Modules.restrictFunctor
      (C.U : S.X.Opens).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀)).symm ≪≫
    ρ.mapDerivedCategory.mapIso r ≪≫
    ρ.mapDerivedCategoryFactors.app (((tilde.functor Γ(S.X, C.U) ⋙
      Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.complex.toCochainComplex) ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ C.U.2.restrictIsoSpecCompIso ≪≫
        Functor.rightUnitor _) (ComplexShape.up ℤ)).app C.complex.toCochainComplex)⟩

/-- **The derived décalage on an affine chart.**  Let `(U, A, f, M^•)` be an affine chart for
`(X, D, M)`.  The restriction of `Lη_I M` to `U` is isomorphic, in `D(𝒪_U)`, to the complex of
`𝒪_U`-modules `(η_f M^•)^~` associated with the algebraic décalage of the chart.

`Lη_I M` is the chain-level décalage `η_I F^•` of a complex of `I`-torsion-free modules
representing `M`.  Restricted to `U`, which is pulled back to `Spec A` and pushed forward along
`Spec A ≅ U`, it becomes the décalage of the pulled-back complex, by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullbackEtaObjFromSpecIso`; on
`Spec A` the pulled-back complex and `M̃^•` represent the same object and are both termwise
torsion-free, so their décalages agree in the derived category; and the décalage of `M̃^•` is
`(η_f M^•)^~` by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.etaObjSpecTildeComplexIso`. -/
theorem nonempty_restrictModules_derivedEta_iso (E : Stacks.Divisors.Eta.DerivedEta S.D)
    (C : AffineChart S) :
    Nonempty ((RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace
        C.U.1).mapDerivedCategory.obj (E.functor.obj S.M) ≅
      DerivedCategory.Q.obj C.specEtaComplex) := by
  obtain ⟨F, htf, ⟨eF⟩⟩ := E.exists_isIdealTorsionFree_rep S.M
  obtain ⟨eA⟩ := C.nonempty_restrictFromSpec_iso_specTildeComplex F eF
  have := IsAffineOpen.isOpenImmersion_fromSpec C.U.2
  let R := RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace C.U.1
  let ψ := (RingedSpace.PseudoCoherence.moduleEquivOfIso C.specIso).functor
  let EA := Stacks.Divisors.Eta.derivedEtaData (S.D.comap C.U.2.fromSpec)
  have e₂ : (DerivedCategory.Q (C := (Spec Γ(S.X, C.U)).Modules)).obj
      (Stacks.IdealTorsion.Eta.pullbackComplex C.U.2.fromSpec.toLRSHom.toShHom F) ≅
        DerivedCategory.Q.obj C.specTildeComplex :=
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (Scheme.Modules.restrictFunctorIsoPullback C.U.2.fromSpec)
        (ComplexShape.up ℤ)).app F).symm ≪≫ eA
  exact ⟨R.mapDerivedCategory.mapIso (E.functor.mapIso eF.symm ≪≫ E.objIso F htf) ≪≫
    R.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun i => C.restrictModulesIsoPullbackFromSpec.app (Stacks.IdealTorsion.Eta.etaObj
        S.X.toRingedSpace (idealSheaf S.D) (idealSheafι S.D) F htf |>.X i))
      (fun i j _ => (C.restrictModulesIsoPullbackFromSpec.hom.naturality _).symm) :
        (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Stacks.IdealTorsion.Eta.etaObj
          S.X.toRingedSpace (idealSheaf S.D) (idealSheafι S.D) F htf) ≅
        (ψ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (Stacks.IdealTorsion.Eta.pullbackComplex C.U.2.fromSpec.toLRSHom.toShHom
            (Stacks.IdealTorsion.Eta.etaObj S.X.toRingedSpace (idealSheaf S.D) (idealSheafι S.D)
              F htf))) ≪≫
    DerivedCategory.Q.mapIso ((ψ.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (C.pullbackEtaObjFromSpecIso F htf)) ≪≫
    (ψ.mapDerivedCategoryFactors.app _).symm ≪≫
    ψ.mapDerivedCategory.mapIso
      ((EA.objIso _ (C.isIdealTorsionFree_pullbackComplex_fromSpec F htf)).symm ≪≫
        EA.functor.mapIso e₂ ≪≫ EA.objIso _ C.isIdealTorsionFree_specTildeComplex) ≪≫
    ψ.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((ψ.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      C.etaObjSpecTildeComplexIso)⟩

end Derived

end AffineChart

/-! ### The comparison, and the perfectness of the décalage -/

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 100001] ComplexAndDivisorSituation.hasDerivedCategory
attribute [local instance 100000] modulesHasDerivedCategory

/-- **The derived décalage of a triple on its affine charts with principal determinantal
ideals**, for every triple `(X, D, M)` and every derived décalage `Lη_I` of its divisor: on such
a chart `(U, A, f, M^•)` the restriction of `Lη_I M` to `U` is the complex of `𝒪_U`-modules
associated with `η_f M^•`, as a roof of quasi-isomorphisms.  The comparison is
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.nonempty_restrictModules_derivedEta_iso`,
which holds on every affine chart.  For the derived décalage
`Stacks.Divisors.Eta.derivedEtaData` of a triple at the standard model this is
`AlgebraicGeometry.ComplexAndDivisorSituation.chartDecalage`. -/
@[stacks 0GTV "the second assertion, on an affine chart with principal determinantal ideals"]
theorem chartDecalage_of_derivedEta (S : ComplexAndDivisorSituation.{u, d})
    (E : Stacks.Divisors.Eta.DerivedEta S.D) : ChartDecalage S E where
  roof C _ := (C.nonempty_restrictModules_derivedEta_iso E).elim (ChartDecalage.roof_of_iso C)

/-- **Stacks tag 0GTW.**  Let `X`, `D`, `I`, `M` be as in Situation 0F8S.  If `(X, D, M)` is a
good triple, then `Lη_I M` is a perfect object of `D(𝒪_X)`.

This is `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEta_obj`, whose
comparison on affine charts is
`AlgebraicGeometry.ComplexAndDivisorSituation.chartDecalage_of_derivedEta` and whose charts off the
divisor are
`ComplexAndDivisorSituation.exists_chart_isPrincipal_determinantalIdeal_of_notMem_supportSet`.
The derived décalage is any `Stacks.Divisors.Eta.DerivedEta` of the divisor at the model of
`D(𝒪_X)` the triple carries; for a triple at the standard model it may be taken to be
`Stacks.Divisors.Eta.derivedEtaData`. -/
@[stacks 0GTW]
theorem IsGoodTriple.isPerfect_derivedEta_obj (S : ComplexAndDivisorSituation.{u, d})
    (E : Stacks.Divisors.Eta.DerivedEta S.D) (hS : IsGoodTriple S) :
    RingedSpace.IsPerfect (X := S.X.toRingedSpace) (E.functor.obj S.M) :=
  _root_.AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEta_obj S E hS
    (fun _ hx => S.exists_chart_isPrincipal_determinantalIdeal_of_notMem_supportSet hx)
    (S.chartDecalage_of_derivedEta E)

end AlgebraicGeometry.ComplexAndDivisorSituation

end
