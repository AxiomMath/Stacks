module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsUlift
public import StacksFrontier.Algebra.Homology.DoubleMapFunctor
public import StacksFrontier.Deformation.SquareZero.ExtBaseChange
public import StacksFrontier.Deformation.SquareZero.NaiveCotangentUlifted
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.RingTheory.Henselian.Pair
public import StacksFrontier.RingTheory.NaiveCotangent.Henselization

/-!
# The naive cotangent complex of the henselization of a pair, in the derived category

Let `k` be a commutative ring, let `B` be a `k`-algebra, let `J ⊆ B` be an ideal and let
`(Bʰ, Jʰ)` be the henselization of the pair `(B, J)`.  Stacks 0D08 for that case —
`Algebra.naiveCotangentComplex_quasiIso_henselizationPair` — says that the canonical comparison

`NL_{B/k} ⊗_B Bʰ ⟶ NL_{Bʰ/k}`

induces isomorphisms on all homology groups.  This file turns that statement into an
isomorphism in the derived category of `Bʰ`-modules, and hence into an identification of the
first extension groups out of the two complexes.

## Main definitions

* `Stacks.Deformation.naiveCotangentBaseChangeChainComplex`: `NL_{B/k} ⊗_B Bʰ`, universe-lifted
  into the module category the cochain presentation uses.
* `Stacks.Deformation.naiveCotangentBaseChangeCochainComplex`: the same complex read in
  cohomological degrees `-1` and `0`.
* `Stacks.Deformation.naiveCotangentHenselizationComparison`: the comparison map between the
  cochain presentations, with the same two components as the comparison of Stacks 0D08.

## Main results

* `Stacks.Deformation.quasiIso_naiveCotangentHenselizationComparison`: that comparison is a
  quasi-isomorphism.
* `Stacks.Deformation.naiveCotangentHenselizationDerivedIso`: hence an isomorphism
  `NL_{B/k} ⊗_B Bʰ ≅ NL_{Bʰ/k}` in `D(Bʰ)`.
* `Stacks.Deformation.naiveCotangentExtOneHenselizationSourceEquiv`: hence
  `Ext¹_{Bʰ}(NL_{B/k} ⊗_B Bʰ, M) ≅ Ext¹_{Bʰ}(NL_{Bʰ/k}, M)` for every coefficient object `M`.

## Implementation notes

Three presentation gaps separate Stacks 0D08 from a statement about
`Stacks.Deformation.naiveCotangentExtOne`.

*Universes.* `Algebra.naiveCotangentComplexBaseChangeComparison` is a morphism of complexes of
modules in `ModuleCat.{max uk uB} Bʰ`, while the cochain presentation
`Stacks.Deformation.naiveCotangentCochainComplex` carries an extra universe lift and lives in
`ModuleCat.{max uk uB v} Bʰ`.  The comparison is therefore pushed forward along
`ModuleCat.uliftFunctor`, which is additive and preserves and reflects homology, so
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology` carries the quasi-isomorphism with it.

*Two-term presentation.* The lifted complexes are images of `HomologicalComplex.double`s, not
`double`s on the nose; `HomologicalComplex.doubleSelfIso` identifies each with the two-term
complex of its own differential, which is the form the cochain presentation is built from.  The
comparison is conjugated into that form, and `quasiIso_of_arrow_mk_iso` carries the
quasi-isomorphism across the conjugation.

*Complex shape.* Stacks 0D08 is stated in `ComplexShape.down ℕ` at `(1, 0)` and the derived
category of cochain complexes only accepts `ComplexShape.up ℤ` at `(-1, 0)`.  The cochain
comparison is built from the two components of the chain comparison by
`HomologicalComplex.mkHomFromDouble`, and
`HomologicalComplex.quasiIso_double_of_quasiIso_double` — along
`ComplexShape.embeddingDownNat` — transfers the quasi-isomorphism, which is what makes the two
components the *only* thing the cochain comparison depends on.

The degree-`0` term of `NL_{Bʰ/k}` in the cochain presentation is the degree-`0` term of
`Stacks.Deformation.naiveCotangentCochainComplex k Bʰ` on the nose: the target of the comparison
of Stacks 0D08 is `Algebra.naiveCotangentComplex k Bʰ`, so after the universe lift the two-term
complex of its differential *is* that cochain complex, with no further comparison, so the
conclusion is stated against `naiveCotangentCochainComplex`, and hence against
`naiveCotangentExtOne`.

## References

* [Stacks Project, Tag 0D08](https://stacks.math.columbia.edu/tag/0D08)
* [Stacks Project, Tag 0DZC](https://stacks.math.columbia.edu/tag/0DZC)
-/

@[expose] public section

open CategoryTheory Category Limits HomologicalComplex

universe uk uB v

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (k : Type uk) [CommRing k] (B : Type uB) [CommRing B] [Algebra k B]
  (Bh : Type uB) [CommRing Bh] [Algebra B Bh] [Algebra k Bh] [IsScalarTower k B Bh]

/-- `NL_{B/k} ⊗_B Bʰ`, the source of the comparison of Stacks 0D08, lifted termwise into the
module category `ModuleCat.{max uk uB v} Bʰ` that the cochain presentation of the naive cotangent
complex uses. -/
public abbrev naiveCotangentBaseChangeChainComplex : ChainComplex (ModuleCat.{max uk uB v} Bh) ℕ :=
  ((ModuleCat.uliftFunctor.{v} Bh).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Algebra.naiveCotangentComplexBaseChange k B Bh)

/-- `NL_{Bʰ/k}` lifted termwise into `ModuleCat.{max uk uB v} Bʰ`.  This is the complex the
cochain presentation `Stacks.Deformation.naiveCotangentCochainComplex k Bʰ` is the two-term
complex of. -/
public abbrev naiveCotangentHenselizationChainComplex :
    ChainComplex (ModuleCat.{max uk uB v} Bh) ℕ :=
  ((ModuleCat.uliftFunctor.{v} Bh).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Algebra.naiveCotangentComplex k Bh)

/-- `NL_{B/k} ⊗_B Bʰ` read as a two-term cochain complex, in cohomological degrees `-1` and `0`,
matching the presentation of `Stacks.Deformation.naiveCotangentCochainComplex`. -/
public abbrev naiveCotangentBaseChangeCochainComplex :
    CochainComplex (ModuleCat.{max uk uB v} Bh) ℤ :=
  HomologicalComplex.double
    ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
    ComplexShape.upIntRelNegOneZero

/-- The two-term cochain complex of the differential of `NL_{Bʰ/k}` is the cochain presentation
of the naive cotangent complex of `Bʰ` over `k`. -/
public theorem double_naiveCotangentHenselizationChainComplex_d :
    HomologicalComplex.double
        ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
        ComplexShape.upIntRelNegOneZero =
      naiveCotangentCochainComplex.{uk, uB, v} k Bh :=
  rfl

section ExtendScalars

/-- Three commuting squares pasted horizontally.  The outer square is the one
`HomologicalComplex.doubleSquareIso` asks for, and the three inner ones are the change of
two-term presentation, the commutation of extension of scalars with the universe lift, and the
change of two-term presentation on the other side. -/
private theorem comm_paste {C : Type*} [Category C] {X₁ X₀ A₁ A₀ D₁ D₀ E₁ E₀ : C}
    (d : X₁ ⟶ X₀) (p₁ : X₁ ⟶ A₁) (p₀ : X₀ ⟶ A₀) (m : A₁ ⟶ A₀)
    (q₁ : A₁ ⟶ D₁) (q₀ : A₀ ⟶ D₀) (n : D₁ ⟶ D₀)
    (r₁ : D₁ ⟶ E₁) (r₀ : D₀ ⟶ E₀) (d' : E₁ ⟶ E₀)
    (h₁ : d ≫ p₀ = p₁ ≫ m) (h₂ : m ≫ q₀ = q₁ ≫ n) (h₃ : n ≫ r₀ = r₁ ≫ d') :
    d ≫ p₀ ≫ q₀ ≫ r₀ = (p₁ ≫ q₁ ≫ r₁) ≫ d' := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc m, h₂, Category.assoc, h₃]
  simp only [Category.assoc]


/-- The degree-`1` comparison of `NL_{B/k} ⊗_B Bʰ` with the extension of scalars of `NL_{B/k}`:
both terms are `Bʰ ⊗_B I/I²`, one with the tensor product taken inside the complex and one with
it taken by `ModuleCat.extendScalars`. -/
public def baseChangeExtendScalarsXOne :
    (naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).X 1 ≅
      (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).obj
        ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).X 1) :=
  (ModuleCat.uliftFunctor.{v} Bh).mapIso
      (HomologicalComplex.doubleXIso₀ _ ComplexShape.downNatRelOneZero) ≪≫
    (ModuleCat.extendScalarsUliftIso.{uB, uB, v, max uk uB} (S := Bh)
      (ModuleCat.of B (Algebra.Generators.self k B).toExtension.Cotangent)).symm ≪≫
    (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).mapIso
      ((ModuleCat.uliftFunctor.{v} B).mapIso
        (HomologicalComplex.doubleXIso₀ _ ComplexShape.downNatRelOneZero).symm)

/-- The degree-`0` comparison of `NL_{B/k} ⊗_B Bʰ` with the extension of scalars of `NL_{B/k}`:
both terms are `Bʰ ⊗_B (Ω_{k[B]/k} ⊗ B)`. -/
public def baseChangeExtendScalarsXZero :
    (naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).X 0 ≅
      (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).obj
        ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).X 0) :=
  (ModuleCat.uliftFunctor.{v} Bh).mapIso
      (HomologicalComplex.doubleXIso₁ _ ComplexShape.downNatRelOneZero one_ne_zero) ≪≫
    (ModuleCat.extendScalarsUliftIso.{uB, uB, v, max uk uB} (S := Bh)
      (ModuleCat.of B (Algebra.Generators.self k B).toExtension.CotangentSpace)).symm ≪≫
    (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).mapIso
      ((ModuleCat.uliftFunctor.{v} B).mapIso
        (HomologicalComplex.doubleXIso₁ _ ComplexShape.downNatRelOneZero one_ne_zero).symm)

omit [Algebra k Bh] [IsScalarTower k B Bh] in
/-- The degree-`1` comparison, with `ModuleCat.uliftFunctor` and `ModuleCat.extendScalars`
applied to morphisms rather than to isomorphisms. -/
public theorem baseChangeExtendScalarsXOne_hom :
    (baseChangeExtendScalarsXOne.{uk, uB, v} k B Bh).hom =
      (ModuleCat.uliftFunctor.{v} Bh).map
          (HomologicalComplex.doubleXIso₀ _ ComplexShape.downNatRelOneZero).hom ≫
        (ModuleCat.extendScalarsUliftIso.{uB, uB, v, max uk uB} (S := Bh)
          (ModuleCat.of B (Algebra.Generators.self k B).toExtension.Cotangent)).inv ≫
        (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).map
          ((ModuleCat.uliftFunctor.{v} B).map
            (HomologicalComplex.doubleXIso₀ _ ComplexShape.downNatRelOneZero).inv) := rfl

omit [Algebra k Bh] [IsScalarTower k B Bh] in
/-- The degree-`0` comparison, with `ModuleCat.uliftFunctor` and `ModuleCat.extendScalars`
applied to morphisms rather than to isomorphisms. -/
public theorem baseChangeExtendScalarsXZero_hom :
    (baseChangeExtendScalarsXZero.{uk, uB, v} k B Bh).hom =
      (ModuleCat.uliftFunctor.{v} Bh).map
          (HomologicalComplex.doubleXIso₁ _ ComplexShape.downNatRelOneZero one_ne_zero).hom ≫
        (ModuleCat.extendScalarsUliftIso.{uB, uB, v, max uk uB} (S := Bh)
          (ModuleCat.of B (Algebra.Generators.self k B).toExtension.CotangentSpace)).inv ≫
        (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).map
          ((ModuleCat.uliftFunctor.{v} B).map
            (HomologicalComplex.doubleXIso₁ _ ComplexShape.downNatRelOneZero
              one_ne_zero).inv) := rfl

omit [Algebra k Bh] [IsScalarTower k B Bh] in
/-- The conormal differential of `NL_{B/k} ⊗_B Bʰ`, read through the identification of the
degree-`0` term of its two-term presentation, is the base change of the conormal differential. -/
public theorem baseChangeChainComplex_d_comm :
    (naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0 ≫
        (ModuleCat.uliftFunctor.{v} Bh).map
          (HomologicalComplex.doubleXIso₁ _ ComplexShape.downNatRelOneZero one_ne_zero).hom =
      (ModuleCat.uliftFunctor.{v} Bh).map
          (HomologicalComplex.doubleXIso₀ _ ComplexShape.downNatRelOneZero).hom ≫
        (ModuleCat.uliftFunctor.{v} Bh).map (ModuleCat.ofHom (LinearMap.baseChange Bh
          (Algebra.Generators.self k B).toExtension.cotangentComplex)) :=
  ((ModuleCat.uliftFunctor.{v} Bh).map_comp _ _).symm.trans
    (congrArg ((ModuleCat.uliftFunctor.{v} Bh).map)
      (HomologicalComplex.double_d_comp_doubleXIso₁_hom _ ComplexShape.downNatRelOneZero
        one_ne_zero))

/-- The conormal differential of `NL_{B/k}`, read through the identification of the degree-`1`
term of its two-term presentation, is the conormal differential. -/
public theorem liftedChainComplex_d_comm :
    (ModuleCat.uliftFunctor.{v} B).map
          (HomologicalComplex.doubleXIso₀ _ ComplexShape.downNatRelOneZero).inv ≫
        (naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0 =
      (ModuleCat.uliftFunctor.{v} B).map (ModuleCat.ofHom
          (Algebra.Generators.self k B).toExtension.cotangentComplex) ≫
        (ModuleCat.uliftFunctor.{v} B).map
          (HomologicalComplex.doubleXIso₁ _ ComplexShape.downNatRelOneZero one_ne_zero).inv :=
  (((ModuleCat.uliftFunctor.{v} B).map_comp _ _).symm.trans
    (congrArg ((ModuleCat.uliftFunctor.{v} B).map)
      (HomologicalComplex.doubleXIso₀_inv_comp_double_d _ ComplexShape.downNatRelOneZero
        one_ne_zero))).trans ((ModuleCat.uliftFunctor.{v} B).map_comp _ _)

omit [Algebra k Bh] [IsScalarTower k B Bh] in
/-- The naturality square crossed by the degreewise comparisons: the base change of the conormal
differential is its extension of scalars. -/
public theorem baseChangeExtendScalars_naturality :
    (ModuleCat.uliftFunctor.{v} Bh).map (ModuleCat.ofHom (LinearMap.baseChange Bh
          (Algebra.Generators.self k B).toExtension.cotangentComplex)) ≫
        (ModuleCat.extendScalarsUliftIso.{uB, uB, v, max uk uB} (S := Bh)
          (ModuleCat.of B (Algebra.Generators.self k B).toExtension.CotangentSpace)).inv =
      (ModuleCat.extendScalarsUliftIso.{uB, uB, v, max uk uB} (S := Bh)
          (ModuleCat.of B (Algebra.Generators.self k B).toExtension.Cotangent)).inv ≫
        (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).map
          ((ModuleCat.uliftFunctor.{v} B).map (ModuleCat.ofHom
            (Algebra.Generators.self k B).toExtension.cotangentComplex)) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (ModuleCat.extendScalarsUliftIso_naturality.{uB, uB, v, max uk uB} (S := Bh)
    (ModuleCat.ofHom (Algebra.Generators.self k B).toExtension.cotangentComplex)).symm

omit [Algebra k Bh] [IsScalarTower k B Bh] in
/-- The two degreewise comparisons form a commuting square with the two differentials: the
base-changed conormal differential is the extension of scalars of the conormal differential. -/
public theorem baseChangeExtendScalars_comm :
    (naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0 ≫
        (baseChangeExtendScalarsXZero.{uk, uB, v} k B Bh).hom =
      (baseChangeExtendScalarsXOne.{uk, uB, v} k B Bh).hom ≫
        (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).map
          ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0) := by
  rw [baseChangeExtendScalarsXOne_hom.{uk, uB, v} k B Bh,
    baseChangeExtendScalarsXZero_hom.{uk, uB, v} k B Bh]
  refine comm_paste _ _ _ _ _ _ _ _ _ _
    (baseChangeChainComplex_d_comm.{uk, uB, v} k B Bh)
    (baseChangeExtendScalars_naturality.{uk, uB, v} k B Bh)
    ?_
  exact (((ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).map_comp
      _ _).symm.trans (congrArg ((ModuleCat.extendScalars.{uB, uB, max uk uB v}
        (algebraMap B Bh)).map) (liftedChainComplex_d_comm.{uk, uB, v} k B).symm)).trans
    ((ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).map_comp _ _)

/-- **`NL_{B/k} ⊗_B Bʰ` is the termwise extension of scalars of `NL_{B/k}`.**  This identifies
the cochain presentation of the source of the comparison of Stacks 0D08 with the complex the
base-change identification of Stacks 0GPY is stated out of. -/
public def naiveCotangentBaseChangeExtendScalarsIso :
    letI : (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).IsLeftAdjoint :=
      ModuleCat.instIsLeftAdjointExtendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)
    naiveCotangentBaseChangeCochainComplex.{uk, uB, v} k B Bh ≅
      ((ModuleCat.extendScalars.{uB, uB, max uk uB v}
        (algebraMap B Bh)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (naiveCotangentCochainComplex.{uk, uB, v} k B) :=
  letI : (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).IsLeftAdjoint :=
    ModuleCat.instIsLeftAdjointExtendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)
  HomologicalComplex.doubleSquareIso
      ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
      ComplexShape.upIntRelNegOneZero (by decide)
      ((ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh)).map
        ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0))
      (baseChangeExtendScalarsXOne.{uk, uB, v} k B Bh)
      (baseChangeExtendScalarsXZero.{uk, uB, v} k B Bh)
      (baseChangeExtendScalars_comm.{uk, uB, v} k B Bh) ≪≫
    HomologicalComplex.doubleMapFunctorIso
      (ModuleCat.extendScalars.{uB, uB, max uk uB v} (algebraMap B Bh))
      ((naiveCotangentUliftedChainComplex.{uk, uB, v} k B).d 1 0)
      ComplexShape.upIntRelNegOneZero (by decide)

end ExtendScalars

section Comparison

omit [Algebra k Bh] [IsScalarTower k B Bh] in
/-- The lifted complex `NL_{B/k} ⊗_B Bʰ` has no differential out of degree `0`. -/
public theorem d_eq_zero_naiveCotangentBaseChangeChainComplex (j : ℕ)
    (hj : (ComplexShape.down ℕ).Rel 0 j) :
    (naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 0 j = 0 :=
  absurd hj (by simp [ComplexShape.down])

/-- The lifted complex `NL_{Bʰ/k}` has no differential out of degree `0`. -/
public theorem d_eq_zero_naiveCotangentHenselizationChainComplex (j : ℕ)
    (hj : (ComplexShape.down ℕ).Rel 0 j) :
    (naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 0 j = 0 :=
  absurd hj (by simp [ComplexShape.down])

omit [Algebra k Bh] [IsScalarTower k B Bh] in
/-- The lifted complex `NL_{B/k} ⊗_B Bʰ` vanishes outside degrees `1` and `0`. -/
public theorem isZero_naiveCotangentBaseChangeChainComplex_X (j : ℕ) (h₁ : j ≠ 1) (h₀ : j ≠ 0) :
    IsZero ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).X j) :=
  Functor.map_isZero (ModuleCat.uliftFunctor.{v} Bh)
    (HomologicalComplex.isZero_double_X _ _ j h₁ h₀)

/-- The lifted complex `NL_{Bʰ/k}` vanishes outside degrees `1` and `0`. -/
public theorem isZero_naiveCotangentHenselizationChainComplex_X (j : ℕ) (h₁ : j ≠ 1)
    (h₀ : j ≠ 0) :
    IsZero ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).X j) :=
  Functor.map_isZero (ModuleCat.uliftFunctor.{v} Bh)
    (HomologicalComplex.isZero_double_X _ _ j h₁ h₀)

/-- The comparison of Stacks 0D08, lifted termwise into `ModuleCat.{max uk uB v} Bʰ`. -/
public def liftedComparison :
    naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh ⟶
      naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh :=
  ((ModuleCat.uliftFunctor.{v} Bh).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (Algebra.naiveCotangentComplexBaseChangeComparison k k B Bh)

/-- The lifted comparison, conjugated into the two-term presentation in `ComplexShape.down ℕ`. -/
public def chainComparison :
    HomologicalComplex.double
        ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
        ComplexShape.downNatRelOneZero ⟶
      HomologicalComplex.double
        ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
        ComplexShape.downNatRelOneZero :=
  (HomologicalComplex.doubleSelfIso ComplexShape.downNatRelOneZero one_ne_zero _
      (d_eq_zero_naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh)
      (isZero_naiveCotangentBaseChangeChainComplex_X.{uk, uB, v} k B Bh)).hom ≫
    liftedComparison.{uk, uB, v} k B Bh ≫
    (HomologicalComplex.doubleSelfIso ComplexShape.downNatRelOneZero one_ne_zero _
      (d_eq_zero_naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh)
      (isZero_naiveCotangentHenselizationChainComplex_X.{uk, uB, v} k Bh)).inv

/-- The degree-`1` component of the chain comparison, read through the canonical identification
of the two-term complex's terms. -/
public def comparisonCoeffOne :
    (naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).X 1 ⟶
      (naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).X 1 :=
  (HomologicalComplex.doubleXIso₀
      ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
       ComplexShape.downNatRelOneZero).inv ≫
    (chainComparison.{uk, uB, v} k B Bh).f 1 ≫
    (HomologicalComplex.doubleXIso₀
      ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
       ComplexShape.downNatRelOneZero).hom

/-- The degree-`0` component of the chain comparison, read through the canonical identification
of the two-term complex's terms. -/
public def comparisonCoeffZero :
    (naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).X 0 ⟶
      (naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).X 0 :=
  (HomologicalComplex.doubleXIso₁
      ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
      ComplexShape.downNatRelOneZero one_ne_zero).inv ≫
    (chainComparison.{uk, uB, v} k B Bh).f 0 ≫
    (HomologicalComplex.doubleXIso₁
      ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
      ComplexShape.downNatRelOneZero one_ne_zero).hom

/-- The two components of the chain comparison commute with the differentials. -/
public theorem comparisonCoeff_comm :
    comparisonCoeffOne.{uk, uB, v} k B Bh ≫
        (naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0 =
      (naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0 ≫
        comparisonCoeffZero.{uk, uB, v} k B Bh := by
  have hc := (chainComparison.{uk, uB, v} k B Bh).comm 1 0
  rw [HomologicalComplex.double_d _ ComplexShape.downNatRelOneZero one_ne_zero,
    HomologicalComplex.double_d _ ComplexShape.downNatRelOneZero one_ne_zero] at hc
  rw [comparisonCoeffOne, comparisonCoeffZero]
  rw [← cancel_mono (HomologicalComplex.doubleXIso₁
    ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
      ComplexShape.downNatRelOneZero one_ne_zero).inv]
  simp only [Category.assoc]
  rw [← cancel_epi (HomologicalComplex.doubleXIso₀
    ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
       ComplexShape.downNatRelOneZero).hom]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [Category.assoc] using hc

/-- **The comparison `NL_{B/k} ⊗_B Bʰ ⟶ NL_{Bʰ/k}` in the cochain presentation.**  Its two
components are those of the comparison of Stacks 0D08, so it carries no information beyond that
morphism; what it adds is the complex shape the derived category of cochain complexes accepts. -/
public def naiveCotangentHenselizationComparison :
    naiveCotangentBaseChangeCochainComplex.{uk, uB, v} k B Bh ⟶
      naiveCotangentCochainComplex.{uk, uB, v} k Bh :=
  HomologicalComplex.mkHomFromDouble ComplexShape.upIntRelNegOneZero (by decide)
    (comparisonCoeffOne.{uk, uB, v} k B Bh ≫
      (HomologicalComplex.doubleXIso₀
        ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
        ComplexShape.upIntRelNegOneZero).inv)
    (comparisonCoeffZero.{uk, uB, v} k B Bh ≫
      (HomologicalComplex.doubleXIso₁
        ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
        ComplexShape.upIntRelNegOneZero (by decide)).inv)
    (by
      rw [HomologicalComplex.double_d _ ComplexShape.upIntRelNegOneZero (by decide)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, comparisonCoeff_comm, Category.assoc])
    (fun j hj ↦ by
      rw [HomologicalComplex.double_d_eq_zero₀ _
        ComplexShape.upIntRelNegOneZero 0 j (by decide), comp_zero])

/-- The degree-`-1` component of the cochain comparison is the degree-`1` component of the chain
comparison, read through the canonical identifications. -/
public theorem naiveCotangentHenselizationComparison_coeffOne :
    (HomologicalComplex.doubleXIso₀
          ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
          ComplexShape.upIntRelNegOneZero).inv ≫
        (naiveCotangentHenselizationComparison.{uk, uB, v} k B Bh).f (-1) ≫
        (HomologicalComplex.doubleXIso₀
          ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
          ComplexShape.upIntRelNegOneZero).hom =
      (HomologicalComplex.doubleXIso₀
          ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
          ComplexShape.downNatRelOneZero).inv ≫
        (chainComparison.{uk, uB, v} k B Bh).f 1 ≫
        (HomologicalComplex.doubleXIso₀
          ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
          ComplexShape.downNatRelOneZero).hom := by
  rw [naiveCotangentHenselizationComparison, HomologicalComplex.mkHomFromDouble_f₀]
  simp [comparisonCoeffOne]

/-- The degree-`0` component of the cochain comparison is the degree-`0` component of the chain
comparison, read through the canonical identifications. -/
public theorem naiveCotangentHenselizationComparison_coeffZero :
    (HomologicalComplex.doubleXIso₁
          ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
          ComplexShape.upIntRelNegOneZero (by decide)).inv ≫
        (naiveCotangentHenselizationComparison.{uk, uB, v} k B Bh).f 0 ≫
        (HomologicalComplex.doubleXIso₁
          ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
          ComplexShape.upIntRelNegOneZero (by decide)).hom =
      (HomologicalComplex.doubleXIso₁
          ((naiveCotangentBaseChangeChainComplex.{uk, uB, v} k B Bh).d 1 0)
          ComplexShape.downNatRelOneZero one_ne_zero).inv ≫
        (chainComparison.{uk, uB, v} k B Bh).f 0 ≫
        (HomologicalComplex.doubleXIso₁
          ((naiveCotangentHenselizationChainComplex.{uk, uB, v} k Bh).d 1 0)
          ComplexShape.downNatRelOneZero one_ne_zero).hom := by
  rw [naiveCotangentHenselizationComparison, HomologicalComplex.mkHomFromDouble_f₁]
  simp [comparisonCoeffZero]

end Comparison

section Henselization

variable (J : Ideal B)
  (hhens : HenselianPair Bh (J.map (algebraMap B Bh)))
  (huniv : ∀ (C : Type uB) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
    ∀ f : B →+* C, J ≤ JC.comap f →
      ∃! g : Bh →+* C, g.comp (algebraMap B Bh) = f ∧
        J.map (algebraMap B Bh) ≤ JC.comap g)

include J hhens huniv in
/-- The chain comparison, in the two-term presentation, is a quasi-isomorphism. -/
public theorem quasiIso_chainComparison : QuasiIso (chainComparison.{uk, uB, v} k B Bh) := by
  have h := Algebra.naiveCotangentComplex_quasiIso_henselizationPair k B J Bh hhens huniv
  have : QuasiIso (liftedComparison.{uk, uB, v} k B Bh) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
      (ModuleCat.uliftFunctor.{v} Bh)).mpr h
  rw [chainComparison]
  infer_instance

include J hhens huniv in
/-- **The cochain comparison `NL_{B/k} ⊗_B Bʰ ⟶ NL_{Bʰ/k}` is a quasi-isomorphism.**  This is
Stacks 0D08 for the henselization of a pair, carried across the universe lift, the two-term
presentation and the change of complex shape. -/
public theorem quasiIso_naiveCotangentHenselizationComparison :
    QuasiIso (naiveCotangentHenselizationComparison.{uk, uB, v} k B Bh) := by
  have hchain : QuasiIso (chainComparison.{uk, uB, v} k B Bh) :=
    quasiIso_chainComparison.{uk, uB, v} k B Bh J hhens huniv
  exact HomologicalComplex.quasiIso_double_of_quasiIso_double _
    ComplexShape.embeddingDownNat ComplexShape.downNatRelOneZero one_ne_zero
    (chainComparison.{uk, uB, v} k B Bh)
    (naiveCotangentHenselizationComparison.{uk, uB, v} k B Bh)
    (naiveCotangentHenselizationComparison_coeffOne.{uk, uB, v} k B Bh)
    (naiveCotangentHenselizationComparison_coeffZero.{uk, uB, v} k B Bh)

include J hhens huniv in
/-- **Stacks 0D08 for the henselization of a pair, in the derived category.**  The canonical
comparison identifies `NL_{B/k} ⊗_B Bʰ` with `NL_{Bʰ/k}` as objects of `D(Bʰ)`. -/
public def naiveCotangentHenselizationDerivedIso :
    DerivedCategory.Q.obj (naiveCotangentBaseChangeCochainComplex.{uk, uB, v} k B Bh) ≅
      DerivedCategory.Q.obj (naiveCotangentCochainComplex.{uk, uB, v} k Bh) :=
  have : IsIso (DerivedCategory.Q.map
      (naiveCotangentHenselizationComparison.{uk, uB, v} k B Bh)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _
      (naiveCotangentHenselizationComparison.{uk, uB, v} k B Bh)).mpr
      (quasiIso_naiveCotangentHenselizationComparison.{uk, uB, v} k B Bh J hhens huniv)
  asIso (DerivedCategory.Q.map (naiveCotangentHenselizationComparison.{uk, uB, v} k B Bh))

include J hhens huniv in
/-- **First extension groups out of `NL_{B/k} ⊗_B Bʰ` and out of `NL_{Bʰ/k}` agree.**
Precomposition with the canonical comparison, which is invertible in `D(Bʰ)`, identifies the two
groups for every coefficient object `M`. -/
public def naiveCotangentExtOneHenselizationSourceEquiv
    (M : DerivedCategory (ModuleCat.{max uk uB v} Bh)) :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj (naiveCotangentBaseChangeCochainComplex.{uk, uB, v} k B Bh)) M 1 ≃+
      DerivedCategory.Ext
        (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{uk, uB, v} k Bh)) M 1 :=
  extOneSourceIso (naiveCotangentHenselizationDerivedIso.{uk, uB, v} k B Bh J hhens huniv)

end Henselization

end

end Stacks.Deformation

end
