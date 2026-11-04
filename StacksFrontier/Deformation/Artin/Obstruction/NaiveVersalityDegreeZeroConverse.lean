module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFormallySmoothComparison
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldCartesianLift
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldClassEquation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityTangentFactorization

/-!
# Stacks 07YM, the direction `(2) ⇒ (1)` in degree zero

Let `x` be a family over `Spec A` whose tangent theory is represented by `ξ : E ⟶ NL_{A/Λ}` in
the sense of hypothesis (ii) of Stacks 07YM. The proof of `(2) ⇒ (1)` opens with the sentence

> The map `dη` on tangent spaces is surjective because it is identified with the dual of the
> injective map `H^0(E ⊗ᴸ_A k) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A k)`,

and the identification it appeals to is the one the previous paragraph of the source sets up:
`Ext⁰_A(NL_{A/Λ}, k) = Der_Λ(A, k)` and `Ext⁰_A(E, k) = T_x(k)`, under which the map induced
by `ξ` *is* the map on tangent spaces. This file supplies that step, read in the direction
`(2) ⇒ (1)`: condition (2) in degree `0` makes the map `Der_Λ(A, k) ⟶ T_x(k)` surjective.

Only one half of the identification was available. The tangent side,
`Deformation.Artin.tangentEquiv_canonicalTangentMap`, records that the map on tangent spaces
sends `θ : Ω_{A/Λ} →ₗ[A] k` to `ξ` followed by the augmentation
`Deformation.Artin.naiveCotangentToDifferentials` followed by `θ`; that is enough for
`(1) ⇒ (2)`, which only needs the image of the tangent map to consist of such composites.
For `(2) ⇒ (1)` the equality `Ext⁰_A(NL_{A/Λ}, k) = Der_Λ(A, k)` is needed as an equality:
hypothesis (2) produces an *arbitrary* morphism `NL_{A/Λ} ⟶ k[0]` of `D(A)`, and it has to be
recognized as coming from a tangent vector. That is the first half of this file.

The second half turns the surjectivity on tangent spaces into the statement the criterion of
Stacks 06IU consumes at the dual numbers: every infinitesimal deformation of `x₀` over `k[k]`
extends to `x`. That is the converse of
`Deformation.Artin.exists_extends_of_liftsAtResiduePoint`, and it reuses the class equation
`Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap` the forward direction is
built from, run backwards.

What is **not** here is the last step of the criterion's first condition, the surjectivity of
`Deformation.mapIsomorphismClasses` for the associated morphism of the formal object over
`A_𝔭^∧`. That statement is about the formal object itself, which the comparison of Stacks 0CXK
(`Deformation.Artin.isVersalAt_iff_isVersal`) produces from a complete-local restriction of `x`;
until that object is in hand the statement cannot be formed.

## Main definitions

* `Deformation.Artin.kaehlerProjection` — the degree-`0` component of the augmentation
  `NL_{A/Λ} ⟶ Ω_{A/Λ}[0]`: the identification of the degree-`0` term of the two-term complex
  with the cotangent space of the canonical presentation, followed by
  `Algebra.Extension.toKaehler`.
* `Deformation.Artin.kaehlerShortComplex` — the conormal sequence
  `J/J² ⟶ ⊕_i A dx_i ⟶ Ω_{A/Λ}` of the canonical presentation, as a short complex.
* `Deformation.Artin.kaehlerOpcyclesIso` and `Deformation.Artin.kaehlerHomologyIso` — the
  resulting identifications of the degree-`0` opcycles and of `H⁰` of the two-term complex
  with `Ω_{A/Λ}`.

## Main results

* `Deformation.Artin.naiveCotangentToDifferentials_eq` — the augmentation is the canonical
  chain map onto `H⁰` placed in degree `0`, taken through
  `Deformation.Artin.kaehlerHomologyIso`.
* `Deformation.Artin.isIso_homologyFunctor_map_naiveCotangentToDifferentials` — the
  augmentation is an isomorphism on `H⁰`.
* `Deformation.Artin.bijective_comp_naiveCotangentToDifferentials` — **the identification
  `Ext⁰_A(NL_{A/Λ}, M) = Der_Λ(A, M)`**: composing the augmentation with a module map
  `Ω_{A/Λ} ⟶ M` is a bijection onto the morphisms `NL_{A/Λ} ⟶ M[0]` of `D(A)`.
* `Deformation.Artin.surjective_canonicalTangentMap_of_surjective_comp` — **Stacks 07YM,
  `(2) ⇒ (1)` in degree `0`**: if precomposition with `ξ` is surjective on morphisms
  `NL_{A/Λ} ⟶ k[0]`, which is what condition (2) in degree `0` says by
  `Deformation.Artin.injective_derivedTensorFibre_zero_iff_surjective_comp`, then the map
  `Der_Λ(A, k) ⟶ T_x(k)` on tangent spaces is surjective.
* `Deformation.Artin.exists_extends_of_surjective_canonicalTangentMap` — the geometric form of
  that conclusion, and the exact converse of
  `Deformation.Artin.exists_extends_of_liftsAtResiduePoint`: a surjective map on tangent spaces
  makes every lift of `x₀` over the dual numbers of `k` extend to `x`.

## Implementation notes

`Ext⁰_A(NL_{A/Λ}, M) = Der_Λ(A, M)` is the statement that the augmentation is an isomorphism
on `H⁰` together with the fact that `H⁰` computes the morphisms out of a complex in degrees
`≤ 0` into one in degrees `≥ 0`
(`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE`, Stacks 06XS, which was
sealed `private` in `StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic.lean` and is
published there by this file's branch). The complement is that `D(A)`'s single functor is
fully faithful, so a morphism `Ω_{A/Λ}[0] ⟶ M[0]` is a module map.

That the augmentation is an isomorphism on `H⁰` is *not* proved by computing its homology map
directly. The augmentation is a `HomologicalComplex.mkHomFromDouble`, whereas the canonical
chain map onto `H⁰` placed in degree `0` is
`Stacks.NaiveCotangentFormallySmoothComparison.homToSingleHomology`, whose homology map in that
degree is the chosen identification of `H⁰` by
`Stacks.NaiveCotangentFormallySmoothComparison.homologyMap_homToSingleHomology` — a general
fact carrying no hypothesis on the complex, the formal smoothness of its own file entering only
in the vanishing of the other cohomology objects. So the two chain maps are identified instead,
which is an equality of their degree-`0` components (`HomologicalComplex.to_single_hom_ext`),
and the passage from the chain-level homology map to the derived-category one is
`CategoryTheory.NatIso.isIso_map_iff` at `DerivedCategory.homologyFunctorFactors` — the same
one-line argument as
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isIso_homologyFunctor_map_Q_map_iff`, which
is generic but lives behind a ringed-space import a deformation file should not take on;
and the identification of `H⁰` is chosen to make that equality hold: it is the comparison of
the degree-`0` opcycles with `Ω_{A/Λ}` through the cokernel property, so that the comparison
composed with the projection from the degree-`0` term is the augmentation's own degree-`0`
component.

The statements are for an arbitrary coefficient module `M` and carry no Noetherian or
finite-type hypothesis: the presentation used is `Algebra.Generators.self Λ A`, by the whole of
`A`, and the only property of it that enters is the exactness and surjectivity of its conormal
sequence.

`Deformation.Artin.surjective_canonicalTangentMap_of_surjective_comp` takes neither
`Mono baseMap` nor the containments of the field and of its dual numbers in the site, which the
`(1) ⇒ (2)` half needs: its proof is the functorial isomorphism of hypothesis (ii) at the one
site module `ModuleCat.of A k`, together with the bijection above, and no arrow of the site is
built.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YC](https://stacks.math.columbia.edu/tag/07YC)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex
open ComplexShape (upIntRelNegOneZero)

universe u v

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

/-! ### The conormal sequence of the canonical presentation -/

section Conormal

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The canonical presentation of `A` over `Λ` — by the whole of `A` — read as an extension.
This is the presentation whose two-term complex is
`Deformation.Artin.naiveCotangentDouble`. -/
public abbrev selfExtension : Algebra.Extension Λ A :=
  (Algebra.Generators.self Λ A).toExtension

/-- The degree-`0` component of the augmentation `NL_{A/Λ} ⟶ Ω_{A/Λ}[0]`: the identification
of the degree-`0` term of the two-term complex with the cotangent space of the canonical
presentation, followed by `Algebra.Extension.toKaehler`. -/
public def kaehlerProjection :
    (naiveCotangentDouble Λ A).X 0 ⟶ differentialsModule Λ A :=
  (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (selfExtension Λ A).cotangentComplex)
      upIntRelNegOneZero (by omega)).hom ≫
    ModuleCat.ofHom (selfExtension Λ A).toKaehler

/-- The differential of the two-term complex is killed by
`Deformation.Artin.kaehlerProjection`: this is the exactness of the conormal sequence at its
middle term, in the weak form that the composite vanishes. -/
public theorem d_comp_kaehlerProjection :
    (naiveCotangentDouble Λ A).d (-1) 0 ≫ kaehlerProjection Λ A = 0 := by
  rw [HomologicalComplex.double_d _ _ (by omega)]
  dsimp only [kaehlerProjection]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext z
  exact (selfExtension Λ A).exact_cotangentComplex_toKaehler.apply_apply_eq_zero
    ((HomologicalComplex.doubleXIso₀
      (ModuleCat.ofHom (selfExtension Λ A).cotangentComplex) upIntRelNegOneZero).hom z)

/-- `Deformation.Artin.kaehlerProjection` is an epimorphism: `Algebra.Extension.toKaehler` is
surjective and the other factor is an isomorphism. -/
public instance epi_kaehlerProjection : Epi (kaehlerProjection Λ A) := by
  have h : Epi (ModuleCat.ofHom (selfExtension Λ A).toKaehler) :=
    (ModuleCat.epi_iff_surjective _).2 Algebra.Extension.toKaehler_surjective
  change Epi ((HomologicalComplex.doubleXIso₁
      (ModuleCat.ofHom (selfExtension Λ A).cotangentComplex) upIntRelNegOneZero (by omega)).hom ≫
    ModuleCat.ofHom (selfExtension Λ A).toKaehler)
  infer_instance

/-- The conormal sequence `J/J² ⟶ ⊕_i A dx_i ⟶ Ω_{A/Λ}` of the canonical presentation, with
its first two terms read as the two terms of `Deformation.Artin.naiveCotangentDouble`. -/
public def kaehlerShortComplex : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk ((naiveCotangentDouble Λ A).d (-1) 0) (kaehlerProjection Λ A)
    (d_comp_kaehlerProjection Λ A)

/-- The conormal sequence of the canonical presentation is exact at its middle term. -/
public theorem kaehlerShortComplex_exact : (kaehlerShortComplex Λ A).Exact := by
  let S := ModuleCat.shortComplexOfCompEqZero
    (selfExtension Λ A).cotangentComplex (selfExtension Λ A).toKaehler
    (LinearMap.ext fun z =>
      (selfExtension Λ A).exact_cotangentComplex_toKaehler.apply_apply_eq_zero z)
  have hS : S.Exact :=
    ModuleCat.shortComplex_exact _ (selfExtension Λ A).exact_cotangentComplex_toKaehler
  have e : S ≅ kaehlerShortComplex Λ A :=
    ShortComplex.isoMk
      (HomologicalComplex.doubleXIso₀
        (ModuleCat.ofHom (selfExtension Λ A).cotangentComplex) upIntRelNegOneZero).symm
      (HomologicalComplex.doubleXIso₁
        (ModuleCat.ofHom (selfExtension Λ A).cotangentComplex)
        upIntRelNegOneZero (by omega)).symm
      (Iso.refl _)
      (by
        dsimp only [S, kaehlerShortComplex, ShortComplex.mk,
          ModuleCat.shortComplexOfCompEqZero]
        rw [HomologicalComplex.double_d _ _ (by omega)]
        simp)
      (by simp [S, kaehlerShortComplex, kaehlerProjection,
        ModuleCat.shortComplexOfCompEqZero])
  exact ShortComplex.exact_of_iso e hS

/-- The last map of the conormal sequence is an epimorphism. Stated at the short complex, for
the cokernel property that `Deformation.Artin.kaehlerOpcyclesIso` consumes. -/
public instance epi_kaehlerShortComplex_g : Epi (kaehlerShortComplex Λ A).g :=
  inferInstanceAs (Epi (kaehlerProjection Λ A))

end Conormal

/-! ### `H⁰` of the two-term complex is the module of differentials -/

section HomologyZero

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The degree-`0` opcycles of the two-term complex are `Ω_{A/Λ}`: both the projection from
the degree-`0` term and `Deformation.Artin.kaehlerProjection` are cokernels of the only
differential, the second by the exactness of the conormal sequence. -/
public def kaehlerOpcyclesIso :
    (naiveCotangentDouble Λ A).opcycles 0 ≅ differentialsModule Λ A :=
  IsColimit.coconePointUniqueUpToIso
    ((naiveCotangentDouble Λ A).opcyclesIsCokernel (-1) 0 (by simp))
    (kaehlerShortComplex_exact Λ A).gIsCokernel

/-- The comparison of the degree-`0` opcycles with `Ω_{A/Λ}` carries the projection from the
degree-`0` term to `Deformation.Artin.kaehlerProjection`. -/
public theorem pOpcycles_comp_kaehlerOpcyclesIso :
    (naiveCotangentDouble Λ A).pOpcycles 0 ≫ (kaehlerOpcyclesIso Λ A).hom =
      kaehlerProjection Λ A :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    ((naiveCotangentDouble Λ A).opcyclesIsCokernel (-1) 0 (by simp))
    (kaehlerShortComplex_exact Λ A).gIsCokernel WalkingParallelPair.one

/-- The two-term complex has nothing in degree `1`. -/
public theorem isZero_naiveCotangentDouble_X_one :
    IsZero ((naiveCotangentDouble Λ A).X 1) :=
  HomologicalComplex.isZero_double_X _ upIntRelNegOneZero 1 (by omega) (by omega)

/-- `H⁰` of the two-term complex is `Ω_{A/Λ}`: nothing maps out of degree `0`, so the homology
there is the opcycles, which `Deformation.Artin.kaehlerOpcyclesIso` identifies. -/
public def kaehlerHomologyIso :
    (naiveCotangentDouble Λ A).homology 0 ≅ differentialsModule Λ A :=
  (naiveCotangentDouble Λ A).isoHomologyι 0 1 (by simp)
      ((isZero_naiveCotangentDouble_X_one Λ A).eq_of_tgt _ _) ≪≫
    kaehlerOpcyclesIso Λ A

end HomologyZero

/-! ### The augmentation of the naive cotangent complex, read on `H⁰` -/

section Augmentation

open Stacks.NaiveCotangentFormallySmoothComparison

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- The degree-`0` component of the canonical chain map onto `H⁰` placed in degree `0`, taken
through `Deformation.Artin.kaehlerHomologyIso`, is
`Deformation.Artin.kaehlerProjection`. -/
public theorem kaehlerHomToSingleHomology_f_zero :
    (homToSingleHomology (naiveCotangentDouble Λ A) 0 1 (by simp)
        (isZero_naiveCotangentDouble_X_one Λ A) (kaehlerHomologyIso Λ A)).f 0 =
      kaehlerProjection Λ A ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (differentialsModule Λ A)).inv := by
  unfold homToSingleHomology
  rw [HomologicalComplex.mkHomToSingle_f]
  refine congrArg (· ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (differentialsModule Λ A)).inv) ?_
  unfold toHomologyOfIsZeroNext
  dsimp only [kaehlerHomologyIso, Iso.trans_hom]
  rw [Category.assoc, Iso.inv_hom_id_assoc, pOpcycles_comp_kaehlerOpcyclesIso]

/-- The augmentation `NL_{A/Λ} ⟶ Ω_{A/Λ}[0]` of `D(A)` is the image of the canonical chain map
onto `H⁰` placed in degree `0`, taken through `Deformation.Artin.kaehlerHomologyIso`. Two
chain maps into a complex concentrated in one degree agree as soon as they agree there. -/
public theorem naiveCotangentToDifferentials_eq :
    naiveCotangentToDifferentials Λ A =
      DerivedCategory.Q.map (homToSingleHomology (naiveCotangentDouble Λ A) 0 1 (by simp)
        (isZero_naiveCotangentDouble_X_one Λ A) (kaehlerHomologyIso Λ A)) := by
  unfold naiveCotangentToDifferentials
  refine congrArg DerivedCategory.Q.map (HomologicalComplex.to_single_hom_ext ?_)
  simp only [naiveCotangentToDifferentialsChainMap, HomologicalComplex.mkHomFromDouble_f₁,
    kaehlerHomToSingleHomology_f_zero, kaehlerProjection, Category.assoc]
  rfl

/-- **The augmentation of the naive cotangent complex is an isomorphism on `H⁰`.** The chain
map it comes from induces the chosen identification of `H⁰` by
`Stacks.NaiveCotangentFormallySmoothComparison.homologyMap_homToSingleHomology`. -/
public theorem isIso_homologyFunctor_map_naiveCotangentToDifferentials :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (naiveCotangentToDifferentials Λ A)) := by
  have h : IsIso (HomologicalComplex.homologyMap
      (homToSingleHomology (naiveCotangentDouble Λ A) 0 1 (by simp)
        (isZero_naiveCotangentDouble_X_one Λ A) (kaehlerHomologyIso Λ A)) 0) := by
    rw [homologyMap_homToSingleHomology]
    infer_instance
  rw [naiveCotangentToDifferentials_eq]
  exact (NatIso.isIso_map_iff
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0) _).2 h

end Augmentation

/-! ### `Ext⁰` out of the naive cotangent complex is derivations -/

section ExtZero

/-- A map is bijective as soon as it becomes bijective after an injective map. -/
private theorem bijective_of_comp_bijective {α β γ : Type*} {f : α → β} {g : β → γ}
    (hg : Function.Injective g) (h : Function.Bijective (g ∘ f)) : Function.Bijective f :=
  ⟨fun a b hab => h.injective (by simp only [Function.comp_apply, hab]),
    fun b => by
      obtain ⟨a, ha⟩ := h.surjective (g b)
      exact ⟨a, hg ha⟩⟩

/-- Precomposition with an isomorphism is bijective on morphisms. -/
private theorem bijective_comp_left {D : Type*} [Category D] {X Y Z : D} (a : X ⟶ Y) [IsIso a] :
    Function.Bijective (fun u : Y ⟶ Z => a ≫ u) :=
  ⟨fun u v h => by simpa using congrArg (fun w => inv a ≫ w) h,
    fun w => ⟨inv a ≫ w, by simp⟩⟩

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]

/-- **`Ext⁰_A(NL_{A/Λ}, M) = Der_Λ(A, M)`.** Composing the augmentation
`NL_{A/Λ} ⟶ Ω_{A/Λ}[0]` with a module map `Ω_{A/Λ} ⟶ M` is a bijection onto the morphisms
`NL_{A/Λ} ⟶ M[0]` of `D(A)`.

This is the identification the proof of [Stacks, Tag 07YM] writes as
`Ext⁰_A(NL_{A/Λ}, k) = Der_Λ(A, k)`. The naive cotangent complex lies in degrees `≤ 0` and
`M[0]` in degrees `≥ 0`, so `H⁰` computes the morphisms between them
(`DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE`); the augmentation is an
isomorphism on `H⁰`
(`Deformation.Artin.isIso_homologyFunctor_map_naiveCotangentToDifferentials`), and the single
functor of `D(A)` is fully faithful, so a morphism `Ω_{A/Λ}[0] ⟶ M[0]` is a module map. -/
@[stacks 07YM "Ext^0_A(NL_{A/Lambda}, M) = Der_Lambda(A, M)"]
public theorem bijective_comp_naiveCotangentToDifferentials (M : ModuleCat.{u} A) :
    Function.Bijective (fun θ : differentialsModule Λ A ⟶ M =>
      naiveCotangentToDifferentials Λ A ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map θ) := by
  have hle : (derivedNaiveCotangentComplex Λ A).IsLE 0 := by
    change (DerivedCategory.Q.obj (naiveCotangentDouble Λ A)).IsLE 0
    have : (naiveCotangentDouble Λ A).IsStrictlyLE 0 := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact HomologicalComplex.isZero_double_X _ upIntRelNegOneZero i (by omega) (by omega)
    infer_instance
  have ht := isIso_homologyFunctor_map_naiveCotangentToDifferentials Λ A
  have hNL := DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    (derivedNaiveCotangentComplex Λ A)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) 0
  have hOmega := DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (differentialsModule Λ A))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) 0
  refine Function.Bijective.comp ?_ ((Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _)
  refine bijective_of_comp_bijective hNL.injective ?_
  convert (bijective_comp_left
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (naiveCotangentToDifferentials Λ A))).comp hOmega using 1
  funext f
  simp

end ExtZero

/-! ### Condition (2) in degree zero makes the tangent map surjective -/

section TangentSurjective

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable (E : DerivedCategory (ModuleCat.{u} A))
  (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
  (tangentEquiv : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) ≃+
      (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.obj))
  (tangentEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M),
    tangentEquiv N ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map f z) =
      tangentEquiv M z ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom)
  (tangentEquiv_canonical : tangentEquiv (differentialsSiteModule Λ A B hΩ)
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization).element =
      ξ ≫ naiveCotangentToDifferentials Λ A)

include hRS baseFactorization tangentEquiv_natural tangentEquiv_canonical in
/-- **Stacks 07YM, `(2) ⇒ (1)` in degree `0`.** If precomposition with `ξ` is surjective on
morphisms `NL_{A/Λ} ⟶ k[0]` of `D(A)`, then the map `Der_Λ(A, k) ⟶ T_x(k)` on tangent spaces
is surjective.

The hypothesis is condition (2) of the tag in degree `0`: by
`Deformation.Artin.injective_derivedTensorFibre_zero_iff_surjective_comp` the injectivity of
`H^0(ξ ⊗ᴸ_A k)` is exactly this surjectivity, and
`DerivedCategory.surjective_extZero_comp_iff_surjective_comp` reads it on `Ext⁰` if wanted.
The conclusion is the first condition of the versality criterion of Stacks 06IU, read through
the identification of `T_x(k)` with the infinitesimal deformations of `x₀`.

The source's sentence is that the map on tangent spaces is the dual of `H^0(ξ ⊗ᴸ_A k)` under
`Ext⁰_A(NL_{A/Λ}, k) = Der_Λ(A, k)` and `Ext⁰_A(E, k) = T_x(k)`. The second identification is
hypothesis (ii), and `Deformation.Artin.tangentEquiv_canonicalTangentMap` is its value on the
map on tangent spaces: a tangent vector `θ` goes to `ξ` followed by the augmentation followed
by `θ`. The first identification is
`Deformation.Artin.bijective_comp_naiveCotangentToDifferentials`, which is what turns the
arbitrary morphism `NL_{A/Λ} ⟶ k[0]` produced by the hypothesis into such a `θ`. -/
@[stacks 07YM "(2) implies (1), degree 0: the map on tangent spaces is surjective"]
public theorem surjective_canonicalTangentMap_of_surjective_comp
    (hsurj : Function.Surjective (fun f : derivedNaiveCotangentComplex Λ A ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A k) =>
      ξ ≫ f)) :
    Function.Surjective (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
      baseFactorization) := by
  intro z
  obtain ⟨f, hf⟩ := hsurj (tangentEquiv (⟨ModuleCat.of A k, hk⟩ : SiteModule A B) z)
  obtain ⟨θ, hθ⟩ :=
    (bijective_comp_naiveCotangentToDifferentials Λ A (ModuleCat.of A k)).surjective f
  refine ⟨θ.hom, (tangentEquiv (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)).injective ?_⟩
  rw [tangentEquiv_canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
    baseFactorization E ξ tangentEquiv tangentEquiv_natural tangentEquiv_canonical θ.hom]
  have hθ' : naiveCotangentToDifferentials Λ A ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map θ = f := hθ
  rw [show ModuleCat.ofHom θ.hom = θ from rfl, hθ']
  exact hf

end TangentSurjective


/-! ### Every infinitesimal deformation over the dual numbers extends -/

section Extends

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include B S hS toS hA hAk x hx hp hRS hΩ hk hkk baseMap baseFactorization in
/-- **Stacks 07YM, `(2) ⇒ (1)` at the dual numbers.** If the map `Der_Λ(A, k) ⟶ T_x(k)` on
tangent spaces is surjective, then every lift of `x₀` along the square-zero immersion
`Spec k ⟶ Spec k[k]` extends to `x`: its structure arrow composes with an arrow from its
target to `x` to give the chosen restriction arrow.

This is the exact converse of `Deformation.Artin.exists_extends_of_liftsAtResiduePoint`, and
is the dual-numbers content of the first condition of the versality criterion of Stacks 06IU.

The class of the lift is hit by a tangent vector `θ`, through the two bijections
`Deformation.Artin.canonicalFieldBaseChangeEquiv` and the tangent functor's `liftEquiv`. By
`Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap` that class is also the
class of the connecting arrow `χ` attached to *any* lift `(y, φ)` of `x` along
`Deformation.Artin.canonicalDualNumbersArrow θ`, one of which exists because `p` is fibred in
groupoids (`Deformation.Artin.exists_canonicalDualNumbersLift`). Two lifts in one class are
isomorphic over `k[k]` compatibly with their arrows from `x₀`, so the isomorphism's component
at the target carries the given lift's structure arrow to `χ`, and
`Deformation.Artin.canonicalDualNumbersConnectingArrow_fac` says `χ ≫ φ` is the chosen
restriction arrow.

`Mono baseMap` is not needed here, although the forward direction needs it: it enters the
forward direction through `Deformation.Artin.exists_unique_eq_canonicalDualNumbersArrow`, which
recovers a tangent vector from an arrow of the site, and this direction is handed the tangent
vector instead. -/
@[stacks 07YM "(2) implies (1): an infinitesimal deformation over the dual numbers extends"]
public theorem exists_extends_of_surjective_canonicalTangentMap
    (hsurj : Function.Surjective (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk
      baseMap baseFactorization)) :
    letI : p.IsFibered := hp.isFibered
    ∀ (w : (Under.post p).Fiber (Under.mk (eqToHom
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2 ≫
        squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)))),
      ∃ b : w.1.right ⟶ x,
        w.1.hom ≫ b = (Functor.chosenPullbacks p).map
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩ := by
  let : p.IsFibered := hp.isFibered
  intro w
  obtain ⟨c, hc⟩ := (canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk
    hkk).surjective (Quotient.mk _ w)
  obtain ⟨t, ht⟩ := ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
    (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)).surjective c
  obtain ⟨θ, hθ⟩ := hsurj t
  obtain ⟨y, φ, -, hφ⟩ := exists_canonicalDualNumbersLift Λ A k B S hS toS hA p x hx hp hRS hΩ
    hkk baseMap baseFactorization θ
  have hclass := canonicalFieldBaseChangeEquiv_canonicalTangentMap Λ A k B S hS toS hA hAk p x hx
    hp hRS hΩ hk hkk baseMap baseFactorization θ y φ hφ
  obtain ⟨e⟩ := Quotient.exact (hclass.symm.trans (by rw [hθ, ht, hc]))
  refine ⟨e.inv.1.right ≫ φ, ?_⟩
  rw [← Category.assoc, Under.w e.inv.1]
  exact canonicalDualNumbersConnectingArrow_fac Λ A k B S hS toS hA hAk p x hx hp hRS hΩ hkk
    baseMap baseFactorization θ y φ hφ

end Extends

end Deformation.Artin

end
