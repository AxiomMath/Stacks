module

public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.HodgeToDeRham
public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.Convergence
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.FirstQuadrantTotalFiltration
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexAsAFilteredComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbutmentOfAFilteredComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FirstQuadrantAbutmentLowDegrees
import StacksCore.Tactic.StacksAttribute

/-!
# The two spectral sequences of the de Rham complex

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X` — for a morphism of schemes `p : X → S` this is
`p^{-1}𝒪_S ⟶ 𝒪_X` — and let `Ω^•_{X/S}` be the relative de Rham complex. Following Stacks
Section 0FM6, take a Cartan-Eilenberg resolution of `Ω^•_{X/S}` ([Stacks, Tag 015I]) and apply
[Stacks, Tag 015J] to the global sections functor `Γ(X, -)`. This gives two spectral sequences,
both bounded and both converging to the de Rham cohomology `H^*_{dR}(X/S)`:

* the **Hodge-to-de Rham spectral sequence**, with first page `E_1^{p,q} = H^q(X, Ω^p_{X/S})`
  and differential `d_1^{p,q} : H^q(X, Ω^p_{X/S}) → H^q(X, Ω^{p+1}_{X/S})` induced by the de Rham
  differential;
* the **conjugate spectral sequence**, with second page `E_2^{p,q} = H^p(X, 𝓗^q)`, where
  `𝓗^q = H^q(Ω^•_{X/S})` is the `q`-th cohomology sheaf of the de Rham complex, and differentials
  `E_2^{p,q} → E_2^{p+2,q-1}`.

Reading them in low degrees gives `H^0_{dR}(X/S) = Ker(d : H^0(X, 𝒪_X) → H^0(X, Ω^1_{X/S}))`,
`H^0_{dR}(X/S) = H^0(X, 𝓗^0)`, and the exact sequence
`0 → H^1(X, 𝓗^0) → H^1_{dR}(X/S) → H^0(X, 𝓗^1) → H^2(X, 𝓗^0) → H^2_{dR}(X/S)`.

## Main results

* `AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRham_and_conjugate_spectralSequences`: the
  two spectral sequences, their first and second pages, boundedness and convergence.
* `AlgebraicGeometry.Scheme.Hom.exists_hodgeToDeRham_and_conjugate_spectralSequences`: the same
  for a morphism of schemes `X → S`, converging to `AlgebraicGeometry.Scheme.Hom.deRhamCohomology`.
* `AlgebraicGeometry.SheafOfModules.nonempty_deRhamCohomologyAbelian_zero_iso_kernel`:
  `H^0_{dR}(X/S) = Ker(d : H^0(X, Ω^0_{X/S}) → H^0(X, Ω^1_{X/S}))`.
* `AlgebraicGeometry.SheafOfModules.nonempty_deRhamCohomologyAbelian_zero_iso_cohomologySheaf`:
  `H^0_{dR}(X/S) = H^0(X, 𝓗^0)`.
* `AlgebraicGeometry.SheafOfModules.exists_exact_deRhamCohomologyAbelian_one_two`: the exact
  sequence `0 → H^1(X, 𝓗^0) → H^1_{dR}(X/S) → H^0(X, 𝓗^1) → H^2(X, 𝓗^0) → H^2_{dR}(X/S)`.

## Implementation notes

De Rham cohomology is `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian`, the
hypercohomology of the de Rham complex of abelian sheaves computed by the bounded-below derived
functor of global sections; for a morphism of schemes this is
`AlgebraicGeometry.Scheme.Hom.deRhamCohomology` ([Stacks, Tag 0FL6]) by definition. The
Cartan-Eilenberg resolution is accordingly taken in the category of abelian sheaves on `X`, which
has enough injectives; the cohomology groups `H^q(X, -)` are the right derived functors
`CategoryTheory.Functor.rightDerivedPlus` of `Γ(X, -)` ([Stacks, Tag 015A]). The complex
`Ω^•_{X/S}` is read extended by zero to negative degrees, so its term in degree `p ≥ 0` is
`Ω^p_{X/S}` and its term `Ω^0_{X/S}` is the exterior power `⋀^0 Ω_{X/S} = 𝒪_X`.

The spectral sequences are those of `Tot(Γ(I^{•,•}))` filtered by the first and by the second
coordinate. Both filtrations are first quadrant, because `I^{p,q} = 0` for `p < 0` or `q < 0`,
so `CochainComplex.Filtered.firstQuadrantAbutmentOfFiltered` presents each of them as a
first-quadrant `E₂` spectral sequence abutting to `H^*_{dR}(X/S)`. The low-degree statements are
read off that presentation: `H^0 = E_2^{0,0}` for both, and the five-term exact sequence of
`Stacks.Cohomology.Leray.FirstQuadrantAbutment` for the conjugate one.

## References

* [Stacks Project, Section 0FM6](https://stacks.math.columbia.edu/tag/0FM6)
* [Stacks Project, Tag 015I](https://stacks.math.columbia.edu/tag/015I)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open CochainComplex FilteredComplexSpectralSequence CochainComplex.Filtered
open Stacks.Cohomology.Leray (sectionsFunctor FirstQuadrantAbutment)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}
variable {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The Hodge-to-de Rham and the conjugate spectral sequences** of Stacks Section 0FM6.

There are two cohomological spectral sequences `E₁` (starting at the page `0`) and `E₂` such that

* `E₁` is the Hodge-to-de Rham spectral sequence: its first page is
  `E_1^{p,q} = H^q(X, Ω^p_{X/S})`, and under this identification `d_1^{p,q}` is the map
  `H^q(X, Ω^p_{X/S}) → H^q(X, Ω^{p+1}_{X/S})` induced by the de Rham differential;
* `E₂` is the conjugate spectral sequence: its second page is `E_2^{p,q} = H^p(X, 𝓗^q)`, with
  `𝓗^q = H^q(Ω^•_{X/S})` the `q`-th cohomology sheaf of the de Rham complex;
* both are bounded, and both converge to `H^*_{dR}(X/S)`: every `H^n_{dR}(X/S)` carries a finite
  decreasing filtration whose graded pieces are the terms `E_∞^{p, n - p}`.

Both come from [Stacks, Tag 015J] applied to `Γ(X, -)` and a Cartan-Eilenberg resolution of the
de Rham complex ([Stacks, Tag 015I]). -/
@[stacks 0FM6 "the two spectral sequences of a Cartan-Eilenberg resolution of the de Rham
complex (Tag 015J for Γ(X, -)), both bounded and converging to H^*_dR(X/S): the Hodge-to-de Rham
spectral sequence with E_1^{p,q} = H^q(X, Ω^p) and d_1 induced by d, and the conjugate spectral
sequence with E_2^{p,q} = H^p(X, H^q(Ω^•)); the resolution is taken in abelian sheaves, the
category in which H^*_dR(X/S) is computed"]
theorem exists_hodgeToDeRham_and_conjugate_spectralSequences :
    ∃ E₁ E₂ : CohomologicalSpectralSequence AddCommGrpCat.{u} 0,
      (∃ α : ∀ p q : ℤ, (E₁.page 1 zero_le_one).X (p, q) ≅
          ((sectionsFunctor X.carrier ⊤).rightDerivedPlus q).obj
            ((deRhamAbelianComplexInt B D).X p),
        ∀ p q : ℤ, (E₁.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (α (p + 1) q).hom =
          (α p q).hom ≫ ((sectionsFunctor X.carrier ⊤).rightDerivedPlus q).map
            ((deRhamAbelianComplexInt B D).d p (p + 1))) ∧
      Nonempty (∀ p q : ℤ, (E₂.page 2 zero_le_two).X (p, q) ≅
        ((sectionsFunctor X.carrier ⊤).rightDerivedPlus p).obj
          ((deRhamAbelianComplexInt B D).homology q)) ∧
      IsBounded E₁ ∧ IsBounded E₂ ∧
      SpectralSequence.AbutsTo E₁ (deRhamCohomologyAbelian B D) ∧
      SpectralSequence.AbutsTo E₂ (deRhamCohomologyAbelian B D) := by
  obtain ⟨I, -⟩ := (deRhamAbelianComplexInt B D).exists_cartanEilenbergResolution 0
  obtain ⟨hα, -, hβ, hb₁, hb₂, -, -, -, -, -, ha₁, ha₂⟩ :=
    I.spectralSequences_rightDerivedPlus (sectionsFunctor X.carrier ⊤)
      (deRhamAbelianComplexPlus B D).property
  exact ⟨_, _, hα, hβ, hb₁, hb₂, ha₁, ha₂⟩

/-! ### Low degrees -/

section LowDegrees

variable {B D}

variable (I : (deRhamAbelianComplexInt B D).CartanEilenbergResolution)

/-- The double complex `Γ(X, I^{•,•})` of global sections of a Cartan-Eilenberg resolution of
the de Rham complex. -/
private abbrev cartanEilenbergSections :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((sectionsFunctor X.carrier ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I.bicomplex

variable {I} (hI : CochainComplex.IsStrictlyGE I.bicomplex 0)

include hI in
/-- `Γ(X, I^{p,q}) = 0` as soon as `p < 0`. -/
private lemma isZero_cartanEilenbergSections_of_fst_neg (i j : ℤ) (hi : i < 0) :
    IsZero (((cartanEilenbergSections I).X i).X j) :=
  (sectionsFunctor X.carrier ⊤).map_isZero
    ((HomologicalComplex.eval _ _ j).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex 0 i hi))

/-- `Γ(X, I^{p,q}) = 0` as soon as `q < 0`. -/
private lemma isZero_cartanEilenbergSections_of_snd_neg (i j : ℤ) (hj : j < 0) :
    IsZero (((cartanEilenbergSections I).X i).X j) := by
  obtain ⟨i₀, hq, -⟩ := StacksDraft.CartanEilenbergResolutions.exists_bounds_bicomplex I
  exact (sectionsFunctor X.carrier ⊤).map_isZero (hq i j hj)

include hI in
/-- The spectral sequence of `Tot(Γ(X, I^{•,•}))` filtered by the first coordinate, as a
first-quadrant `E₂` spectral sequence abutting to `H^*(Tot(Γ(X, I^{•,•})))`. -/
private def firstAbutment :=
  firstQuadrantAbutmentOfFiltered (cartanEilenbergSections I).totalFiltration₁
    (HomologicalComplex₂.isIso_totalFiltration₁_ι_f _
      (isZero_cartanEilenbergSections_of_fst_neg hI))
    (HomologicalComplex₂.isZero_totalFiltration₁_obj_X _
      isZero_cartanEilenbergSections_of_snd_neg)

include hI in
/-- The spectral sequence of `Tot(Γ(X, I^{•,•}))` filtered by the second coordinate, as a
first-quadrant `E₂` spectral sequence abutting to `H^*(Tot(Γ(X, I^{•,•})))`. -/
private def secondAbutment :=
  firstQuadrantAbutmentOfFiltered (cartanEilenbergSections I).totalFiltration₂
    (HomologicalComplex₂.isIso_totalFiltration₂_ι_f _
      isZero_cartanEilenbergSections_of_snd_neg)
    (HomologicalComplex₂.isZero_totalFiltration₂_obj_X _
      (isZero_cartanEilenbergSections_of_fst_neg hI))

end LowDegrees

/-- **`H^0_{dR}(X/S) = Ker(d : H^0(X, 𝒪_X) → H^0(X, Ω^1_{X/S}))`**, read off the Hodge-to-de Rham
spectral sequence of Stacks Section 0FM6: in total degree `0` only `E_2^{0,0}` survives, and
`E_2^{0,0}` is the kernel of `d_1^{0,0} : H^0(X, Ω^0_{X/S}) → H^0(X, Ω^1_{X/S})`, the map induced on
`H^0(X, -)` by the de Rham differential `d : Ω^0_{X/S} = 𝒪_X → Ω^1_{X/S}`. -/
@[stacks 0FM6 "the conclusion read off the Hodge-to-de Rham spectral sequence in degree 0:
H^0_dR(X/S) = Ker(d : H^0(X, O_X) → H^0(X, Ω^1_{X/S})), with O_X = Ω^0_{X/S} the degree 0 term
of the de Rham complex"]
theorem nonempty_deRhamCohomologyAbelian_zero_iso_kernel :
    Nonempty (deRhamCohomologyAbelian B D 0 ≅
      kernel (((sectionsFunctor X.carrier ⊤).rightDerivedPlus 0).map
        ((deRhamAbelianComplexInt B D).d 0 1))) := by
  obtain ⟨I, hI⟩ := (deRhamAbelianComplexInt B D).exists_cartanEilenbergResolution 0
  obtain ⟨⟨α, hα⟩, -, -, -, -, -, -, -, -, ⟨eH⟩, -, -⟩ :=
    I.spectralSequences_rightDerivedPlus (sectionsFunctor X.carrier ⊤)
      (deRhamAbelianComplexPlus B D).property
  let K := (cartanEilenbergSections I).totalFiltration₁
  have hfq := isFirstQuadrant_of_firstQuadrantFiltration K (filtrationSubobject K)
    (fun _ _ => rfl) (cycles K.X (filtrationSubobject K)) (fun _ _ _ => rfl)
    (boundaries K.X (filtrationSubobject K)) (fun _ _ _ => rfl) (spectralSequenceFunctor.obj K)
    (fun r p' q' n' hr hn' => by subst hn'; exact pageIso K r p' q' hr)
    (HomologicalComplex₂.isIso_totalFiltration₁_ι_f _
      (isZero_cartanEilenbergSections_of_fst_neg hI))
    (HomologicalComplex₂.isZero_totalFiltration₁_obj_X _
      isZero_cartanEilenbergSections_of_snd_neg)
  let P := (spectralSequenceFunctor.obj K).page 1 zero_le_one
  have hz : IsZero (P.X ((-1 : ℤ), (0 : ℤ))) := hfq 1 zero_le_one _ (Or.inl (by norm_num))
  have hprev : (ComplexShape.up' ((1 : ℤ), (1 : ℤ) - 1)).prev ((0 : ℤ), (0 : ℤ)) =
      ((-1 : ℤ), (0 : ℤ)) :=
    ComplexShape.prev_eq' _ (by ext <;> simp)
  have hnext : (ComplexShape.up' ((1 : ℤ), (1 : ℤ) - 1)).next ((0 : ℤ), (0 : ℤ)) =
      ((1 : ℤ), (0 : ℤ)) :=
    ComplexShape.next_eq' _ (by ext <;> simp)
  have hd : P.d ((-1 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ)) = 0 := hz.eq_of_src _ _
  have e₁ : deRhamCohomologyAbelian B D 0 ≅
      ((spectralSequenceFunctor.obj K).page 2 zero_le_two).X ((0 : ℤ), (0 : ℤ)) :=
    (eH 0).symm ≪≫ (firstAbutment hI).zeroIso
  have e₂ : ((spectralSequenceFunctor.obj K).page 2 zero_le_two).X ((0 : ℤ), (0 : ℤ)) ≅
      P.homology ((0 : ℤ), (0 : ℤ)) :=
    ((spectralSequenceFunctor.obj K).iso 1 2 (0, 0) (by norm_num) zero_le_one).symm
  have e₃ : P.homology ((0 : ℤ), (0 : ℤ)) ≅
      kernel (P.d ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ))) :=
    (P.isoHomologyπ _ _ hprev hd).symm ≪≫
      IsLimit.conePointUniqueUpToIso (P.cyclesIsKernel _ _ hnext) (limit.isLimit _)
  have hα₀ : P.d ((0 : ℤ), (0 : ℤ)) ((1 : ℤ), (0 : ℤ)) ≫ (α 1 0).hom =
      (α 0 0).hom ≫ ((sectionsFunctor X.carrier ⊤).rightDerivedPlus 0).map
        ((deRhamAbelianComplexInt B D).d 0 1) :=
    hα 0 0
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ kernel.mapIso _ _ (α 0 0) (α 1 0) hα₀⟩

/-- **`H^0_{dR}(X/S) = H^0(X, 𝓗^0)`**, read off the conjugate spectral sequence of Stacks Section
0FM6: in total degree `0` only `E_2^{0,0} = H^0(X, 𝓗^0)` survives, where `𝓗^0 = H^0(Ω^•_{X/S})`
is the zeroth cohomology sheaf of the de Rham complex. -/
@[stacks 0FM6 "the conclusion read off the conjugate spectral sequence in degree 0:
H^0_dR(X/S) = H^0(X, H^0), with H^0 = H^0(Ω^•_{X/S}) the zeroth cohomology sheaf"]
theorem nonempty_deRhamCohomologyAbelian_zero_iso_cohomologySheaf :
    Nonempty (deRhamCohomologyAbelian B D 0 ≅
      ((sectionsFunctor X.carrier ⊤).rightDerivedPlus 0).obj
        ((deRhamAbelianComplexInt B D).homology 0)) := by
  obtain ⟨I, hI⟩ := (deRhamAbelianComplexInt B D).exists_cartanEilenbergResolution 0
  obtain ⟨-, -, ⟨eE⟩, -, -, -, -, -, -, ⟨eH⟩, -, -⟩ :=
    I.spectralSequences_rightDerivedPlus (sectionsFunctor X.carrier ⊤)
      (deRhamAbelianComplexPlus B D).property
  exact ⟨(eH 0).symm ≪≫ (secondAbutment hI).zeroIso ≪≫ eE 0 0⟩

/-- **The exact sequence of Stacks Section 0FM6 in degrees `1` and `2`**, read off the conjugate
spectral sequence: with `𝓗^q = H^q(Ω^•_{X/S})` the cohomology sheaves of the de Rham complex,
there is an exact sequence
`0 → H^1(X, 𝓗^0) → H^1_{dR}(X/S) → H^0(X, 𝓗^1) → H^2(X, 𝓗^0) → H^2_{dR}(X/S)`.
It is the five term exact sequence of the first-quadrant spectral sequence
`E_2^{p,q} = H^p(X, 𝓗^q) ⇒ H^{p+q}_{dR}(X/S)`, the third map being `d_2^{0,1}`. -/
@[stacks 0FM6 "the exact sequence read off the conjugate spectral sequence in degree 1:
0 → H^1(X, H^0) → H^1_dR(X/S) → H^0(X, H^1) → H^2(X, H^0) → H^2_dR(X/S)"]
theorem exists_exact_deRhamCohomologyAbelian_one_two :
    ∃ (a : ((sectionsFunctor X.carrier ⊤).rightDerivedPlus 1).obj
          ((deRhamAbelianComplexInt B D).homology 0) ⟶ deRhamCohomologyAbelian B D 1)
      (b : deRhamCohomologyAbelian B D 1 ⟶ ((sectionsFunctor X.carrier ⊤).rightDerivedPlus 0).obj
          ((deRhamAbelianComplexInt B D).homology 1))
      (c : ((sectionsFunctor X.carrier ⊤).rightDerivedPlus 0).obj
          ((deRhamAbelianComplexInt B D).homology 1) ⟶
        ((sectionsFunctor X.carrier ⊤).rightDerivedPlus 2).obj
          ((deRhamAbelianComplexInt B D).homology 0))
      (t : ((sectionsFunctor X.carrier ⊤).rightDerivedPlus 2).obj
          ((deRhamAbelianComplexInt B D).homology 0) ⟶ deRhamCohomologyAbelian B D 2)
      (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hct : c ≫ t = 0),
      Mono a ∧ (ShortComplex.mk a b hab).Exact ∧ (ShortComplex.mk b c hbc).Exact ∧
        (ShortComplex.mk c t hct).Exact := by
  obtain ⟨I, hI⟩ := (deRhamAbelianComplexInt B D).exists_cartanEilenbergResolution 0
  obtain ⟨-, -, ⟨eE⟩, -, -, -, -, -, -, ⟨eH⟩, -, -⟩ :=
    I.spectralSequences_rightDerivedPlus (sectionsFunctor X.carrier ⊤)
      (deRhamAbelianComplexPlus B D).property
  exact (secondAbutment hI).exists_exact_of_iso (eE 1 0) (eH 1) (eE 0 1) (eE 2 0) (eH 2)

end AlgebraicGeometry.SheafOfModules

/-! ### For a morphism of schemes -/

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The Hodge-to-de Rham and the conjugate spectral sequences of a morphism of schemes**
`f : X → S` (Stacks Section 0FM6): two bounded spectral sequences converging to
`H^*_{dR}(X/S)` (`AlgebraicGeometry.Scheme.Hom.deRhamCohomology`), the first with
`E_1^{p,q} = H^q(X, Ω^p_{X/S})` and `d_1` induced by the de Rham differential, the second with
`E_2^{p,q} = H^p(X, 𝓗^q)`. This is
`AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRham_and_conjugate_spectralSequences` for
`f^{-1}𝒪_S ⟶ 𝒪_X`. -/
@[stacks 0FM6 "for a morphism of schemes X → S: the Hodge-to-de Rham spectral sequence
E_1^{p,q} = H^q(X, Ω^p_{X/S}) with d_1 induced by d, and the conjugate spectral sequence
E_2^{p,q} = H^p(X, H^q(Ω^•_{X/S})), both bounded and converging to H^*_dR(X/S)"]
theorem exists_hodgeToDeRham_and_conjugate_spectralSequences :
    ∃ E₁ E₂ : CohomologicalSpectralSequence AddCommGrpCat.{u} 0,
      (∃ α : ∀ p q : ℤ, (E₁.page 1 zero_le_one).X (p, q) ≅
          ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedPlus q).obj
            ((SheafOfModules.deRhamAbelianComplexInt (deRhamAlgebras f)
              (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).X p),
        ∀ p q : ℤ, (E₁.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (α (p + 1) q).hom =
          (α p q).hom ≫ ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedPlus
            q).map ((SheafOfModules.deRhamAbelianComplexInt (deRhamAlgebras f)
              (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).d p (p + 1))) ∧
      Nonempty (∀ p q : ℤ, (E₂.page 2 zero_le_two).X (p, q) ≅
        ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedPlus p).obj
          ((SheafOfModules.deRhamAbelianComplexInt (deRhamAlgebras f)
            (SheafOfModules.deRhamDifferential (deRhamAlgebras f))).homology q)) ∧
      IsBounded E₁ ∧ IsBounded E₂ ∧
      SpectralSequence.AbutsTo E₁ (f.deRhamCohomology) ∧
      SpectralSequence.AbutsTo E₂ (f.deRhamCohomology) :=
  SheafOfModules.exists_hodgeToDeRham_and_conjugate_spectralSequences _ _

end AlgebraicGeometry.Scheme.Hom

end
