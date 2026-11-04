module

public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDegreeZero
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDerivedFibre
public import StacksFrontier.Homology.TwoTermComplex.Ext

/-!
# Stacks 07YM, the obstruction step of `(2) ⇒ (1)`

Let `ξ : E ⟶ NL_{A/Λ}` be a morphism of `D⁻(A)` and let `A' → A` be a square-zero surjection
of `Λ`-algebras whose kernel `I` is a one-dimensional vector space over an `A`-algebra field
`k`. In the direction `(2) ⇒ (1)` of [Stacks, Tag 07YM] such an extension arises as a
deformation situation for which hypothesis (i) of the tag asks for a lift, and the step this
file carries out is the one that produces it: condition (2) in degree `-1` forces the
obstruction class of the extension to vanish, and a vanishing obstruction class splits the
extension.

The argument is the one of [Stacks, Tag 07YI] run on the canonical presentation of `A` over
`Λ`:

* condition (2) in degree `-1` is the injectivity of precomposition with `ξ` on
  `Ext¹_A(−, k)` (`Deformation.Artin.surjective_derivedTensorFibre_neg_one_iff_injective_extOne`),
  and the extension class `NL_{A/Λ} ⟶ I[1]` of the thickening
  (`Deformation.Artin.cotangentExtensionClass`) is such a class, killed by `ξ` because `ξ`
  composed with `NL_{A/Λ} ⟶ NL_{A/A'}` vanishes and the extension class is that base-change
  morphism followed by the square-zero identification; so the extension class is zero;
* computed through a presentation
  (`Deformation.Artin.derivedNaiveCotangentComplexIso_hom_comp_cotangentExtensionClass`) the
  extension class is the map `J/J² → I`, `f ↦ f(a'_1, …, a'_n)`, of [Stacks, Tag 07YI],
  placed in degree `-1` of the two-term complex `J/J² → ⊕_i A dx_i`;
* a morphism out of a two-term complex with projective degree-`0` term vanishes in the
  derived category exactly when it is null homotopic, and the only component of such a
  homotopy is a map `⊕_i A dx_i → I` through which the functional factors;
* correcting the lifts `a'_i` by that map produces lifts at which every element of `J`
  vanishes, so the corrected evaluation `Λ[x_i] → A'` factors through `A = Λ[x_i]/J`.

## Main results

* `Deformation.Artin.exists_comp_eq_of_Q_map_twoTermProjection_comp_eq_zero` — a functional on
  the conormal term of a two-term complex with projective degree-`0` term factors through the
  differential as soon as the induced morphism to the shifted target vanishes in `D(A)`.
* `Deformation.Artin.cotangentExtensionClass_eq_zero_of_surjective_derivedTensorFibre_neg_one`
  — condition (2) in degree `-1` kills the extension class of such a thickening.
* `Deformation.Artin.exists_algHom_section_of_cotangentComplex_comp_eq` — a factorization of
  the conormal map through the differential splits the thickening.
* `Deformation.Artin.exists_algHom_section_of_surjective_derivedTensorFibre_neg_one` — **the
  obstruction step**: the three previous results chained, giving a `Λ`-algebra section of
  `A' → A`.

## Implementation notes

The presentation used is `Algebra.Generators.self Λ A`, by the whole of `A`: no finiteness of
`Λ → A` is needed anywhere, the only property of the presentation that enters being that its
cotangent space `⊕_i A dx_i` is free, hence projective, which holds for any index type. In
particular the statements here are not restricted to algebras of finite type, even though
that is the setting of [Stacks, Tag 07YM]; neither is any Noetherian hypothesis used.

The kernel `I` carries the module structure `Stacks.Smooth.kerModule` over `A`, and
"one-dimensional over `k`" is taken in the form in which [Stacks, Tag 07YL] produces it and
the tag consumes it: an isomorphism `I ≃ₗ[A] k` of `A`-modules. The coefficient module of the
`Ext` groups that condition (2) is stated at is `ULift k` restricted along `A ⟶ k`, and
`Deformation.Artin.uliftRestrictScalarsIso` moves between it and the `A`-module `ULift k`, as
in the degree `0` half.

The morphisms of extensions attached to a family of lifts of the generators are formed with
`Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq`, the extension of `A` over `A'` whose
conormal module `Deformation.Artin.squareZeroKernelCotangentEquiv` identifies `A`-linearly
with `I`; that identification is the only place where the two descriptions `I` and `I/I²` of
the kernel meet, and no algebra structure is rebuilt from a ring map anywhere in this file.
That the corrected lifts differ from the chosen ones by `δ` on the basis `dx_i`, and hence by
`δ` on all of `⊕_i A dx_i`, is Mathlib's `Algebra.Extension.Hom.sub` together with
`Algebra.Extension.Hom.sub_one_tmul`; this is the verification [Stacks, Tag 07YI] omits.

Hypothesis (i) of the tag is not mentioned: the conclusion is a section of `A' → A` in the
category of `Λ`-algebras, which is the input hypothesis (i) is applied to, and the passage
from a section to a lift of the family `x` happens in the site and is a separate step.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YI](https://stacks.math.columbia.edu/tag/07YI)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex NaiveCotangent
open ComplexShape (upIntRelNegOneZero)

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

universe u

/-! ### Factoring a functional on the conormal term through the differential -/

section Factorization

variable {A : Type u} [CommRing A] {N M G : ModuleCat.{u} A}

/-- A functional `φ : N ⟶ G` on the degree `-1` term of a two-term complex `d : N ⟶ M` with
`M` projective factors through `d` as soon as the morphism it induces from the two-term
complex to `G[1]` vanishes in the derived category: the vanishing produces a null homotopy,
whose only possibly nonzero component is a map `M ⟶ G` through which `φ` factors. -/
public theorem exists_comp_eq_of_Q_map_twoTermProjection_comp_eq_zero
    (d : N ⟶ M) [Projective M] (φ : N ⟶ G)
    (h : DerivedCategory.Q.map (twoTermProjection d) ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).map φ = 0) :
    ∃ δ : M ⟶ G, φ = d ≫ δ := by
  have hg : DerivedCategory.Q.map (twoTermProjection d ≫
      (CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).map φ) = 0 := by
    rw [Functor.map_comp]
    exact h
  have hMpos : ∀ i, 0 < i → IsZero ((double d upIntRelNegOneZero).X i) := fun i hi =>
    isZero_double_X d upIntRelNegOneZero i (by omega) (by omega)
  have hM0 : Projective ((double d upIntRelNegOneZero).X 0) :=
    Projective.of_iso (doubleXIso₁ d upIntRelNegOneZero (by omega)).symm inferInstance
  have hLz : ∀ i ≤ (-2 : ℤ),
      IsZero (((CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).obj G).X i) := fun i hi =>
    isZero_single_obj_X (ComplexShape.up ℤ) (-1) G i (by omega)
  have hbij := TwoTermComplexExt.toHomD_bijective (double d upIntRelNegOneZero)
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).obj G) hMpos hM0 hLz
  have hq0 : (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map
      (twoTermProjection d ≫
        (CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).map φ) = 0 := by
    refine hbij.injective ?_
    show TwoTermComplexExt.toHomD _ = TwoTermComplexExt.toHomD 0
    rw [TwoTermComplexExt.toHomD_quotient_map, TwoTermComplexExt.toHomD_zero]
    exact hg
  obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).1 hq0
  have hLd : ((CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).obj G).d (-2) (-1) = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) (-1) G (-2) (-1)
  have hcomm := H.comm (-1)
  rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
    prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp), hLd] at hcomm
  have hgf : (twoTermProjection d ≫
        (CochainComplex.singleFunctor (ModuleCat.{u} A) (-1)).map φ).f (-1) =
      (doubleXIso₀ d upIntRelNegOneZero).hom ≫ φ ≫
        (singleObjXSelf (ComplexShape.up ℤ) (-1) G).inv := by
    simp only [HomologicalComplex.comp_f, twoTermProjection_f_neg_one,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hgf, show (double d upIntRelNegOneZero).d (-1) 0 =
      (doubleXIso₀ d upIntRelNegOneZero).hom ≫ d ≫
        (doubleXIso₁ d upIntRelNegOneZero (by omega)).inv from
    double_d d upIntRelNegOneZero (by omega)] at hcomm
  simp only [comp_zero, HomologicalComplex.zero_f, add_zero, Category.assoc] at hcomm
  refine ⟨(doubleXIso₁ d upIntRelNegOneZero (by omega)).inv ≫ H.hom 0 (-1) ≫
    (singleObjXSelf (ComplexShape.up ℤ) (-1) G).hom, ?_⟩
  simpa using (cancel_epi (doubleXIso₀ d upIntRelNegOneZero).hom).1 hcomm =≫
    (singleObjXSelf (ComplexShape.up ℤ) (-1) G).hom

end Factorization

/-! ### Vanishing of the extension class of the thickening -/

section ExtensionClassVanishing

variable {Λ A A' k : Type u} [CommRing Λ] [CommRing A] [CommRing A'] [Field k]
  [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A] [Algebra A k]

/-- **Condition (2) in degree `-1` makes the extension class of a thickening vanish.** Let
`A' → A` be a square-zero surjection of `Λ`-algebras whose kernel `I` is a one-dimensional
`k`-vector space for an `A`-algebra field `k`, and let `ξ : E ⟶ NL_{A/Λ}` be a morphism of
`D⁻(A)` with `H^{-1}(ξ ⊗ᴸ_A k)` surjective. If `ξ` composed with `NL_{A/Λ} ⟶ NL_{A/A'}`
vanishes, then the extension class `NL_{A/Λ} ⟶ I[1]` of the thickening is itself zero.

Surjectivity of `H^{-1}(ξ ⊗ᴸ_A k)` is the injectivity of precomposition with `ξ` on
`Ext¹_A(−, k)`, and the extension class is the `Ext¹`-class annihilated by `ξ`: the
identification `I ≅ k` of `A`-modules carries the class into the coefficient module that
condition (2) is stated at, and the class map `NL_{A/Λ} ⟶ I[1]` is an `Ext¹` class because
`I[1]` is the shift of `I[0]`. -/
public theorem cotangentExtensionClass_eq_zero_of_surjective_derivedTensorFibre_neg_one
    (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (eI : letI := Stacks.Smooth.kerModule hq hsq
      RingHom.ker (algebraMap A' A) ≃ₗ[A] k)
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
    (hsurj : Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)))
    (hkill : ξ ≫ naiveCotangentBaseMap Λ A' A = 0) :
    letI := Stacks.Smooth.kerModule hq hsq
    cotangentExtensionClass Λ A' A hq hsq = 0 := by
  let := Stacks.Smooth.kerModule hq hsq
  let N := (ModuleCat.restrictScalars (algebraMap A k)).obj
    (ModuleCat.of k (ULift.{u} k))
  let eIso : ModuleCat.of A (RingHom.ker (algebraMap A' A)) ≅ N :=
    eI.toModuleIso ≪≫ (ULift.moduleEquiv (R := A) (M := k)).symm.toModuleIso ≪≫
      (uliftRestrictScalarsIso A k).symm
  let e := ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso 1 (-1) 0
    (by omega)).app N
  let ι : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).obj
        (ModuleCat.of A (RingHom.ker (algebraMap A' A))) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)⟦(1 : ℤ)⟧ :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-1)).mapIso eIso ≪≫ e.symm
  have hinj := (surjective_derivedTensorFibre_neg_one_iff_injective_extOne
    (k := k) T E hE ξ).1 hsurj
  have hξ : ξ ≫ cotangentExtensionClass Λ A' A hq hsq = 0 := by
    rw [show cotangentExtensionClass Λ A' A hq hsq =
      naiveCotangentBaseMap Λ A' A ≫ squareZeroCotangentClass A' A hq hsq from rfl,
      ← Category.assoc, hkill, Limits.zero_comp]
  have hα : ξ ≫ (cotangentExtensionClass Λ A' A hq hsq ≫ ι.hom) = ξ ≫ 0 := by
    rw [← Category.assoc, hξ, Limits.zero_comp, Limits.comp_zero]
  have hα0 : cotangentExtensionClass Λ A' A hq hsq ≫ ι.hom = 0 := hinj hα
  rw [← cancel_mono ι.hom, hα0, Limits.zero_comp]

end ExtensionClassVanishing

/-! ### Correcting a lift of the generators -/

section Splitting

variable {Λ A A' : Type u} [CommRing Λ] [CommRing A] [CommRing A']
  [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]

/-- The morphism of extensions `(Λ[x_i] → A) → (A' → A)` determined by a family of lifts
`a'_i ∈ A'` of the generators: it evaluates a polynomial at the `a'_i`. -/
public def generatorsLiftHom {ι : Type u} (P : Algebra.Generators Λ A ι)
    (hq : Function.Surjective (algebraMap A' A))
    (a' : ι → A') (ha' : ∀ i, algebraMap A' A (a' i) = P.val i) :
    P.toExtension.Hom (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq) where
  toRingHom := (MvPolynomial.aeval a' : MvPolynomial ι Λ →ₐ[Λ] A').toRingHom
  toRingHom_algebraMap x := by
    change MvPolynomial.aeval a' (algebraMap Λ (MvPolynomial ι Λ) x) = algebraMap Λ A' x
    simp
  algebraMap_toRingHom x := by
    have h : ((IsScalarTower.toAlgHom Λ A' A).comp (MvPolynomial.aeval a') :
        MvPolynomial ι Λ →ₐ[Λ] A) = MvPolynomial.aeval P.val :=
      MvPolynomial.algHom_ext fun i => by simpa using ha' i
    have h2 := AlgHom.congr_fun h x
    have h3 : (algebraMap P.toExtension.Ring A) x = MvPolynomial.aeval P.val x :=
      RingHom.congr_fun P.algebraMap_eq x
    change algebraMap A' A (MvPolynomial.aeval a' x) = algebraMap P.toExtension.Ring A x
    rw [h3]
    exact h2

/-- The morphism of extensions attached to a family of lifts evaluates at the lifts. -/
public theorem generatorsLiftHom_toRingHom_apply {ι : Type u}
    (P : Algebra.Generators Λ A ι) (hq : Function.Surjective (algebraMap A' A))
    (a' : ι → A') (ha' : ∀ i, algebraMap A' A (a' i) = P.val i) (f : MvPolynomial ι Λ) :
    (generatorsLiftHom P hq a' ha').toRingHom f = MvPolynomial.aeval a' f :=
  rfl

/-- **A factorization of the conormal map through the differential splits the thickening.**
Let `A' → A` be a square-zero surjection, let `a'_i ∈ A'` lift the generators of a
presentation `P` of `A` over `Λ`, and suppose the map `J/J² → I`, `f ↦ f(a'_1, …)`, factors
through the differential `J/J² → ⊕_i A dx_i` by `δ`. Then `A' → A` has a `Λ`-algebra section.

Correcting the lifts to `a'_i - δ(dx_i)` produces a second morphism of extensions whose
difference from the first is `-δ` on the basis `dx_i`, hence `-δ` on all of `⊕_i A dx_i`;
by `Algebra.Extension.Cotangent.map_sub_map` the corrected lifts therefore induce the zero
map on conormal modules, which says that every element of `J` vanishes at them. The
corrected evaluation then factors through `A = Λ[x_i]/J`. -/
public theorem exists_algHom_section_of_cotangentComplex_comp_eq {ι : Type u}
    (P : Algebra.Generators Λ A ι)
    (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (a' : ι → A') (ha' : ∀ i, algebraMap A' A (a' i) = P.val i)
    (δ : letI := Stacks.Smooth.kerModule hq hsq
      P.toExtension.CotangentSpace →ₗ[A] RingHom.ker (algebraMap A' A))
    (hδ : letI := Stacks.Smooth.kerModule hq hsq
      ∀ x : P.toExtension.ker,
        (δ (P.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk x))).1 =
          MvPolynomial.aeval a' (x.1 : MvPolynomial ι Λ)) :
    ∃ σ : A →ₐ[Λ] A', (algebraMap A' A).comp (σ : A →+* A') = RingHom.id A := by
  let := Stacks.Smooth.kerModule hq hsq
  let h₁ := generatorsLiftHom P hq a' ha'
  -- the corrected lifts
  let b' : ι → A' := fun i => a' i - (δ (P.cotangentSpaceBasis i)).1
  have hb'spec : ∀ i, algebraMap A' A (b' i) = P.val i := by
    intro i
    show algebraMap A' A (a' i - (δ (P.cotangentSpaceBasis i)).1) = P.val i
    rw [map_sub, RingHom.mem_ker.1 (δ (P.cotangentSpaceBasis i)).2, sub_zero, ha' i]
  let h₂ := generatorsLiftHom P hq b' hb'spec
  let δ' : P.toExtension.CotangentSpace →ₗ[A]
      (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq).Cotangent :=
    (squareZeroKernelCotangentEquiv A' A hq hsq).toLinearMap ∘ₗ δ
  have hδ'apply : ∀ y, δ' y = Algebra.Extension.Cotangent.mk (δ y) := fun _ => rfl
  -- the difference of the two morphisms of extensions is `-δ'`
  have hsubeq : Algebra.Extension.Hom.sub h₂ h₁ = -δ' := by
    refine Module.Basis.ext P.cotangentSpaceBasis fun i => ?_
    have hcoe := Algebra.Extension.Hom.subToKer_apply_coe h₂ h₁ (MvPolynomial.X i)
    have hker : Algebra.Extension.Hom.subToKer h₂ h₁ (MvPolynomial.X i) =
        -(δ (P.cotangentSpaceBasis i)) := by
      refine Subtype.ext (hcoe.trans ?_)
      show MvPolynomial.aeval b' (MvPolynomial.X i) -
        MvPolynomial.aeval a' (MvPolynomial.X i) = -(δ (P.cotangentSpaceBasis i)).1
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      show a' i - (δ (P.cotangentSpaceBasis i)).1 - a' i =
        -(δ (P.cotangentSpaceBasis i)).1
      ring
    have h1 : Algebra.Extension.Hom.sub h₂ h₁ (P.cotangentSpaceBasis i) =
        Algebra.Extension.Cotangent.mk
          (Algebra.Extension.Hom.subToKer h₂ h₁ (MvPolynomial.X i)) := by
      rw [P.cotangentSpaceBasis_apply i]
      exact Algebra.Extension.Hom.sub_one_tmul h₂ h₁ (MvPolynomial.X i)
    rw [h1, hker, LinearMap.neg_apply, hδ'apply]
    exact map_neg _ _
  -- the first morphism induces `δ' ∘ d` on conormal modules
  have hmap₁ : Algebra.Extension.Cotangent.map h₁ = δ' ∘ₗ P.toExtension.cotangentComplex := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
    rw [Algebra.Extension.Cotangent.map_mk h₁ x, LinearMap.comp_apply, hδ'apply]
    refine congrArg Algebra.Extension.Cotangent.mk (Subtype.ext ?_)
    show MvPolynomial.aeval a' (x.1 : MvPolynomial ι Λ) =
      (δ (P.toExtension.cotangentComplex (Algebra.Extension.Cotangent.mk x))).1
    exact (hδ x).symm
  -- hence the corrected morphism induces zero
  have hmap₂ : Algebra.Extension.Cotangent.map h₂ = 0 := by
    have h := Algebra.Extension.Cotangent.map_sub_map h₂ h₁
    rw [hsubeq, LinearMap.neg_comp, hmap₁] at h
    have h' := sub_eq_iff_eq_add.1 h
    rwa [neg_add_cancel] at h'
  -- so every element of the kernel of the presentation vanishes at the corrected lifts
  have hkill : ∀ f : MvPolynomial ι Λ, f ∈ P.ker → MvPolynomial.aeval b' f = 0 := by
    intro f hf
    have hz : Algebra.Extension.Cotangent.map h₂
        (Algebra.Extension.Cotangent.mk (⟨f, hf⟩ : P.toExtension.ker)) = 0 := by
      rw [hmap₂]
      exact LinearMap.zero_apply _
    rw [Algebra.Extension.Cotangent.map_mk h₂ ⟨f, hf⟩] at hz
    have h0 := (Algebra.Extension.Cotangent.mk_eq_zero_iff
      (P := Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq) _).1 hz
    rw [show (Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq).ker ^ 2 = ⊥ from hsq,
      Ideal.mem_bot] at h0
    exact h0
  -- the corrected evaluation factors through `A`
  have hsurjP : Function.Surjective
      ⇑(MvPolynomial.aeval P.val : MvPolynomial ι Λ →ₐ[Λ] A) :=
    fun s => ⟨P.σ s, P.aeval_val_σ s⟩
  have hkerEq : RingHom.ker (MvPolynomial.aeval P.val :
      MvPolynomial ι Λ →ₐ[Λ] A) = P.ker :=
    (Algebra.Generators.ker_eq_ker_aeval_val P).symm
  let τ : (MvPolynomial ι Λ ⧸ RingHom.ker (MvPolynomial.aeval P.val :
      MvPolynomial ι Λ →ₐ[Λ] A)) →ₐ[Λ] A' :=
    Ideal.Quotient.liftₐ
      (RingHom.ker (MvPolynomial.aeval P.val : MvPolynomial ι Λ →ₐ[Λ] A))
      (MvPolynomial.aeval b') (fun f hf => hkill f (hkerEq ▸ hf))
  have hτ : ∀ f : MvPolynomial ι Λ,
      τ (Ideal.Quotient.mk (RingHom.ker (MvPolynomial.aeval P.val :
        MvPolynomial ι Λ →ₐ[Λ] A)) f) = MvPolynomial.aeval b' f := fun _ => rfl
  let σ : A →ₐ[Λ] A' :=
    τ.comp (Ideal.quotientKerAlgEquivOfSurjective hsurjP).symm.toAlgHom
  have hσ : ∀ s : A, algebraMap A' A (σ s) = s := by
    intro s
    obtain ⟨g, rfl⟩ := hsurjP s
    have hgo : (Ideal.quotientKerAlgEquivOfSurjective hsurjP).symm
        (MvPolynomial.aeval P.val g) =
        Ideal.Quotient.mk (RingHom.ker (MvPolynomial.aeval P.val :
          MvPolynomial ι Λ →ₐ[Λ] A)) g := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    have hfin : algebraMap A' A (MvPolynomial.aeval b' g) = MvPolynomial.aeval P.val g := by
      have h := h₂.algebraMap_toRingHom g
      have h3 : (algebraMap P.toExtension.Ring A) g = MvPolynomial.aeval P.val g :=
        RingHom.congr_fun P.algebraMap_eq g
      rw [h3] at h
      exact h
    have hval : σ (MvPolynomial.aeval P.val g) = MvPolynomial.aeval b' g := by
      show τ ((Ideal.quotientKerAlgEquivOfSurjective hsurjP).symm
        (MvPolynomial.aeval P.val g)) = MvPolynomial.aeval b' g
      rw [hgo]
      exact hτ g
    rw [hval]
    exact hfin
  refine ⟨σ, RingHom.ext fun s => ?_⟩
  rw [RingHom.comp_apply, RingHom.id_apply]
  exact hσ s

end Splitting

/-! ### The obstruction step of `(2) ⇒ (1)` -/

section Obstruction

variable (Λ A A' k : Type u) [CommRing Λ] [CommRing A] [CommRing A'] [Field k]
  [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A] [Algebra A k]

/-- **Stacks 07YM, the obstruction step of `(2) ⇒ (1)`.** Let `A' → A` be a square-zero
surjection of `Λ`-algebras whose kernel `I` is one-dimensional over an `A`-algebra field `k`,
and let `ξ : E ⟶ NL_{A/Λ}` be a morphism of `D⁻(A)` with `H^{-1}(ξ ⊗ᴸ_A k)` surjective. If
`ξ` composed with `NL_{A/Λ} ⟶ NL_{A/A'}` vanishes, then `A' → A` admits a `Λ`-algebra
section.

Condition (2) in degree `-1` kills the extension class `NL_{A/Λ} ⟶ I[1]` of the thickening
(`Deformation.Artin.cotangentExtensionClass_eq_zero_of_surjective_derivedTensorFibre_neg_one`).
Computed through the canonical presentation of `A` over `Λ`
(`Deformation.Artin.derivedNaiveCotangentComplexIso_hom_comp_cotangentExtensionClass`), that
class is the map `J/J² → I`, `f ↦ f(a'_1, …)`, read in the derived category, and its
vanishing makes that map factor through the differential `J/J² → ⊕_i A dx_i`
(`Deformation.Artin.exists_comp_eq_of_Q_map_twoTermProjection_comp_eq_zero`). Correcting the
chosen lifts of the generators by the factorization produces lifts at which every element of
`J` vanishes, hence the section
(`Deformation.Artin.exists_algHom_section_of_cotangentComplex_comp_eq`). -/
@[stacks 07YM "(2) implies (1): condition (2) in degree -1 forces the obstruction class of a \
square-zero extension with one-dimensional kernel to vanish, so the extension splits"]
public theorem exists_algHom_section_of_surjective_derivedTensorFibre_neg_one
    (hq : Function.Surjective (algebraMap A' A))
    (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (eI : letI := Stacks.Smooth.kerModule hq hsq
      RingHom.ker (algebraMap A' A) ≃ₗ[A] k)
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
    (hsurj : Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)))
    (hkill : ξ ≫ naiveCotangentBaseMap Λ A' A = 0) :
    ∃ σ : A →ₐ[Λ] A', (algebraMap A' A).comp (σ : A →+* A') = RingHom.id A := by
  classical
  let := Stacks.Smooth.kerModule hq hsq
  have hzero := cotangentExtensionClass_eq_zero_of_surjective_derivedTensorFibre_neg_one
    (Λ := Λ) hq hsq eI T E hE ξ hsurj hkill
  let P := Algebra.Generators.self Λ A
  choose a' ha' using fun i : A => hq (P.val i)
  let h₁ := generatorsLiftHom P hq a' ha'
  let Φ := squareZeroKernelCotangentEquiv A' A hq hsq
  let kmap : P.toExtension.Cotangent →ₗ[A] RingHom.ker (algebraMap A' A) :=
    Φ.symm.toLinearMap ∘ₗ Algebra.Extension.Cotangent.map h₁
  have hψ : ∀ x, algebraMap A' A (h₁.toRingHom x) = algebraMap P.toExtension.Ring A x :=
    h₁.algebraMap_toRingHom
  have hk : ∀ x : P.toExtension.ker,
      (kmap (Algebra.Extension.Cotangent.mk x)).1 =
        h₁.toRingHom (x.1 : MvPolynomial A Λ) := by
    intro x
    have hmem : h₁.toRingHom (x.1 : MvPolynomial A Λ) ∈ RingHom.ker (algebraMap A' A) :=
      RingHom.mem_ker.2 ((hψ _).trans (RingHom.mem_ker.1 x.2))
    have hΦz : Φ ⟨h₁.toRingHom (x.1 : MvPolynomial A Λ), hmem⟩
        = Algebra.Extension.Cotangent.map h₁ (Algebra.Extension.Cotangent.mk x) := by
      rw [Algebra.Extension.Cotangent.map_mk h₁ x]
      rfl
    show (Φ.symm (Algebra.Extension.Cotangent.map h₁
      (Algebra.Extension.Cotangent.mk x))).1 = _
    rw [← hΦz, LinearEquiv.symm_apply_apply]
  have hbridge := derivedNaiveCotangentComplexIso_hom_comp_cotangentExtensionClass
    P (P.defaultHom (NaiveCotangent.canonicalGenerators Λ A)) hq hsq h₁.toRingHom hψ
    h₁.toRingHom_algebraMap kmap hk
  rw [hzero, Limits.comp_zero] at hbridge
  have : Projective (ModuleCat.of A (nlRestrict A P).X₀) := inferInstance
  obtain ⟨δ, hδeq⟩ := exists_comp_eq_of_Q_map_twoTermProjection_comp_eq_zero
    (ModuleCat.ofHom (nlRestrict A P).d) (ModuleCat.ofHom kmap) hbridge.symm
  refine exists_algHom_section_of_cotangentComplex_comp_eq P hq hsq a' ha' δ.hom ?_
  intro x
  have h : kmap (Algebra.Extension.Cotangent.mk x)
      = δ.hom ((nlRestrict A P).d (Algebra.Extension.Cotangent.mk x)) := by
    have h2 := congrArg (fun m : ModuleCat.of A (nlRestrict A P).X₁ ⟶
      ModuleCat.of A (RingHom.ker (algebraMap A' A)) =>
        m.hom (Algebra.Extension.Cotangent.mk x)) hδeq
    simpa [ModuleCat.comp_apply] using h2
  have hval : (δ.hom ((nlRestrict A P).d (Algebra.Extension.Cotangent.mk x))).1
      = MvPolynomial.aeval a' (x.1 : MvPolynomial A Λ) := by
    rw [← h]
    exact hk x
  exact hval

end Obstruction

end Deformation.Artin

end
