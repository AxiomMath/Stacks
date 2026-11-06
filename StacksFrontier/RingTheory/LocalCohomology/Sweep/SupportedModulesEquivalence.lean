module

public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.RingTheory.Ideal.Quotient.Small
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.Duality.TorsionCounit.BoundedBelow
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.RightAdjoint
public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.DimensionBoundUnconditional
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.SupportedSectionsAdjunction
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.SupportedModulesComparisonPlus
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticModelTransport

/-!
# The derived category of modules supported in a subset, in the unbounded case

Let `A` be a Noetherian ring and let `T ⊆ Spec(A)` be stable under specialization. The file
`StacksFrontier/RingTheory/LocalCohomology/Sweep/SupportedModulesComparison.lean` constructs the
canonical comparison functor
$$ D(\mathrm{Mod}_{A,T}) \longrightarrow D_T(A) $$
and `SupportedModulesComparisonPlus.lean` shows that its bounded-below restriction is an
equivalence (Tag 0EF2). This file removes the boundedness hypothesis when `A` has finite Krull
dimension, which is Tag 0EF3.

## Main results

* `Stacks.LocalCohomology.supportedModulesComparison_isEquivalence` — **Tag 0EF3**: the
  comparison functor is an equivalence when `A` is Noetherian of finite Krull dimension and `T`
  is stable under specialization.

## Implementation notes

Finite Krull dimension is expressed by `ringKrullDim A < ⊤`; unlike the typeclass
`FiniteRingKrullDim A`, this also includes the zero ring, whose Krull dimension is `⊥`.

The argument is the one of the source. Sections with support in `T`, read as a functor into the
supported modules, is right adjoint to the inclusion (Tag 0EF0, in
`StacksFrontier/RingTheory/LocalCohomology/SupportedSectionsAdjunction.lean`), and the comparison
functor is an equivalence as soon as the counit of the derived adjunction is invertible. On
bounded-below objects that is Tag 0EF2. To descend to the unbounded derived category one needs
`Γ_T` to have *bounded* cohomological dimension, and Tag 07K7 then says that the derived functor
commutes with the canonical truncations `τ^{≥ a}` in a range of degrees; the counit is invertible
on all of `D_T(A)` because it is so on every truncation.

Bounded cohomological dimension of `Γ_T` is where the Krull dimension enters. The library's
bound (Tag 0DXC, through Tag 0DX7) is stated for the *coreflection* model `RΓ_Z` of local
cohomology, while what is needed is the same bound for the total right derived functor of
`Γ_{V(I)}`; the comparison between the two models is Tag 0955, which this library does not
have in general. It is proved here at a module placed in degree zero, which is all the
truncation argument consumes:

* applying derived supported sections to the coreflection counit `RΓ_Z(X) ⟶ X` gives an
  isomorphism, because the derived inclusion of the supported modules lands in the objects with
  torsion cohomology, on which the coreflection counit is universal (Yoneda in
  `D(Mod_{A,V(I)})`);
* at a bounded-below object with torsion cohomology the comparison of the two models is already
  known to be invertible, by
  `Dualizing.TorsionCounit.isIso_compareSectionsWithSupportLocalCohomology_app_of_isGE`;
* `RΓ_Z(M[0])` is such an object, so naturality of the comparison along the counit identifies
  the two models at `M[0]`.

The passage from a closed support `V(I)` to an arbitrary specialization-stable `T` is the
colimit calculation of Tag 0EF1, in
`StacksFrontier/RingTheory/LocalCohomology/Sweep/ClosedSupportColimit.lean`: at a K-injective
complex the closed-support cocone is a colimit cocone, and a filtered colimit of zero modules
is zero.

Finally the module universe is cut down to the universe of the ring: the statement for the
large module category is transported along restriction of scalars to a quotient `A ⧸ J` which
is small and has the same category of modules, which is what makes the two universe parameters
of `supportedModulesComparison` independent.

## References

* [Stacks Project, Tag 0EF3](https://stacks.math.columbia.edu/tag/0EF3)
* [Stacks Project, Tag 0EF2](https://stacks.math.columbia.edu/tag/0EF2)
* [Stacks Project, Tag 0EF1](https://stacks.math.columbia.edu/tag/0EF1)
* [Stacks Project, Tag 0EF0](https://stacks.math.columbia.edu/tag/0EF0)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open DerivedCategory TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v w x y z w'

namespace Stacks.LocalCohomology

/-! ### Cutting the module universe down to the universe of the ring -/

private lemma exists_small_quotient_annihilator_le {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [Small.{v} (A ⧸ I)] :
    ∃ s : A, (Ideal.span {s}).annihilator ≤ I ∧
      Small.{v} (A ⧸ (Ideal.span {s}).annihilator) := by
  let J : Ideal A := ⨅ n : ℕ, I ^ n
  have hJ (n : ℕ) : I ^ n • (⊤ : Ideal A) ⊓ J = J := by
    rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
    exact inf_eq_right.mpr (iInf_le _ n)
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul J
  have hle : J ≤ I • J := by
    have h := hk (k + 1) (by omega)
    rw [hJ, hJ, Nat.add_sub_cancel_left, pow_one] at h
    exact h.le
  obtain ⟨r, hr, hfix⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    I J (Ideal.fg_of_isNoetherianRing J) hle
  have he : (Ideal.span {1 - r}).annihilator = J := by
    ext x
    rw [Submodule.mem_annihilator_span_singleton]
    show x * (1 - r) = 0 ↔ x ∈ J
    constructor
    · intro hx
      have hf : r * x = x := by linear_combination -hx
      have hm := (I.mem_iInf_smul_pow_eq_bot_iff x).2 ⟨⟨r, hr⟩, hf⟩
      simpa only [smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hm
    · intro hx
      have hf := hfix x hx
      change r * x = x at hf
      linear_combination -hf
  refine ⟨1 - r, ?_, ?_⟩
  · rw [he]
    exact (iInf_le (fun n : ℕ ↦ I ^ n) 1).trans_eq (pow_one I)
  · rw [he]
    have (n : ℕ) : Small.{v} (A ⧸ I ^ n) :=
      Ideal.small_quotient_pow I (Ideal.fg_of_isNoetherianRing I) n
    exact Ideal.small_quotient_iInf _

private lemma small_quotient_inf {A : Type u} [CommRing A]
    (I J : Ideal A) [Small.{v} (A ⧸ I)] [Small.{v} (A ⧸ J)] :
    Small.{v} (A ⧸ I ⊓ J) := by
  apply small_of_injective (f := fun x : A ⧸ I ⊓ J ↦
    (Ideal.Quotient.factor inf_le_left x, Ideal.Quotient.factor inf_le_right x))
  intro x y h
  induction x using Quotient.inductionOn' with | h x =>
    induction y using Quotient.inductionOn' with | h y =>
      apply Ideal.Quotient.eq.2
      exact ⟨Ideal.Quotient.eq.1 (congrArg Prod.fst h),
        Ideal.Quotient.eq.1 (congrArg Prod.snd h)⟩

private lemma exists_small_quotient_le_all_small_quotients
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    ∃ J : Ideal A, Small.{v} (A ⧸ J) ∧
      ∀ K : Ideal A, Small.{v} (A ⧸ K) → J ≤ K := by
  obtain ⟨I, hI, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun I : Ideal A ↦ Small.{v} (A ⧸ I.annihilator))
    ⟨⊥, by rw [Submodule.annihilator_bot]; infer_instance⟩
  refine ⟨I.annihilator, hI, ?_⟩
  intro K hK
  have : Small.{v} (A ⧸ I.annihilator ⊓ K) := small_quotient_inf _ _
  obtain ⟨s, hs, hsmall⟩ := exists_small_quotient_annihilator_le (I.annihilator ⊓ K)
  have he : (I ⊔ Ideal.span {s}).annihilator = (Ideal.span {s}).annihilator := by
    rw [Submodule.annihilator_sup]
    exact inf_eq_right.mpr (hs.trans inf_le_left)
  have hle : I ⊔ Ideal.span {s} ≤ I := hmax (by dsimp; rwa [he]) le_sup_left
  exact (Submodule.annihilator_mono (le_sup_right.trans hle)).trans
    (hs.trans inf_le_right)

private lemma exists_small_quotient_annihilating_small_modules
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    ∃ J : Ideal A, Small.{v} (A ⧸ J) ∧
      ∀ M : ModuleCat.{v} A, J ≤ Module.annihilator A M := by
  obtain ⟨J, hJ, h⟩ := exists_small_quotient_le_all_small_quotients.{u, v} A
  exact ⟨J, hJ, fun M ↦ h _ (Module.small_quotient_annihilator M)⟩

private lemma restrictScalars_full_of_surjective
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) : (ModuleCat.restrictScalars.{v} f).Full := by
  constructor
  intro X Y g
  refine ⟨ModuleCat.ofHom
    { g.hom.toAddMonoidHom with
      map_smul' := fun b x ↦ ?_ }, ?_⟩
  · obtain ⟨a, rfl⟩ := hf b
    exact g.hom.map_smul a x
  · rfl

private lemma restrictScalars_quotient_isEquivalence
    {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : ∀ M : ModuleCat.{v} A, J ≤ Module.annihilator A M) :
    (ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk J)).IsEquivalence := by
  have := restrictScalars_full_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  have : (ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk J)).EssSurj := by
    constructor
    intro M
    let hM : Module.IsTorsionBySet A M J := fun m a ↦
      (Module.mem_annihilator.1 (hJ M a.property)) m
    let := hM.module
    exact ⟨ModuleCat.of (A ⧸ J) M, ⟨(LinearEquiv.refl A M).toModuleIso⟩⟩
  exact {}

private lemma exists_small_ring_restrictScalars_isEquivalence
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    ∃ (B : Type v) (_ : CommRing B) (f : A →+* B), Function.Surjective f ∧
      (ModuleCat.restrictScalars.{v} f).IsEquivalence := by
  obtain ⟨J, hJ, h⟩ := exists_small_quotient_annihilating_small_modules.{u, v} A
  let B := Shrink.{v} (A ⧸ J)
  let e : (A ⧸ J) ≃+* B := (Shrink.ringEquiv (A ⧸ J)).symm
  let f := e.toRingHom.comp (Ideal.Quotient.mk J)
  have := restrictScalars_quotient_isEquivalence J h
  have : (ModuleCat.restrictScalars.{v} e.toRingHom).IsEquivalence := inferInstance
  exact ⟨B, inferInstance, f, e.surjective.comp Ideal.Quotient.mk_surjective,
    Functor.isEquivalence_of_iso
      (ModuleCat.restrictScalarsComp (Ideal.Quotient.mk J) e.toRingHom).symm⟩

/-! ### Local cohomology with support in `T` of a module vanishes above the dimension -/

/-- **Local cohomology with closed support vanishes above the dimension of the ring**, in the
coreflection model of [Stacks, Tag 0A6Q]. This is Tag 0DXC fed into the vanishing criterion of
Tag 0DX7. -/
private theorem isZero_localCohomologyModule_of_lt
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (i : ℤ)
    (hi : ((ringKrullDim A).unbotD 0).toNat < i.toNat) :
    IsZero (localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) M i) := by
  let d : ℕ := ((ringKrullDim A).unbotD 0).toNat
  have hd : ringKrullDim A ≤ (d : WithBot ℕ∞) := by
    cases h : ringKrullDim A with
    | bot => exact bot_le
    | coe n =>
      have hn : n ≠ ⊤ := by
        intro hn
        apply hdim.ne
        rw [h]
        simp [hn]
      simp only [d, h, WithBot.unbotD_coe]
      exact_mod_cast (ENat.natCast_toNat hn).symm.le
  have hcd := cohomologicalDimension_le_ringKrullDim A I (Ideal.fg_of_isNoetherianRing I) d hd
  have hboundD : IsLocalCohomologyBound A I (Ideal.fg_of_isNoetherianRing I) (d : ℤ) :=
    ⟨by omega, fun j hj ↦ (isLocalCohomologyBound_cohomologicalDimension A I
      (Ideal.fg_of_isNoetherianRing I)).2 j (hcd.trans_lt hj)⟩
  have hmodule : ∀ (N : ModuleCat.{max u v} A) (j : ℤ), (d : ℤ) < j →
      IsZero (localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) N j) :=
    ((localCohomology_vanishing_tfae A I (Ideal.fg_of_isNoetherianRing I) (d : ℤ)
      hboundD.1).out 1 2).mp hboundD.2
  change ((((ringKrullDim A).unbotD 0).toNat : ℕ) < i.toNat) at hi
  exact hmodule M i (by omega)

/-- Local cohomology with support in a closed subset `V(I)` of a module placed in degree zero
vanishes above the Krull dimension, in the model given by the total right derived functor of
`Γ_{V(I)}`. -/
private theorem isZero_localCohomologyWithSupportIn_zeroLocus_single
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (I : Ideal A)
    (M : ModuleCat.{max u v} A) (i : ℤ)
    (hi : ((ringKrullDim A).unbotD 0).toNat < i.toNat) :
    IsZero (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  have := isIso_compareSectionsWithSupportLocalCohomology_app.{u, v} A I
    (Ideal.fg_of_isNoetherianRing I)
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
  refine (isZero_localCohomologyModule_of_lt.{u, v} A hdim I M i hi).of_iso ?_
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
    (asIso ((compareSectionsWithSupportLocalCohomology.{u, v} A I
      (Ideal.fg_of_isNoetherianRing I)).app
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))

/-- A colimit of zero objects is zero. -/
private lemma isZero_of_isColimit_of_isZero {C : Type w} [Category.{w'} C]
    [HasZeroMorphisms C] {J : Type x} [Category.{y} J] {F : J ⥤ C} {c : Cocone F}
    (hc : IsColimit c) (h : ∀ j, IsZero (F.obj j)) : IsZero c.pt := by
  rw [IsZero.iff_id_eq_zero]
  exact hc.hom_ext fun j ↦ (h j).eq_of_src _ _

/-- **Local cohomology with support in `T` of a module vanishes above the Krull dimension.**
Tag 0EF1 writes it as the filtered colimit of local cohomology with closed support, and each
stage vanishes by `isZero_localCohomologyWithSupportIn_zeroLocus_single`. -/
private theorem isZero_localCohomologyWithSupportIn_single
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [K.IsKInjective]
    (e : DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
    (i : ℤ) (hi : ((ringKrullDim A).unbotD 0).toNat < i.toNat) :
    IsZero (localCohomologyWithSupportIn A T (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K)) i) := by
  have eY : DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ)).obj K) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app K ≪≫ e
  refine isZero_of_isColimit_of_isZero
    (isColimitClosedSupportCoconeOfKInjective.{u, v} T i K) (fun J ↦ ?_)
  refine (isZero_localCohomologyWithSupportIn_zeroLocus_single.{u, v} A hdim
    (OrderDual.ofDual J).1 M i hi).of_iso ?_
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
    ((derivedSectionsWithSupportIn.{u, v} A (ClosedSupportIdeal.support A J)).mapIso eY)

/-- The complex of `T`-supported sections of a K-injective resolution of a module is exact in
every degree above the Krull dimension. -/
private theorem supportedSections_exactAt_injective_resolution
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [K.IsKInjective]
    (e : DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
    (i : ℤ) (hi : ((ringKrullDim A).unbotD 0).toNat < i.toNat) :
    (((supportedSectionsFunctor.{u, v} A T).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt i := by
  let F := (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)).ι
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  apply IsZero.of_full_of_faithful_of_isZero F
  have h : IsZero ((((sectionsWithSupportInFunctor.{u, v} A T).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology i) :=
    (isZero_localCohomologyWithSupportIn_single.{u, v} A hdim T M K e i hi).of_iso
      (localCohomologyWithSupportInIsoOfKInjective.{u, v} T i K).symm
  exact h.of_iso ((StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso
    F i).app _).symm

/-! ### Bounded cohomological dimension of supported sections -/

private def plusQuotientCompQhIso {C : Type w} [Category.{w'} C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) :
    Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj K) ≅ Plus.Q.obj K :=
  Plus.ι.preimageIso
    ((Plus.QhCompιIsoιCompQh C).app _ ≪≫
      Qh.mapIso ((HomotopyCategory.Plus.quotientCompιIso C).app K) ≪≫
      (quotientCompQhIso C).app K.obj)

/-- The bounded-below right derived functor of supported sections kills a module placed in
degree zero in every degree above the Krull dimension. -/
private lemma supportedSections_rightDerivedPlus_isZero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) (i : ℤ)
    (hi : ((ringKrullDim A).unbotD 0).toNat < i.toNat) :
    let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
    IsZero ((Plus.homologyFunctor (ModulesSupportedIn.{u, max u v} A T) i).obj
      ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus.obj
        ((Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M))) := by
  let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let C := ModuleCat.{max u v} A
  let D := ModulesSupportedIn.{u, max u v} A T
  let F := supportedSectionsFunctor.{u, v} A T
  let X := (Plus.singleFunctor C 0).obj M
  obtain ⟨L, hL, ⟨e⟩⟩ := Plus.exists_injective_nonempty_iso X 0
  let K := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  let qK := (HomotopyCategory.Plus.quotient C).obj K
  have : ∀ n : ℤ, Injective (qK.obj.as.X n) := fun n ↦ by
    dsimp [qK, K]
    infer_instance
  let : IsIso (F.rightDerivedFunctorPlusUnith.app qK) := by infer_instance
  let unitIso := asIso (F.rightDerivedFunctorPlusUnith.app qK)
  let e₁ : Plus.Q.obj (F.mapCochainComplexPlus.obj K) ≅ F.rightDerivedFunctorPlus.obj X :=
    (plusQuotientCompQhIso (F.mapCochainComplexPlus.obj K)).symm ≪≫
      unitIso ≪≫
      F.rightDerivedFunctorPlus.mapIso (plusQuotientCompQhIso K ≪≫ e)
  have he : Q.obj K.obj ≅ (singleFunctor C 0).obj M := Plus.ι.mapIso e
  have : K.obj.IsKInjective := by
    show CochainComplex.IsKInjective
      (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
    infer_instance
  have hzero := supportedSections_exactAt_injective_resolution.{u, v} A hdim T M K.obj he i hi
  have hz : IsZero ((Plus.homologyFunctor D i).obj
      (Plus.Q.obj (F.mapCochainComplexPlus.obj K))) :=
    hzero.isZero_homology.of_iso ((homologyFunctorFactors D i).app _)
  exact hz.of_iso ((Plus.homologyFunctor D i).mapIso e₁.symm)

private lemma isIso_unit_iff_computesRightDerived
    {C : Type w} [Category.{w'} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory C]
    {D : Type x} [Category.{y} D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (X : C) :
    IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj X)) ↔
      (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso C)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj X) := by
  classical
  have hres (K : HomotopyCategory.Plus C) :
      ∃ (Y : HomotopyCategory.Plus C) (f : K ⟶ Y)
        (_ : HomotopyCategory.Plus.quasiIso C f),
        IsIso (F.rightDerivedFunctorPlusUnith.app Y) := by
    let r : (HomotopyCategory.Plus.localizerMorphism C).RightResolution K :=
      Classical.arbitrary _
    exact ⟨_, r.w, r.hw, inferInstance⟩
  have : (HomotopyCategory.Plus.quasiIso C).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  exact (Functor.computesRightDerived_iff_isIso_app
    (F.mapHomotopyCategoryPlus ⋙ Plus.Qh) Plus.Qh F.rightDerivedFunctorPlus
    (HomotopyCategory.Plus.quasiIso C) F.rightDerivedFunctorPlusUnith
    ((HomotopyCategory.Plus.singleFunctor C 0).obj X) hres).symm

/-- **Derived supported sections commutes with a deep enough truncation.** For every object `K`
of `D(A)` and every degree `i` there is a bound `a ≤ i` such that the truncation map
`K ⟶ τ^{≥ a} K` becomes an isomorphism in degree `i` after applying derived supported sections.

This is Tag 07K7 applied to `Γ_T`, whose cohomological dimension is bounded by the Krull
dimension of `A`. -/
private lemma supportedSections_truncGE_comparison
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    ∃ a : ℤ, a ≤ i ∧ IsIso ((homologyFunctor (ModuleCat.{max u v} A) i).map
      ((derivedSupportedSections.{u, v} A T ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory).map
          ((TStructure.t.truncGEπ a).app K))) := by
  let C := ModuleCat.{max u v} A
  let D := ModulesSupportedIn.{u, max u v} A T
  let F := supportedSectionsFunctor.{u, v} A T
  let G := (supportModuleProperty A T : ObjectProperty C).ι
  have : EnoughInjectives C := ModuleCat.enoughInjectives A
  have : F.IsRightAdjoint := (inclusion_adj_supportedSectionsFunctor.{u, v} A T).isRightAdjoint
  have : PreservesFiniteLimits F := inferInstance
  let n := ((ringKrullDim A).unbotD 0).toNat + 1
  let P : ObjectProperty C := fun Y ↦ IsIso (F.rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.singleFunctor C 0).obj Y))
  have hmono (Y : C) : ∃ (Z : C) (f : Y ⟶ Z) (_ : Mono f), P Z := by
    refine ⟨Injective.under Y, Injective.ι Y, inferInstance, ?_⟩
    show IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj (Injective.under Y)))
    have : ∀ m : ℤ, Injective
        (((HomotopyCategory.Plus.singleFunctor C 0).obj (Injective.under Y)).obj.as.X m) :=
      fun m ↦ inferInstanceAs (Injective
        (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (Injective.under Y)).X m))
    infer_instance
  have h07 := Functor.hasRightDerivedFunctor_of_isZero_rightDerived F
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith P
    (isIso_unit_iff_computesRightDerived F) hmono n
    (fun N ↦ supportedSections_rightDerivedPlus_isZero.{u, v} A hdim T N n (by
      dsimp [n]
      omega))
  let R := derivedSupportedSections.{u, v} A T
  let η := derivedSupportedSectionsUnit.{u, v} A T
  have h := ((h07.2.2 R η).2 K).2.1 i i le_rfl
  refine ⟨i - (n : ℤ) + 1, by dsimp [n]; omega, ?_⟩
  let f := R.map ((TStructure.t.truncGEπ (i - (n : ℤ) + 1)).app K)
  have : IsIso ((homologyFunctor D i).map f) := h
  exact (NatIso.isIso_map_iff
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso G i) f).mpr
    (inferInstanceAs (IsIso (G.map ((homologyFunctor D i).map f))))

/-! ### From the bounded-below equivalence to the unbounded one -/

private lemma mapDerivedCategory_reflectsIsomorphisms
    {C D : Type w} [Category.{w'} C] [Abelian C] [HasDerivedCategory C]
    [Category.{w'} D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    rw [DerivedCategory.isIso_iff]
    intro i
    have h : IsIso ((F.mapDerivedCategory ⋙ homologyFunctor D i).map f) := by
      dsimp
      infer_instance
    have : IsIso (F.map ((homologyFunctor C i).map f)) :=
      (NatIso.isIso_map_iff
        (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i) f).mp h
    exact isIso_of_reflects_iso _ F

private lemma isGE_rightAdjoint_mapDerivedCategory
    {C D : Type w} [Category.{w'} C] [Abelian C] [HasDerivedCategory C]
    [Category.{w'} D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (R : DerivedCategory D ⥤ DerivedCategory C) (adj : F.mapDerivedCategory ⊣ R)
    (K : DerivedCategory D) (a : ℤ) [K.IsGE a] : (R.obj K).IsGE a := by
  apply (TStructure.t.isGE_iff_orthogonal (a - 1) a (by omega) (R.obj K)).mpr
  intro Y f hY
  have : (F.mapDerivedCategory.obj Y).IsLE (a - 1) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact (F.map_isZero (Y.isZero_of_isLE (a - 1) i hi)).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app Y)
  apply (adj.homEquiv Y K).symm.injective
  show F.mapDerivedCategory.map f ≫ adj.counit.app K =
    F.mapDerivedCategory.map 0 ≫ adj.counit.app K
  rw [F.mapDerivedCategory.map_zero, zero_comp]
  exact (TStructure.t (C := D)).zero_of_isLE_of_isGE
    (F.mapDerivedCategory.map f ≫ adj.counit.app K) (a - 1) a (by omega)
    inferInstance (inferInstanceAs (K.IsGE a))

/-- The counit of the derived adjunction is invertible at a bounded-below object of `D_T(A)`.
This is Tag 0EF2 in the canonical form of
`Stacks.LocalCohomology.supportedModulesComparisonPlus_isEquivalence`. -/
private lemma isIso_counit_on_supportedPlus
    (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T)
    (R : DerivedCategory (ModuleCat.{v} A) ⥤
      DerivedCategory (ModulesSupportedIn.{u, v} A T))
    (adj : (supportModuleProperty A T :
      ObjectProperty (ModuleCat.{v} A)).ι.mapDerivedCategory ⊣ R)
    (K : derivedCategorySupportedIn.{u, v} A T) (a : ℤ) [K.obj.IsGE a] :
    IsIso (adj.counit.app K.obj) := by
  have := supportedModulesComparisonPlus_isEquivalence.{u, v} A T hT
  let P := supportModuleProperty.{u, v} A T
  let Bplus := DerivedCategoryB.derivedCategoryBPlus P
  let Rp : Bplus.FullSubcategory ⥤ DerivedCategory.Plus (ModulesSupportedIn.{u, v} A T) :=
    TStructure.t.plus.lift (Bplus.ι ⋙ R) (fun Y ↦ by
      obtain ⟨b, hb⟩ := Y.property.1
      have : Y.obj.IsGE b := (DerivedCategory.isGE_iff _ _).mpr hb
      exact ⟨b, isGE_rightAdjoint_mapDerivedCategory P.ι R adj Y.obj b⟩)
  let comm1 : DerivedCategory.Plus.ι ⋙ P.ι.mapDerivedCategory ≅
      supportedModulesComparisonPlus.{u, v} A T ⋙ Bplus.ι :=
    (Bplus.liftCompιIso _ (derivedCategoryBPlus_mapDerivedCategory_obj.{u, v} A T)).symm
  let comm2 : Bplus.ι ⋙ R ≅ Rp ⋙ DerivedCategory.Plus.ι := Iso.refl _
  let hp : supportedModulesComparisonPlus.{u, v} A T ⊣ Rp :=
    adj.restrictFullyFaithful TStructure.t.plus.fullyFaithfulι Bplus.fullyFaithfulι
      comm1 comm2
  have : Rp.IsEquivalence := hp.isEquivalence_right_of_isEquivalence_left
  let Y : Bplus.FullSubcategory := ⟨K.obj,
    ⟨⟨a, fun i hi ↦ K.obj.isZero_of_isGE a i hi⟩, K.property⟩⟩
  have hcu : IsIso (hp.counit.app Y) := by infer_instance
  have hh := adj.map_restrictFullyFaithful_counit_app TStructure.t.plus.fullyFaithfulι
    Bplus.fullyFaithfulι comm1 comm2 Y
  have hcomp : IsIso (comm1.hom.app (Rp.obj Y) ≫ adj.counit.app Y.obj) := by
    have hh' : Bplus.ι.map (hp.counit.app Y) =
        comm1.hom.app (Rp.obj Y) ≫ adj.counit.app Y.obj := by
      change Bplus.ι.map (hp.counit.app Y) = comm1.hom.app (Rp.obj Y) ≫
        P.ι.mapDerivedCategory.map (𝟙 (R.obj Y.obj)) ≫ adj.counit.app Y.obj at hh
      have hm := P.ι.mapDerivedCategory.map_id (R.obj Y.obj)
      rw [hm] at hh
      exact hh.trans (congrArg (fun f ↦ comm1.hom.app (Rp.obj Y) ≫ f)
        (Category.id_comp (adj.counit.app Y.obj)))
    rw [← hh']
    exact (Bplus.ι.mapIso (@asIso _ _ _ _ _ hcu)).isIso_hom
  exact IsIso.of_isIso_comp_left (comm1.hom.app (Rp.obj Y)) _

private lemma isIso_homology_map_truncGEπ
    {C : Type w} [Category.{w'} C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ a).app K)) := by
  let Δ := (TStructure.t.triangleLEGE (a - 1) a (by omega)).obj K
  have hΔ := TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) K
  have : Δ.obj₁.IsLE (a - 1) := by
    show ((TStructure.t.truncLE (a - 1)).obj K).IsLE (a - 1)
    infer_instance
  have hz : IsZero ((homologyFunctor C i).obj Δ.obj₁) :=
    Δ.obj₁.isZero_of_isLE (a - 1) i (by omega)
  have hz' : IsZero ((homologyFunctor C (i + 1)).obj Δ.obj₁) :=
    Δ.obj₁.isZero_of_isLE (a - 1) (i + 1) (by omega)
  have : Mono ((homologyFunctor C i).map Δ.mor₂) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff Δ hΔ i).2
      (hz.eq_of_src _ _)
  have : Epi ((homologyFunctor C i).map Δ.mor₂) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff
      Δ hΔ i (i + 1) rfl).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((homologyFunctor C i).map Δ.mor₂)

private lemma supported_truncGE (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (K : derivedCategorySupportedIn.{u, v} A T) (a : ℤ) :
    DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A))
      ((TStructure.t.truncGE a).obj K.obj) := by
  intro i
  by_cases hi : a ≤ i
  · have := isIso_homology_map_truncGEπ K.obj a i hi
    exact (supportModuleProperty A T).prop_of_iso
      (asIso ((homologyFunctor (ModuleCat.{v} A) i).map
        ((TStructure.t.truncGEπ a).app K.obj))) (K.property i)
  · exact (supportModuleProperty A T).prop_of_isZero
      (((TStructure.t.truncGE a).obj K.obj).isZero_of_isGE a i (by omega))

private lemma isIso_on_supported_of_truncGE
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (R : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    (ε : R ⟶ 𝟭 _)
    (hplus : ∀ (K : derivedCategorySupportedIn.{u, v} A T) (a : ℤ),
      K.obj.IsGE a → IsIso (ε.app K.obj))
    (htrunc : ∀ (K : derivedCategorySupportedIn.{u, v} A T) (i : ℤ),
      ∃ a : ℤ, a ≤ i ∧ IsIso ((homologyFunctor (ModuleCat.{v} A) i).map
        (R.map ((TStructure.t.truncGEπ a).app K.obj))))
    (K : derivedCategorySupportedIn.{u, v} A T) : IsIso (ε.app K.obj) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  obtain ⟨a, hai, ha⟩ := htrunc K i
  let π := (TStructure.t.truncGEπ a).app K.obj
  let H := homologyFunctor (ModuleCat.{v} A) i
  have : IsIso (H.map (R.map π)) := ha
  have : IsIso (H.map π) := isIso_homology_map_truncGEπ K.obj a i hai
  have : IsIso (ε.app ((TStructure.t.truncGE a).obj K.obj)) :=
    hplus ⟨_, supported_truncGE A T K a⟩ a inferInstance
  have hn : H.map (R.map π) ≫ H.map (ε.app ((TStructure.t.truncGE a).obj K.obj)) =
      H.map (ε.app K.obj) ≫ H.map π := by
    simpa only [Functor.map_comp, Functor.id_map, Functor.id_obj] using
      congrArg H.map (ε.naturality π)
  have : IsIso (H.map (ε.app K.obj) ≫ H.map π) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H.map π)

private lemma supportedModulesComparison_isEquivalence_of_counit
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (R : DerivedCategory (ModuleCat.{v} A) ⥤
      DerivedCategory (ModulesSupportedIn.{u, v} A T))
    (adj : (supportModuleProperty A T :
      ObjectProperty (ModuleCat.{v} A)).ι.mapDerivedCategory ⊣ R)
    (h : ∀ K : derivedCategorySupportedIn.{u, v} A T, IsIso (adj.counit.app K.obj)) :
    (supportedModulesComparison.{u, v} A T).IsEquivalence := by
  let F := (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A)).ι
  let : F.mapDerivedCategory.ReflectsIsomorphisms :=
    mapDerivedCategory_reflectsIsomorphisms F
  have hu (X : DerivedCategory (ModulesSupportedIn.{u, v} A T)) :
      IsIso (adj.unit.app X) := by
    have : IsIso (adj.counit.app (F.mapDerivedCategory.obj X)) :=
      h ((supportedModulesComparison.{u, v} A T).obj X)
    have : IsIso (F.mapDerivedCategory.map (adj.unit.app X)) :=
      isIso_of_comp_hom_eq_id (adj.counit.app (F.mapDerivedCategory.obj X))
        (adj.left_triangle_components X)
    exact isIso_of_reflects_iso _ F.mapDerivedCategory
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  have : F.mapDerivedCategory.Full := adj.fullyFaithfulLOfIsIsoUnit.full
  have : F.mapDerivedCategory.Faithful := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have : (supportedModulesComparison.{u, v} A T).Full := by
    show ((DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T)).lift F.mapDerivedCategory _).Full
    exact ObjectProperty.instFullFullSubcategoryLift _ _ _
  have : (supportedModulesComparison.{u, v} A T).Faithful := by
    show ((DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T)).lift F.mapDerivedCategory _).Faithful
    exact ObjectProperty.instFaithfulFullSubcategoryLift _ _ _
  have : (supportedModulesComparison.{u, v} A T).EssSurj := ⟨fun K ↦ by
    let := h K
    let counitIso := asIso (adj.counit.app K.obj)
    exact ⟨R.obj K.obj, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso counitIso⟩⟩⟩
  exact {}

private lemma supportedModulesComparison_isEquivalence_large
    (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) :
    (supportedModulesComparison.{u, max u v} A T).IsEquivalence := by
  obtain ⟨adj⟩ := derivedInclusion_adj_derivedSupportedSections.{u, v} A T hT
  exact supportedModulesComparison_isEquivalence_of_counit A T
    (derivedSupportedSections.{u, v} A T) adj fun K ↦ isIso_on_supported_of_truncGE A T
    (derivedSupportedSections.{u, v} A T ⋙
      (supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory)
    adj.counit (fun L a _ ↦
      isIso_counit_on_supportedPlus A T hT (derivedSupportedSections.{u, v} A T) adj L a)
    (fun L i ↦ supportedSections_truncGE_comparison.{u, v} A hdim T L.obj i) K

/-! ### Descending the module universe -/

universe t₁ t₂ t₃ t₄ s₁ s₂ s₃ s₄ r₁ r₂ r₃

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Deriving a composite of exact functors is the composite of the derived functors. -/
private def derivedCompIso
    {C : Type t₁} [Category.{s₁} C] [Abelian C] [HasDerivedCategory.{r₁} C]
    {D : Type t₂} [Category.{s₂} D] [Abelian D] [HasDerivedCategory.{r₂} D]
    {E : Type t₃} [Category.{s₃} E] [Abelian E] [HasDerivedCategory.{r₃} E]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory := by
  apply Localization.liftNatIso Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory))
    (Q ⋙ (F ⋙ G).mapDerivedCategory)
  exact Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactors ≪≫
    (F ⋙ G).mapDerivedCategoryFactors.symm

/-- A natural isomorphism between exact functors induces one between the functors they
induce on derived categories. -/
private def mapDerivedCategoryNatIso
    {C : Type t₁} [Category.{s₁} C] [Abelian C] [HasDerivedCategory.{r₁} C]
    {D : Type t₂} [Category.{s₂} D] [Abelian D] [HasDerivedCategory.{r₂} D]
    (F G : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (α : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory := by
  apply Localization.liftNatIso Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (Q ⋙ F.mapDerivedCategory) (Q ⋙ G.mapDerivedCategory)
  exact F.mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)) Q ≪≫
    G.mapDerivedCategoryFactors.symm

/-- Being an equivalence transports across a commuting square whose other three sides are
equivalences. -/
private lemma isEquivalence_of_commSq
    {C₁ : Type t₁} [Category.{s₁} C₁] {C₂ : Type t₂} [Category.{s₂} C₂]
    {D₁ : Type t₃} [Category.{s₃} D₁] {D₂ : Type t₄} [Category.{s₄} D₂]
    (L : C₁ ⥤ C₂) (M : D₁ ⥤ D₂) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    [L.IsEquivalence] [M.IsEquivalence] [F₁.IsEquivalence]
    (iso : L ⋙ F₂ ≅ F₁ ⋙ M) : F₂.IsEquivalence := by
  have : (F₁ ⋙ M).IsEquivalence := inferInstance
  have : (L ⋙ F₂).IsEquivalence := Functor.isEquivalence_of_iso iso.symm
  exact Functor.isEquivalence_of_comp_left L F₂

/-- Restriction of scalars along a surjective ring map matches supports: a prime of the
quotient lies in the support of a module exactly when its image lies in the support of the
restriction. -/
private lemma mem_support_restrictScalars_iff {A : Type u} [CommRing A] {B : Type v}
    [CommRing B] (f : A →+* B) (hf : Function.Surjective f) (N : ModuleCat.{v} B)
    (q : PrimeSpectrum B) :
    PrimeSpectrum.comap f q ∈ Module.support A ((ModuleCat.restrictScalars.{v} f).obj N) ↔
      q ∈ Module.support B N := by
  rw [← not_iff_not, Module.notMem_support_iff', Module.notMem_support_iff']
  constructor
  · intro h m
    obtain ⟨a, ha, hm⟩ := h m
    refine ⟨f a, fun hfa ↦ ha ?_, hm⟩
    rwa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  · intro h m
    obtain ⟨b, hb, hm⟩ := h m
    obtain ⟨a, rfl⟩ := hf b
    refine ⟨a, fun ha ↦ hb ?_, hm⟩
    rwa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at ha

/-- A module over the quotient is supported in `T` after restriction of scalars exactly when
it is supported in the preimage of `T`. -/
private lemma support_restrictScalars_subset_iff {A : Type u} [CommRing A] {B : Type v}
    [CommRing B] (f : A →+* B) (hf : Function.Surjective f) (N : ModuleCat.{v} B)
    (T : Set (PrimeSpectrum A)) :
    Module.support A ((ModuleCat.restrictScalars.{v} f).obj N) ⊆ T ↔
      Module.support B N ⊆ PrimeSpectrum.comap f ⁻¹' T := by
  constructor
  · intro h q hq
    exact h ((mem_support_restrictScalars_iff f hf N q).2 hq)
  · intro h p hp
    have hker : RingHom.ker f ≤
        Module.annihilator A ((ModuleCat.restrictScalars.{v} f).obj N) := by
      intro a ha
      rw [Module.mem_annihilator]
      intro m
      show f a • m = 0
      rw [RingHom.mem_ker.1 ha, zero_smul]
    have hp' : p ∈ Set.range (PrimeSpectrum.comap f) := by
      rw [_root_.range_comap_of_surjective B f hf, PrimeSpectrum.mem_zeroLocus,
        SetLike.coe_subset_coe]
      exact hker.trans (Module.annihilator_le_of_mem_support hp)
    obtain ⟨q, rfl⟩ := hp'
    exact h ((mem_support_restrictScalars_iff f hf N q).1 hp)

/-- The property of being supported in `T` pulls back along restriction of scalars to the
property of being supported in the preimage of `T`. -/
private lemma supportModuleProperty_inverseImage_restrictScalars
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (T : Set (PrimeSpectrum A)) :
    (supportModuleProperty A T :
        ObjectProperty (ModuleCat.{v} A)).inverseImage (ModuleCat.restrictScalars.{v} f) =
      supportModuleProperty B (PrimeSpectrum.comap f ⁻¹' T) := by
  funext N
  exact propext (support_restrictScalars_subset_iff f hf N T)

private instance restrictScalars_asEquivalence_functor_additive
    {A : Type u} [CommRing A] {B : Type v} [CommRing B] (f : A →+* B)
    [(ModuleCat.restrictScalars.{v} f).IsEquivalence] :
    (ModuleCat.restrictScalars.{v} f).asEquivalence.functor.Additive :=
  inferInstanceAs (ModuleCat.restrictScalars.{v} f).Additive

/-- Restriction of scalars along a surjection restricts to an equivalence between the
categories of supported modules. -/
private def modulesSupportedInEquivalence
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    [(ModuleCat.restrictScalars.{v} f).IsEquivalence] (T : Set (PrimeSpectrum A)) :
    ModulesSupportedIn.{v, v} B (PrimeSpectrum.comap f ⁻¹' T) ≌
      ModulesSupportedIn.{u, v} A T :=
  Equivalence.congrFullSubcategory (ModuleCat.restrictScalars.{v} f).asEquivalence
    (supportModuleProperty_inverseImage_restrictScalars f hf T)

private instance modulesSupportedInEquivalence_functor_additive
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    [(ModuleCat.restrictScalars.{v} f).IsEquivalence] (T : Set (PrimeSpectrum A)) :
    (modulesSupportedInEquivalence f hf T).functor.Additive := by
  dsimp [modulesSupportedInEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- Having cohomology supported in `T` pulls back along the derived restriction of scalars to
having cohomology supported in the preimage of `T`. -/
private lemma derivedCategoryB_inverseImage_mapDerivedCategory
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    [(ModuleCat.restrictScalars.{v} f).IsEquivalence] (T : Set (PrimeSpectrum A)) :
    (DerivedCategoryB.derivedCategoryB
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{v} A))).inverseImage
          (ModuleCat.restrictScalars.{v} f).mapDerivedCategory =
      DerivedCategoryB.derivedCategoryB
        (supportModuleProperty B (PrimeSpectrum.comap f ⁻¹' T) :
          ObjectProperty (ModuleCat.{v} B)) := by
  funext X
  exact propext <| forall_congr' fun i ↦
    ((supportModuleProperty A T).prop_iff_of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (ModuleCat.restrictScalars.{v} f) i).app X)).trans
      (support_restrictScalars_subset_iff f hf _ T)

/-- The comparison functor for `A` is an equivalence as soon as it is one for a quotient of `A`
whose restriction of scalars is an equivalence of module categories. -/
private lemma supportedModulesComparison_isEquivalence_of_restrictScalars
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    [(ModuleCat.restrictScalars.{v} f).IsEquivalence] (T : Set (PrimeSpectrum A))
    (h : (supportedModulesComparison.{v, v} B (PrimeSpectrum.comap f ⁻¹' T)).IsEquivalence) :
    (supportedModulesComparison.{u, v} A T).IsEquivalence := by
  have : (modulesSupportedInEquivalence f hf T).functor.IsEquivalence :=
    (modulesSupportedInEquivalence f hf T).isEquivalence_functor
  have : (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.IsEquivalence :=
    Stacks.ModulesOnACategory.mapDerivedCategory_isEquivalence_of_equivalence
      (ModuleCat.restrictScalars.{v} f).asEquivalence
  have : (modulesSupportedInEquivalence f hf T).functor.mapDerivedCategory.IsEquivalence :=
    Stacks.ModulesOnACategory.mapDerivedCategory_isEquivalence_of_equivalence
      (modulesSupportedInEquivalence f hf T)
  have : (DerivedCategoryB.derivedCategoryB
      (supportModuleProperty A T :
        ObjectProperty (ModuleCat.{v} A))).IsClosedUnderIsomorphisms :=
    ⟨fun {_ _} e hX n ↦ (supportModuleProperty A T).prop_of_iso
      ((homologyFunctor (ModuleCat.{v} A) n).mapIso e) (hX n)⟩
  let MM := Equivalence.congrFullSubcategory
    (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.asEquivalence
    (derivedCategoryB_inverseImage_mapDerivedCategory f hf T)
  have : MM.functor.IsEquivalence := MM.isEquivalence_functor
  have α : (modulesSupportedInEquivalence f hf T).functor ⋙
        (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A)).ι ≅
      (supportModuleProperty B (PrimeSpectrum.comap f ⁻¹' T) :
          ObjectProperty (ModuleCat.{v} B)).ι ⋙ ModuleCat.restrictScalars.{v} f :=
    Iso.refl _
  have sq : (modulesSupportedInEquivalence f hf T).functor.mapDerivedCategory ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{v} A)).ι.mapDerivedCategory ≅
      (supportModuleProperty B (PrimeSpectrum.comap f ⁻¹' T) :
          ObjectProperty (ModuleCat.{v} B)).ι.mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{v} f).mapDerivedCategory :=
    derivedCompIso (modulesSupportedInEquivalence f hf T).functor
        (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A)).ι ≪≫
      mapDerivedCategoryNatIso _ _ α ≪≫
      (derivedCompIso
        (supportModuleProperty B (PrimeSpectrum.comap f ⁻¹' T) :
          ObjectProperty (ModuleCat.{v} B)).ι (ModuleCat.restrictScalars.{v} f)).symm
  exact isEquivalence_of_commSq
    (modulesSupportedInEquivalence f hf T).functor.mapDerivedCategory MM.functor
    (supportedModulesComparison.{v, v} B (PrimeSpectrum.comap f ⁻¹' T))
    (supportedModulesComparison.{u, v} A T)
    (Functor.fullyFaithfulCancelRight
      (DerivedCategoryB.derivedCategoryB
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{v} A))).ι sq)

/-- **Stacks Project, Tag 0EF3.** Let `A` be a Noetherian ring of finite Krull dimension and let
`T ⊆ Spec(A)` be stable under specialization. The canonical functor from the derived category of
the modules supported in `T` to the full subcategory of `D(A)` on the objects whose cohomology is
supported in `T` is an equivalence. -/
@[stacks 0EF3]
theorem supportedModulesComparison_isEquivalence (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (hdim : ringKrullDim A < ⊤) :
    (supportedModulesComparison.{u, v} A T).IsEquivalence := by
  obtain ⟨B, hB, f, hf, hF⟩ := exists_small_ring_restrictScalars_isEquivalence.{u, v} A
  let : CommRing B := hB
  have : IsNoetherianRing B := isNoetherianRing_of_surjective A B f hf
  have : (ModuleCat.restrictScalars.{v} f).IsEquivalence := hF
  let T' := PrimeSpectrum.comap f ⁻¹' T
  have hT' : StableUnderSpecialization T' :=
    hT.preimage (PrimeSpectrum.continuous_comap f)
  have hdimB : ringKrullDim B < ⊤ :=
    (ringKrullDim_le_of_surjective f hf).trans_lt hdim
  have hcomparison := supportedModulesComparison_isEquivalence_large.{v, v} B T' hT' hdimB
  exact supportedModulesComparison_isEquivalence_of_restrictScalars f hf T hcomparison

end Stacks.LocalCohomology
