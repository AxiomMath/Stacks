module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverRingCatSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeAffineBase
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.FiniteFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived global sections of the twists of projective space over a ring

Let `A` be a commutative ring, `n` a natural number and `π : ℙⁿ_A ⟶ Spec A` the structure
morphism. This file computes what the unbounded `A`-linear derived global sections
`RΓ_A = AlgebraicGeometry.derivedGlobalSectionsOver π` do on quasi-coherent objects.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceDirectImage.isLE_derivedGlobalSectionsOver_obj`: the
  cohomological dimension of `RΓ_A` on `D_QCoh(𝒪_{ℙⁿ_A})` is at most `n`: if the cohomology
  sheaves of `E` are quasi-coherent and vanish above `b`, then `RΓ_A(E)` vanishes above `b + n`.
* `AlgebraicGeometry.ProjectiveSpaceDirectImage.isPseudoCoherent_derivedGlobalSectionsOver_twist`:
  `RΓ_A(𝒪(e)[0])` is a pseudo-coherent object of `D(A)` for every integer `e`.
* `AlgebraicGeometry.ProjectiveSpaceDirectImage.isZero_homology_derivedGlobalSectionsOver_twist`:
  for `e ≥ -n` the object `RΓ_A(𝒪(e)[0])` has no cohomology outside degree `0`.

## Implementation notes

The cohomology of `RΓ_A(F[0])` in degree `q` is the `q`-th right derived functor of `A`-linear
global sections at `F`
(`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`), which is Serre's
module `H^q(ℙⁿ_A, 𝒪(e))` of `Stacks.ProjectiveSpace.Cohomology.twistCohomology` read over `A`
(`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistCohomologyIsoRestrictScalars`);
[Stacks, Tag 01XT] makes it a finite free module, concentrated in degree `0` or in degree `n`.
The cohomological dimension is [Stacks, Tag 08D4] part (3)
(`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus`), fed with the
vanishing of the cohomology of a quasi-coherent module above `n` on a scheme covered by `n + 1`
affine opens with affine intersections ([Stacks, Tag 01XI]).

The derived categories are the standard model `HasDerivedCategory.standard`, installed at a
raised priority because the import closure carries the locally small instances.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveSpaceDirectImage

attribute [local instance 100000] HasDerivedCategory.standard

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

variable {A : Type u} [CommRing A] (n : ℕ)

/-- The structure morphism `ℙⁿ_A ⟶ Spec A`. -/
abbrev proj : projectiveSpaceOver n (Spec (.of A)) ⟶ Spec (.of A) :=
  projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A)

/-- **Cohomology of a quasi-coherent module on `ℙⁿ_A` vanishes above `n`**, for the `A`-linear
global sections. -/
theorem isZero_rightDerived_globalSectionsOver (F : (projectiveSpaceOver n (Spec (.of A))).Modules)
    [F.IsQuasicoherent] (p : ℕ) (hp : n < p) :
    IsZero (((globalSectionsOver (proj (A := A) n)).rightDerived p).obj F) := by
  have h : IsZero (((globalSectionsOver (proj (A := A) n) ⋙
      forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).rightDerived p).obj F) :=
    Stacks.Cohomology.AffineCover.isZero_cohomology_of_finite_affine_cover
      (projectiveSpaceOver n (Spec (.of A))) (AlgebraicGeometry.ProjectiveSpace.standardOpen n _)
      (AlgebraicGeometry.ProjectiveSpace.isAffineOpen_standardOpen n _)
      (AlgebraicGeometry.ProjectiveSpace.iSup_standardOpen_eq_top n _) F p (by omega)
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (globalSectionsOver (proj (A := A) n)) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) p F
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero
      (show IsZero (((globalSectionsOver (proj (A := A) n)).rightDerived p ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj F) from h.of_iso e))

/-- **The cohomological dimension of `RΓ_A` on `D_QCoh(𝒪_{ℙⁿ_A})` is at most `n`.** If the
cohomology sheaves of `E` are quasi-coherent and vanish in degrees above `b`, then `RΓ_A(E)`
vanishes in degrees above `b + n`. This is [Stacks, Tag 08D4] part (3) with the vanishing of
[Stacks, Tag 01XI] for the `n + 1` standard affine opens. -/
theorem isLE_derivedGlobalSectionsOver_obj
    (E : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules) (b : ℤ) (hE : E.IsLE b)
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (projectiveSpaceOver n (Spec (.of A))).Modules i).obj E).IsQuasicoherent) :
    ((derivedGlobalSectionsOver (proj (A := A) n)).obj E).IsLE (b + n) := by
  have key := AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus
    (projectiveSpaceOver n (Spec (.of A))) (AlgebraicGeometry.secsOver (proj (A := A) n))
    (AlgebraicGeometry.derSecs (proj (A := A) n)) (AlgebraicGeometry.derSecsUnit (proj (A := A) n))
    (n + 1)
    (fun M hM p hp => by
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ p by omega)
      exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
        (AlgebraicGeometry.secsOver (proj (A := A) n)) rfl M).2
        (isZero_rightDerived_globalSectionsOver n M k (by omega)))
    E hcoh b hE
  rwa [show b + ((n + 1 : ℕ) : ℤ) - 1 = b + n by omega] at key

/-! ### The cohomology of the twists, read over `A` -/

open Stacks.ProjectiveSpace.Cohomology (twistCohomology twistCohomologyMonomial negativeTwistPart
  negativeLaurentMonomials)

/-- **`H^q(RΓ_A(F[0]))` is the `q`-th right derived functor of `A`-linear global sections.** -/
theorem nonempty_homology_derivedGlobalSectionsOver_single_iso
    (F : (projectiveSpaceOver n (Spec (.of A))).Modules) (q : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((derivedGlobalSectionsOver (proj (A := A) n)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      ((AlgebraicGeometry.secsOver (proj (A := A) n)).rightDerivedPlus q).obj F) := by
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (AlgebraicGeometry.secsOver (proj (A := A) n)) (AlgebraicGeometry.derSecs (proj (A := A) n))
    (AlgebraicGeometry.derSecsUnit (proj (A := A) n))
    (fun I hI => Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective
      (AlgebraicGeometry.secsOver (proj (A := A) n)) (AlgebraicGeometry.derSecs (proj (A := A) n))
      (AlgebraicGeometry.derSecsUnit (proj (A := A) n))
      Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso I hI)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 (by
      change ((DerivedCategory.singleFunctor _ 0).obj F).IsGE 0
      infer_instance)
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).mapIso e⟩

/-- **`H^q(RΓ_A(𝒪(e)[0]))` is Serre's module `H^q(ℙⁿ_A, 𝒪(e))`, read over `A`.** -/
theorem nonempty_homology_derivedGlobalSectionsOver_twist_iso (e : ℤ) (q : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((derivedGlobalSectionsOver (proj (A := A) n)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) e))) ≅
      (ModuleCat.restrictScalars
        (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.toRingHom).obj
        (twistCohomology Γ(Spec (.of A), ⊤) n e q)) := by
  obtain ⟨e₁⟩ := nonempty_homology_derivedGlobalSectionsOver_single_iso (A := A) n
    (twistOver n (Spec (.of A)) e) q
  refine ⟨e₁ ≪≫ ((Stacks.DerivedIndexing.rightDerivedIso
      (AlgebraicGeometry.secsOver (proj (A := A) n)) q).app _).symm ≪≫
    ((moduleGlobalSections (projectiveSpaceOver n (Spec (.of A)))).rightDerivedCompIso
      (ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of A)).inv ≫
        (proj (A := A) n).appTop).hom)) q).app _ ≪≫
    ModuleCat.restrictScalarsComp'App ((Scheme.ΓSpecIso (.of A)).inv.hom)
      ((proj (A := A) n).appTop.hom) _ rfl _ ≪≫
    (ModuleCat.restrictScalars
        (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.toRingHom).mapIso
      (Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistCohomologyIsoRestrictScalars
        n (Spec (.of A)) e q).symm⟩

/-- **`H^q(ℙⁿ_R, 𝒪(e))` is a finite free `R`-module**, in every degree. -/
@[ega "III 2.1.14" "more general"]
theorem finite_free_twistCohomology (R : Type u) [CommRing R] (e : ℤ) (q : ℕ) :
    Module.Finite R (twistCohomology R n e q) ∧ Module.Free R (twistCohomology R n e q) := by
  by_cases h0 : q = 0 ∧ 0 ≤ e
  · obtain ⟨rfl, he⟩ := h0
    let i := ((twistCohomologyMonomial R n e).degreeZero he).toLinearEquiv
    exact ⟨Module.Finite.equiv i.symm, Module.Free.of_equiv i.symm⟩
  by_cases hn : q = n ∧ e < 0
  · obtain ⟨rfl, he⟩ := hn
    let i := ((twistCohomologyMonomial R q e).degreeTop he).toLinearEquiv
    have : Module.Free R (negativeTwistPart R q e) :=
      Module.Free.of_basis (Stacks.ProjectiveSpace.Cohomology.negativeTwistPartBasis R q e)
    exact ⟨Module.Finite.equiv i.symm, Module.Free.of_equiv i.symm⟩
  · have : Subsingleton (twistCohomology R n e q) :=
      ModuleCat.isZero_iff_subsingleton.mp ((twistCohomologyMonomial R n e).vanishing q (by tauto))
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton R _⟩

/-- **`H^q(RΓ_A(𝒪(e)[0]))` is a finite free `A`-module**, in every degree. -/
@[ega "III 2.1.14" "more general"]
theorem finite_free_homology_derivedGlobalSectionsOver_twist (e q : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((derivedGlobalSectionsOver (proj (A := A) n)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) e)))) ∧
      Module.Free A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((derivedGlobalSectionsOver (proj (A := A) n)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) e)))) := by
  rcases lt_or_ge q 0 with hq | hq
  · obtain ⟨e₁⟩ := nonempty_homology_derivedGlobalSectionsOver_single_iso (A := A) n
      (twistOver n (Spec (.of A)) e) q
    have := ModuleCat.isZero_iff_subsingleton.mp
      ((Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ q hq _).of_iso e₁)
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton A _⟩
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    obtain ⟨e₁⟩ := nonempty_homology_derivedGlobalSectionsOver_twist_iso (A := A) n e k
    obtain ⟨h1, h2⟩ := finite_free_twistCohomology n Γ(Spec (.of A), ⊤) e k
    obtain ⟨h3, h4⟩ := StacksDraft.PseudoCoherence.restrictScalars_finiteFree
      (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
      (twistCohomology Γ(Spec (.of A), ⊤) n e k)
    exact ⟨Module.Finite.equiv e₁.symm.toLinearEquiv, Module.Free.of_equiv e₁.symm.toLinearEquiv⟩

/-- `H^q(RΓ_A(𝒪(e)[0]))` vanishes outside the degrees `0` and `n` of [Stacks, Tag 01XT]:
in every degree other than `0` when `e ≥ 0`, and in every degree other than `n` when `e < 0`. -/
theorem isZero_homology_derivedGlobalSectionsOver_twist_of_ne (e q : ℤ)
    (hq : ¬ ((q = 0 ∧ 0 ≤ e) ∨ (q = n ∧ e < 0))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((derivedGlobalSectionsOver (proj (A := A) n)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) e)))) := by
  rcases lt_or_ge q 0 with hq' | hq'
  · obtain ⟨e₁⟩ := nonempty_homology_derivedGlobalSectionsOver_single_iso (A := A) n
      (twistOver n (Spec (.of A)) e) q
    exact (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ q hq' _).of_iso e₁
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hq'
    obtain ⟨e₁⟩ := nonempty_homology_derivedGlobalSectionsOver_twist_iso (A := A) n e k
    have := ModuleCat.isZero_iff_subsingleton.mp
      ((twistCohomologyMonomial Γ(Spec (.of A), ⊤) n e).vanishing k (by
        rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp_all))
    have : Subsingleton ((ModuleCat.restrictScalars
        (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.toRingHom).obj
        (twistCohomology Γ(Spec (.of A), ⊤) n e k)) := this
    exact (ModuleCat.isZero_of_subsingleton _).of_iso e₁

/-- **An object of `D(A)` with cohomology concentrated in one degree, where it is finite free,
is pseudo-coherent.** -/
theorem isPseudoCoherent_of_homology_concentrated (K : DerivedCategory (ModuleCat.{u} A)) (q₀ : ℤ)
    (hz : ∀ q, q ≠ q₀ → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj K))
    (hf : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q₀).obj K))
    (hfr : Module.Free A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q₀).obj K)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
  have : K.IsGE q₀ := by
    rw [DerivedCategory.isGE_iff]
    exact fun q hq => hz q (by omega)
  have : K.IsLE q₀ := by
    rw [DerivedCategory.isLE_iff]
    exact fun q hq => hz q (by omega)
  obtain ⟨Y, ⟨eY⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE q₀
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q₀).obj K ≅ Y :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q₀).mapIso eY ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) q₀).app Y
  have : Module.Finite A Y := Module.Finite.equiv eH.toLinearEquiv
  have : Module.Free A Y := Module.Free.of_equiv eH.toLinearEquiv
  exact StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 fun m =>
      StacksDraft.PseudoCoherence.isPseudoCoherentFrom_single Y q₀ m
        ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1
          (StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free (R := A) Y)
          (m - q₀))) eY.symm

/-- **[G1] `RΓ_A(𝒪(e)[0])` is a pseudo-coherent object of `D(A)`**, for every integer `e`: by
[Stacks, Tag 01XT] its cohomology is a finite free `A`-module concentrated in degree `0` (if
`e ≥ 0`) or in degree `n` (if `e < 0`). -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_twist (e : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (proj (A := A) n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) e))) := by
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℤ, ∀ q, q ≠ q₀ → ¬ ((q = 0 ∧ 0 ≤ e) ∨ (q = n ∧ e < 0)) := by
    rcases le_or_gt 0 e with he | he
    · exact ⟨0, fun q hq h => by rcases h with ⟨h, -⟩ | ⟨-, h⟩ <;> omega⟩
    · exact ⟨n, fun q hq h => by rcases h with ⟨-, h⟩ | ⟨h, -⟩ <;> omega⟩
  obtain ⟨hf, hfr⟩ := finite_free_homology_derivedGlobalSectionsOver_twist (A := A) n e q₀
  exact isPseudoCoherent_of_homology_concentrated _ q₀
    (fun q hq => isZero_homology_derivedGlobalSectionsOver_twist_of_ne (A := A) n e q (hq₀ q hq))
    hf hfr

/-- **[G1] For `e ≥ -n` the object `RΓ_A(𝒪(e)[0])` has no cohomology outside degree `0`**: the
degree-`n` cohomology of a twist `-n ≤ e < 0` is free on the degree-`e` Laurent monomials with
every exponent negative, of which there are none. -/
theorem isZero_homology_derivedGlobalSectionsOver_twist (e : ℤ) (he : -(n : ℤ) ≤ e) (q : ℤ)
    (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((derivedGlobalSectionsOver (proj (A := A) n)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (.of A)) e)))) := by
  by_cases hqn : q = n ∧ e < 0
  · obtain ⟨rfl, hneg⟩ := hqn
    obtain ⟨e₁⟩ := nonempty_homology_derivedGlobalSectionsOver_twist_iso (A := A) n e n
    have : Subsingleton (negativeTwistPart Γ(Spec (.of A), ⊤) n e) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx := x.2
      have hy := y.2
      change _ ∈ Finsupp.supported _ _ _ at hx hy
      rw [(Stacks.ProjectiveSpace.Cohomology.negativeLaurentMonomials_eq_empty_iff n e).2 he,
        Finsupp.supported_empty, Submodule.mem_bot] at hx hy
      rw [hx, hy]
    have : Subsingleton ((ModuleCat.restrictScalars
        (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.toRingHom).obj
        (twistCohomology Γ(Spec (.of A), ⊤) n e n)) :=
      Equiv.subsingleton
        ((twistCohomologyMonomial Γ(Spec (.of A), ⊤) n e).degreeTop hneg).toLinearEquiv.toEquiv
    exact (ModuleCat.isZero_of_subsingleton _).of_iso e₁
  · exact isZero_homology_derivedGlobalSectionsOver_twist_of_ne (A := A) n e q (by tauto)

end AlgebraicGeometry.ProjectiveSpaceDirectImage

end
