module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Submodule
public import StacksFrontier.Homology.ExtendScalars.Localization
public import StacksFrontier.RingTheory.Flat.DerivedFlat.Basic

/-!
# Local and flat descent for flat modules in degree zero

Let `N ∈ D(R)`. Whether `N` is isomorphic to a flat module placed in degree zero can be tested
after derived base change to the localizations of `R` at its maximal ideals, and it descends
along a finite family of flat ring maps `R → C_j` that is jointly surjective on spectra. Along a
flat ring map derived base change is computed on cohomology, so both statements reduce to the
corresponding statements for modules: vanishing and flatness are local (Stacks 00HT), and they
descend along a faithfully flat ring map (Stacks 03C4).

## Main results

* `StacksDraft.DerivedFlat.isFlatInDegreeZero_of_forall_maximal`: the local criterion, and
  `StacksDraft.DerivedFlat.BaseChangeLE.of_forall_maximal` its analogue for the vanishing of
  positive cohomology.
* `StacksDraft.DerivedFlat.isFlatInDegreeZero_of_faithfullyFlat`: descent along a faithfully flat
  ring map.
* `StacksDraft.DerivedFlat.BaseChangeFlat.of_flat_family`: descent along a jointly surjective
  family of flat ring maps.
* `StacksDraft.DerivedFlat.exists_comap_includeLeft_eq`: a prime of `R'` and a prime of `B` over
  the same prime of `A` are both under a prime of `R' ⊗[A] B`.

## References

* [Stacks Project, Tag 00HT](https://stacks.math.columbia.edu/tag/00HT)
* [Stacks Project, Tag 03C4](https://stacks.math.columbia.edu/tag/03C4)
* [Stacks Project, Tag 01JT](https://stacks.math.columbia.edu/tag/01JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace StacksDraft.DerivedFlat

/-- Extension of scalars along the structure map of an algebra is the base change
`P ⊗[R] M`. -/
def extendScalarsObjTensorIso {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
    (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R P)).obj M ≅
      ModuleCat.of P (P ⊗[R] M) := by
  let X := (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P P)
  have : IsScalarTower R P X := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let e : X ≃ₗ[P] P := LinearEquiv.refl P P
  exact (AlgebraTensorModule.congr e (LinearEquiv.refl R M)).toModuleIso

/-- Along a flat ring map, the cohomology of a derived base change is the base change of the
cohomology. -/
def homologyBaseChangeIso {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
    [Module.Flat R P] (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} P) i).obj
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R P)).functor.obj K) ≅
      ModuleCat.of P (P ⊗[R] (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) :=
  derivedExtensionScalarsHomologyIso.{u, u, u} (algebraMap R P)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) K i ≪≫
    extendScalarsObjTensorIso _

/-- **Descent along a faithfully flat ring map.** -/
lemma isFlatInDegreeZero_of_faithfullyFlat {R P : Type u} [CommRing R] [CommRing P]
    [Algebra R P] [Module.FaithfullyFlat R P] (K : DerivedCategory (ModuleCat.{u} R))
    (h : IsFlatInDegreeZero ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R P)).functor.obj
      K)) : IsFlatInDegreeZero K := by
  rw [isFlatInDegreeZero_iff_homology] at h ⊢
  obtain ⟨hzero, hflat⟩ := h
  refine ⟨fun i hi => ?_, ?_⟩
  · have hP := (hzero i hi).of_iso (homologyBaseChangeIso K i).symm
    have : Subsingleton (P ⊗[R] (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) :=
      ModuleCat.subsingleton_of_isZero hP
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) :=
      (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right (R := R) (M := P)).1 this
    exact ModuleCat.isZero_of_subsingleton _
  · have : Module.Flat P (P ⊗[R] (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj K) :=
      Module.Flat.of_linearEquiv (homologyBaseChangeIso K 0).symm.toLinearEquiv
    exact Module.Flat.of_flat_tensorProduct R _ P

/-- **The local criterion.** An object of `D(R)` is a flat module in degree zero as soon as its
derived base change to the localization at every maximal ideal is. -/
lemma isFlatInDegreeZero_of_forall_maximal {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R))
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsFlatInDegreeZero
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R (Localization.AtPrime P))).functor.obj
        K)) : IsFlatInDegreeZero K := by
  rw [isFlatInDegreeZero_iff_homology]
  let H : ℤ → ModuleCat.{u} R := fun i =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K
  have hloc : ∀ (P : Ideal R) [P.IsMaximal] (i : ℤ),
      Nonempty ((Localization.AtPrime P ⊗[R] H i) ≃ₗ[Localization.AtPrime P]
        LocalizedModule P.primeCompl (H i)) := fun P _ i =>
    ⟨(IsLocalizedModule.isBaseChange P.primeCompl (Localization.AtPrime P)
      (LocalizedModule.mkLinearMap P.primeCompl (H i))).equiv⟩
  refine ⟨fun i hi => ?_, ?_⟩
  · have : Subsingleton (H i) := by
      refine Module.subsingleton_of_localization_maximal
        (fun (P : Ideal R) [P.IsMaximal] => LocalizedModule P.primeCompl (H i))
        (fun (P : Ideal R) [P.IsMaximal] => LocalizedModule.mkLinearMap P.primeCompl (H i))
        fun P _ => ?_
      have h0 := (((isFlatInDegreeZero_iff_homology _).1 (h P)).1 i hi).of_iso
        (homologyBaseChangeIso K i).symm
      have : Subsingleton (Localization.AtPrime P ⊗[R] H i) :=
        ModuleCat.subsingleton_of_isZero h0
      obtain ⟨e⟩ := hloc P i
      exact e.symm.toEquiv.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · refine Module.flat_of_localized_maximal _ fun P _ => ?_
    have h0 := ((isFlatInDegreeZero_iff_homology _).1 (h P)).2
    have : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] H 0) :=
      Module.Flat.of_linearEquiv (homologyBaseChangeIso K 0).symm.toLinearEquiv
    obtain ⟨e⟩ := hloc P 0
    have : Module.Flat (Localization.AtPrime P) (LocalizedModule P.primeCompl (H 0)) :=
      Module.Flat.of_linearEquiv e.symm
    exact Module.Flat.trans R (Localization.AtPrime P) _

variable {A : Type u} [CommRing A] {N : DerivedCategory (ModuleCat.{u} A)}

/-- The local criterion for a derived base change. -/
lemma BaseChangeFlat.of_forall_maximal {R : Type u} [CommRing R] (φ : A →+* R)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      BaseChangeFlat N ((algebraMap R (Localization.AtPrime P)).comp φ)) :
    BaseChangeFlat N φ :=
  isFlatInDegreeZero_of_forall_maximal _ fun P _ =>
    (h P).of_iso ((totalDerivedExtensionScalarsComp.{u, u} φ _).app N).symm

/-- The local criterion for the vanishing of positive cohomology of a derived base change. -/
lemma BaseChangeLE.of_forall_maximal {R : Type u} [CommRing R] (φ : A →+* R)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      BaseChangeLE N ((algebraMap R (Localization.AtPrime P)).comp φ)) :
    BaseChangeLE N φ := by
  intro i hi
  let K := (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj N
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K
  have : Subsingleton H := by
    refine Module.subsingleton_of_localization_maximal
      (fun (P : Ideal R) [P.IsMaximal] => LocalizedModule P.primeCompl H)
      (fun (P : Ideal R) [P.IsMaximal] => LocalizedModule.mkLinearMap P.primeCompl H)
      fun P _ => ?_
    have h0 := ((h P i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      ((totalDerivedExtensionScalarsComp.{u, u} φ _).app N))).of_iso
        (homologyBaseChangeIso (P := Localization.AtPrime P) K i).symm
    have : Subsingleton (Localization.AtPrime P ⊗[R] H) := ModuleCat.subsingleton_of_isZero h0
    exact ((IsLocalizedModule.isBaseChange P.primeCompl (Localization.AtPrime P)
      (LocalizedModule.mkLinearMap P.primeCompl H)).equiv).symm.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- Descent along a faithfully flat ring map, for a derived base change. -/
lemma BaseChangeFlat.of_faithfullyFlat {R P : Type u} [CommRing R] [CommRing P] [Algebra R P]
    [Module.FaithfullyFlat R P] (φ : A →+* R)
    (h : BaseChangeFlat N ((algebraMap R P).comp φ)) : BaseChangeFlat N φ :=
  isFlatInDegreeZero_of_faithfullyFlat _
    (h.of_iso ((totalDerivedExtensionScalarsComp.{u, u} φ _).app N).symm)

/-- **Descent along a jointly surjective family of flat ring maps.** -/
lemma BaseChangeFlat.of_flat_family {R : Type u} [CommRing R] (φ : A →+* R) {ι : Type*}
    (C : ι → Type u) [∀ j, CommRing (C j)] [∀ j, Algebra R (C j)] [∀ j, Module.Flat R (C j)]
    (hsurj : ∀ P : PrimeSpectrum R, ∃ j,
      P ∈ Set.range (PrimeSpectrum.comap (algebraMap R (C j))))
    (h : ∀ j, BaseChangeFlat N ((algebraMap R (C j)).comp φ)) : BaseChangeFlat N φ := by
  refine BaseChangeFlat.of_forall_maximal φ fun P _ => ?_
  obtain ⟨j, Q, hQ⟩ := hsurj ⟨P, inferInstance⟩
  have hlies : Q.asIdeal.LiesOver P := ⟨congrArg PrimeSpectrum.asIdeal hQ.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver P Q.asIdeal
  have : Module.Flat R (Localization.AtPrime Q.asIdeal) := inferInstance
  have : Module.Flat (Localization.AtPrime P) (Localization.AtPrime Q.asIdeal) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl _).2 this
  have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q.asIdeal)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : Module.FaithfullyFlat (Localization.AtPrime P) (Localization.AtPrime Q.asIdeal) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine BaseChangeFlat.of_faithfullyFlat (P := Localization.AtPrime Q.asIdeal) _ ?_
  refine ((h j).comp (algebraMap (C j) (Localization.AtPrime Q.asIdeal))).of_eq ?_
  rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq]

/-- A prime of `R'` and a prime of `B` lying over the same prime of `A` both lie under some prime
of `R' ⊗[A] B` (Stacks 01JT, the points of a fibre product of affine schemes). -/
lemma exists_comap_includeLeft_eq {A R' B : Type u} [CommRing A] [CommRing R'] [CommRing B]
    [Algebra A R'] [Algebra A B] (P : PrimeSpectrum R') (q : PrimeSpectrum B)
    (h : P.comap (algebraMap A R') = q.comap (algebraMap A B)) :
    ∃ Q : PrimeSpectrum (R' ⊗[A] B), Q.comap (algebraMap R' (R' ⊗[A] B)) = P := by
  open AlgebraicGeometry in
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Spec.map (CommRingCat.ofHom (algebraMap A R')))
    (g := Spec.map (CommRingCat.ofHom (algebraMap A B))) P q h
  refine ⟨(pullbackSpecIso A R' B).hom z, ?_⟩
  have := congrArg (fun g : pullback (Spec.map (CommRingCat.ofHom (algebraMap A R')))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟶ Spec (CommRingCat.of R') => g z)
    (pullbackSpecIso_hom_fst' A R' B)
  simp only [Scheme.Hom.comp_apply] at this
  rw [← hz, ← this]
  rfl

end StacksDraft.DerivedFlat

end
