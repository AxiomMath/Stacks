module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartComparison
public import StacksFrontier.AlgebraicGeometry.RestrictPushforwardCoherence
public import StacksFrontier.Homology.TwoTermComplex.DeterminantIsoBaseChange
public import StacksFrontier.Homology.TwoTermComplex.DeterminantObjectBaseChangeComp

/-!
# The chart comparison of the determinant, over the rings, is transitive

Let `X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and
`V ≤ V' ≤ W` affine opens of `X`. The chart comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` identifies the base change along the
restriction of functions `Γ(X, W) → Γ(X, V)` of the determinant of `L` on the chart of `W` with
the determinant of `L` on the chart of `V`. Over the rings, the comparison for `V ≤ W` is the
one for `V' ≤ W` followed by the one for `V ≤ V'`.

## Main definitions

* `TwoTermDeterminant.presentationBaseChangeCompIso`: the two-step base change of a presenting
  complex is its one-step base change, degreewise the cancellation `B ⊗_A (A ⊗_R N) ≅ B ⊗_R N`.
* `TwoTermDeterminant.baseChangeCompIsoOf`: the composition isomorphism of the base changes of a
  perfect two-term object, along a third ring homomorphism equal to the composite of the two.
* `TwoTermDeterminant.detBaseChangeIso`: the flat base change of the determinant of a perfect
  two-term object, followed by the determinant of an identification of a second object with that
  base change.

## Main results

* `TwoTermDeterminant.degreeEquivOfIso_presentationBaseChangeCompIso`: in each degree the
  comparison of the two base changes of a presenting complex is the cancellation
  `B ⊗_A (A ⊗_R P^i) ≅ B ⊗_R P^i`.
* `TwoTermDeterminant.baseChangeCompIso_hom_comp_iso` and
  `TwoTermDeterminant.presentationTransport_baseChangeCompIso`: the composition isomorphism of
  the base changes is realised on a two-term presentation by the degreewise cancellation, and the
  transport of determinant lines along it is conjugation by the determinants of the
  cancellations.
* `TwoTermDeterminant.detIsoEquiv_baseChangeCompIso_detBaseChange`: flat base change of the
  determinant of a perfect two-term object is transitive: base changing a section of `det_R(K)`
  to `A` and then to `B`, read through the composition isomorphism of the base changes, is base
  changing it to `B` in one step.
* `TwoTermDeterminant.detBaseChangeIso_trans`: the chart comparison over the rings is transitive,
  for any three identifications of the objects that satisfy the cocycle condition along the
  composition isomorphism of the base changes.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_eq`: the chart comparison
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` is `TwoTermDeterminant.detBaseChangeIso`
  at the restriction of functions and at
  `AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct
open TensorProduct.AlgebraTensorModule (cancelBaseChange)

universe u

namespace TwoTermDeterminant

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] {B : Type u} [CommRing B]

/-! ### The base change of a presenting complex composes -/

section Presentation

variable (φ : R →+* A) (ψ : A →+* B) {M : DerivedCategory (ModuleCat.{u} R)}

/-- **The two-step base change of a presenting complex is its one-step base change.** Degreewise
this is the scalar-tower comparison `ModuleCat.extendScalarsComp`, that is the cancellation
`B ⊗_A (A ⊗_R N) ≅ B ⊗_R N`. -/
def presentationBaseChangeCompIso (P : TwoTermPresentation M) :
    ((P.baseChange φ).baseChange ψ).complex ≅ (P.baseChange (ψ.comp φ)).complex :=
  ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} φ ψ)
    (ComplexShape.up ℤ)).app P.complex).symm

/-- The inverse of `TwoTermDeterminant.presentationBaseChangeCompIso` in degree `i` is the
scalar-tower comparison of `ModuleCat.extendScalarsComp` at the term of degree `i`. -/
theorem presentationBaseChangeCompIso_symm_degreeEquiv (P : TwoTermPresentation M) (i : ℤ)
    (t : (P.baseChange (ψ.comp φ)).complex.X i) :
    (degreeEquivOfIso (presentationBaseChangeCompIso φ ψ P) i).symm t =
      (ModuleCat.extendScalarsComp.{u, u} φ ψ).hom.app (P.complex.X i) t :=
  rfl

/-- **In each degree the two base changes of a presenting complex are identified by the
cancellation.** The component of `TwoTermDeterminant.presentationBaseChangeCompIso` in degree `i`
is `B ⊗_A (A ⊗_R P^i) ≅ B ⊗_R P^i`. -/
theorem degreeEquivOfIso_presentationBaseChangeCompIso (P : TwoTermPresentation M) (i : ℤ) :
    letI : Algebra R A := φ.toAlgebra
    letI : Algebra A B := ψ.toAlgebra
    letI : Algebra R B := (ψ.comp φ).toAlgebra
    haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    degreeEquivOfIso (presentationBaseChangeCompIso φ ψ P) i =
      cancelBaseChange R A B B (P.complex.X i : Type u) := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra A B := ψ.toAlgebra
  let : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine LinearEquiv.symm_bijective.injective (LinearEquiv.ext fun t ↦ ?_)
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add t₁ t₂ ht₁ ht₂ =>
      have hsum : (degreeEquivOfIso (presentationBaseChangeCompIso φ ψ P) i).symm t₁ +
            (degreeEquivOfIso (presentationBaseChangeCompIso φ ψ P) i).symm t₂ =
          (cancelBaseChange R A B B (P.complex.X i : Type u)).symm t₁ +
            (cancelBaseChange R A B B (P.complex.X i : Type u)).symm t₂ :=
        congr (congrArg (fun x ↦ HAdd.hAdd x) ht₁) ht₂
      exact (map_add _ t₁ t₂).trans (hsum.trans (map_add _ t₁ t₂).symm)
  | tmul b m =>
      have h1 := congrArg
        (fun z ↦ (degreeEquivOfIso (presentationBaseChangeCompIso φ ψ P) i).symm z)
        (TensorProduct.tmul_eq_smul_one_tmul b m)
      have h2 : (degreeEquivOfIso (presentationBaseChangeCompIso φ ψ P) i).symm
            (b • ((1 : B) ⊗ₜ[R] m)) =
          b • (degreeEquivOfIso (presentationBaseChangeCompIso φ ψ P) i).symm
            ((1 : B) ⊗ₜ[R] m) := map_smul _ b _
      have h3 := congrArg (fun z ↦ b • z)
        (ModuleCat.extendScalarsComp_hom_app_one_tmul φ ψ (P.complex.X i) m)
      have h4 := (TensorProduct.tmul_eq_smul_one_tmul (R := A) b ((1 : A) ⊗ₜ[R] m)).symm
      have h5 := (TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R A B b m).symm
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- The identification of the base change of a two-term presentation with its presenting complex
is the derived extension of scalars of the original identification, followed by the comparison
with degreewise extension of scalars. -/
theorem baseChange_iso_hom (P : TwoTermPresentation M) :
    (P.baseChange φ).iso.hom =
      (totalDerivedExtensionScalars.{u, u, u} φ).functor.map P.iso.hom ≫
        (totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P.complex :=
  rfl

/-- **The composition isomorphism of the base changes of a perfect two-term object is realised on
a two-term presentation by the degreewise cancellation.** -/
theorem baseChangeCompIso_hom_comp_iso (K : PerfectTwoTermComplex R)
    (P : TwoTermPresentation K.obj) :
    (PerfectTwoTermComplex.baseChangeCompIso φ ψ K).hom ≫
        (P.baseChange (ψ.comp φ)).iso.hom =
      ((P.baseChange φ).baseChange ψ).iso.hom ≫
        DerivedCategory.Q.map (presentationBaseChangeCompIso φ ψ P).hom := by
  have hnat :
      (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map P.iso.hom) ≫
          (totalDerivedExtensionScalarsComp.{u, u} φ ψ).hom.app
            (DerivedCategory.Q.obj P.complex) =
        (totalDerivedExtensionScalarsComp.{u, u} φ ψ).hom.app K.obj ≫
          (totalDerivedExtensionScalars.{u, u, u} (ψ.comp φ)).functor.map P.iso.hom :=
    (totalDerivedExtensionScalarsComp.{u, u} φ ψ).hom.naturality P.iso.hom
  have hcomp :
      (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P.complex) ≫
          (totalDerivedExtensionScalars.{u, u, u} ψ).comparison.app (P.baseChange φ).complex ≫
          DerivedCategory.Q.map (presentationBaseChangeCompIso φ ψ P).hom =
        (totalDerivedExtensionScalarsComp.{u, u} φ ψ).hom.app
            (DerivedCategory.Q.obj P.complex) ≫
          (totalDerivedExtensionScalars.{u, u, u} (ψ.comp φ)).comparison.app P.complex :=
    totalDerivedExtensionScalarsComp_comparison.{u, u} φ ψ P.complex
  have hsplit : ((P.baseChange φ).baseChange ψ).iso.hom =
      (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map P.iso.hom) ≫
          (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P.complex) ≫
          (totalDerivedExtensionScalars.{u, u, u} ψ).comparison.app
            (P.baseChange φ).complex :=
    Functor.map_comp_assoc _ _ _ _
  have main :
      (totalDerivedExtensionScalarsComp.{u, u} φ ψ).hom.app K.obj ≫
          ((totalDerivedExtensionScalars.{u, u, u} (ψ.comp φ)).functor.map P.iso.hom ≫
            (totalDerivedExtensionScalars.{u, u, u} (ψ.comp φ)).comparison.app P.complex) =
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map P.iso.hom) ≫
          (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P.complex) ≫
          (totalDerivedExtensionScalars.{u, u, u} ψ).comparison.app (P.baseChange φ).complex ≫
          DerivedCategory.Q.map (presentationBaseChangeCompIso φ ψ P).hom := by
    rw [hcomp]
    exact (((Category.assoc _ _ _).symm.trans
      (congrArg
        (fun z ↦ z ≫
          (totalDerivedExtensionScalars.{u, u, u} (ψ.comp φ)).comparison.app P.complex)
        hnat)).trans (Category.assoc _ _ _)).symm
  have hassoc :
      ((totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map P.iso.hom) ≫
          ((totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
              ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P.complex) ≫
            (totalDerivedExtensionScalars.{u, u, u} ψ).comparison.app
              (P.baseChange φ).complex)) ≫
          DerivedCategory.Q.map (presentationBaseChangeCompIso φ ψ P).hom =
        (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map P.iso.hom) ≫
          (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
            ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P.complex) ≫
          (totalDerivedExtensionScalars.{u, u, u} ψ).comparison.app (P.baseChange φ).complex ≫
          DerivedCategory.Q.map (presentationBaseChangeCompIso φ ψ P).hom :=
    (Category.assoc _ _ _).trans
      (congrArg
        (fun z ↦ (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map P.iso.hom) ≫ z)
        (Category.assoc _ _ _))
  exact main.trans (hassoc.symm.trans
    (congrArg
      (fun z ↦ z ≫ DerivedCategory.Q.map (presentationBaseChangeCompIso φ ψ P).hom)
      hsplit).symm)

/-- **The transport of determinant lines along the composition isomorphism of the base changes is
conjugation by the determinants of the degreewise cancellations
`B ⊗_A (A ⊗_R P^i) ≅ B ⊗_R P^i`.** -/
theorem presentationTransport_baseChangeCompIso (K : PerfectTwoTermComplex R)
    (P : TwoTermPresentation K.obj) :
    letI : Algebra R A := φ.toAlgebra
    letI : Algebra A B := ψ.toAlgebra
    letI : Algebra R B := (ψ.comp φ).toAlgebra
    haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    presentationTransport ((P.baseChange φ).baseChange ψ) (P.baseChange (ψ.comp φ))
        (PerfectTwoTermComplex.baseChangeCompIso φ ψ K) =
      LinearEquiv.arrowCongr
        (ProjectiveDeterminant.mapEquiv (cancelBaseChange R A B B (P.complex.X (-1) : Type u)))
        (ProjectiveDeterminant.mapEquiv
          (cancelBaseChange R A B B (P.complex.X 0 : Type u))) := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra A B := ψ.toAlgebra
  let : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  have hiso : ((P.baseChange φ).baseChange ψ).iso.symm ≪≫
      PerfectTwoTermComplex.baseChangeCompIso φ ψ K ≪≫ (P.baseChange (ψ.comp φ)).iso =
      DerivedCategory.Q.mapIso (presentationBaseChangeCompIso φ ψ P) :=
    Iso.ext ((Iso.inv_comp_eq _).mpr (baseChangeCompIso_hom_comp_iso φ ψ K P))
  refine (congrArg (fun a ↦ determinantTransport ((P.baseChange φ).baseChange ψ)
    (P.baseChange (ψ.comp φ)) a) hiso).trans ?_
  refine (determinantTransport_Q_mapIso ((P.baseChange φ).baseChange ψ)
    (P.baseChange (ψ.comp φ)) (presentationBaseChangeCompIso φ ψ P)).trans ?_
  rw [degreeEquivOfIso_presentationBaseChangeCompIso,
    degreeEquivOfIso_presentationBaseChangeCompIso]
  rfl

end Presentation

/-! ### Flat base change of the determinant is transitive -/

section Transitive

variable (φ : R →+* A) (ψ : A →+* B)

/-- **Transport undoes conjugation.** Carrying a linear map along two linear equivalences in the
source and the target, and then transporting the result back along the same two equivalences,
returns the map. -/
theorem arrowCongr_conj {S : Type*} [CommSemiring S] {N₁ N₂ N₁' N₂' : Type*}
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₁'] [AddCommMonoid N₂']
    [Module S N₁] [Module S N₂] [Module S N₁'] [Module S N₂']
    (e₁ : N₁ ≃ₗ[S] N₁') (e₂ : N₂ ≃ₗ[S] N₂') (f : N₁' →ₗ[S] N₂') :
    LinearEquiv.arrowCongr e₁ e₂ (e₂.symm.toLinearMap ∘ₗ f ∘ₗ e₁.toLinearMap) = f := by
  ext y
  simp only [LinearEquiv.arrowCongr_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- **Flat base change of the determinant of a perfect two-term object is transitive.** Let
`R → A → B` be a tower of flat ring homomorphisms and `K` a perfect object of `D(R)` of
Tor-amplitude in `[-1, 0]`. Base changing a section of `det_R(K)` to `A` and then to `B`, read
through the composition isomorphism of the base changes, is base changing it to `B` in one step.
-/
theorem detIsoEquiv_baseChangeCompIso_detBaseChange
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (hψ : letI : Algebra A B := ψ.toAlgebra; Module.Flat A B)
    (hφψ : letI : Algebra R B := (ψ.comp φ).toAlgebra; Module.Flat R B)
    (K : PerfectTwoTermComplex R) (x : ((det R).obj ⟨K⟩).of.obj) :
    letI : Algebra R A := φ.toAlgebra
    letI : Algebra A B := ψ.toAlgebra
    letI : Algebra R B := (ψ.comp φ).toAlgebra
    haveI : Module.Flat R A := hφ
    haveI : Module.Flat A B := hψ
    haveI : Module.Flat R B := hφψ
    detIsoEquiv (PerfectTwoTermComplex.baseChangeCompIso φ ψ K)
        (detBaseChange ψ hψ (PerfectTwoTermComplex.baseChange φ K)
          ((1 : B) ⊗ₜ[A] detBaseChange φ hφ K ((1 : A) ⊗ₜ[R] x))) =
      detBaseChange (ψ.comp φ) hφψ K ((1 : B) ⊗ₜ[R] x) := by
  let : Algebra R A := φ.toAlgebra
  let : Algebra A B := ψ.toAlgebra
  let : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat R A := hφ
  have : Module.Flat A B := hψ
  have : Module.Flat R B := hφψ
  have hcoc := detPresentationIso_detBaseChange_comp φ ψ hφ hψ hφψ K (presentation R K) x
  have hT := presentationTransport_baseChangeCompIso φ ψ K (presentation R K)
  have hsplit := (presentationTransport_comp
      (presentation B (PerfectTwoTermComplex.baseChange ψ
        (PerfectTwoTermComplex.baseChange φ K)))
      (((presentation R K).baseChange φ).baseChange ψ)
      ((presentation R K).baseChange (ψ.comp φ)) (Iso.refl _)
      (PerfectTwoTermComplex.baseChangeCompIso φ ψ K)).trans
    (congrArg (fun c ↦ presentationTransport
      (presentation B (PerfectTwoTermComplex.baseChange ψ
        (PerfectTwoTermComplex.baseChange φ K)))
      ((presentation R K).baseChange (ψ.comp φ)) c)
      (Iso.refl_trans (PerfectTwoTermComplex.baseChangeCompIso φ ψ K)))
  have hmerge := (presentationTransport_comp
      (presentation B (PerfectTwoTermComplex.baseChange ψ
        (PerfectTwoTermComplex.baseChange φ K)))
      (presentation B (PerfectTwoTermComplex.baseChange (ψ.comp φ) K))
      ((presentation R K).baseChange (ψ.comp φ))
      (PerfectTwoTermComplex.baseChangeCompIso φ ψ K) (Iso.refl _)).trans
    (congrArg (fun c ↦ presentationTransport
      (presentation B (PerfectTwoTermComplex.baseChange ψ
        (PerfectTwoTermComplex.baseChange φ K)))
      ((presentation R K).baseChange (ψ.comp φ)) c)
      (Iso.trans_refl (PerfectTwoTermComplex.baseChangeCompIso φ ψ K)))
  refine (detPresentationIso (PerfectTwoTermComplex.baseChange (ψ.comp φ) K)
    ((presentation R K).baseChange (ψ.comp φ))).injective ?_
  have hL : detPresentationIso (PerfectTwoTermComplex.baseChange (ψ.comp φ) K)
        ((presentation R K).baseChange (ψ.comp φ))
        (detIsoEquiv (PerfectTwoTermComplex.baseChangeCompIso φ ψ K)
          (detBaseChange ψ hψ (PerfectTwoTermComplex.baseChange φ K)
            ((1 : B) ⊗ₜ[A] detBaseChange φ hφ K ((1 : A) ⊗ₜ[R] x)))) =
      presentationTransport (((presentation R K).baseChange φ).baseChange ψ)
        ((presentation R K).baseChange (ψ.comp φ))
        (PerfectTwoTermComplex.baseChangeCompIso φ ψ K)
        (detPresentationIso (PerfectTwoTermComplex.baseChange ψ
            (PerfectTwoTermComplex.baseChange φ K))
          (((presentation R K).baseChange φ).baseChange ψ)
          (detBaseChange ψ hψ (PerfectTwoTermComplex.baseChange φ K)
            ((1 : B) ⊗ₜ[A] detBaseChange φ hφ K ((1 : A) ⊗ₜ[R] x)))) := by
    refine (congrArg (fun z ↦ detPresentationIso
      (PerfectTwoTermComplex.baseChange (ψ.comp φ) K)
      ((presentation R K).baseChange (ψ.comp φ)) z)
      (DFunLike.congr_fun
        (detIsoEquiv_eq (PerfectTwoTermComplex.baseChangeCompIso φ ψ K)) _)).trans ?_
    exact (DFunLike.congr_fun hmerge _).trans (DFunLike.congr_fun hsplit _).symm
  rw [hL, hcoc, hT]
  exact arrowCongr_conj _ _ _

end Transitive

/-! ### The shape of the chart comparison over the rings -/

section Shape

/-- **The composition isomorphism of the base changes of a perfect two-term object, along a third
ring homomorphism equal to the composite of the two.** -/
def baseChangeCompIsoOf (φ : R →+* A) (ψ : A →+* B) (χ : R →+* B) (hχ : ψ.comp φ = χ)
    (K : PerfectTwoTermComplex R) :
    (PerfectTwoTermComplex.baseChange ψ (PerfectTwoTermComplex.baseChange φ K)).obj ≅
      (PerfectTwoTermComplex.baseChange χ K).obj := by
  subst hχ
  exact PerfectTwoTermComplex.baseChangeCompIso φ ψ K

/-- At the composite itself, `TwoTermDeterminant.baseChangeCompIsoOf` is
`TwoTermDeterminant.PerfectTwoTermComplex.baseChangeCompIso`. -/
theorem baseChangeCompIsoOf_self (φ : R →+* A) (ψ : A →+* B) (K : PerfectTwoTermComplex R) :
    baseChangeCompIsoOf φ ψ (ψ.comp φ) rfl K = PerfectTwoTermComplex.baseChangeCompIso φ ψ K :=
  rfl

/-- **The shape of the chart comparison of determinants over the rings.** For a flat
`φ : R →+* A`, a perfect object `K` of `D(R)` of Tor-amplitude in `[-1, 0]`, a perfect object
`K'` of `D(A)` of Tor-amplitude in `[-1, 0]` and an identification of `K'` with the derived
extension of scalars of `K`, this is the base change `A ⊗_R det_R(K) ≅ det_A(A ⊗^L_R K)` of
`TwoTermDeterminant.detBaseChange` followed by the determinant of that identification. -/
def detBaseChangeIso (φ : R →+* A)
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (K : PerfectTwoTermComplex R) (K' : PerfectTwoTermComplex A)
    (e : K'.obj ≅ (PerfectTwoTermComplex.baseChange φ K).obj) :
    letI : Algebra R A := φ.toAlgebra
    A ⊗[R] ((det R).obj ⟨K⟩).of.obj ≃ₗ[A] ((det A).obj ⟨K'⟩).of.obj :=
  letI : Algebra R A := φ.toAlgebra
  haveI : Module.Flat R A := hφ
  detBaseChange φ hφ K ≪≫ₗ detIsoEquiv e.symm

/-- The chart comparison over the rings, on an element `1 ⊗ₜ x`. -/
theorem detBaseChangeIso_one_tmul (φ : R →+* A)
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (K : PerfectTwoTermComplex R) (K' : PerfectTwoTermComplex A)
    (e : K'.obj ≅ (PerfectTwoTermComplex.baseChange φ K).obj)
    (x : ((det R).obj ⟨K⟩).of.obj) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    detBaseChangeIso φ hφ K K' e ((1 : A) ⊗ₜ[R] x) =
      detIsoEquiv e.symm (detBaseChange φ hφ K ((1 : A) ⊗ₜ[R] x)) :=
  rfl

/-- **The chart comparison of determinants over the rings is transitive.** Let `R → A → B` be a
tower of flat ring homomorphisms, with a third homomorphism `χ` equal to the composite, let `K`,
`K'` and `K''` be perfect objects of Tor-amplitude in `[-1, 0]` over `R`, `A` and `B`, and let
`e'`, `e` and `e''` identify `K'` with the base change of `K`, `K''` with the base change of `K'`
and `K''` with the base change of `K` along `χ`, compatibly with the composition isomorphism of
the base changes. Then the comparison of `TwoTermDeterminant.detBaseChangeIso` for `χ` is the one
for `φ` followed by the one for `ψ`, read through the cancellation
`B ⊗_A (A ⊗_R det_R(K)) ≅ B ⊗_R det_R(K)`. -/
theorem detBaseChangeIso_trans (φ : R →+* A) (ψ : A →+* B) (χ : R →+* B) (hχ : ψ.comp φ = χ)
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (hψ : letI : Algebra A B := ψ.toAlgebra; Module.Flat A B)
    (hχf : letI : Algebra R B := χ.toAlgebra; Module.Flat R B)
    (K : PerfectTwoTermComplex R) (K' : PerfectTwoTermComplex A)
    (K'' : PerfectTwoTermComplex B)
    (e' : K'.obj ≅ (PerfectTwoTermComplex.baseChange φ K).obj)
    (e : K''.obj ≅ (PerfectTwoTermComplex.baseChange ψ K').obj)
    (e'' : K''.obj ≅ (PerfectTwoTermComplex.baseChange χ K).obj)
    (hcocycle : e''.hom =
      e.hom ≫ (PerfectTwoTermComplex.baseChangeIso ψ e').hom ≫
        (baseChangeCompIsoOf φ ψ χ hχ K).hom) :
    letI : Algebra R A := φ.toAlgebra
    letI : Algebra A B := ψ.toAlgebra
    letI : Algebra R B := χ.toAlgebra
    haveI : IsScalarTower R A B :=
      IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hχ r).symm
    haveI : Module.Flat R A := hφ
    haveI : Module.Flat A B := hψ
    haveI : Module.Flat R B := hχf
    (detBaseChangeIso ψ hψ K' K'' e).toLinearMap ∘ₗ
        LinearMap.baseChange B (detBaseChangeIso φ hφ K K' e').toLinearMap ∘ₗ
        (cancelBaseChange R A B B (((det R).obj ⟨K⟩).of.obj)).symm.toLinearMap =
      (detBaseChangeIso χ hχf K K'' e'').toLinearMap := by
  subst hχ
  let : Algebra R A := φ.toAlgebra
  let : Algebra A B := ψ.toAlgebra
  let : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat R A := hφ
  have : Module.Flat A B := hψ
  have : Module.Flat R B := hχf
  have hc : e''.hom =
      e.hom ≫ (PerfectTwoTermComplex.baseChangeIso ψ e').hom ≫
        (PerfectTwoTermComplex.baseChangeCompIso φ ψ K).hom := hcocycle
  have hinv : (PerfectTwoTermComplex.baseChangeIso ψ e'.symm).hom =
      (PerfectTwoTermComplex.baseChangeIso ψ e').inv := rfl
  have hkey : ((PerfectTwoTermComplex.baseChangeIso ψ e'.symm).hom ≫ e.inv) ≫ e''.hom =
      (PerfectTwoTermComplex.baseChangeCompIso φ ψ K).hom := by
    rw [hinv, hc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hbcc : PerfectTwoTermComplex.baseChangeIso ψ e'.symm ≪≫ e.symm =
      PerfectTwoTermComplex.baseChangeCompIso φ ψ K ≪≫ e''.symm :=
    Iso.ext ((Iso.eq_comp_inv e'').mpr hkey)
  refine LinearMap.ext fun t ↦ ?_
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul b x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul b x, map_smul, map_smul]
      refine congrArg (fun z ↦ b • z) ?_
      have hbase := LinearMap.congr_fun
        (detBaseChange_detIsoEquiv ψ hψ e'.symm)
        ((1 : B) ⊗ₜ[A] detBaseChange φ hφ K ((1 : A) ⊗ₜ[R] x))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul] at hbase
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        detBaseChangeIso_one_tmul, LinearMap.baseChange_tmul]
      rw [← hbase, ← LinearEquiv.trans_apply, ← detIsoEquiv_trans, hbcc, detIsoEquiv_trans,
        LinearEquiv.trans_apply, detIsoEquiv_baseChangeCompIso_detBaseChange]

end Shape

end TwoTermDeterminant

/-! ### The chart comparison over the rings -/

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- The two spellings of the determinant of an isomorphism of perfect two-term objects agree:
`AlgebraicGeometry.DeterminantTwoTerm.detLinearEquivOfIso` is
`TwoTermDeterminant.detIsoEquiv`. -/
theorem detLinearEquivOfIso_eq_detIsoEquiv {R : Type u} [CommRing R]
    {K K' : TwoTermDeterminant.PerfectTwoTermComplex R} (e : K.obj ≅ K'.obj) :
    detLinearEquivOfIso e = TwoTermDeterminant.detIsoEquiv e :=
  rfl

/-- Restriction of functions is transitive, read on the underlying ring homomorphisms: for affine
opens `V ≤ V' ≤ W` of `X` the composite of the restrictions attached to `V ≤ V'` and `V' ≤ W` is
the restriction attached to `V ≤ W`. -/
theorem affineRestriction_hom_comp {V V' W : X.affineOpens} (h : V ≤ V') (h' : V' ≤ W) :
    (affineRestriction X h).hom.comp (affineRestriction X h').hom =
      (affineRestriction X (h.trans h')).hom :=
  congrArg CommRingCat.Hom.hom
    (chartRestriction_comp (AffineOpensGlue.coe_le_coe h) (AffineOpensGlue.coe_le_coe h'))

/-- **The chart comparison of determinants over the rings is
`TwoTermDeterminant.detBaseChangeIso`** at the restriction of functions and at the identification
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso` of the chart complex of the
smaller chart with the derived extension of scalars of the chart complex of the larger one. -/
theorem chartDetModuleIso_eq (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W) :
    chartDetModuleIso L h =
      TwoTermDeterminant.detBaseChangeIso (affineRestriction X h).hom
        (V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h))
        (chartComplex L W) (chartComplex L V)
        (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) L) :=
  rfl

end AlgebraicGeometry.DeterminantTwoTerm

end
