module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemarkSquare
public import StacksFrontier.AlgebraicGeometry.Constructions.CoherentMulSections
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Integer
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemarkPowCompare

/-!
# Assertion (ii) of Stacks Tag 01QK: the twist square, for every integer twist

In the situation of Stacks Tag 01QH — `X` a scheme, `𝓛` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, 𝓛)`, `Y = Proj S` and `f : X ⟶ Y` the canonical morphism — let `θ_𝓕 : f^*M̃ ⟶ 𝓕`,
`M = Γ_*(X, 𝓛, 𝓕)`, be the comparison of Stacks Tag 01QJ
(`Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison`). The second assertion of Stacks
Tag 01QK is that the square
```
f^*M̃ ⊗ f^*𝒪_Y(n) ⟶ f^*(M(n)~)
       |                  |
𝓕 ⊗ 𝓛^{⊗ n}      =     𝓕 ⊗ 𝓛^{⊗ n}
```
commutes, the top arrow being the pullback of the multiplication of Equation 01MQ and the right
arrow `θ_{𝓕 ⊗ 𝓛^{⊗ n}}` read through the obvious identification `M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})`.

For an integer `n`, write `n = e - k` with `e, k ≥ 0`. An isomorphism `β : L ^⊗ e ≅ N ⊙ k`
identifies `M(n)` with `Γ_*(X, 𝓛, 𝓕 ⊗ N)` and `S(n)` with `Γ_*(X, 𝓛, N)` (`twistIdent`,
`unitTwistIdent`); the square is proved for every such `β` (`twistSquareOf`), on fractions over the
basic opens `D₊(s)`, and specialized to `N = 𝓛^{⊗ n}` of Stacks Tag 01CU and `β = twistBeta`.

## Main definitions

* `Stacks.SectionRingProjTheta.twistPowIdent`: `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, 𝓛^{⊗ n}))~`.
* `Stacks.SectionRingProjTheta.twistModuleIdent`: `M(n)~ ≅ (Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n}))~`.
* `Stacks.SectionRingProjTheta.twistThetaInt`: `θ_{𝓛^{⊗ n}}`, read on `f^*𝒪_Y(n)`.

## Main results

* `Stacks.SectionRingProjTheta.twistSquareInt`: assertion (ii) of Tag 01QK.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.TwistedSections (twistPow twistSections twistModule moduleGrading)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingProjQuasicoherent (tildeFunctor pullbackTildeFunctor
  pullbackTildeComparison gluedComparison GoodChart localDivision unitSec powMul tildeModule)
open scoped TensorProduct
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeZeroFraction
  associatedModuleSheafStandardOpenEquiv)
open Stacks.GradedModule (shiftedGrading)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap)

universe u

namespace Stacks.SectionRingProjTheta

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)







/-! ### Raising the exponent of a fraction -/

section Raise

variable {S M : Type u} {σ τ : Type*} [CommRing S] [AddCommGroup M] [Module S M] [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮] [SetLike τ M] [AddSubgroupClass τ M]
  (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- **`m / fᵖ = fʳ m / f^{p + r}`.** -/
theorem degreeZeroFraction_raise {f : S} {d : ℕ} (hf : f ∈ 𝒮 d) (p r : ℕ) (m : M)
    (hm : m ∈ 𝒨 (p • (d : ℤ))) (hm' : f ^ r • m ∈ 𝒨 ((p + r) • (d : ℤ))) :
    degreeZeroFraction 𝒮 𝒨 hf p m hm = degreeZeroFraction 𝒮 𝒨 hf (p + r) (f ^ r • m) hm' := by
  apply Subtype.ext
  change LocalizedModule.mk (S := Submonoid.powers f) m ⟨f ^ p, ⟨p, rfl⟩⟩ =
    LocalizedModule.mk (S := Submonoid.powers f) (f ^ r • m) ⟨f ^ (p + r), ⟨p + r, rfl⟩⟩
  refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, pow_add]

end Raise

/-- **Every section of `(Γ_*(X, 𝓛, 𝓖))~` over `D₊(s)` is a fraction `t / sᵖ` with `p` as large as
we like.** -/
theorem exists_twistSection_fraction_ge (G : X.Modules) {d : ℕ} (s₀ : powSections L d)
    (hd : 0 < d) (p₀ : ℕ)
    (y : Γ((tildeFunctor L).obj G,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) :
    ∃ (p : ℕ) (_ : p₀ ≤ p) (t : twistSections G L (p * d))
      (h : DirectSum.of (twistSections G L) (p * d) t ∈ moduleGrading G L (p • (d : ℤ))),
      y = (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading G L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (moduleGrading G L)
            (Stacks.ExternalGrading.of_mem_summand d s₀) p _ h) := by
  have ey := exists_twistSection_fraction L G s₀ hd y
  obtain ⟨p, ey⟩ := ey
  obtain ⟨t, ey⟩ := ey
  obtain ⟨hm, hy⟩ := ey
  subst hy
  have hpow : DirectSum.of (powSections L) d s₀ ^ p₀ ∈ grading L (p₀ • d) :=
    SetLike.pow_mem_graded p₀ (Stacks.ExternalGrading.of_mem_summand d s₀)
  have hsm : DirectSum.of (powSections L) d s₀ ^ p₀ •
      DirectSum.of (twistSections G L) (p * d) t ∈ moduleGrading G L ((p₀ • d) +ᵥ (p • (d : ℤ))) :=
    SetLike.GradedSMul.smul_mem hpow hm
  have hidx : (p₀ • d) +ᵥ (p • (d : ℤ)) = (((p + p₀) * d : ℕ) : ℤ) := by
    change ((p₀ • d : ℕ) : ℤ) + p • (d : ℤ) = _
    rw [nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hsm' : DirectSum.of (powSections L) d s₀ ^ p₀ •
      DirectSum.of (twistSections G L) (p * d) t ∈ moduleGrading G L (((p + p₀) * d : ℕ) : ℤ) :=
    hidx ▸ hsm
  obtain ⟨t', ht'⟩ := hsm'
  have hidx' : (p + p₀) • (d : ℤ) = (((p + p₀) * d : ℕ) : ℤ) := by
    rw [nsmul_eq_mul]; push_cast; ring
  have hm' : DirectSum.of (twistSections G L) ((p + p₀) * d) t' ∈
      moduleGrading G L ((p + p₀) • (d : ℤ)) := hidx'.symm ▸ ⟨t', rfl⟩
  refine ⟨p + p₀, by omega, t', hm', ?_⟩
  refine congrArg (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading G L)
    (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm ?_
  refine (degreeZeroFraction_raise (grading L) (moduleGrading G L)
    (Stacks.ExternalGrading.of_mem_summand d s₀) p p₀ _ hm (ht' ▸ hm')).trans ?_
  exact Stacks.Veronese.degreeZeroFraction_congr (grading L) (moduleGrading G L)
    (Stacks.ExternalGrading.of_mem_summand d s₀) rfl ht'.symm _ _

/-- An isomorphism of modules on `Proj`, its inverse applied after it, on sections. -/
theorem iso_inv_app_hom_app {A B : (AlgebraicGeometry.Proj (grading L)).Modules} (ι : A ≅ B)
    (U : (AlgebraicGeometry.Proj (grading L)).Opens) (y : Γ(A, U)) :
    ι.inv.val.app (op U) (ι.hom.val.app (op U) y) = y :=
  congrArg (fun ψ : A ⟶ A => (ψ.val.app (op U)).hom y) ι.hom_inv_id

/-! ### The identifications on sections -/

section IdentApp

variable (F N : X.Modules) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
  (he : (e : ℤ) = n + k)

/-- On sections over `U`, the inverse of `unitTwistIdent` is the inverse of `identSheafRight`
followed by `unitSheafLeft`. -/
theorem unitTwistIdent_inv_app (U : (AlgebraicGeometry.Proj (grading L)).Opens)
    (y : ((tildeFunctor L).obj N).val.obj (op U)) :
    haveI := isIso_identSheafRight L N k
    (unitTwistIdent L N β he).inv.val.app (op U) y =
      (unitSheafLeft L N β he).val.app (op U) ((inv (identSheafRight L N k)).val.app (op U) y) :=
  rfl

/-- On sections over `U`, `twistIdent` is the inverse of `identSheafLeft` followed by
`identSheafRight`. -/
theorem twistIdent_hom_app (U : (AlgebraicGeometry.Proj (grading L)).Opens)
    (y : (shiftY L F n).val.obj (op U)) :
    haveI := isIso_identSheafLeft L F N β he
    (twistIdent L F N β he).hom.val.app (op U) y =
      (identSheafRight L (F ⊗ N) k).val.app (op U)
        ((inv (identSheafLeft L F N β he)).val.app (op U) y) :=
  rfl

end IdentApp

/-! ### The pieces of the computation on a standard open -/

section Pieces

open Stacks.TwistedSections (twistCongr twistPowMap twistModuleHom twistModuleHom_of)

variable (F N : X.Modules) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
  (he : (e : ℤ) = n + k)

/-- **The numerator identity**: the shift of `z₀` is the external product of `t` and `t'`, up to
the transport of degrees. -/
theorem twistCongr_shift_eq_extProd {d p q j : ℕ} (hj : k + j = q * d)
    (t : twistSections F L (p * d)) (t' : twistSections N L (q * d))
    (π : twistSections (twistPow N L k) L j)
    (hπ : π ≫ eqToHom (twistPow_twistPow N L k j) = twistCongr hj.symm t')
    (z₀ : twistSections (twistPow (F ⊗ N) L k) L (j + p * d))
    (h2 : identLeft F N β (DirectSum.of (twistSections (twistPow (F ⊗ N) L k) L) (j + p * d) z₀) =
      unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π) •
        DirectSum.of (twistSections F L) (p * d) t)
    (hK : k + (j + p * d) = (p + q) * d) :
    twistCongr (Nat.mul_comm (p + q) d) (twistCongr hK (twistShiftSection k (j + p * d) z₀)) =
      (λ_ (𝟙_ X.Modules)).inv ≫ (twistCongr (Nat.mul_comm p d) t ⊗ₘ
        twistCongr (Nat.mul_comm q d) t') ≫ extProd F N (d * p) (d * q) ≫
          eqToHom (congrArg (twistPow (F ⊗ N) L)
            ((Nat.add_comm (d * q) (d * p)).trans (Nat.mul_add d p q).symm)) := by
  have hbase := eq_extProd_of_identLeft F N β t π z₀ h2
  rw [hπ] at hbase
  have hkj : k + j = d * q := by rw [hj, Nat.mul_comm]
  have h3 := twistCongr_tensorHom_extProd F N (Nat.mul_comm p d) hkj t (twistCongr hj.symm t')
  have h4 : twistCongr hkj (twistCongr hj.symm t') = twistCongr (Nat.mul_comm q d) t' := by
    simp [twistCongr]
  rw [h4] at h3
  rw [reassoc_of% h3, ← reassoc_of% hbase]
  simp [twistCongr, twistShiftSection]

/-- The homogeneous element of `Γ_*(X, 𝓛, 𝓕)` built from a section of `𝓕 ⊗ 𝓛^{⊗ j}` lies in every
degree `i` equal to `j`. -/
private theorem of_mem_moduleGrading_of_eq (L G : X.Modules) {j : ℕ}
    (t : twistSections G L j) {i : ℤ} (h : i = j) :
    DirectSum.of (twistSections G L) j t ∈ moduleGrading G L i :=
  mem_moduleGrading_of_eq (L := L) h.symm
    ((Stacks.TwistedSections.mem_moduleGrading_natCast_iff (F := G) (L := L)).2 ⟨_, rfl⟩)

/-- The shift comparison sends a homogeneous element to the same section, reindexed. -/
private theorem twistShiftLinearMap_of_twistCongr (G : X.Modules) {k j m : ℕ} (h : k + j = m)
    (π : twistSections (twistPow G L k) L j) :
    twistShiftLinearMap G L k (DirectSum.of (twistSections (twistPow G L k) L) j π) =
      DirectSum.of (twistSections G L) m (twistCongr h (twistShiftSection k j π)) := by
  rw [twistShiftLinearMap_apply, twistShiftHom_of, of_twistCongr]

/-- **Every section of `(Γ_*(X, 𝓛, 𝓖))~` over `D₊(s)` is the fraction of a shift**: of an element
of `Γ_*(X, 𝓛, 𝓖 ⊙ k)` homogeneous of degree `q d - k`. -/
theorem exists_shift_fraction (G : X.Modules) (k : ℕ) {d : ℕ} (s₀ : powSections L d)
    (hd : 0 < d)
    (y : Γ((tildeFunctor L).obj G,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) :
    ∃ (q j : ℕ) (hj : k + j = q * d) (π : twistSections (twistPow G L k) L j)
      (hx : DirectSum.of (twistSections (twistPow G L k) L) j π ∈
        shiftedGrading (moduleGrading (twistPow G L k) L) (-(k : ℤ)) (q • (d : ℤ))),
      twistShiftLinearMap G L k (DirectSum.of (twistSections (twistPow G L k) L) j π) =
          DirectSum.of (twistSections G L) (q * d) (twistCongr hj (twistShiftSection k j π)) ∧
        y = (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading G L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
            (degreeZeroFraction (grading L) (moduleGrading G L)
              (Stacks.ExternalGrading.of_mem_summand d s₀) q _ (identRight_mem G k _ _ hx)) := by
  have eb := exists_twistSection_fraction_ge L G s₀ hd k y
  obtain ⟨q, eb⟩ := eb
  obtain ⟨hq, eb⟩ := eb
  obtain ⟨t', eb⟩ := eb
  obtain ⟨ht', hw⟩ := eb
  have hkq : k ≤ q * d := le_trans hq (Nat.le_mul_of_pos_right q hd)
  have ej : ∃ j, k + j = q * d := ⟨q * d - k, by omega⟩
  obtain ⟨j, hj⟩ := ej
  subst hw
  have hj' := congrArg (Nat.cast : ℕ → ℤ) hj
  push_cast at hj'
  have hx : DirectSum.of (twistSections (twistPow G L k) L) j
      (t' ≫ eqToHom ((congrArg (twistPow G L) hj.symm).trans (twistPow_twistPow G L k j).symm)) ∈
      shiftedGrading (moduleGrading (twistPow G L k) L) (-(k : ℤ)) (q • (d : ℤ)) :=
    of_mem_moduleGrading_of_eq L _ _ (by rw [nsmul_eq_mul]; linarith)
  have ht'' : twistCongr hj (twistShiftSection k j
      (t' ≫ eqToHom ((congrArg (twistPow G L) hj.symm).trans
        (twistPow_twistPow G L k j).symm))) = t' := by
    simp [twistCongr, twistShiftSection]
  have hshift : twistShiftLinearMap G L k (DirectSum.of (twistSections (twistPow G L k) L) j
      (t' ≫ eqToHom ((congrArg (twistPow G L) hj.symm).trans
        (twistPow_twistPow G L k j).symm))) =
      DirectSum.of (twistSections G L) (q * d) (twistCongr hj (twistShiftSection k j
        (t' ≫ eqToHom ((congrArg (twistPow G L) hj.symm).trans
          (twistPow_twistPow G L k j).symm)))) := by
    exact twistShiftLinearMap_of_twistCongr L G hj _
  refine ⟨q, j, hj, _, hx, hshift, ?_⟩
  refine congrArg (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading G L)
    (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm ?_
  exact Stacks.Veronese.degreeZeroFraction_congr (grading L) (moduleGrading G L)
    (Stacks.ExternalGrading.of_mem_summand d s₀) rfl (hshift.trans (by rw [ht''])).symm _ _

/-- **The identification `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, N))~` on a fraction**, read backwards: the
fraction of the shift of `x` goes to the fraction of the image of `x` in `S`. -/
theorem unitTwistIdent_inv_fraction {d : ℕ} (s₀ : powSections L d) (hd : 0 < d) (q : ℕ)
    (x : twistModule (twistPow N L k) L)
    (hx : x ∈ shiftedGrading (moduleGrading (twistPow N L k) L) (-(k : ℤ)) (q • (d : ℤ))) :
    (unitTwistIdent L N β he).inv.val.app
        (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
        ((associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading N L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
            (degreeZeroFraction (grading L) (moduleGrading N L)
              (Stacks.ExternalGrading.of_mem_summand d s₀) q _ (identRight_mem N k _ _ hx))) =
      (associatedModuleSheafStandardOpenEquiv (grading L)
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L)
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
            (Stacks.ExternalGrading.of_mem_summand d s₀) q (unitIdent N β x)
            (unitIdent_mem N β he _ _ hx)) := by
  have : IsIso (associatedModuleSheafMap (grading L)
      (shiftedGrading (moduleGrading (twistPow N L k) L) (-(k : ℤ))) (moduleGrading N L)
      (twistShiftLinearMap N L k) (identRight_mem N k)) := isIso_identSheafRight L N k
  refine (unitTwistIdent_inv_app L N β he _ _).trans ?_
  exact (congrArg (fun y => (unitSheafLeft L N β he).val.app
    (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) y)
    (inv_app_fraction L (shiftedGrading (moduleGrading (twistPow N L k) L) (-(k : ℤ)))
      (moduleGrading N L) (twistShiftLinearMap N L k) (identRight_mem N k)
      (Stacks.ExternalGrading.of_mem_summand d s₀) hd q x hx)).trans
    (associatedModuleSheafMap_fraction (grading L)
      (shiftedGrading (moduleGrading (twistPow N L k) L) (-(k : ℤ)))
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n) (unitIdent N β)
      (unitIdent_mem N β he) (Stacks.ExternalGrading.of_mem_summand d s₀) hd q x hx)

/-- **The identification `M(n)~ ≅ (Γ_*(X, 𝓛, 𝓕 ⊗ N))~` on a fraction**: the fraction of the image
of `x` under the left leg goes to the fraction of the shift of `x`. -/
theorem twistIdent_hom_fraction {d : ℕ} (s₀ : powSections L d) (hd : 0 < d) (P : ℕ)
    (x : twistModule (twistPow (F ⊗ N) L k) L)
    (hx : x ∈ shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ)) (P • (d : ℤ))) :
    (twistIdent L F N β he).hom.val.app
        (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
        ((associatedModuleSheafStandardOpenEquiv (grading L)
          (shiftedGrading (moduleGrading F L) n)
          (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
            (degreeZeroFraction (grading L) (shiftedGrading (moduleGrading F L) n)
              (Stacks.ExternalGrading.of_mem_summand d s₀) P _ (identLeft_mem F N β he _ _ hx))) =
      (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading (F ⊗ N) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (moduleGrading (F ⊗ N) L)
            (Stacks.ExternalGrading.of_mem_summand d s₀) P _ (identRight_mem (F ⊗ N) k _ _ hx)) :=
              by
  have : IsIso (associatedModuleSheafMap (grading L)
      (shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ)))
      (shiftedGrading (moduleGrading F L) n) (identLeft F N β) (identLeft_mem F N β he)) :=
    isIso_identSheafLeft L F N β he
  refine (twistIdent_hom_app L F N β he _ _).trans ?_
  exact (congrArg (fun y => (identSheafRight L (F ⊗ N) k).val.app
    (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) y)
    (inv_app_fraction L (shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ)))
      (shiftedGrading (moduleGrading F L) n) (identLeft F N β) (identLeft_mem F N β he)
      (Stacks.ExternalGrading.of_mem_summand d s₀) hd P x hx)).trans
    (associatedModuleSheafMap_fraction (grading L)
      (shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ)))
      (moduleGrading (F ⊗ N) L) (twistShiftLinearMap (F ⊗ N) L k) (identRight_mem (F ⊗ N) k)
      (Stacks.ExternalGrading.of_mem_summand d s₀) hd P x hx)

/-- **A section of `𝒪_Y(n)` from its image**: if its image under `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, N))~` is the
fraction of the shift of `x`, the section is the fraction of the image of `x` in `S`. -/
theorem eq_symm_of_unitTwistIdent_hom {d : ℕ} (s₀ : powSections L d) (hd : 0 < d) (q : ℕ)
    (x : twistModule (twistPow N L k) L)
    (hx : x ∈ shiftedGrading (moduleGrading (twistPow N L k) L) (-(k : ℤ)) (q • (d : ℤ)))
    (b : Γ(twistY L n,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
    (hc : (unitTwistIdent L N β he).hom.val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) b =
      (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading N L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
        (degreeZeroFraction (grading L) (moduleGrading N L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q _ (identRight_mem N k _ _ hx))) :
    b = (associatedModuleSheafStandardOpenEquiv (grading L)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
          (grading L) n)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q (unitIdent N β x)
            (unitIdent_mem N β he _ _ hx)) :=
  (iso_inv_app_hom_app L (unitTwistIdent L N β he) _ b).symm.trans
    ((congrArg (fun y => (unitTwistIdent L N β he).inv.val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) y)
      hc).trans
      (unitTwistIdent_inv_fraction L N β he s₀ hd q x hx))

/-- The image of `π` in `S`, as a homogeneous element. -/
theorem unitIdent_of (j : ℕ) (π : twistSections (twistPow N L k) L j) :
    unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π) =
      DirectSum.of (powSections L) (e + j)
        (π ≫ twistPowMap L β.inv j ≫ eqToHom (twistPow_natTensorPow L e j)) := by
  change unitShiftHom L e (twistModuleHom (L := L) β.inv
      (DirectSum.of (twistSections (twistPow N L k) L) j π)) = _
  rw [twistModuleHom_of, unitShiftHom_of]
  rfl

/-- The product of the image of `π` in `S` with `t` is homogeneous of degree `(p + q) d` in
`M(n)`. -/
theorem unitIdent_smul_mem (he : (e : ℤ) = n + k) {d p q j : ℕ} (hj : k + j = q * d)
    (t : twistSections F L (p * d))
    (π : twistSections (twistPow N L k) L j) :
    unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π) •
      (DirectSum.of (twistSections F L) (p * d) t) ∈ (shiftedGrading (moduleGrading F L) n)
      ((p + q) • (d : ℤ)) := by
  have hj' := congrArg (Nat.cast : ℕ → ℤ) hj
  push_cast at hj'
  rw [unitIdent_of L N β j π, Stacks.TwistedSections.of_smul_of]
  refine of_mem_moduleGrading_of_eq L F _ ?_
  rw [nsmul_eq_mul]
  push_cast
  linarith

/-- The product of the image of `π` in `S` with `t` comes from `Γ_*(X, 𝓛, (𝓕 ⊗ N) ⊙ k)`. -/
theorem exists_identLeft_eq (he : (e : ℤ) = n + k) {d p q j : ℕ} (hj : k + j = q * d)
    (t : twistSections F L (p * d))
    (π : twistSections (twistPow N L k) L j) :
    ∃ z₀ : twistSections (twistPow (F ⊗ N) L k) L (j + p * d),
      identLeft F N β (DirectSum.of (twistSections (twistPow (F ⊗ N) L k) L) (j + p * d) z₀) =
        unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π) •
          (DirectSum.of (twistSections F L) (p * d) t) := by
  have hj' := congrArg (Nat.cast : ℕ → ℤ) hj
  push_cast at hj'
  have ex := identLeft_surjective F N β he ((p + q) • (d : ℤ))
    (by rw [nsmul_eq_mul]; push_cast; nlinarith) _ (unitIdent_smul_mem L F N β he hj t π)
  obtain ⟨x, ex⟩ := ex
  obtain ⟨hx, hxe⟩ := ex
  have hx2 : x ∈ moduleGrading (twistPow (F ⊗ N) L k) L ((j + p * d : ℕ) : ℤ) :=
    mem_moduleGrading_of_eq (L := L) (by
      rw [nsmul_eq_mul]; push_cast; linarith) hx
  obtain ⟨z₀, hz₀⟩ := hx2
  exact ⟨z₀, (congrArg (identLeft F N β) hz₀).trans hxe⟩

/-- **The upper-right path of the square on two fractions.** -/
theorem twistSquareInt_right {d : ℕ} (s₀ : powSections L d) (hd : 0 < d) (p q j : ℕ)
    (hj : k + j = q * d) (hK : k + (j + p * d) = (p + q) * d) (t : twistSections F L (p * d))
    (hm : (DirectSum.of (twistSections F L) (p * d) t) ∈ moduleGrading F L (p • (d : ℤ)))
    (π : twistSections (twistPow N L k) L j)
    (hx' : (DirectSum.of (twistSections (twistPow N L k) L) j π) ∈
      shiftedGrading (moduleGrading (twistPow N L k) L) (-(k : ℤ)) (q • (d : ℤ)))
    (z₀ : twistSections (twistPow (F ⊗ N) L k) L (j + p * d))
    (h2 : identLeft F N β (DirectSum.of (twistSections (twistPow (F ⊗ N) L k) L) (j + p * d) z₀) =
      unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π) •
        (DirectSum.of (twistSections F L) (p * d) t)) :
    ∃ hZ : (DirectSum.of (twistSections (F ⊗ N) L) ((p + q) * d)
      (twistCongr hK (twistShiftSection k (j + p * d) z₀))) ∈ moduleGrading (F ⊗ N) L
      ((p + q) • (d : ℤ)),
      (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading (F ⊗ N) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd)
          ((twistIdent L F N β he).hom.val.app
          (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
          ((Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (grading L) (moduleGrading F L)
            n).val.app
          (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
            (AlgebraicGeometry.Proj (grading L)).toRingedSpace _ _
              (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
            ((associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading F L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (moduleGrading F L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) p
            (DirectSum.of (twistSections F L) (p * d) t) hm) ⊗ₜ
              (associatedModuleSheafStandardOpenEquiv (grading L)
                (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
          (grading L) n)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q
            (unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π))
            (unitIdent_mem N β he _ _ hx')))))) =
            (degreeZeroFraction (grading L) (moduleGrading (F ⊗ N) L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) (p + q) _ hZ) := by
  have hrm := unitIdent_smul_mem L F N β he hj t π
  have e4 := moduleTwistMap_fraction (grading L) (moduleGrading F L) n
    (Stacks.ExternalGrading.of_mem_summand d s₀) hd p q _ hm _ (unitIdent_mem N β he _ _ hx') hrm
  have hK' := congrArg (Nat.cast : ℕ → ℤ) hK
  push_cast at hK'
  have hx : DirectSum.of (twistSections (twistPow (F ⊗ N) L k) L) (j + p * d) z₀ ∈
      shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ)) ((p + q) • (d : ℤ)) :=
    of_mem_moduleGrading_of_eq L _ _ (by rw [nsmul_eq_mul]; push_cast; linarith)
  have e5 := (congrArg (fun y => (twistIdent L F N β he).hom.val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
      ((associatedModuleSheafStandardOpenEquiv (grading L) (shiftedGrading (moduleGrading F L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm y))
    (Stacks.Veronese.degreeZeroFraction_congr (grading L) (shiftedGrading (moduleGrading F L) n)
      (Stacks.ExternalGrading.of_mem_summand d s₀) rfl h2.symm hrm
      (identLeft_mem F N β he _ _ hx))).trans
    (twistIdent_hom_fraction L F N β he s₀ hd (p + q) _ hx)
  have hshift2 : twistShiftLinearMap (F ⊗ N) L k
      (DirectSum.of (twistSections (twistPow (F ⊗ N) L k) L) (j + p * d) z₀) =
        (DirectSum.of (twistSections (F ⊗ N) L) ((p + q) * d)
        (twistCongr hK (twistShiftSection k (j + p * d) z₀))) := by
    exact twistShiftLinearMap_of_twistCongr L (F ⊗ N) hK _
  have hZ : (DirectSum.of (twistSections (F ⊗ N) L) ((p + q) * d)
      (twistCongr hK (twistShiftSection k (j + p * d) z₀))) ∈ moduleGrading (F ⊗ N) L
      ((p + q) • (d : ℤ)) :=
    hshift2 ▸ identRight_mem (F ⊗ N) k _ _ hx
  refine ⟨hZ, ?_⟩
  exact (congrArg (fun y => (associatedModuleSheafStandardOpenEquiv (grading L)
      (moduleGrading (F ⊗ N) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd)
          ((twistIdent L F N β he).hom.val.app
          (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) y))
          e4).trans
    ((congrArg (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading (F ⊗ N) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd) e5).trans
          (((associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading (F ⊗ N) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).apply_symm_apply _).trans
      (Stacks.Veronese.degreeZeroFraction_congr (grading L) (moduleGrading (F ⊗ N) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) rfl hshift2 _ hZ)))

/-- **The square on two fractions.** -/
theorem twistSquareInt_fraction {d : ℕ} (s₀ : powSections L d) (hd : 0 < d)
    (hU : nvOpen L s₀ ≤ nvOpen L s₀) (p : ℕ) (t : twistSections F L (p * d))
    (hm : (DirectSum.of (twistSections F L) (p * d) t) ∈ moduleGrading F L (p • (d : ℤ))) (q j : ℕ)
      (hj : k + j = q * d)
    (π : twistSections (twistPow N L k) L j)
    (hx' : (DirectSum.of (twistSections (twistPow N L k) L) j π) ∈
      shiftedGrading (moduleGrading (twistPow N L k) L) (-(k : ℤ)) (q • (d : ℤ)))
    (hshift : twistShiftLinearMap N L k (DirectSum.of (twistSections (twistPow N L k) L) j π) =
      DirectSum.of (twistSections N L) (q * d) (twistCongr hj (twistShiftSection k j π)))
    (hc : (unitTwistIdent L N β he).hom.val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
        ((associatedModuleSheafStandardOpenEquiv (grading L)
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
          (grading L) n)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q
            (unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π))
            (unitIdent_mem N β he _ _ hx'))) =
      (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading N L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (moduleGrading N L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q _ (identRight_mem N k _ _ hx'))) :
    Stacks.SectionTensorFormula.tensorSection F N
        (localDivision L F s₀ hU ((associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading F L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd)
          ((associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading F L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (moduleGrading F L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) p
            (DirectSum.of (twistSections F L) (p * d) t) hm))))
        (localDivision L N s₀ hU ((associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading N L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd)
          ((unitTwistIdent L N β he).hom.val.app
          (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
          ((associatedModuleSheafStandardOpenEquiv (grading L)
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
          (grading L) n)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q
            (unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π))
            (unitIdent_mem N β he _ _ hx')))))) =
      localDivision L (F ⊗ N) s₀ hU ((associatedModuleSheafStandardOpenEquiv (grading L)
        (moduleGrading (F ⊗ N) L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd)
          ((twistIdent L F N β he).hom.val.app
          (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
          ((Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (grading L) (moduleGrading F L)
            n).val.app
          (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
            (AlgebraicGeometry.Proj (grading L)).toRingedSpace _ _
              (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
            ((associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading F L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (moduleGrading F L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) p
            (DirectSum.of (twistSections F L) (p * d) t) hm) ⊗ₜ
              (associatedModuleSheafStandardOpenEquiv (grading L)
                (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (grading L) n)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).symm
          (degreeZeroFraction (grading L) (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading
          (grading L) n)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q
            (unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π))
            (unitIdent_mem N β he _ _ hx'))))))) := by
  have hK : k + (j + p * d) = (p + q) * d := by rw [Nat.add_mul, ← hj]; ring
  have ez := exists_identLeft_eq L F N β he hj t π
  obtain ⟨z₀, h2⟩ := ez
  have eR := twistSquareInt_right L F N β he s₀ hd p q j hj hK t hm π hx' z₀ h2
  obtain ⟨hZ, l3⟩ := eR
  have hv : DirectSum.of (twistSections N L) (q * d) (twistCongr hj (twistShiftSection k j π)) ∈
      moduleGrading N L (q • (d : ℤ)) :=
    hshift ▸ identRight_mem N k _ _ hx'
  have hz := twistCongr_shift_eq_extProd L F N β hj t (twistCongr hj (twistShiftSection k j π)) π
    (by simp [twistCongr, twistShiftSection]) z₀ h2 hK
  have key := tensorSection_localDivision L F N s₀ hU p q
    (degreeZeroFraction (grading L) (moduleGrading F L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) p
            (DirectSum.of (twistSections F L) (p * d) t) hm)
            (degreeZeroFraction (grading L) (moduleGrading N L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) q _ hv)
            (degreeZeroFraction (grading L) (moduleGrading (F ⊗ N) L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) (p + q) _ hZ) t _ _ rfl rfl rfl hz
  have l1 := (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading F L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).apply_symm_apply
          (degreeZeroFraction (grading L) (moduleGrading F L)
          (Stacks.ExternalGrading.of_mem_summand d s₀) p
            (DirectSum.of (twistSections F L) (p * d) t) hm)
  have l2 := (congrArg (associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading N L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd) hc).trans
          (((associatedModuleSheafStandardOpenEquiv (grading L) (moduleGrading N L)
        (Stacks.ExternalGrading.of_mem_summand d s₀) hd).apply_symm_apply _).trans
    (Stacks.Veronese.degreeZeroFraction_congr (grading L) (moduleGrading N L)
      (Stacks.ExternalGrading.of_mem_summand d s₀) rfl hshift _ hv))
  exact ((congrArg₂ (fun x y => Stacks.SectionTensorFormula.tensorSection F N
    (localDivision L F s₀ hU x) (localDivision L N s₀ hU y)) l1 l2).trans
      key).trans (congrArg (localDivision L (F ⊗ N) s₀ hU) l3).symm

end Pieces

/-! ### The square on a standard open, in every integer degree -/

section Chart

variable (F N : X.Modules) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
  (he : (e : ℤ) = n + k)

/-- **The square on a standard open `D₊(s)`, in every integer degree**, after the reduction to
fractions: for `β : 𝓛^{⊗ e} ≅ N ⊙ k` with `e = n + k`. -/
theorem twistSquareInt_basicOpen {d : ℕ} (s₀ : powSections L d) (hd : 0 < d)
    (hU : nvOpen L s₀ ≤ nvOpen L s₀)
    (a : Γ((tildeFunctor L).obj F,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
    (b : Γ(twistY L n,
      ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) :
    Stacks.SectionTensorFormula.tensorSection F N
        (localDivision L F s₀ hU
          (associatedModuleSheafStandardOpenEquiv (grading L)
            (moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd a))
        (localDivision L N s₀ hU
          (associatedModuleSheafStandardOpenEquiv (grading L)
            (moduleGrading N L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd
            ((unitTwistIdent L N β he).hom.val.app
              (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
              b))) =
      localDivision L (F ⊗ N) s₀ hU
        (associatedModuleSheafStandardOpenEquiv (grading L)
          (moduleGrading (F ⊗ N) L) (Stacks.ExternalGrading.of_mem_summand d s₀) hd
          ((twistIdent L F N β he).hom.val.app
            (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
            ((Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap
              (grading L) (moduleGrading F L) n).val.app
              (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
              (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
                (AlgebraicGeometry.Proj (grading L)).toRingedSpace _ _
                (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀)))
                (a ⊗ₜ b))))) := by
  have ea := exists_twistSection_fraction L F s₀ hd a
  obtain ⟨p, ea⟩ := ea
  obtain ⟨t, ea⟩ := ea
  obtain ⟨hm, ha⟩ := ea
  subst ha
  have ec := exists_shift_fraction L N k s₀ hd
    ((unitTwistIdent L N β he).hom.val.app
      (op (ProjectiveSpectrum.basicOpen (grading L) (DirectSum.of (powSections L) d s₀))) b)
  obtain ⟨q, ec⟩ := ec
  obtain ⟨j, ec⟩ := ec
  obtain ⟨hj, ec⟩ := ec
  obtain ⟨π, ec⟩ := ec
  obtain ⟨hx', ec⟩ := ec
  obtain ⟨hshift, hc⟩ := ec
  have hb := eq_symm_of_unitTwistIdent_hom L N β he s₀ hd q _ hx' b hc
  subst hb
  exact twistSquareInt_fraction L F N β he s₀ hd hU p t hm q j hj π hx' hshift hc

end Chart

/-! ### The square, in every integer degree -/

section Sheaf

variable (F N : X.Modules) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
  (he : (e : ℤ) = n + k)

/-- **`θ_N`, read on `f^*𝒪_Y(n)`**: Tag 01QJ's comparison for `N`, precomposed with the pullback of
the identification `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, N))~` attached to `β : 𝓛^{⊗ e} ≅ N ⊙ k`, `e = n + k`. -/
def twistThetaOf :
    (Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj (twistY L n) ⟶ N :=
  (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map (unitTwistIdent L N β he).hom ≫
    (pullbackTildeComparison L hL).app N

/-- **The twist square, for an identification `β : 𝓛^{⊗ e} ≅ N ⊙ k` with `e = n + k`.** -/
theorem twistSquareOf :
    ((pullbackTildeComparison L hL).app F ⊗ₘ twistThetaOf L hL N β he) =
      twistTop L hL F n ≫
        (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map (twistIdent L F N β he).hom ≫
        (pullbackTildeComparison L hL).app (F ⊗ N) := by
  have := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  refine monoidal_hom_ext_of_isBasis (fun c : GoodChart L hL => nvOpen L c.1.val)
    (Stacks.SectionRingProjQuasicoherent.isBasis_goodChart L hL) fun c x y => ?_
  obtain ⟨a, rfl⟩ := pullbackSection_surjective L hL _ c x
  obtain ⟨b, rfl⟩ := pullbackSection_surjective L hL _ c y
  refine (tensorHom_app_pullbackSection L hL F N c (unitTwistIdent L N β he).hom a
    b).trans (Eq.trans ?_ (twistTop_comp_app_pullbackSection L hL F (F ⊗ N) n c
      (twistIdent L F N β he).hom a b).symm)
  exact twistSquareInt_basicOpen L F N β he c.1.val c.1.deg_pos le_rfl a b

end Sheaf

/-! ### `N = 𝓛^{⊗ n}` -/

section Power

open Stacks.AmpleProjectiveImmersion (tensorPowerModule)

/-- `n.toNat = n + (-n).toNat`, the degree bookkeeping of the identifications below. -/
theorem toNat_eq_add_toNat_neg (n : ℤ) : ((n.toNat : ℕ) : ℤ) = n + (((-n).toNat : ℕ) : ℤ) := by
  omega

/-- **`𝓛^{⊗ n⁺} ≅ 𝓛^{⊗ n} ⊙ n⁻`**, for `n = n⁺ - n⁻` the decomposition of an integer into its
positive and negative parts: the identification that reads `(Γ_*(X, 𝓛, 𝓛^{⊗ n}))~` as `𝒪_Y(n)`.
It compares the iterated tensor power with Tag 01CU's power, splits `𝓛^{⊗ n⁺} = 𝓛^{⊗ (n + n⁻)}`
by Tag 01CU's multiplication `𝓛^{⊗ n} ⊗ 𝓛^{⊗ n⁻} ⟶ 𝓛^{⊗ (n + n⁻)}`, and reads the factor
`𝓛^{⊗ n⁻}` as `n⁻` further copies of `𝓛`. -/
def twistBeta (n : ℤ) :
    natTensorPow L n.toNat ≅ twistPow (tensorPowerModule X L n) L (-n).toNat :=
  letI := Stacks.PowerFamilyBridge.instIsInvertible X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L
  Stacks.SheafOfModules.Invertible.twistPowBeta X.presheaf
    (Stacks.AlgebraicGeometry.CoherentMulSections.hStruct X) L n n.toNat (-n).toNat
    (toNat_eq_add_toNat_neg n)

/-- **The obvious identification `𝒪_Y(n) ≅ (Γ_*(X, 𝓛, 𝓛^{⊗ n}))~`**, for every integer `n`. -/
def twistPowIdent (n : ℤ) :
    twistY L n ≅ (tildeFunctor L).obj (tensorPowerModule X L n) :=
  unitTwistIdent L (tensorPowerModule X L n) (twistBeta L n) (toNat_eq_add_toNat_neg n)

/-- **The obvious identification `M(n)~ ≅ (Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n}))~`** of Stacks Tag 01QK, for
`M = Γ_*(X, 𝓛, 𝓕)` and every integer `n`. -/
def twistModuleIdent (F : X.Modules) (n : ℤ) :
    shiftY L F n ≅ (tildeFunctor L).obj (F ⊗ tensorPowerModule X L n) :=
  twistIdent L F (tensorPowerModule X L n) (twistBeta L n) (toNat_eq_add_toNat_neg n)

/-- **`θ_{𝓛^{⊗ n}}`, read on `f^*𝒪_Y(n)`**, for every integer `n`: Tag 01QJ's comparison
`f^*(Γ_*(X, 𝓛, 𝓛^{⊗ n}))~ ⟶ 𝓛^{⊗ n}` precomposed with the pullback of `twistPowIdent`. -/
def twistThetaInt (n : ℤ) :
    (Scheme.Modules.pullback (projHomOfIsAmple L hL)).obj (twistY L n) ⟶ tensorPowerModule X L n :=
  (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map (twistPowIdent L n).hom ≫
    (pullbackTildeComparison L hL).app (tensorPowerModule X L n)

/-- **The twist square commutes**, for every `𝒪_X`-module `𝓕` and every integer `n`:
`θ_𝓕 ⊗ θ_{𝓛^{⊗ n}}` is the pullback of the multiplication `M̃ ⊗ 𝒪_Y(n) ⟶ M(n)~` of Equation 01MQ
(`twistTop`) followed by `θ_{𝓕 ⊗ 𝓛^{⊗ n}}`, read through `twistModuleIdent`. -/
@[stacks 01QK "assertion (ii), with no extra hypothesis: the square commutes -- theta_F (x)
theta_{L^n} is the pullback of the multiplication of Equation 01MQ followed by theta_{F (x) L^n},
read through the obvious identification M(n) = Gamma_*(X, L, F (x) L^n), for every O_X-module F
and every integer n, theta being the constructed comparison pullbackTildeComparison of Tag 01QJ,
so no compatibility of a binder family is assumed (contrast pullbackComparison_tensorHom)"]
theorem twistSquareInt (F : X.Modules) (n : ℤ) :
    ((pullbackTildeComparison L hL).app F ⊗ₘ twistThetaInt L hL n) =
      twistTop L hL F n ≫
        (Scheme.Modules.pullback (projHomOfIsAmple L hL)).map (twistModuleIdent L F n).hom ≫
        (pullbackTildeComparison L hL).app (F ⊗ tensorPowerModule X L n) :=
  twistSquareOf L hL F (tensorPowerModule X L n) (twistBeta L n) (toNat_eq_add_toNat_neg n)

end Power

end Stacks.SectionRingProjTheta

end
