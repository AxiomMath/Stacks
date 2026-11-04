module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Bijective
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SerreFiniteness
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedDivision
public import StacksFrontier.AlgebraicGeometry.SectionRingChartBijective.Basic

/-!
# The sections of the tensor powers over a nonvanishing open are graded pieces of `Γ_*(X, L)_a`

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module,
`A = Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` its section ring, graded by
`Stacks.AmpleFiniteAvoidance.grading L`, and regard `A` as a `ℤ`-graded module over itself through
`AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading`. For `a` a global section of `L^{⊗ d}`,
`d > 0`, with nonvanishing open `X_a`, this file identifies

`Γ(X_a, L^{⊗ e}) ≅ (A_a)_e`

for every `e ≥ 0`, where `(A_a)_e` is `Stacks.GradedLocalization.gradedPiece`, the degree-`e`
part of the localization of `A` at `a`. This is [Stacks, Tag 01PW] read in every degree at once,
in the form the Čech complex `Cech.cechComplex fam A` of a family of homogeneous elements
consumes: its terms are direct sums of localizations `A_{∏ i ∈ s, fam i}`, graded by
`Stacks.GradedLocalization.gradedPiece`, and its transition maps are the localization maps of
`Cech.cechι_mk_pow`, which `chartSectionsEquiv_restrict` matches with the restriction of sections.

## Main definitions

* `Stacks.Algebraization.SectionRingCone.chartSectionsEquiv`: **`Γ(X_a, L^{⊗ e}) ≃+ (A_a)_e`**.
* `Stacks.Algebraization.SectionRingCone.chartFunctionsEquiv`: the ring isomorphism
  `A_{(a)} ≃+* Γ(X_a, 𝒪_X)` of the degree-zero homogeneous localization with the functions on
  `X_a`.
* `Stacks.Algebraization.SectionRingCone.degreeZeroShiftEquiv`: the algebraic step, for an
  arbitrary graded ring — an injective degree-raising linear map `ψ : M ⟶ N`, surjective up to
  powers of `g` in high degrees, identifies `M_{(g)}` with the degree-`e` part of `N_g`.

## Main results

* `chartSectionsEquiv_eq_mk_of_powMul`: **the characterization**: if `aⁿ σ` is the restriction of
  the global section `ρ` of `L^{⊗ (e + n d)}`, then `σ` goes to the fraction `ρ / aⁿ`.
* `chartSectionsEquiv_unitSec`: a global section `ρ` of `L^{⊗ e}` goes to `ρ / 1`.
* `chartSectionsEquiv_restrict`: **naturality**: for `q = a c` homogeneous, restriction from `X_a`
  to `X_q` is the localization map `ρ / aᵐ ↦ cᵐ ρ / qᵐ`.
* `chartSectionsEquiv_mulMap`: **multiplicativity**: multiplying a section by a global section `b`
  of `L^{⊗ k}` is multiplying by `b` in `A_a`, landing in degree `k + e`.
* `chartSectionsEquiv_smul` and `chartSectionsEquiv_chartRingMap_smul`: linearity over the
  functions on `X_a`, read through `chartFunctionsEquiv`.

## Implementation notes

The tensor powers are `Stacks.TensorPowers.natTensorPow L e`, the spelling of the section ring
`Stacks.GradedSections.sectionRing L` itself; in nonnegative degree it is definitionally
`Stacks.Ample.tensorPowModule X L e` (`AlgebraicGeometry.SheafOfModules.tensorPow_natCast`).

The bijectivity is not reproved: it is [Stacks, Tag 01PW] for the division
`Stacks.SectionRingProjQuasicoherent.localDivision` of a twisted section by a power of `a`, proved
as `Stacks.SectionRingProjQuasicoherent.localDivision_injective` and
`Stacks.SectionRingProjQuasicoherent.localDivision_surjective` for every quasi-coherent module. Its
domain is the degree-zero localization of the module `Γ_*(X, L, L^{⊗ e})` of twisted sections,
and `twistSectionRingShift` identifies that module with the part of `A` in degrees `≥ e`, raising
degrees by `e`, by `Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPow_natTensorPow`; the
missing degrees `< e` are killed by inverting `a`, which is what `degreeZeroShiftEquiv` records.
Naturality and multiplicativity are read off `localDivision_change` and
`localDivision_naturality`, and the degree-zero ring is
`Stacks.SectionRingChartBijective.chartRingMap_bijective`.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap sectionRing)
open Stacks.TwistedSections (twistPow twistSections twistModule actMap twistPowMap)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading integerGrading_natCast)
open DirectSum
open scoped Stacks.GradedLocalization

universe u

namespace Stacks.Algebraization.SectionRingCone

section Generic

variable {S M N : Type*} {σ τ υ : Type*} [CommRing S] [AddCommGroup M] [Module S M]
  [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ)
  (ψ : M →ₗ[S] N) (e : ℤ) {g : S} {d : ℕ} (hg : g ∈ 𝒜 d)

/-- **The degree-zero localization of `M` maps to the degree-`e` part of the localization of `N`**,
for an `S`-linear map `ψ : M ⟶ N` raising degrees by `e`: the map on localizations at `g` induced
by `ψ`, restricted to the degree-zero part. -/
def degreeZeroShiftMap (hψ : ∀ (i : ℤ) (x : M), x ∈ 𝒨 i → ψ x ∈ 𝒩 (i + e)) :
    GradedModuleDegreeZeroLocalization 𝒜 𝒨 g →+
      Stacks.GradedLocalization.gradedPiece 𝒜 𝒩 g e where
  toFun z := ⟨LocalizedModule.map (Submonoid.powers g) ψ (z : LocalizedModule.Away g M), by
    obtain ⟨n, x, hx, hz⟩ :=
      Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree 𝒜 𝒨 hg z
    rw [hz, LocalizedModule.map_mk]
    refine Stacks.GradedLocalization.mk_mem_gradedPiece 𝒜 𝒩 hg ?_
    have h := hψ _ x hx
    rwa [show ((n * d : ℕ) : ℤ) + e = e + n • (d : ℤ) by push_cast; ring] at h⟩
  map_zero' := Subtype.ext (by
    change LocalizedModule.map _ ψ ((0 : GradedModuleDegreeZeroLocalization 𝒜 𝒨 g) :
      LocalizedModule.Away g M) = 0
    rw [ZeroMemClass.coe_zero, map_zero])
  map_add' z w := Subtype.ext (by
    change LocalizedModule.map _ ψ (((z + w : GradedModuleDegreeZeroLocalization 𝒜 𝒨 g)) :
      LocalizedModule.Away g M) = _ + _
    rw [AddMemClass.coe_add, map_add])

omit [AddSubgroupClass υ N] in
/-- `degreeZeroShiftMap` is the map of localizations induced by `ψ`. -/
theorem degreeZeroShiftMap_coe (hψ : ∀ (i : ℤ) (x : M), x ∈ 𝒨 i → ψ x ∈ 𝒩 (i + e))
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 g) :
    ((degreeZeroShiftMap 𝒜 𝒨 𝒩 ψ e hg hψ z : Stacks.GradedLocalization.gradedPiece 𝒜 𝒩 g e) :
      LocalizedModule.Away g N) =
      LocalizedModule.map (Submonoid.powers g) ψ (z : LocalizedModule.Away g M) := rfl

omit [AddSubgroupClass υ N] in
/-- An injective `ψ` gives an injective map on the degree-zero localizations. -/
theorem degreeZeroShiftMap_injective (hψ : ∀ (i : ℤ) (x : M), x ∈ 𝒨 i → ψ x ∈ 𝒩 (i + e))
    (hinj : Function.Injective ψ) :
    Function.Injective (degreeZeroShiftMap 𝒜 𝒨 𝒩 ψ e hg hψ) := by
  intro z w hzw
  have h := congrArg (fun y : Stacks.GradedLocalization.gradedPiece 𝒜 𝒩 g e =>
    (y : LocalizedModule.Away g N)) hzw
  simp only [degreeZeroShiftMap_coe] at h
  exact Subtype.ext (IsLocalizedModule.map_injective (Submonoid.powers g)
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) ψ hinj h)

omit [AddSubgroupClass υ N] in
/-- **Surjectivity onto the degree-`e` part.** If every homogeneous element of `N` of degree
`e + n d` becomes, after multiplication by a power of `g`, the image of a homogeneous element of
`M` of the matching degree, then every element of the degree-`e` part of `N_g` comes from the
degree-zero part of `M_g`. -/
theorem degreeZeroShiftMap_surjective (hψ : ∀ (i : ℤ) (x : M), x ∈ 𝒨 i → ψ x ∈ 𝒩 (i + e))
    (hsurj : ∀ (n : ℕ) (y : N), y ∈ 𝒩 (e + n • (d : ℤ)) →
      ∃ (k : ℕ) (x : M), x ∈ 𝒨 (((n + k) * d : ℕ) : ℤ) ∧ ψ x = g ^ k • y) :
    Function.Surjective (degreeZeroShiftMap 𝒜 𝒨 𝒩 ψ e hg hψ) := by
  classical
  let := Module.compHom (R := Localization.Away g) (LocalizedModule.Away (R := S) g M)
    (algebraMap (HomogeneousLocalization.Away 𝒜 g) (Localization.Away g))
  by_cases hg0 : g = 0
  · have : Subsingleton (LocalizedModule.Away (R := S) g N) :=
      LocalizedModule.subsingleton_iff.mpr (fun m => ⟨g, ⟨1, pow_one g⟩, by simp [hg0]⟩)
    exact fun _ => ⟨0, Subtype.ext (Subsingleton.elim _ _)⟩
  let H : AddSubgroup (LocalizedModule.Away (R := S) g N) :=
    ((Stacks.GradedLocalization.gradedPiece 𝒜 𝒩 g e).subtype.comp
      (degreeZeroShiftMap 𝒜 𝒨 𝒩 ψ e hg hψ)).range
  suffices hle : Stacks.GradedLocalization.gradedPiece 𝒜 𝒩 g e ≤ H by
    intro y
    obtain ⟨z, hz⟩ := hle y.2
    exact ⟨z, Subtype.ext hz⟩
  refine (AddSubgroup.closure_le H).mpr ?_
  rintro y ⟨d', n, hgd', x', hx', rfl⟩
  by_cases hgn : g ^ n = 0
  · have : Subsingleton (LocalizedModule.Away (R := S) g N) :=
      LocalizedModule.subsingleton_iff.mpr (fun m => ⟨g ^ n, ⟨n, rfl⟩, by simp [hgn]⟩)
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain rfl : d' = d := DirectSum.degree_eq_of_mem_mem 𝒜 hgd' hg hg0
  obtain ⟨k, x, hx, hψx⟩ := hsurj n x' hx'
  refine ⟨⟨LocalizedModule.mk x ⟨g ^ (n + k), ⟨n + k, rfl⟩⟩,
    Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree 𝒜 𝒨 hg (n + k) x hx⟩, ?_⟩
  change LocalizedModule.map (Submonoid.powers g) ψ (LocalizedModule.mk x _) = _
  rw [LocalizedModule.map_mk, hψx, LocalizedModule.mk_eq]
  exact ⟨1, by simp only [one_smul, Submonoid.smul_def, smul_smul, ← pow_add]⟩

/-- **The degree-zero localization of `M` is the degree-`e` part of the localization of `N`**, for
`ψ` injective, raising degrees by `e`, and surjective up to powers of `g` in the degrees
`e + n d`. -/
def degreeZeroShiftEquiv (hψ : ∀ (i : ℤ) (x : M), x ∈ 𝒨 i → ψ x ∈ 𝒩 (i + e))
    (hinj : Function.Injective ψ)
    (hsurj : ∀ (n : ℕ) (y : N), y ∈ 𝒩 (e + n • (d : ℤ)) →
      ∃ (k : ℕ) (x : M), x ∈ 𝒨 (((n + k) * d : ℕ) : ℤ) ∧ ψ x = g ^ k • y) :
    GradedModuleDegreeZeroLocalization 𝒜 𝒨 g ≃+ Stacks.GradedLocalization.gradedPiece 𝒜 𝒩 g e :=
  AddEquiv.ofBijective (degreeZeroShiftMap 𝒜 𝒨 𝒩 ψ e hg hψ)
    ⟨degreeZeroShiftMap_injective 𝒜 𝒨 𝒩 ψ e hg hψ hinj,
      degreeZeroShiftMap_surjective 𝒜 𝒨 𝒩 ψ e hg hψ hsurj⟩

end Generic

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

local notation "tpow" => Stacks.AlgebraicGeometry.ProperAmpleCohomology.twistPow_natTensorPow

/-- The degree-`n` component of the comparison `Γ_*(X, L^{⊗ e}, L) ⟶ Γ_*(X, L)`: a twisted section
of `L^{⊗ e} ⊙ n` is a section of `L^{⊗ (e + n)}`, placed in degree `e + n`. -/
def twistSectionRingShiftComponent (e n : ℕ) :
    twistSections (natTensorPow L e) L n →+ sectionRing L where
  toFun t := DirectSum.of (powSections L) (e + n) (t ≫ eqToHom (tpow L e n))
  map_zero' := by simp
  map_add' x y := by rw [Preadditive.add_comp, map_add]

/-- **The comparison `Γ_*(X, L^{⊗ e}, L) ⟶ Γ_*(X, L)`**, raising degrees by `e`: the graded module
of twisted sections of the tensor power `L^{⊗ e}` is the section ring in the degrees `≥ e`. -/
def twistSectionRingShift (e : ℕ) : twistModule (natTensorPow L e) L →+ sectionRing L :=
  DirectSum.toAddMonoid fun n => twistSectionRingShiftComponent L e n

omit [Ample.IsInvertibleModule X L] in
/-- The comparison on a homogeneous element. -/
theorem twistSectionRingShift_of (e n : ℕ) (t : twistSections (natTensorPow L e) L n) :
    twistSectionRingShift L e (DirectSum.of _ n t) =
      DirectSum.of (powSections L) (e + n) (t ≫ eqToHom (tpow L e n)) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The comparison carries the action of a homogeneous element of the section ring on a homogeneous
twisted section to the product in the section ring. -/
theorem twistSectionRingShift_smul_of (e j m : ℕ) (x : powSections L j)
    (t : twistSections (natTensorPow L e) L m) :
    twistSectionRingShift L e (DirectSum.of (powSections L) j x • DirectSum.of _ m t) =
      DirectSum.of (powSections L) j x * twistSectionRingShift L e (DirectSum.of _ m t) := by
  rw [Stacks.TwistedSections.of_smul_of, twistSectionRingShift_of, twistSectionRingShift_of,
    Stacks.TwistedSections.gsmul_def, Stacks.TwistedSections.twistCongr,
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.actMap_eq_mulMap]
  simp only [Category.assoc, eqToHom_trans]
  rw [← Stacks.SectionRingChartMap.of_mul_eq]
  set t' := t ≫ eqToHom (tpow L e m)
  have h1 : DirectSum.of (powSections L) (e + (j + m)) (x ≫ mulMap t' j ≫ eqToHom
      (congrArg (natTensorPow L) (by omega : e + m + j = e + (j + m)))) =
      DirectSum.of (powSections L) (e + m) t' * DirectSum.of (powSections L) j x := by
    rw [← Category.assoc, Stacks.SectionRingProjQuasicoherent.of_comp_eqToHom L
      (by omega : e + m + j = e + (j + m)) (x ≫ mulMap t' j),
      ← Stacks.SectionRingChartMap.of_mul_eq]; rfl
  rw [Stacks.SectionRingChartMap.of_mul_eq, mul_comm, ← h1]

/-- The comparison is linear over the section ring. -/
theorem twistSectionRingShift_smul (e : ℕ) (r : sectionRing L)
    (y : twistModule (natTensorPow L e) L) :
    twistSectionRingShift L e (r • y) = r * twistSectionRingShift L e y := by
  induction r using DirectSum.induction_on with
  | zero => rw [zero_smul, zero_mul, map_zero]
  | of j x =>
      induction y using DirectSum.induction_on with
      | zero => rw [smul_zero, map_zero, mul_zero]
      | of m t => exact twistSectionRingShift_smul_of L e j m x t
      | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', mul_add]
  | add r r' hr hr' => rw [add_smul, map_add, hr, hr', add_mul]

/-- The comparison `Γ_*(X, L^{⊗ e}, L) ⟶ Γ_*(X, L)`, as a linear map over the section ring. -/
def twistSectionRingShiftLinearMap (e : ℕ) :
    twistModule (natTensorPow L e) L →ₗ[sectionRing L] sectionRing L where
  toFun := twistSectionRingShift L e
  map_add' := map_add _
  map_smul' := twistSectionRingShift_smul L e

/-- The degree-`k` component of a left inverse of the comparison: a section of `L^{⊗ k}` with
`k ≥ e` is a twisted section of `L^{⊗ e}` of degree `k - e`; the components of degree `< e` go to
zero. -/
def twistSectionRingUnshiftComponent (e k : ℕ) :
    powSections L k →+ twistModule (natTensorPow L e) L :=
  if h : e ≤ k then
    { toFun := fun ρ => DirectSum.of (twistSections (natTensorPow L e) L) (k - e)
        (ρ ≫ eqToHom ((congrArg (natTensorPow L) (Nat.add_sub_cancel' h).symm).trans
          (tpow L e (k - e)).symm))
      map_zero' := by simp
      map_add' := fun x y => by rw [Preadditive.add_comp, map_add] }
  else 0

/-- A left inverse of the comparison `Γ_*(X, L^{⊗ e}, L) ⟶ Γ_*(X, L)`. -/
def twistSectionRingUnshift (e : ℕ) : sectionRing L →+ twistModule (natTensorPow L e) L :=
  DirectSum.toAddMonoid fun k => twistSectionRingUnshiftComponent L e k

omit [Ample.IsInvertibleModule X L] in
/-- `twistSectionRingUnshift` is a left inverse of `twistSectionRingShift`. -/
theorem twistSectionRingUnshift_shift (e : ℕ) (y : twistModule (natTensorPow L e) L) :
    twistSectionRingUnshift L e (twistSectionRingShift L e y) = y := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of n t =>
      rw [twistSectionRingShift_of, twistSectionRingUnshift, DirectSum.toAddMonoid_of,
        twistSectionRingUnshiftComponent,
        dite_eq_left (Nat.le_add_right e n)]
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc, eqToHom_trans]
      exact Stacks.SectionRingProjQuasicoherent.of_twistCongr (by omega) t
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']

omit [Ample.IsInvertibleModule X L] in
/-- The comparison `Γ_*(X, L^{⊗ e}, L) ⟶ Γ_*(X, L)` is injective. -/
theorem twistSectionRingShift_injective (e : ℕ) : Function.Injective (twistSectionRingShift L e) :=
  Function.LeftInverse.injective (twistSectionRingUnshift_shift L e)


/-- The comparison raises the `ℤ`-degree by `e`. -/
theorem twistSectionRingShift_mem (e : ℕ) (i : ℤ) (x : twistModule (natTensorPow L e) L)
    (hx : x ∈ Stacks.TwistedSections.moduleGrading (natTensorPow L e) L i) :
    twistSectionRingShiftLinearMap L e x ∈
      integerGrading (S := sectionRing L) (grading L) (i + (e : ℤ)) := by
  obtain ⟨m⟩ | ⟨k⟩ := i
  · obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.mp hx
    change twistSectionRingShift L e (DirectSum.of _ m t) ∈
      integerGrading (S := sectionRing L) (grading L) _
    rw [twistSectionRingShift_of, show (Int.ofNat m : ℤ) + (e : ℤ) = ((e + m : ℕ) : ℤ) by
        rw [Int.ofNat_eq_natCast]; push_cast; ring,
      integerGrading_natCast]
    exact ⟨_, rfl⟩
  · have hx0 : x = 0 := by
      simpa [Stacks.TwistedSections.moduleGrading_negSucc] using hx
    rw [hx0, map_zero]
    exact zero_mem _

/-- Every homogeneous element of the section ring of degree `e + n d` is the image of a homogeneous
twisted section of degree `n d`; no power of `g` is needed. -/
theorem twistSectionRingShift_exists_preimage (e : ℕ) {d : ℕ} (g : sectionRing L) (n : ℕ)
    (y : sectionRing L)
    (hy : y ∈ integerGrading (S := sectionRing L) (grading L) ((e : ℤ) + n • (d : ℤ))) :
    ∃ (k : ℕ) (x : twistModule (natTensorPow L e) L),
      x ∈ Stacks.TwistedSections.moduleGrading (natTensorPow L e) L (((n + k) * d : ℕ) : ℤ) ∧
        twistSectionRingShiftLinearMap L e x = g ^ k • y := by
  rw [show (e : ℤ) + n • (d : ℤ) = ((e + n * d : ℕ) : ℤ) by push_cast; ring,
    integerGrading_natCast] at hy
  obtain ⟨y₀, rfl⟩ := hy
  refine ⟨0, DirectSum.of (twistSections (natTensorPow L e) L) (n * d)
    (y₀ ≫ eqToHom (tpow L e (n * d)).symm), ⟨_, rfl⟩, ?_⟩
  change twistSectionRingShift L e (DirectSum.of _ (n * d) _) = _
  rw [twistSectionRingShift_of, pow_zero, one_smul, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- The tensor powers of an invertible module are quasi-coherent. -/
private instance isQuasicoherent_natTensorPow (e : ℕ) : (natTensorPow L e).IsQuasicoherent :=
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

variable (hL : Stacks.Ample.IsAmple X L) {d : ℕ} (hd : 0 < d) (a : powSections L d)

/-- **The sections of `L^{⊗ e}` over `X_a` are the degree-`e` part of `Γ_*(X, L)_a`**, for `L`
ample and `a` a global section of `L^{⊗ d}` with `d > 0`: [Stacks, Tag 01PW] read in every
nonnegative degree.

It is the inverse of the division `Γ_*(X, L, L^{⊗ e})_{(a)} ⟶ Γ(X_a, L^{⊗ e})` of
`Stacks.SectionRingProjQuasicoherent.localDivision`, which is bijective by
`Stacks.SectionRingProjQuasicoherent.localDivision_injective` and
`Stacks.SectionRingProjQuasicoherent.localDivision_surjective`, followed by the identification of
`Γ_*(X, L, L^{⊗ e})_{(a)}` with the degree-`e` part of the localization of the section ring,
which is `degreeZeroShiftEquiv` along `twistSectionRingShiftLinearMap`. -/
def chartSectionsEquiv (e : ℕ) :
    Γ(natTensorPow L e, nvOpen L a) ≃+
      Stacks.GradedLocalization.gradedPiece (grading L)
        (integerGrading (S := sectionRing L) (grading L))
        (DirectSum.of (powSections L) d a) (e : ℤ) :=
  haveI : (natTensorPow L e).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  (AddEquiv.ofBijective (Stacks.SectionRingProjQuasicoherent.localDivision L (natTensorPow L e) a
      le_rfl)
    ⟨Stacks.SectionRingProjQuasicoherent.localDivision_injective L _ hL hd a,
      Stacks.SectionRingProjQuasicoherent.localDivision_surjective L _ hL hd a⟩).symm.trans
    (degreeZeroShiftEquiv (grading L) (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
      (integerGrading (S := sectionRing L) (grading L)) (twistSectionRingShiftLinearMap L e) (e : ℤ)
      (Stacks.ExternalGrading.of_mem_summand d a) (twistSectionRingShift_mem L e)
      (twistSectionRingShift_injective L e)
      (twistSectionRingShift_exists_preimage L e _))

open Stacks.SectionRingProjQuasicoherent (powMul unitSec localDivision) in
/-- On a division, the chart comparison is the induced map of localizations. -/
theorem chartSectionsEquiv_localDivision (e : ℕ)
    (z : GradedModuleDegreeZeroLocalization (grading L)
      (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
      (DirectSum.of (powSections L) d a)) :
    ((chartSectionsEquiv L hL hd a e (localDivision L (natTensorPow L e) a le_rfl z) :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) =
      LocalizedModule.map (Submonoid.powers (DirectSum.of (powSections L) d a))
        (twistSectionRingShiftLinearMap L e)
        (z : LocalizedModule.Away (DirectSum.of (powSections L) d a)
          (twistModule (natTensorPow L e) L)) := by
  simp only [chartSectionsEquiv, AddEquiv.trans_apply]
  have h : (AddEquiv.ofBijective (localDivision L (natTensorPow L e) a le_rfl)
      ⟨Stacks.SectionRingProjQuasicoherent.localDivision_injective L _ hL hd a,
        Stacks.SectionRingProjQuasicoherent.localDivision_surjective L _ hL hd a⟩).symm
      (localDivision L (natTensorPow L e) a le_rfl z) = z :=
    (AddEquiv.symm_apply_eq _).mpr rfl
  rw [h]
  rfl

omit [Ample.IsInvertibleModule X L] in
/-- The transport `L^{e + n d} = L^e ⊙ (d n)`. -/
theorem natTensorPow_eq_twistPow (e n : ℕ) :
    natTensorPow L (e + n * d) = twistPow (natTensorPow L e) L (d * n) :=
  (congrArg (natTensorPow L) (by ring)).trans (tpow L e (d * n)).symm

open Stacks.SectionRingProjQuasicoherent (powMul unitSec localDivision) in
/-- **The chart comparison on a section, read off its multiple by a power of `a`.** -/
theorem chartSectionsEquiv_eq_mk_of_powMul (e n : ℕ) (σ : Γ(natTensorPow L e, nvOpen L a))
    (ρ : powSections L (e + n * d))
    (hσ : (powMul L (natTensorPow L e) a n).app (nvOpen L a) σ =
      unitSec (ρ ≫ eqToHom (natTensorPow_eq_twistPow L e n)) (nvOpen L a)) :
    ((chartSectionsEquiv L hL hd a e σ :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (powSections L) (e + n * d) ρ)
        ⟨DirectSum.of (powSections L) d a ^ n, n, rfl⟩ := by
  set t : twistSections (natTensorPow L e) L (n * d) := ρ ≫ eqToHom (tpow L e (n * d)).symm
    with ht
  set z : GradedModuleDegreeZeroLocalization (grading L)
      (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
      (DirectSum.of (powSections L) d a) :=
    ⟨LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
      (DirectSum.of (twistSections (natTensorPow L e) L) (n * d) t)
      ⟨DirectSum.of (powSections L) d a ^ n, n, rfl⟩,
      Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree (grading L)
        (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
        (Stacks.ExternalGrading.of_mem_summand d a) n _ ⟨t, rfl⟩⟩ with hz
  have hσz : σ = localDivision L (natTensorPow L e) a le_rfl z := by
    apply (Stacks.SectionRingProjQuasicoherent.bijective_powMul_app L (natTensorPow L e) a
      le_rfl n).1
    rw [hσ, Stacks.SectionRingProjQuasicoherent.powMul_app_localDivision L (natTensorPow L e) a
      le_rfl z n t rfl]
    simp only [ht, Stacks.TwistedSections.twistCongr, Category.assoc, eqToHom_trans]
  rw [hσz, chartSectionsEquiv_localDivision, hz]
  change LocalizedModule.map _ (twistSectionRingShiftLinearMap L e) (LocalizedModule.mk _ _) = _
  rw [LocalizedModule.map_mk]
  change LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
    (twistSectionRingShift L e (DirectSum.of (twistSections (natTensorPow L e) L) (n * d) t)) _ = _
  rw [twistSectionRingShift_of, ht, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

open Stacks.SectionRingProjQuasicoherent (unitSec) in
/-- **A global section goes to the fraction with denominator one.** -/
theorem chartSectionsEquiv_unitSec (e : ℕ) (ρ : powSections L e) :
    ((chartSectionsEquiv L hL hd a e (unitSec ρ (nvOpen L a)) :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (powSections L) e ρ) 1 := by
  have h := chartSectionsEquiv_eq_mk_of_powMul L hL hd a e 0 (unitSec ρ (nvOpen L a))
    (ρ ≫ eqToHom (congrArg (natTensorPow L) (by ring : e = e + 0 * d))) (by
      simp only [Category.assoc, eqToHom_trans]
      rfl)
  rw [h, Stacks.SectionRingProjQuasicoherent.of_comp_eqToHom L (by ring : e = e + 0 * d) ρ]
  congr 1

include hL hd in
open Stacks.SectionRingProjQuasicoherent (localDivision) in
/-- Every section of `L^{⊗ e}` over `X_a` is the division of a homogeneous fraction. -/
theorem exists_eq_localDivision_mk (e : ℕ) (σ : Γ(natTensorPow L e, nvOpen L a)) :
    ∃ (n : ℕ) (t : twistSections (natTensorPow L e) L (n * d)),
      σ = localDivision L (natTensorPow L e) a le_rfl
        ⟨LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
          (DirectSum.of (twistSections (natTensorPow L e) L) (n * d) t)
          ⟨DirectSum.of (powSections L) d a ^ n, n, rfl⟩,
          Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree (grading L)
            (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
            (Stacks.ExternalGrading.of_mem_summand d a) n _ ⟨t, rfl⟩⟩ := by
  obtain ⟨z, rfl⟩ := Stacks.SectionRingProjQuasicoherent.localDivision_surjective L _ hL hd a σ
  obtain ⟨n, x, hx, hz⟩ :=
    Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree (grading L)
      (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
      (Stacks.ExternalGrading.of_mem_summand d a) z
  obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.mp hx
  exact ⟨n, t, congrArg _ (Subtype.ext hz)⟩

open Stacks.SectionRingProjQuasicoherent (localDivision) in
/-- The chart comparison on the division of a homogeneous fraction. -/
theorem chartSectionsEquiv_localDivision_mk (e n : ℕ)
    (t : twistSections (natTensorPow L e) L (n * d)) :
    ((chartSectionsEquiv L hL hd a e (localDivision L (natTensorPow L e) a le_rfl
        ⟨LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
          (DirectSum.of (twistSections (natTensorPow L e) L) (n * d) t)
          ⟨DirectSum.of (powSections L) d a ^ n, n, rfl⟩,
          Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree (grading L)
            (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
            (Stacks.ExternalGrading.of_mem_summand d a) n _ ⟨t, rfl⟩⟩) :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (twistSectionRingShift L e (DirectSum.of (twistSections (natTensorPow L e) L) (n * d) t))
        ⟨DirectSum.of (powSections L) d a ^ n, n, rfl⟩ := by
  rw [chartSectionsEquiv_localDivision]
  exact LocalizedModule.map_mk _ _ _ _

/-- Cross-multiplication in a localization at a product. -/
theorem localizedModule_mk_mul_pow_eq_of_mk_eq {R : Type*} [CommRing R] {g h Q : R} (hQ : Q = g * h)
    {x y : R} {n m : ℕ}
    (H : LocalizedModule.mk (S := Submonoid.powers g) x ⟨g ^ n, n, rfl⟩ =
      LocalizedModule.mk (S := Submonoid.powers g) y ⟨g ^ m, m, rfl⟩) :
    LocalizedModule.mk (S := Submonoid.powers Q) (h ^ n * x) ⟨Q ^ n, n, rfl⟩ =
      LocalizedModule.mk (S := Submonoid.powers Q) (h ^ m * y) ⟨Q ^ m, m, rfl⟩ := by
  rw [LocalizedModule.mk_eq] at H ⊢
  obtain ⟨⟨u, k, rfl⟩, hu⟩ := H
  refine ⟨⟨Q ^ k, k, rfl⟩, ?_⟩
  simp only [Submonoid.smul_def, smul_eq_mul] at hu ⊢
  subst hQ
  linear_combination h ^ (k + m + n) * hu

open Stacks.SectionRingProjQuasicoherent (localDivision) in
/-- **The chart comparison is natural for the inclusion `X_q ⊆ X_a` with `q = a c`.** -/
theorem chartSectionsEquiv_restrict {d' j : ℕ} (hd' : 0 < d') (q : powSections L d')
    (c : powSections L j) (hdeg : d + j = d')
    (hq : DirectSum.of (powSections L) d a * DirectSum.of (powSections L) j c =
      DirectSum.of (powSections L) d' q)
    (i : nvOpen L q ⟶ nvOpen L a) (e : ℕ) (σ : Γ(natTensorPow L e, nvOpen L a)) (m : ℕ)
    (y : sectionRing L)
    (hσ : ((chartSectionsEquiv L hL hd a e σ :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a)) y
        ⟨DirectSum.of (powSections L) d a ^ m, m, rfl⟩) :
    ((chartSectionsEquiv L hL hd' q e ((natTensorPow L e).presheaf.map i.op σ) :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d' q)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d' q) (sectionRing L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d' q))
        (DirectSum.of (powSections L) j c ^ m * y)
        ⟨DirectSum.of (powSections L) d' q ^ m, m, rfl⟩ := by
  obtain ⟨n, t, rfl⟩ := exists_eq_localDivision_mk L hL hd a e σ
  rw [chartSectionsEquiv_localDivision_mk] at hσ
  set c' := Stacks.SectionExtension.powSec L c n with hc'
  have hof : DirectSum.of (powSections L) (j * n) c' = DirectSum.of (powSections L) j c ^ n :=
    Stacks.SectionRingChartMap.of_powSec_eq_pow L c n
  have hN : j * n + n * d = n * d' := by rw [← hdeg]; ring
  have hmem : DirectSum.of (powSections L) (j * n) c' •
      DirectSum.of (twistSections (natTensorPow L e) L) (n * d) t ∈
      Stacks.TwistedSections.moduleGrading (natTensorPow L e) L ((n * d' : ℕ) : ℤ) :=
    ⟨Stacks.TwistedSections.twistCongr hN (Stacks.TwistedSections.gsmul c' t), by
      rw [Stacks.SectionRingProjQuasicoherent.of_twistCongr, Stacks.TwistedSections.of_smul_of]⟩
  set z' : GradedModuleDegreeZeroLocalization (grading L)
      (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
      (DirectSum.of (powSections L) d' q) :=
    ⟨LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d' q))
      (DirectSum.of (powSections L) (j * n) c' •
        DirectSum.of (twistSections (natTensorPow L e) L) (n * d) t)
      ⟨DirectSum.of (powSections L) d' q ^ n, n, rfl⟩,
      Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree (grading L)
        (Stacks.TwistedSections.moduleGrading (natTensorPow L e) L)
        (Stacks.ExternalGrading.of_mem_summand d' q) n _ hmem⟩ with hz'
  rw [← Stacks.SectionRingProjQuasicoherent.localDivision_change L (natTensorPow L e) a q c'
    le_rfl le_rfl i n n (by rw [← hdeg]; ring) (by rw [hof, ← mul_pow, hq]) _ z' t rfl rfl,
    chartSectionsEquiv_localDivision, hz']
  change LocalizedModule.map _ (twistSectionRingShiftLinearMap L e) (LocalizedModule.mk _ _) = _
  rw [LocalizedModule.map_mk]
  change LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d' q))
    (twistSectionRingShift L e (DirectSum.of (powSections L) (j * n) c' •
      DirectSum.of (twistSections (natTensorPow L e) L) (n * d) t)) _ = _
  rw [twistSectionRingShift_smul, hof]
  exact (localizedModule_mk_mul_pow_eq_of_mk_eq hq.symm hσ.symm).symm

/-- **The chart comparison is semilinear over the chart ring map.** -/
theorem chartSectionsEquiv_chartRingMap_smul (e : ℕ)
    (y : HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a))
    (σ : Γ(natTensorPow L e, nvOpen L a)) :
    ((chartSectionsEquiv L hL hd a e
        (Stacks.SectionRingChartMap.chartRingMap L a le_rfl y • σ) :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) =
      y.val • ((chartSectionsEquiv L hL hd a e σ :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) := by
  obtain ⟨z, rfl⟩ := Stacks.SectionRingProjQuasicoherent.localDivision_surjective L _ hL hd a σ
  rw [← Stacks.SectionRingProjQuasicoherent.localDivision_smul, chartSectionsEquiv_localDivision,
    chartSectionsEquiv_localDivision]
  exact LinearMap.map_smul _ y.val _

/-- **The ring of functions on `X_a` is the degree-zero localization** (Stacks 01PW for `𝒪_X`). -/
def chartFunctionsEquiv :
    HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a) ≃+*
      Γ(X, nvOpen L a) :=
  RingEquiv.ofBijective (Stacks.SectionRingChartMap.chartRingMap L a le_rfl)
    (Stacks.SectionRingChartBijective.chartRingMap_bijective L hL hd a)

/-- The value of `chartFunctionsEquiv` is the chart ring map. -/
theorem chartFunctionsEquiv_apply
    (y : HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a)) :
    chartFunctionsEquiv L hL hd a y = Stacks.SectionRingChartMap.chartRingMap L a le_rfl y := rfl

/-- **The chart comparison is linear over the functions on `X_a`.** -/
theorem chartSectionsEquiv_smul (e : ℕ) (r : Γ(X, nvOpen L a))
    (σ : Γ(natTensorPow L e, nvOpen L a)) :
    ((chartSectionsEquiv L hL hd a e (r • σ) :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) =
      ((chartFunctionsEquiv L hL hd a).symm r).val • ((chartSectionsEquiv L hL hd a e σ :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) := by
  conv_lhs => rw [← (chartFunctionsEquiv L hL hd a).apply_symm_apply r]
  exact chartSectionsEquiv_chartRingMap_smul L hL hd a e _ σ

omit [Ample.IsInvertibleModule X L] in
/-- Twisting left multiplication by `b` is left multiplication by `b` on the tensor powers. -/
theorem twistPowMap_mulMap {k : ℕ} (b : powSections L k) (e : ℕ) : ∀ n : ℕ,
    twistPowMap L (mulMap b e) n ≫ eqToHom (tpow L (k + e) n) =
      eqToHom (tpow L e n) ≫ mulMap b (e + n) ≫
        eqToHom (congrArg (natTensorPow L) (Nat.add_assoc k e n).symm)
  | 0 => by
      change mulMap b e ≫ eqToHom rfl = eqToHom rfl ≫ mulMap b e ≫ eqToHom rfl
      simp
  | n + 1 => by
      have hw := congrArg (fun φ => φ ▷ L) (twistPowMap_mulMap b e n)
      simp only [comp_whiskerRight, eqToHom_whiskerRight] at hw
      exact hw

omit [Ample.IsInvertibleModule X L] in
/-- Under the comparison, the map of twisted sections induced by multiplication by `b` is
multiplication by `b` in the section ring. -/
theorem twistSectionRingShift_twistModuleHom_mulMap {k : ℕ} (b : powSections L k) (e : ℕ)
    (x : twistModule (natTensorPow L e) L) :
    twistSectionRingShift L (k + e)
        (Stacks.TwistedSections.twistModuleHom (L := L) (mulMap b e) x) =
      DirectSum.of (powSections L) k b * twistSectionRingShift L e x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n t =>
      rw [Stacks.TwistedSections.twistModuleHom_of, twistSectionRingShift_of,
        twistSectionRingShift_of,
        Stacks.TwistedSections.twistSectionsMap, Category.assoc, twistPowMap_mulMap,
        ← Stacks.SectionRingChartMap.of_mul_eq, Stacks.GradedSections.mul_def,
        ← Category.assoc, ← Category.assoc,
        Stacks.SectionRingProjQuasicoherent.of_comp_eqToHom L (Nat.add_assoc k e n).symm,
        Category.assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]

/-- **The chart comparison is multiplicative**: multiplying by a global section `b` of
`L^{⊗ k}` is multiplying by `b` in the localization. -/
theorem chartSectionsEquiv_mulMap {k : ℕ} (b : powSections L k) (e : ℕ)
    (σ : Γ(natTensorPow L e, nvOpen L a)) :
    ((chartSectionsEquiv L hL hd a (k + e) ((mulMap b e).app (nvOpen L a) σ) :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          ((k + e : ℕ) : ℤ)) :
        LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) =
      DirectSum.of (powSections L) k b • ((chartSectionsEquiv L hL hd a e σ :
        Stacks.GradedLocalization.gradedPiece (grading L)
          (integerGrading (S := sectionRing L) (grading L)) (DirectSum.of (powSections L) d a)
          (e : ℤ)) : LocalizedModule.Away (DirectSum.of (powSections L) d a) (sectionRing L)) := by
  obtain ⟨n, t, rfl⟩ := exists_eq_localDivision_mk L hL hd a e σ
  set t' := Stacks.TwistedSections.twistSectionsMap (L := L) (mulMap b e) (n * d) t
  rw [← Stacks.SectionRingProjQuasicoherent.localDivision_naturality L _ (mulMap b e) a le_rfl _
    ⟨LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
      (DirectSum.of (twistSections (natTensorPow L (k + e)) L) (n * d) t')
      ⟨DirectSum.of (powSections L) d a ^ n, n, rfl⟩,
      Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree (grading L)
        (Stacks.TwistedSections.moduleGrading (natTensorPow L (k + e)) L)
        (Stacks.ExternalGrading.of_mem_summand d a) n _ ⟨t', rfl⟩⟩ (by
      change _ = LocalizedModule.map _ _ (LocalizedModule.mk _ _)
      rw [LocalizedModule.map_mk, Stacks.TwistedSections.twistModuleLinearMap_apply,
        Stacks.TwistedSections.twistModuleHom_of]),
    chartSectionsEquiv_localDivision_mk, chartSectionsEquiv_localDivision_mk,
    LocalizedModule.smul'_mk]
  congr 1
  rw [smul_eq_mul, ← twistSectionRingShift_twistModuleHom_mulMap,
    Stacks.TwistedSections.twistModuleHom_of]

end Stacks.Algebraization.SectionRingCone
end
