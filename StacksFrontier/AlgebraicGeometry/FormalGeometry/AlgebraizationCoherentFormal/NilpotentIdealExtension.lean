module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AnnihilatedComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ClopenCriterion

/-!
# Extension to `X` over a nilpotent ideal

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`.  When `I` is nilpotent every object of
`Coh(U, I𝒪_U)` extends to `X`.  Indeed, if `Iᵗ = 0` then the ideal sheaf `I𝒪_U` has `t`-th
power zero on every affine open, so every morphism of `Coh(U, I𝒪_U)` has kernel and cokernel
annihilated by a power of `I𝒪_U`; applied to the morphism to the zero system, [Stacks, Tag 0EIU]
part (1) says the system extends to `X` exactly when the zero system does, and the zero system
is the restriction of the zero system on `X`.

The second result is the ring-theoretic input that produces this situation: over a Noetherian
local ring, an ideal `I ⊆ 𝔪` with `cd(A, I) ≤ 0` is nilpotent.  By the clopen criterion of
[Stacks, Tag 0DX7] the zero locus `V(I)` is open and closed; it contains the closed point, and an
open subset of the spectrum of a local ring containing the closed point is everything, so `I`
lies in the nilradical and, being finitely generated, is nilpotent.

## Main results

* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_ideal_pow_eq_bot` — a morphism of
  systems along an ideal sheaf whose `t`-th power vanishes on every affine open has kernel and
  cokernel annihilated by a power of it.
* `Stacks.Algebraization.extendsToX_of_isZero` — a zero system on `U` extends to `X`.
* `Stacks.Algebraization.extendsToX_of_pow_eq_bot` — over a nilpotent ideal every object of
  `Coh(U, I𝒪_U)` extends to `X`.
* `Stacks.Algebraization.exists_pow_eq_bot_of_cohomologicalDimension_le_zero` — over a Noetherian
  local ring an ideal inside the maximal ideal of nonpositive cohomological dimension is
  nilpotent.

## References

* [Stacks Project, Tag 0EIU](https://stacks.math.columbia.edu/tag/0EIU)
* [Stacks Project, Tag 0EIM](https://stacks.math.columbia.edu/tag/0EIM)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u

namespace Stacks.Algebraization

/-- If the `t`-th power of an ideal sheaf vanishes on every affine open, with `t > 0`, then every
morphism of inverse systems of modules has its levelwise kernels and cokernels annihilated by a
power of that ideal sheaf. -/
public theorem isKernelCokernelAnnihilatedByPower_of_ideal_pow_eq_bot {X : Scheme.{u}}
    (K : X.IdealSheafData) {t : ℕ} (ht : 0 < t) (hK : ∀ V : X.affineOpens, K.ideal V ^ t = ⊥)
    {F G : ℕᵒᵖ ⥤ X.Modules} (α : F ⟶ G) : IsKernelCokernelAnnihilatedByPower K α := by
  have hM (M : X.Modules) : idealPowerMultiple K t M = ⊥ :=
    idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun V r hr x => by
      rw [hK V, Ideal.mem_bot] at hr
      rw [hr, zero_smul]
  exact IsKernelCokernelAnnihilatedByPower.of_eq_bot ht fun _ => ⟨hM _, hM _⟩

variable (S : AlgebraizationSituation.{u})

/-- If `Iᵗ = 0` then the `t`-th power of the ideal sheaf `I𝒪_U` vanishes on every affine open of
`U`. -/
public theorem idealOnOpen_ideal_pow_eq_bot {t : ℕ} (ht : S.I ^ t = ⊥)
    (V : S.U.toScheme.affineOpens) : (idealOnOpen S).ideal V ^ t = ⊥ := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ofIdealTop_ideal]
  refine le_bot_iff.mp ((Ideal.le_comap_pow _ t).trans ?_)
  rw [← Ideal.map_pow, ← Ideal.map_pow, ht, Ideal.map_bot, Ideal.map_bot]
  exact (Ideal.comap_bot_of_injective _
    ((ConcreteCategory.bijective_of_isIso (S.U.ι.appIso V).inv).1)).le

/-- A zero object of `Coh(U, I𝒪_U)` extends to `X`: it is the restriction of the zero system
on `X`. -/
public theorem extendsToX_of_isZero
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) (hF : IsZero F) :
    ExtendsToX S F := by
  let G : Stacks.Coherent.CoherentAdicSystems S.Yι.ker := 0
  have hG : IsZero (G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι) :=
    Functor.isZero _ fun n => Functor.map_isZero (Scheme.Modules.restrictFunctor S.U.ι)
      ((Functor.map_isZero (ObjectProperty.ι _) (isZero_zero _)).obj n)
  exact ⟨G, ⟨hG.iso (Functor.map_isZero (ObjectProperty.ι _) hF)⟩⟩

/-- **Extension over a nilpotent ideal.**  In Situation 0EHC, if `Iᵗ = 0` for some `t`, then
every object of `Coh(U, I𝒪_U)` extends to `X`.

Every morphism of `Coh(U, I𝒪_U)` then has kernel and cokernel annihilated by a power of `I𝒪_U`,
so [Stacks, Tag 0EIU] part (1) applied to the morphism to the zero system reduces the claim to
the zero system, which extends by `Stacks.Algebraization.extendsToX_of_isZero`. -/
public theorem extendsToX_of_pow_eq_bot {t : ℕ} (ht : S.I ^ t = ⊥)
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) :
    ExtendsToX S F := by
  have ht' : S.I ^ (t + 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ t)).trans ht.le)
  have hK : ∀ V : S.U.toScheme.affineOpens, (S.Yι.ker.comap S.U.ι).ideal V ^ (t + 1) = ⊥ := by
    rw [← idealOnOpen_eq_ker_comap]
    exact idealOnOpen_ideal_pow_eq_bot S ht'
  let α : F ⟶ 0 := 0
  exact (extendsToX_iff_extendsToX_of_isKernelCokernelAnnihilatedByPower S α
    (isKernelCokernelAnnihilatedByPower_of_ideal_pow_eq_bot _ t.succ_pos hK α.hom)).mpr
    (extendsToX_of_isZero S 0 (isZero_zero _))

end Stacks.Algebraization

namespace Stacks.LocalCohomology

/-- Over a Noetherian local ring, an ideal contained in the maximal ideal whose cohomological
dimension is at most zero is nilpotent.

By the clopen criterion of [Stacks, Tag 0DX7], `V(I)` is open and closed.  It contains the closed
point, and every prime of a local ring specializes to the closed point, so the open set `V(I)` is
the whole spectrum; hence `I` lies in the nilradical, and a finitely generated ideal inside the
nilradical is nilpotent. -/
public theorem exists_pow_eq_bot_of_cohomologicalDimension_le_zero (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    (hfg : I.FG) (h : cohomologicalDimension A I hfg ≤ 0) : ∃ t : ℕ, I ^ t = ⊥ := by
  have hclopen := (isClopen_zeroLocus_iff_cohomologicalDimension_le_zero A I hfg).mp h
  have hclosed : IsLocalRing.closedPoint A ∈ PrimeSpectrum.zeroLocus (I : Set A) := hI
  have huniv : PrimeSpectrum.zeroLocus (I : Set A) = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    have hsp : p ⤳ IsLocalRing.closedPoint A :=
      (PrimeSpectrum.le_iff_specializes p _).mp (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
    exact hsp.mem_open hclopen.isOpen hclosed
  have hnil : I ≤ (⊥ : Ideal A).radical :=
    (PrimeSpectrum.zeroLocus_eq_univ_iff (I : Set A)).mp huniv
  obtain ⟨t, ht⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hnil hfg
  exact ⟨t, le_bot_iff.mp ht⟩

end Stacks.LocalCohomology

end
