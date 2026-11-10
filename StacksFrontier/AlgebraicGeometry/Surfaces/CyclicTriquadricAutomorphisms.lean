module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmplePredicateBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingSectionDivisor
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCube.TriquadraticInvolution
public import StacksFrontier.AlgebraicGeometry.Surfaces.AutomorphismIntersectionGrowth
public import StacksFrontier.AlgebraicGeometry.Surfaces.CyclicTriquadric
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.SurfaceEulerCharacteristic

/-!
# A surface with an automorphism of infinite order and unbounded intersection numbers

Let `X ⊂ ℙ¹ × ℙ¹ × ℙ¹` over `ℚ` be the cyclically symmetric surface of tridegree `(2, 2, 2)`
of `AlgebraicGeometry.projectiveLineCube.cyclicTriquadric`: an integral surface, proper over
`ℚ`, on which `𝒪(1, 1, 1)|_X` is ample. Write `𝓗_i` for the pullback of `𝒪(1)` along the
`i`-th projection, `ρ` for the cyclic permutation of the factors and `σ` for the covering
involution of the projection to the first two factors. Then

* `ρ^*𝓗_i ≅ 𝓗_{i+1}` (the cyclic permutation moves the pencils),
* `σ^*𝓗_0 ≅ 𝓗_0`, `σ^*𝓗_1 ≅ 𝓗_1` and `σ^*𝓗_2 ⊗ 𝓗_2² ≅ (𝓗_0² ⊗ 𝓗_1²) ⊗ 𝓗_2`,
* `𝒪(1, 1, 1)|_X ≅ (𝓗_0 ⊗ 𝓗_1) ⊗ 𝓗_2`, the pullback along the closed immersion commuting with
  tensor products ([Stacks, Tag 01CD]),

so `X` carries the numerical relations `AlgebraicGeometry.WehlerRelations`. Consequently
`τ = σ ∘ ρ` is an automorphism of `X` over `ℚ` of infinite order, and the ample modules
`𝓐 = 𝒪(1, 1, 1)|_X` and `(τ^n)^*𝓐` have the same Hilbert function and the same
self-intersection while `(𝓐 · (τ^n)^*𝓐)` grows without bound. By the formula
`(𝓝 · 𝓛) = χ(𝓝 ⊗ 𝓛) - χ(𝓝) - χ(𝓛) + χ(𝒪)` the Euler characteristic of `𝓐 ⊗ (τ^n)^*𝓐` grows
without bound too. A section of `𝓐` not vanishing at a point makes `𝓐` and its pullbacks the
sheaves of effective Cartier divisors.

This is the content of [Stacks, Tag 0DSR]: on a projective surface over a field there is no a
priori bound on the Hilbert polynomial of `𝓝 ⊗ 𝓛` in terms of the Hilbert polynomials of the
ample invertible modules `𝓝` and `𝓛`, nor on `H₁ · H₂` in terms of `H₁ · H₁` and `H₂ · H₂` for
ample effective Cartier divisors `H₁`, `H₂`; and a surface over a field can have an infinite
discrete group of automorphisms.

## Main definitions

* `AlgebraicGeometry.projectiveLineCube.cyclicTriquadricInvolution`: the covering involution `σ`.
* `AlgebraicGeometry.projectiveLineCube.cyclicTriquadricAutomorphism`: `τ = σ ∘ ρ`.

## Main results

* `AlgebraicGeometry.projectiveLineCube.wehlerRelations_cyclicTriquadric`: the relations.
* `AlgebraicGeometry.WehlerRelations.not_exists_hilbertFunction_bound` and
  `AlgebraicGeometry.WehlerRelations.not_exists_intersectionNumber_bound`: no bound, on any
  surface with Wehler relations.
* `AlgebraicGeometry.exists_surface_not_bounded`: **[Stacks, Tag 0DSR]**.

## Implementation notes

The remark's first sentence says that the boundedness argument in the proof of
[Stacks, Tag 0DSQ] fails for moduli of surfaces and that the corresponding statement is false;
this concerns a moduli stack of surfaces, which is not constructed here, and is not formalized.
What is formalized of it is the reason the remark gives: a surface over a field whose group of
automorphisms over the field is infinite, generated in part by an automorphism of infinite
order. The surface is a `(2, 2, 2)`-hypersurface in `ℙ¹ × ℙ¹ × ℙ¹` over `ℚ`; such a surface is a
K3 surface when it is smooth, but smoothness is not proved here, and the statement only asserts
what is proved: integral, proper over `ℚ`, of dimension two and with an ample invertible module.

A Hilbert polynomial is recorded by its values at the natural numbers,
`AlgebraicGeometry.hilbertFunction`, which determine it. An effective Cartier divisor `H` is
ample when `𝒪_X(H)` is, and `H₁ · H₂` is the intersection number of `𝒪_X(H₁)` and `𝒪_X(H₂)`.

## References

* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace WehlerRelations

variable {k : Type u} [Field k] {S : Scheme.{u}} {p : S ⟶ Spec (.of k)} [IsProper p]
  [IsIntegral S] {hS : topologicalKrullDim S = (2 : ℕ)} {H : Fin 3 → S.Modules}
  [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (H i)] {A : S.Modules}
  [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A] {ρ σ : Aut S}

/-- **The automorphisms over `k` of a surface with Wehler relations form an infinite set**: the
powers of `τ = σ ∘ ρ` are pairwise distinct. -/
theorem infinite_setOf_comp_eq (h : WehlerRelations k p hS H A ρ σ) :
    {g : Aut S | g.asIso.hom ≫ p = p}.Infinite := by
  have hinj : Function.Injective fun n : ℕ => (σ * ρ) ^ n := by
    refine injective_pow_iff_not_isOfFinOrder.mpr fun hfin => ?_
    obtain ⟨n, hn, h1⟩ := (isOfFinOrder_iff_pow_eq_one).mp hfin
    exact h.pow_ne_one hn h1
  exact Set.infinite_of_injective_forall_mem hinj fun n => h.pow_hom_comp n

/-- The pullback of the ample module `𝓐` along `τ^n` is ample with the self-intersection of `𝓐`,
and `(𝓐 · (τ^n)^*𝓐) ≥ (𝓐 · 𝓐) + n`. -/
private theorem pow_pullback_isAmple_and_intersectionNumber
    (h : WehlerRelations k p hS H A ρ σ) (n : ℕ) :
    Scheme.Modules.IsAmple S ((Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj A) ∧
      intersectionNumber k p (𝟙 S) 2 hS.le
          ![(Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj A,
        (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj A] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] ∧
      intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] + n ≤
        intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj A] := by
  have : IsIso ((σ * ρ) ^ n).asIso.hom := @Iso.isIso_hom _ _ S S _
  obtain ⟨hamp, hself⟩ :=
    isAmple_pullback_and_intersectionNumber_eq k p hS _ (h.pow_hom_comp n) A h.isAmple
  exact ⟨hamp, hself, h.intersectionNumber_add_le_pow_pullback n⟩

/-- **Ample effective Cartier divisors with fixed self-intersection and large intersection
number.** If the ample module `𝓐` of a surface with Wehler relations has a global section not
vanishing at some point, then for every `N` there are ample effective Cartier divisors `D₁`,
`D₂` with `D₁ · D₁ = D₂ · D₂ = (𝓐 · 𝓐)` and `N < D₁ · D₂`: `𝒪(D₁) ≅ 𝓐` and
`𝒪(D₂) ≅ (τ^n)^*𝓐` for large `n`. -/
theorem exists_isEffectiveCartierDivisor_intersectionNumber_gt
    (h : WehlerRelations k p hS H A ρ σ) {s : Γ(A, ⊤)} {y : S}
    (hy : y ∈ Stacks.Ample.nonvanishingLocus A s) (N : ℤ) :
    ∃ (D₁ D₂ : S.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor D₁)
      (_ : Stacks.Divisors.IsEffectiveCartierDivisor D₂),
      Scheme.Modules.IsAmple S (Stacks.Divisors.divisorSheaf D₁) ∧
      Scheme.Modules.IsAmple S (Stacks.Divisors.divisorSheaf D₂) ∧
      intersectionNumber k p (𝟙 S) 2 hS.le
          ![Stacks.Divisors.divisorSheaf D₁, Stacks.Divisors.divisorSheaf D₁] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] ∧
      intersectionNumber k p (𝟙 S) 2 hS.le
          ![Stacks.Divisors.divisorSheaf D₂, Stacks.Divisors.divisorSheaf D₂] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] ∧
      N < intersectionNumber k p (𝟙 S) 2 hS.le
          ![Stacks.Divisors.divisorSheaf D₁, Stacks.Divisors.divisorSheaf D₂] := by
  obtain ⟨n, hn⟩ := exists_nat_gt (N - intersectionNumber k p (𝟙 S) 2 hS.le ![A, A])
  obtain ⟨hamp, hself, hgrow⟩ := h.pow_pullback_isAmple_and_intersectionNumber n
  have : IsIso ((σ * ρ) ^ n).asIso.hom := @Iso.isIso_hom _ _ S S _
  obtain ⟨D₁, hD₁, ⟨e₁⟩⟩ := exists_isEffectiveCartierDivisor_iso_of_mem_nonvanishingLocus A s hy
  have hy' : ((σ * ρ) ^ n).asIso.hom.base (((σ * ρ) ^ n).asIso.inv.base y) ∈
      Stacks.Ample.nonvanishingLocus A s := by
    rw [← Scheme.Hom.comp_apply, ((σ * ρ) ^ n).asIso.inv_hom_id]; exact hy
  obtain ⟨D₂, hD₂, ⟨e₂⟩⟩ := exists_isEffectiveCartierDivisor_iso_of_mem_nonvanishingLocus
    ((Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj A) _
    (Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections _ A s hy')
  have := hD₁
  have := hD₂
  refine ⟨D₁, D₂, hD₁, hD₂, Scheme.Modules.isAmple_of_iso e₁.symm h.isAmple,
    Scheme.Modules.isAmple_of_iso e₂.symm hamp, ?_, ?_, ?_⟩
  · rw [intersectionNumber_vecCons_congr_left k p hS.le _ e₁,
      intersectionNumber_vecCons_congr_right k p hS.le _ e₁]
  · rw [intersectionNumber_vecCons_congr_left k p hS.le _ e₂,
      intersectionNumber_vecCons_congr_right k p hS.le _ e₂, hself]
  · rw [intersectionNumber_vecCons_congr_left k p hS.le _ e₁,
      intersectionNumber_vecCons_congr_right k p hS.le _ e₂]
    linarith

/-- **No bound on `H₁ · H₂` in terms of `H₁ · H₁` and `H₂ · H₂`** for ample effective Cartier
divisors on a surface with Wehler relations whose ample module has a section not vanishing at
some point. -/
theorem not_exists_intersectionNumber_bound (h : WehlerRelations k p hS H A ρ σ)
    {s : Γ(A, ⊤)} {y : S} (hy : y ∈ Stacks.Ample.nonvanishingLocus A s) :
    ¬ ∃ Φ : ℤ → ℤ → ℤ, ∀ (H₁ H₂ : S.IdealSheafData)
      [Stacks.Divisors.IsEffectiveCartierDivisor H₁] [Stacks.Divisors.IsEffectiveCartierDivisor H₂],
      Scheme.Modules.IsAmple S (Stacks.Divisors.divisorSheaf H₁) →
      Scheme.Modules.IsAmple S (Stacks.Divisors.divisorSheaf H₂) →
        intersectionNumber k p (𝟙 S) 2 hS.le
            ![Stacks.Divisors.divisorSheaf H₁, Stacks.Divisors.divisorSheaf H₂] ≤
          Φ (intersectionNumber k p (𝟙 S) 2 hS.le
              ![Stacks.Divisors.divisorSheaf H₁, Stacks.Divisors.divisorSheaf H₁])
            (intersectionNumber k p (𝟙 S) 2 hS.le
              ![Stacks.Divisors.divisorSheaf H₂, Stacks.Divisors.divisorSheaf H₂]) := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨D₁, D₂, hD₁, hD₂, hA₁, hA₂, h₁, h₂, hlt⟩ :=
    h.exists_isEffectiveCartierDivisor_intersectionNumber_gt hy
      (Φ (intersectionNumber k p (𝟙 S) 2 hS.le ![A, A])
        (intersectionNumber k p (𝟙 S) 2 hS.le ![A, A]))
  have := hΦ D₁ D₂ hA₁ hA₂
  rw [h₁, h₂] at this
  exact absurd this (not_le.mpr hlt)

/-- **No bound on the Hilbert polynomial of `𝓝 ⊗ 𝓛` in terms of those of `𝓝` and `𝓛`** for
ample invertible modules on a surface with Wehler relations: `𝓐` and `(τ^n)^*𝓐` have the
Hilbert function of `𝓐`, while `χ(𝓐 ⊗ (τ^n)^*𝓐) = (𝓐 · (τ^n)^*𝓐) + 2 χ(𝓐) - χ(𝒪)` is
unbounded. -/
theorem not_exists_hilbertFunction_bound (h : WehlerRelations k p hS H A ρ σ) :
    ¬ ∃ Φ : (ℕ → ℤ) → (ℕ → ℤ) → ℕ → ℤ, ∀ (N L : S.Modules)
      [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N]
      [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L],
      Scheme.Modules.IsAmple S N → Scheme.Modules.IsAmple S L → ∀ n : ℕ,
        hilbertFunction k p (Scheme.Modules.tensorObj N L) n ≤
          Φ (hilbertFunction k p N) (hilbertFunction k p L) n := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (Φ (hilbertFunction k p A) (hilbertFunction k p A) 1 -
    2 * hilbertFunction k p A 1 + hilbertFunction k p A 0 -
    intersectionNumber k p (𝟙 S) 2 hS.le ![A, A])
  set g := (σ * ρ) ^ n with hg
  have hgp := h.pow_hom_comp n
  have : IsIso g.asIso.hom := @Iso.isIso_hom _ _ S S g.asIso
  obtain ⟨hamp, -, hgrow⟩ := h.pow_pullback_isAmple_and_intersectionNumber n
  have hB := hilbertFunction_pullback_of_isIso k p A g.asIso.hom hgp
  have hbound := hΦ A ((Scheme.Modules.pullback g.asIso.hom).obj A) h.isAmple hamp 1
  rw [hB, hilbertFunction_one] at hbound
  have hAB := intersectionNumber_two_eq_eulerCharacteristic k p hS.le
    ![A, (Scheme.Modules.pullback g.asIso.hom).obj A]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hAB
  have hB1 := congrFun hB 1
  rw [hilbertFunction_one, hilbertFunction_one] at hB1
  rw [hilbertFunction_one, hilbertFunction_zero] at hn
  linarith

end WehlerRelations

namespace projectiveLineCube

/-- The closed immersion of the cyclically symmetric triquadric into `ℙ¹ × ℙ¹ × ℙ¹` over `ℚ`. -/
abbrev cyclicTriquadricι : cyclicTriquadric ⟶ projectiveLineCube (Spec (.of ℚ)) :=
  triquadraticSurfaceι cyclicTriquadricCoefficients (Spec (.of ℚ))

/-- The structure morphism of the cyclically symmetric triquadric over `ℚ`. -/
abbrev cyclicTriquadricToBase : cyclicTriquadric ⟶ Spec (.of ℚ) :=
  triquadraticSurfaceToBase cyclicTriquadricCoefficients (Spec (.of ℚ))

/-- The pencil `𝓗_i`, the restriction of `pr_i^*𝒪(1)` to the cyclically symmetric triquadric. -/
abbrev cyclicTriquadricPencil (i : Fin 3) : cyclicTriquadric.Modules :=
  (Scheme.Modules.pullback cyclicTriquadricι).obj (lineBundle (Spec (.of ℚ)) i)

/-- The ample module `𝒪(1, 1, 1)|_X` of the cyclically symmetric triquadric. -/
abbrev cyclicTriquadricAmple : cyclicTriquadric.Modules :=
  (Scheme.Modules.pullback cyclicTriquadricι).obj (twist (Spec (.of ℚ)) 1 1 1)

/-- **The covering involution `σ` of the cyclically symmetric triquadric**, exchanging the two
points of the fibres of the projection to the first two factors. -/
abbrev cyclicTriquadricInvolution : cyclicTriquadric ≅ cyclicTriquadric :=
  triquadraticSurfaceInvolutionIso (Spec (.of ℚ)) cyclicTriquadricCoefficients
    generatesStalks_triquadraticCoefficient_cyclicTriquadricCoefficients

/-- **The cyclic permutation moves the pencils**: `ρ^*𝓗_i ≅ 𝓗_{i+1}`, since `ρ` is the
restriction of the cyclic permutation of the factors of `ℙ¹ × ℙ¹ × ℙ¹`. -/
def cyclicTriquadricRotationPencilIso (i : Fin 3) :
    (Scheme.Modules.pullback cyclicTriquadricRotation.hom).obj (cyclicTriquadricPencil i) ≅
      cyclicTriquadricPencil (i + 1) :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (surfaceRotation_hom_ι _ _)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (rotationPullbackLineBundleIso _ i)

/-- `𝒪(1, 1, 1)|_X ≅ (𝓗_0 ⊗ 𝓗_1) ⊗ 𝓗_2`: restriction commutes with tensor products
([Stacks, Tag 01CD]). -/
def cyclicTriquadricAmpleIso :
    cyclicTriquadricAmple ≅
      Scheme.Modules.tensorObj
        (Scheme.Modules.tensorObj (cyclicTriquadricPencil 0) (cyclicTriquadricPencil 1))
        (cyclicTriquadricPencil 2) :=
  ((Stacks.RingedSpace.comparisonBifunctorIso cyclicTriquadricι.toLRSHom.toShHom).app
      (Scheme.Modules.tensorObj (lineBundle _ 0) (lineBundle _ 1), lineBundle _ 2) :
    cyclicTriquadricAmple ≅
      Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback cyclicTriquadricι).obj
          (Scheme.Modules.tensorObj (lineBundle _ 0) (lineBundle _ 1)))
        (cyclicTriquadricPencil 2)) ≪≫
    Scheme.Modules.tensorObjCongr
      ((Stacks.RingedSpace.comparisonBifunctorIso cyclicTriquadricι.toLRSHom.toShHom).app
        (lineBundle _ 0, lineBundle _ 1) :
        (Scheme.Modules.pullback cyclicTriquadricι).obj
          (Scheme.Modules.tensorObj (lineBundle _ 0) (lineBundle _ 1)) ≅
        Scheme.Modules.tensorObj (cyclicTriquadricPencil 0) (cyclicTriquadricPencil 1))
      (Iso.refl _)

/-- `M|_X ≅ (𝓗_0 ⊗ 𝓗_0) ⊗ (𝓗_1 ⊗ 𝓗_1)` for the module `M = 𝓗_0² ⊗ 𝓗_1²` of the coefficients
([Stacks, Tag 01CD]). -/
def cyclicTriquadricBiquadraticIso :
    (Scheme.Modules.pullback cyclicTriquadricι).obj (biquadraticModule (Spec (.of ℚ))) ≅
      Scheme.Modules.tensorObj
        (Scheme.Modules.tensorObj (cyclicTriquadricPencil 0) (cyclicTriquadricPencil 0))
        (Scheme.Modules.tensorObj (cyclicTriquadricPencil 1) (cyclicTriquadricPencil 1)) :=
  ((Stacks.RingedSpace.comparisonBifunctorIso cyclicTriquadricι.toLRSHom.toShHom).app
      (lineBundleSq _ 0, lineBundleSq _ 1) :
    (Scheme.Modules.pullback cyclicTriquadricι).obj (biquadraticModule (Spec (.of ℚ))) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback cyclicTriquadricι).obj (lineBundleSq _ 0))
        ((Scheme.Modules.pullback cyclicTriquadricι).obj (lineBundleSq _ 1))) ≪≫
    Scheme.Modules.tensorObjCongr
      ((Stacks.RingedSpace.comparisonBifunctorIso cyclicTriquadricι.toLRSHom.toShHom).app
        (lineBundle _ 0, lineBundle _ 0) :
        (Scheme.Modules.pullback cyclicTriquadricι).obj (lineBundleSq _ 0) ≅
        Scheme.Modules.tensorObj (cyclicTriquadricPencil 0) (cyclicTriquadricPencil 0))
      ((Stacks.RingedSpace.comparisonBifunctorIso cyclicTriquadricι.toLRSHom.toShHom).app
        (lineBundle _ 1, lineBundle _ 1) :
        (Scheme.Modules.pullback cyclicTriquadricι).obj (lineBundleSq _ 1) ≅
        Scheme.Modules.tensorObj (cyclicTriquadricPencil 1) (cyclicTriquadricPencil 1))

/-- **The cyclically symmetric triquadric carries the Wehler relations** for its three pencils,
the ample module `𝒪(1, 1, 1)|_X`, the cyclic permutation `ρ` and the covering involution `σ`. -/
theorem wehlerRelations_cyclicTriquadric :
    WehlerRelations ℚ cyclicTriquadricToBase topologicalKrullDim_cyclicTriquadric
      cyclicTriquadricPencil cyclicTriquadricAmple
      (Aut.of cyclicTriquadricRotation) (Aut.of cyclicTriquadricInvolution) :=
  WehlerRelations.of_isos_of_twist
    (surfaceRotation_hom_toBase _ _)
    (triquadraticSurfaceInvolution_toBase _ _ _)
    (isAmple_pullback_twist_one_one_one _ _)
    cyclicTriquadricAmpleIso
    cyclicTriquadricRotationPencilIso
    (triquadraticSurfaceInvolutionLineBundleIso _ _ _ 0 (by decide))
    (triquadraticSurfaceInvolutionLineBundleIso _ _ _ 1 (by decide))
    (triquadraticSurfaceInvolutionTwistIso _ _ _ ≪≫
      Scheme.Modules.tensorObjCongr cyclicTriquadricBiquadraticIso (Iso.refl _))

/-- `𝒪(1, 1, 1)|_X` has a global section not vanishing at some point: the restriction of
`x₀ y₀ z₀`, at a point of the chart `x₀ y₀ z₀ ≠ 0`. -/
theorem exists_mem_nonvanishingLocus_cyclicTriquadric :
    ∃ (s : Γ(cyclicTriquadricAmple, ⊤))
      (y : cyclicTriquadric), y ∈ Stacks.Ample.nonvanishingLocus _ s := by
  obtain ⟨y, hy⟩ := exists_forall_mem_surfaceChart
  have h1 : cyclicTriquadricι y ∈ (Stacks.SheafOfModules.nonvanishingOpen
      (X := (projectiveLineCube (Spec (.of ℚ))).toRingedSpace) (twist _ 1 1 1)
      (coordinateMonomial _ 0 0 0) : Set _) := by
    rw [nonvanishingOpen_coordinateMonomial]
    exact hy originChart
  rw [Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval] at h1
  exact ⟨_, y,
    Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections cyclicTriquadricι _ _
      h1⟩

/-- The automorphisms of the cyclically symmetric triquadric over `ℚ` form an infinite set. -/
theorem infinite_setOf_comp_cyclicTriquadricToBase :
    {g : Aut cyclicTriquadric |
      g.asIso.hom ≫ cyclicTriquadricToBase = cyclicTriquadricToBase}.Infinite :=
  wehlerRelations_cyclicTriquadric.infinite_setOf_comp_eq

/-- **The automorphism `τ = σ ∘ ρ`** of the cyclically symmetric triquadric. -/
def cyclicTriquadricAutomorphism : Aut cyclicTriquadric :=
  HMul.hMul (α := Aut cyclicTriquadric) (β := Aut cyclicTriquadric)
    (Aut.of cyclicTriquadricInvolution)
    (Aut.of cyclicTriquadricRotation)

/-- `τ` is an automorphism over `ℚ`. -/
theorem cyclicTriquadricAutomorphism_hom_comp :
    cyclicTriquadricAutomorphism.asIso.hom ≫ cyclicTriquadricToBase = cyclicTriquadricToBase := by
  have h := wehlerRelations_cyclicTriquadric.pow_hom_comp 1
  rw [pow_one] at h
  exact h

/-- **`τ` has infinite order.** -/
theorem not_isOfFinOrder_cyclicTriquadricAutomorphism :
    ¬ IsOfFinOrder cyclicTriquadricAutomorphism := fun hfin =>
  have ⟨_, hn, h1⟩ := (isOfFinOrder_iff_pow_eq_one).mp hfin
  wehlerRelations_cyclicTriquadric.pow_ne_one hn h1

/-- **No bound on the Hilbert polynomial of `𝓝 ⊗ 𝓛`** in terms of those of the ample invertible
modules `𝓝`, `𝓛` on the cyclically symmetric triquadric. -/
theorem not_exists_hilbertFunction_bound_cyclicTriquadric :
    ¬ ∃ Φ : (ℕ → ℤ) → (ℕ → ℤ) → ℕ → ℤ, ∀ (N L : cyclicTriquadric.Modules)
      [SheafOfModules.IsInvertible cyclicTriquadric.presheaf cyclicTriquadric.ringCatSheaf.2 N]
      [SheafOfModules.IsInvertible cyclicTriquadric.presheaf cyclicTriquadric.ringCatSheaf.2 L],
      Scheme.Modules.IsAmple cyclicTriquadric N → Scheme.Modules.IsAmple cyclicTriquadric L →
        ∀ n : ℕ, hilbertFunction ℚ cyclicTriquadricToBase (Scheme.Modules.tensorObj N L) n ≤
          Φ (hilbertFunction ℚ cyclicTriquadricToBase N)
            (hilbertFunction ℚ cyclicTriquadricToBase L) n :=
  wehlerRelations_cyclicTriquadric.not_exists_hilbertFunction_bound

/-- **No bound on `H₁ · H₂` in terms of `H₁ · H₁` and `H₂ · H₂`** for ample effective Cartier
divisors on the cyclically symmetric triquadric. -/
theorem not_exists_intersectionNumber_bound_cyclicTriquadric :
    ¬ ∃ Φ : ℤ → ℤ → ℤ, ∀ (H₁ H₂ : cyclicTriquadric.IdealSheafData)
      [Stacks.Divisors.IsEffectiveCartierDivisor H₁] [Stacks.Divisors.IsEffectiveCartierDivisor H₂],
      Scheme.Modules.IsAmple cyclicTriquadric (Stacks.Divisors.divisorSheaf H₁) →
      Scheme.Modules.IsAmple cyclicTriquadric (Stacks.Divisors.divisorSheaf H₂) →
        intersectionNumber ℚ cyclicTriquadricToBase (𝟙 _) 2
            topologicalKrullDim_cyclicTriquadric.le
            ![Stacks.Divisors.divisorSheaf H₁, Stacks.Divisors.divisorSheaf H₂] ≤
          Φ (intersectionNumber ℚ cyclicTriquadricToBase (𝟙 _) 2
              topologicalKrullDim_cyclicTriquadric.le
              ![Stacks.Divisors.divisorSheaf H₁, Stacks.Divisors.divisorSheaf H₁])
            (intersectionNumber ℚ cyclicTriquadricToBase (𝟙 _) 2
              topologicalKrullDim_cyclicTriquadric.le
              ![Stacks.Divisors.divisorSheaf H₂, Stacks.Divisors.divisorSheaf H₂]) := by
  obtain ⟨s, y, hy⟩ := exists_mem_nonvanishingLocus_cyclicTriquadric
  exact wehlerRelations_cyclicTriquadric.not_exists_intersectionNumber_bound hy

end projectiveLineCube

/-- **[Stacks, Tag 0DSR].** There is a surface `S` over the field `ℚ` — integral, proper over
`ℚ`, of dimension two and carrying an ample invertible module, so projective — such that

* `S` has an automorphism over `ℚ` of infinite order, and its group of automorphisms over `ℚ` is
  infinite;
* there is no a priori bound on the Hilbert polynomial of `𝓝 ⊗ 𝓛` given the Hilbert polynomials
  of the ample invertible modules `𝓝` and `𝓛`: no function `Φ` of the Hilbert functions of `𝓝`
  and `𝓛` bounds the Hilbert function of `𝓝 ⊗ 𝓛` from above;
* there is no upper bound on the intersection number `H₁ · H₂` of ample effective Cartier
  divisors in terms of `H₁ · H₁` and `H₂ · H₂`.

The surface is the cyclically symmetric `(2, 2, 2)`-hypersurface
`AlgebraicGeometry.projectiveLineCube.cyclicTriquadric` of `ℙ¹ × ℙ¹ × ℙ¹`. The remark's
statement that the boundedness argument of [Stacks, Tag 0DSQ] fails for a moduli stack of
surfaces is not formalized. -/
theorem exists_surface_not_bounded :
    ∃ (S : Scheme.{0}) (p : S ⟶ Spec (.of ℚ)) (_ : IsProper p) (_ : IsIntegral S)
      (hS : topologicalKrullDim S = (2 : ℕ)),
      (∃ A : S.Modules, ∃ (_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A),
        Scheme.Modules.IsAmple S A) ∧
      (∃ τ : Aut S, τ.asIso.hom ≫ p = p ∧ ¬ IsOfFinOrder τ) ∧
      {g : Aut S | g.asIso.hom ≫ p = p}.Infinite ∧
      (¬ ∃ Φ : (ℕ → ℤ) → (ℕ → ℤ) → ℕ → ℤ, ∀ (N L : S.Modules)
        [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N]
        [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L],
        Scheme.Modules.IsAmple S N → Scheme.Modules.IsAmple S L →
          ∀ n : ℕ, hilbertFunction ℚ p (Scheme.Modules.tensorObj N L) n ≤
            Φ (hilbertFunction ℚ p N) (hilbertFunction ℚ p L) n) ∧
      (¬ ∃ Φ : ℤ → ℤ → ℤ, ∀ (H₁ H₂ : S.IdealSheafData)
        [Stacks.Divisors.IsEffectiveCartierDivisor H₁]
        [Stacks.Divisors.IsEffectiveCartierDivisor H₂],
        Scheme.Modules.IsAmple S (Stacks.Divisors.divisorSheaf H₁) →
        Scheme.Modules.IsAmple S (Stacks.Divisors.divisorSheaf H₂) →
          intersectionNumber ℚ p (𝟙 S) 2 hS.le
              ![Stacks.Divisors.divisorSheaf H₁, Stacks.Divisors.divisorSheaf H₂] ≤
            Φ (intersectionNumber ℚ p (𝟙 S) 2 hS.le
                ![Stacks.Divisors.divisorSheaf H₁, Stacks.Divisors.divisorSheaf H₁])
              (intersectionNumber ℚ p (𝟙 S) 2 hS.le
                ![Stacks.Divisors.divisorSheaf H₂, Stacks.Divisors.divisorSheaf H₂])) :=
  ⟨_, projectiveLineCube.cyclicTriquadricToBase, inferInstance, inferInstance,
    projectiveLineCube.topologicalKrullDim_cyclicTriquadric,
    ⟨_, inferInstance, projectiveLineCube.isAmple_pullback_twist_one_one_one _ _⟩,
    ⟨_, projectiveLineCube.cyclicTriquadricAutomorphism_hom_comp,
      projectiveLineCube.not_isOfFinOrder_cyclicTriquadricAutomorphism⟩,
    projectiveLineCube.infinite_setOf_comp_cyclicTriquadricToBase,
    projectiveLineCube.not_exists_hilbertFunction_bound_cyclicTriquadric,
    projectiveLineCube.not_exists_intersectionNumber_bound_cyclicTriquadric⟩


end AlgebraicGeometry
