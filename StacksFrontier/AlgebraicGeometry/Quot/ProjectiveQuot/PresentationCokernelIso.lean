module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.KernelTwistCounit

/-!
# The cokernel of `u_m` for the presentation of `K ∈ Quot^P(T)` is `𝒬(m)`

Let `K ∈ Quot^P(T)` with quotient `𝒬 = 𝒪^{⊕ r}/K` on `π : ℙⁿ_T ⟶ T`, let
`m = AlgebraicGeometry.ProjectiveQuot.regularityIndex n r P`, and let
`q : 𝒪_T^{⊕ N} ≅ π_*𝒪^{⊕ r}(m) ⟶ π_*𝒬(m)` be the Grassmannian presentation of `K`
(`AlgebraicGeometry.ProjectiveQuot.grassmannianPresentation`). The map
`u_m : π^* ker(q) ⟶ 𝒪^{⊕ r}(m)` factors as an epimorphism `π^* ker(q) ⟶ 𝒦(m)` followed by the
inclusion `𝒦(m) ⟶ 𝒪^{⊕ r}(m)` (`AlgebraicGeometry.ProjectiveQuot.KernelTwistCounit`), so its
image is `𝒦(m)` and its cokernel `ℱ^{(m)}` is `𝒬(m)`, compatibly with the quotient maps from
`𝒪^{⊕ r}(m)`.

In the proof of Stacks 0DPA this is the identification `ψ(φ(K)) = K`: the family attached to the
point of the Grassmannian classifying `K` is the twist of `𝒬` itself.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.exists_presentationCokernel_iso_twist_quotient`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

/-- A composite through a factorization of a morphism killed by `c` is killed by `c`. -/
theorem comp_eq_zero_of_fac {C : Type*} [Category* C] [HasZeroMorphisms C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (u : A ⟶ D) (h : a ≫ b = u) (hbc : b ≫ c = 0) :
    u ≫ c = 0 := by
  rw [← h, Category.assoc, hbc, comp_zero]

variable {n r : ℕ} {P : Polynomial ℚ}

/-- **The cokernel of `u_m` for the presentation of `K ∈ Quot^P(T)` is `𝒬(m)`**: there is an
isomorphism `ℱ^{(m)} = coker(u_m) ≅ 𝒬(m)` under which the quotient map `𝒪^{⊕ r}(m) ⟶ ℱ^{(m)}`
becomes the twist `𝒪^{⊕ r}(m) ⟶ 𝒬(m)` of the quotient map of `K`. -/
theorem exists_presentationCokernel_iso_twist_quotient
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P))
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    ∃ e : presentationCokernel (regularityIndex.{u} n r P) (grassmannianPresentation hp hK) ≅
        twist (regularityIndex.{u} n r P : ℤ) (quotient K),
      presentationCokernelπ _ _ ≫ e.hom =
        twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K) := by
  have : Epi (presentationKernelCounit hp hK) :=
    epi_presentationKernelCounit_of_epi hp hK (epi_counit_app_twist_subobject hK)
  have hfac := presentationKernelCounit_comp_twistMap hp hK
  let S := twistShortComplex (regularityIndex.{u} n r P : ℤ) K
  let S' : ShortComplex (projectiveSpaceOver n T).Modules :=
    ShortComplex.mk (presentationTwistMap (regularityIndex.{u} n r P)
      (grassmannianPresentation hp hK)) S.g
      (comp_eq_zero_of_fac (C := (projectiveSpaceOver n T).Modules) _ _ _ _ hfac S.zero)
  let ψ : S' ⟶ S :=
    { τ₁ := presentationKernelCounit hp hK
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := hfac.trans (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi ψ.τ₁ := inferInstanceAs (Epi (presentationKernelCounit hp hK))
  have : IsIso ψ.τ₂ := IsIso.id S.X₂
  have : Mono ψ.τ₃ := @IsIso.mono_of_iso _ _ _ _ _ (IsIso.id S.X₃)
  have hS' : S'.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 (twistShortComplex_exact _ K)
  have : Epi S'.g := inferInstanceAs (Epi S.g)
  exact ⟨(cokernelIsCokernel _).coconePointUniqueUpToIso hS'.gIsCokernel,
    (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom hS'.gIsCokernel
      WalkingParallelPair.one⟩

end AlgebraicGeometry.ProjectiveQuot

end
