module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDualSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupModuleSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TransposePresentation

/-!
# The duality input of Tag 0GAC on the blowup

The proof of [Stacks, Tag 0GAC] turns an `A`-linear map `φ : M → Iⁿ/I^{2n}` on an
`(A, n, c)`-module into a section `σ'` of `𝒪_X(n - 2c) ⊗ p^*(M^∨)~` whose evaluation against
the elements of `M` is `φ` twisted down to level `n - 2c`. The source does this by dualizing:
`φ` gives a section of `(p^*M)^∨(n)`, and the twist of that section down by `2c` is lifted
through `can : p^*(M^∨) → (p^*M)^∨`, whose kernel and cokernel are supported on `Y_c` ("small
detail omitted"). The statement
`Stacks.LocalCohomology.UniformityIII.DualSituation.exists_sum_powQuotSmul` carries that section
as the hypothesis `hσ`. This file proves it on the blowup, `exists_blowupEv_eq`.

## The route

No dual sheaf is formed. Choose a presentation `R^{⊕r₁} --d--> R^{⊕r₀} --π--> M → 0`,
`R = A/Iⁿ`. Its transpose splits into `0 → M^∨ → R^{⊕r₀} → L → 0` and `0 → L → R^{⊕r₁} → C → 0`,
both presentations of `(A, n, c)`-modules (`BitUniformityIII/TransposePresentation.lean`); this
is the presentation-level form of the source's `can`, whose kernel and cokernel come from these
two sequences. Then:

* `presSection` is the section of `𝒪_X(n) ⊗ p^*(R^{⊕r₀})~` whose coordinates are the sections of
  `𝒪_{Yₙ}(n)` attached to `φ(π eⱼ)`; its image under the transposed relation matrix vanishes
  (`blowupHmodMap_transD_presSection`), because `φ ∘ π ∘ d = 0`.
* `exists_section_of_transD` is the diagram chase: the image of such a section in `H⁰` of the
  twisted pullback of `L` lies in `H⁰(ℱ)` of the second presentation, which dies on twisting down
  by `c` ([Stacks, Tag 0GA8] there); so its twist lies in `H⁰(𝒢)` of the first presentation, and
  the dotted arrow of [Stacks, Tag 0GAA] lifts the further twist by `c` to the twisted pullback of
  `M^∨`. This is the source's two twists by `c`, and the place where its "small detail" is
  supplied: no `H¹` vanishing is needed.
* `exists_blowupEv_eq` evaluates: `λ ↦ λ(π w)` is the transpose of `π` followed by evaluation
  against `w` (`resEvalHom_eq_comp`), and on the coordinates evaluation is the section attached to
  `φ(π w)`, whose twist down is read back by `cdivInv_blowupHtr_cdiv`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.exists_blowupEv_eq`: **the duality input of
  [Stacks, Tag 0GAC] on the blowup.**

## References

* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
* [Stacks Project, Remark 0GAB](https://stacks.math.columbia.edu/tag/0GAB)
* [Stacks Project, Tag 0GA8](https://stacks.math.columbia.edu/tag/0GA8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

/-- A vector in `(A/Iⁿ)^{⊕r}` is the combination of the basis vectors with its coordinates. -/
private theorem pi_eq_sum_smul_single {A : Type u} [CommRing A] (I : Ideal A) {n r : ℕ}
    (w : Fin r → A ⧸ I ^ n) :
    w = ∑ j, w j • (Pi.single j 1 : Fin r → A ⧸ I ^ n) := by
  conv_lhs => rw [pi_eq_sum_univ w]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1; ext i; simp [Pi.single_apply, eq_comm]

/-- A map out of `(A/Iⁿ)^{⊕r}`, on `b` in the `j`-th slot, is `b` times its value at `eⱼ`. -/
private theorem hom_single_mk {A : Type u} [CommRing A] (I : Ideal A) {n r : ℕ}
    {N : ModuleCat.{u} A}
    (g : ModuleCat.of A (Fin r → A ⧸ I ^ n) ⟶ N) (j : Fin r) (b : A) :
    g.hom (Pi.single j (Ideal.Quotient.mk (I ^ n) b)) = b • g.hom (Pi.single j 1) := by
  rw [← map_smul]
  congr 1
  ext i
  by_cases hij : i = j
  · subst hij; simp [Algebra.smul_def]
  · simp [hij]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {n c : ℕ}

section Chase

variable {M : ANCModule I n c} (P : TwoStepPresentation M)

/-- **The diagram chase of the duality step.** A section `y` of `𝒪_X(n) ⊗ p^*(R^{⊕r₀})~` whose
image under the transposed relation matrix vanishes comes, after twisting down by `2c`, from a
section of `𝒪_X(n - 2c) ⊗ p^*(M^∨)~`.

The image `ȳ` of `y` in `H⁰(𝒪_X(n) ⊗ p^*L~)` lies in `H⁰(ℱ)` for the sheaf `ℱ` of the
presentation `0 → L → R^{⊕r₁} → C → 0`, which dies on twisting down by `c`; so the twist of `y`
lies in `H⁰(𝒢)` for the presentation `0 → M^∨ → R^{⊕r₀} → L → 0`, and the dotted arrow of that
presentation lifts its further twist to `H⁰(𝒪_X(n - 2c) ⊗ p^*(M^∨)~)`. -/
theorem exists_section_of_transD {e f : ℕ} (hf : f + c = n) (he : e + c = f)
    (y : blowupHmodTwistedPullback I P.presL.resShortComplex.X₂ 0 (n : ℤ))
    (hy : blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map
      (P.presL.resShortComplex.g ≫ P.presC.resShortComplex.f)) y = 0) :
    ∃ σ' : blowupHmodTwistedPullback I P.presL.resShortComplex.X₁ 0 (e : ℤ),
      blowupHmodMap I 0 ((twistedPullbackFunctor I (e : ℤ)).map P.presL.resShortComplex.f) σ' =
        blowupHtr I P.presL.resShortComplex.X₂ 0 (n : ℤ) (e : ℤ) (by omega) y := by
  have hSL := P.presL.shortExact_resShortComplex
  have hSC := P.presC.shortExact_resShortComplex
  have hnf : ((f : ℕ) : ℤ) ≤ (n : ℤ) := by omega
  have hfe : ((e : ℕ) : ℤ) ≤ (f : ℤ) := by omega
  have hcf : (c : ℤ) + (f : ℤ) = (n : ℤ) := by omega
  have hce : (c : ℤ) + (e : ℤ) = (f : ℤ) := by omega
  -- the image `ȳ` of `y` in `H⁰(𝒪_X(n) ⊗ p^*L~)`
  set yb := blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map
    P.presL.resShortComplex.g) y with hyb
  -- `ȳ` dies in `H⁰(𝒢)` of the presentation of `C`
  have h1 : blowupHmodMap I 0
      (P.presC.resShortComplex.map (twistedPullbackFunctor I (n : ℤ))).toCycles yb = 0 := by
    apply injective_blowupHmodMap I _ _ _
      (shortExact_twistedPullbackFreeSequence I (n : ℤ) hSC)
    rw [map_zero, ← hy, hyb]
    have e1 : (twistedPullbackFunctor I (n : ℤ)).map
        (P.presL.resShortComplex.g ≫ P.presC.resShortComplex.f) =
        (twistedPullbackFunctor I (n : ℤ)).map P.presL.resShortComplex.g ≫
          ((P.presC.resShortComplex.map (twistedPullbackFunctor I (n : ℤ))).toCycles ≫
            (P.presC.resShortComplex.map (twistedPullbackFunctor I (n : ℤ))).iCycles) :=
      ((twistedPullbackFunctor I (n : ℤ)).map_comp _ _).trans
        (congrArg (fun φ => (twistedPullbackFunctor I (n : ℤ)).map P.presL.resShortComplex.g ≫ φ)
          (P.presC.resShortComplex.map (twistedPullbackFunctor I (n : ℤ))).toCycles_i.symm)
    exact ((blowupHmodMap_comp_apply I 0 _ _ _).symm.trans
      (blowupHmodMap_comp_apply I 0 _ _ _).symm).trans
      (congrArg (fun φ => blowupHmodMap I 0 φ y) e1.symm)
  -- so `ȳ` comes from `H⁰(ℱ)`
  obtain ⟨w, hw⟩ := (exact_blowupHmodMap I _ _ (kernel.condition _)
    (shortExact_twistedPullbackKernelSequence I (n : ℤ) hSC) 0 yb).1 h1
  -- and dies on twisting down by `c`
  have h2 : blowupHtr I P.presL.resShortComplex.X₃ 0 (n : ℤ) (f : ℤ) hnf yb = 0 := by
    rw [← hw]
    have hz := kernelι_comp_twistDown_eq_zero_of_mem I P.presC (n : ℤ) (f : ℤ) hcf hnf
    have := congrArg (fun φ => blowupHmodMap I 0 φ) hz
    simp only [Functor.map_comp, Functor.map_zero] at this
    exact ConcreteCategory.congr_hom this w
  -- so the twist `y'` of `y` lies in `H⁰(𝒢)` of the presentation of `L`
  set y' := blowupHtr I P.presL.resShortComplex.X₂ 0 (n : ℤ) (f : ℤ) hnf y with hy'
  have h3 : blowupHmodMap I 0 ((twistedPullbackFunctor I (f : ℤ)).map
      P.presL.resShortComplex.g) y' = 0 := by
    rw [← h2, hyb, hy']
    exact (ConcreteCategory.congr_hom
      (blowupHtr_naturality I P.presL.resShortComplex.g 0 (n : ℤ) (f : ℤ) hnf) y).symm
  obtain ⟨g1, hg1⟩ := (exact_blowupHmodMap I _ _ _
    (shortExact_twistedPullbackFreeSequence I (f : ℤ) hSL) 0 y').1 h3
  -- the dotted arrow lifts the further twist
  refine ⟨blowupHmodMap I 0 (dottedOfPresentation I P.presL (f : ℤ) (e : ℤ) hce hfe) g1, ?_⟩
  have hd := ConcreteCategory.congr_hom
    (blowupHmodMap_dottedOfPresentation_comp_toCycles I P.presL 0 (f : ℤ) (e : ℤ) hce hfe) g1
  have hi := (P.presL.resShortComplex.map (twistedPullbackFunctor I (e : ℤ))).toCycles_i
  have hcyc := ShortComplex.cyclesMap_i
    (twistDownShortComplexMap I (f : ℤ) (e : ℤ) hfe (S := P.presL.resShortComplex))
  have hcyc' := ConcreteCategory.congr_hom (congrArg (fun φ => blowupHmodMap I 0 φ) hcyc) g1
  simp only [Functor.map_comp] at hcyc'
  calc blowupHmodMap I 0 ((twistedPullbackFunctor I (e : ℤ)).map P.presL.resShortComplex.f)
        (blowupHmodMap I 0 (dottedOfPresentation I P.presL (f : ℤ) (e : ℤ) hce hfe) g1)
      = blowupHmodMap I 0 (P.presL.resShortComplex.map (twistedPullbackFunctor I (e : ℤ))).iCycles
          (blowupHmodMap I 0
            (P.presL.resShortComplex.map (twistedPullbackFunctor I (e : ℤ))).toCycles
            (blowupHmodMap I 0 (dottedOfPresentation I P.presL (f : ℤ) (e : ℤ) hce hfe) g1)) :=
        (congrArg (fun φ => blowupHmodMap I 0 φ
          (blowupHmodMap I 0 (dottedOfPresentation I P.presL (f : ℤ) (e : ℤ) hce hfe) g1))
          hi.symm).trans (blowupHmodMap_comp_apply I 0 _ _ _)
    _ = blowupHmodMap I 0 (P.presL.resShortComplex.map (twistedPullbackFunctor I (e : ℤ))).iCycles
          (blowupHGtr I 0 (f : ℤ) (e : ℤ) hfe (S := P.presL.resShortComplex) g1) := by
        rw [← hd]; rfl
    _ = blowupHtr I P.presL.resShortComplex.X₂ 0 (f : ℤ) (e : ℤ) hfe y' := by
        rw [← hg1]; exact hcyc'
    _ = blowupHtr I P.presL.resShortComplex.X₂ 0 (n : ℤ) (e : ℤ) (by omega) y := by
        rw [hy']
        exact ConcreteCategory.congr_hom
          (blowupHtr_comp I P.presL.resShortComplex.X₂ 0 (n : ℤ) (f : ℤ) (e : ℤ) hfe hnf _) y

end Chase

section Coordinates

/-- The inclusion of the `j`-th summand `A/Iⁿ → (A/Iⁿ)^{⊕r}`, over `A`. -/
def finSingleHom (r : ℕ) (j : Fin r) :
    ModuleCat.of A (A ⧸ I ^ n) ⟶ ModuleCat.of A (Fin r → A ⧸ I ^ n) :=
  ModuleCat.ofHom (LinearMap.single A (fun _ : Fin r => A ⧸ I ^ n) j)

omit [IsNoetherianRing A] in
/-- An `A`-linear map out of `A/Iⁿ` is determined by the image of `1`. -/
theorem quot_hom_apply {N : Type u} [AddCommGroup N] [Module A N] (g : (A ⧸ I ^ n) →ₗ[A] N)
    (x : A ⧸ I ^ n) {b : A} (hb : Ideal.Quotient.mk (I ^ n) b = x) : g x = b • g 1 := by
  rw [← map_smul, ← hb, Algebra.smul_def, mul_one]
  rfl

omit [IsNoetherianRing A] in
/-- **A map between finite free modules, restricted to a summand, in coordinates.** -/
theorem finSingleHom_comp_eq_sum {r r' : ℕ} (j : Fin r)
    (g : ModuleCat.of A (Fin r → A ⧸ I ^ n) ⟶ ModuleCat.of A (Fin r' → A ⧸ I ^ n))
    (a : Fin r' → A) (ha : ∀ k, Ideal.Quotient.mk (I ^ n) (a k) = g.hom (Pi.single j 1) k) :
    finSingleHom I r j ≫ g = ∑ k, a k • finSingleHom I r' k := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 := hom_single_mk I g j b
  funext k
  show g.hom (Pi.single j _) k = (∑ i, a i • finSingleHom I r' i).hom _ k
  rw [h1, ModuleCat.hom_sum, LinearMap.sum_apply, Finset.sum_apply,
    Finset.sum_eq_single k (fun i _ hik => by
      simp [finSingleHom, Pi.single_apply, Ne.symm hik]) (by simp)]
  simp [finSingleHom, Algebra.smul_def, ← ha k, mul_comm]

omit [IsNoetherianRing A] in
/-- **A functional on a finite free module, restricted to a summand, is a scalar.** -/
theorem finSingleHom_comp_eq_smul {r : ℕ} (j : Fin r)
    (g : ModuleCat.of A (Fin r → A ⧸ I ^ n) ⟶ ModuleCat.of A (A ⧸ I ^ n))
    (b : A) (hb : Ideal.Quotient.mk (I ^ n) b = g.hom (Pi.single j 1)) :
    finSingleHom I r j ≫ g = b • 𝟙 (ModuleCat.of A (A ⧸ I ^ n)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 := hom_single_mk I g j b'
  show g.hom (Pi.single j _) = _
  rw [h1, ← hb]
  simp [Algebra.smul_def, mul_comm]

end Coordinates

section Section

variable (q₀ : ℕ) (h : IsBaseThreshold I q₀) {M : ANCModule I n c} (P : TwoStepPresentation M)
  (φ : resModule I n M.1 →ₗ[A] powQuot I n n)

/-- The section of `𝒪_X(n) ⊗ p^*((A/Iⁿ)~) = 𝒪_{Yₙ}(n)` attached to `φ(π eⱼ) ∈ Iⁿ/I^{2n}`. -/
def coordSection (j : Fin P.r₀) :
    blowupHmodTwistedPullback I (ModuleCat.of A (A ⧸ I ^ n)) 0 (n : ℤ) :=
  (blowupHmodTwistedPullbackQuotientEquiv I n 0 n).symm
    ((blowupSituationOf I q₀ h).cdiv n n (φ (P.π (Pi.single j 1))))

/-- **The section of `𝒪_X(n) ⊗ p^*(R^{⊕r₀})~` attached to `φ ∘ π`**, coordinate by
coordinate. -/
def presSection : blowupHmodTwistedPullback I P.presL.resShortComplex.X₂ 0 (n : ℤ) :=
  ∑ j, blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map (finSingleHom I P.r₀ j))
    (coordSection I q₀ h P φ j)

omit [IsNoetherianRing A] in
/-- `π` in coordinates. -/
theorem π_eq_sum_smul (a : Fin P.r₀ → A) :
    P.π (fun j => Ideal.Quotient.mk (I ^ n) (a j)) =
      ∑ j, Ideal.Quotient.mk (I ^ n) (a j) • P.π (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_smul_single I (fun j => Ideal.Quotient.mk (I ^ n) (a j)), map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul _ _ _

omit [IsNoetherianRing A] in
/-- `φ ∘ π` in coordinates. -/
theorem φ_π_eq_sum_smul (a : Fin P.r₀ → A) :
    φ (P.π (fun j => Ideal.Quotient.mk (I ^ n) (a j))) =
      ∑ j, a j • φ (P.π (Pi.single j 1)) := by
  rw [π_eq_sum_smul]
  exact (map_sum φ _ _).trans (Finset.sum_congr rfl fun j _ => φ.map_smul (a j) _)

/-- **A linear combination of the coordinate sections** is the section attached to `φ` at the
corresponding combination of the generators. -/
theorem sum_smul_coordSection (a : Fin P.r₀ → A) :
    ∑ j, a j • coordSection I q₀ h P φ j =
      (blowupHmodTwistedPullbackQuotientEquiv I n 0 n).symm ((blowupSituationOf I q₀ h).cdiv n n
        (φ (P.π (fun j => Ideal.Quotient.mk (I ^ n) (a j))))) := by
  rw [φ_π_eq_sum_smul]
  calc ∑ j, a j • coordSection I q₀ h P φ j
      = ∑ j, (blowupHmodTwistedPullbackQuotientEquiv I n 0 n).symm
          ((blowupSituationOf I q₀ h).cdiv n n (a j • φ (P.π (Pi.single j 1)))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coordSection, map_smul ((blowupSituationOf I q₀ h).cdiv n n)]
        exact ((blowupHmodTwistedPullbackQuotientEquiv I n 0 n).symm.map_smul (a j) _).symm
    _ = (blowupHmodTwistedPullbackQuotientEquiv I n 0 n).symm (∑ j,
          (blowupSituationOf I q₀ h).cdiv n n (a j • φ (P.π (Pi.single j 1)))) :=
        (map_sum _ _ _).symm
    _ = _ := congrArg _ (map_sum _ _ _).symm

/-- `H⁰` of a map out of `R^{⊕r₀}`, applied to `presSection`, coordinate by coordinate. -/
theorem blowupHmodMap_presSection {N : ModuleCat.{u} A} (g : P.presL.resShortComplex.X₂ ⟶ N) :
    blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map g) (presSection I q₀ h P φ) =
      ∑ j, blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map (finSingleHom I P.r₀ j ≫ g))
        (coordSection I q₀ h P φ j) := by
  rw [presSection]
  refine (map_sum (blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map g)).hom _ _).trans
    (Finset.sum_congr rfl fun j _ => ?_)
  refine (blowupHmodMap_comp_apply I 0 _ _ _).symm.trans ?_
  exact congrArg (fun ψ => blowupHmodMap I 0 ψ (coordSection I q₀ h P φ j))
    ((twistedPullbackFunctor I (n : ℤ)).map_comp _ _).symm

/-- `Hⁱ(X, 𝒪_X(q) ⊗ p^*(-))` of a linear combination of maps, on an element. -/
theorem blowupHmodMap_sum_smul_apply (q : ℤ) {N N' : ModuleCat.{u} A} {ι : Type*} (s : Finset ι)
    (a : ι → A) (f : ι → (N ⟶ N')) (x : blowupHmodTwistedPullback I N 0 q) :
    blowupHmodMap I 0 ((twistedPullbackFunctor I q).map (∑ k ∈ s, a k • f k)) x =
      ∑ k ∈ s, a k • blowupHmodMap I 0 ((twistedPullbackFunctor I q).map (f k)) x := by
  let := linear_twistedPullbackCohomologyFunctor I 0 q
  have h1 : (twistedPullbackCohomologyFunctor I 0 q).map (∑ k ∈ s, a k • f k) =
      ∑ k ∈ s, a k • (twistedPullbackCohomologyFunctor I 0 q).map (f k) := by
    rw [Functor.map_sum]
    exact Finset.sum_congr rfl fun k _ => Functor.Linear.map_smul _ _
  have h2 := congrArg (fun ψ => ψ.hom x) h1
  simp only [ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply,
    LinearMap.smul_apply] at h2
  exact h2

/-- **The image of `presSection` under the transposed relation matrix vanishes**: its `k`-th
coordinate is the section attached to `φ(π(d eₖ)) = 0`. -/
theorem blowupHmodMap_transD_presSection :
    blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map
      (P.presL.resShortComplex.g ≫ P.presC.resShortComplex.f)) (presSection I q₀ h P φ) = 0 := by
  classical
  let a : Fin P.r₀ → Fin P.r₁ → A := fun j k =>
    (Ideal.Quotient.mk_surjective (P.d (Pi.single k 1) j)).choose
  have ha : ∀ j k, Ideal.Quotient.mk (I ^ n) (a j k) = P.d (Pi.single k 1) j := fun j k =>
    (Ideal.Quotient.mk_surjective (P.d (Pi.single k 1) j)).choose_spec
  rw [blowupHmodMap_presSection]
  have hcomp : ∀ j, finSingleHom I P.r₀ j ≫
      (P.presL.resShortComplex.g ≫ P.presC.resShortComplex.f) =
        ∑ k, a j k • finSingleHom I P.r₁ k := fun j =>
    finSingleHom_comp_eq_sum I j _ (a j) fun k => by
      rw [ha]; exact (P.transD_single j k).symm
  refine (Finset.sum_congr rfl fun j _ =>
    (congrArg (fun ψ => blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map ψ)
      (coordSection I q₀ h P φ j)) (hcomp j)).trans
      (blowupHmodMap_sum_smul_apply I (n : ℤ) Finset.univ (a j) _ _)).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  set G := (blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map
    (finSingleHom I P.r₁ k))).hom
  refine (Finset.sum_congr rfl fun j _ => (G.map_smul (a j k) _).symm).trans ?_
  refine (map_sum G _ _).symm.trans ?_
  rw [sum_smul_coordSection]
  have hd : (fun j => Ideal.Quotient.mk (I ^ n) (a j k)) = P.d (Pi.single k 1) :=
    funext fun j => ha j k
  have hπd : P.π (P.d (Pi.single k 1)) = 0 := by
    rw [← LinearMap.mem_ker, ← P.range_d]; exact ⟨_, rfl⟩
  rw [hd, hπd]
  exact (congrArg G ((congrArg _ ((congrArg _ (map_zero φ)).trans (map_zero _))).trans
    (map_zero _))).trans (map_zero G)

/-- Evaluation `R^{⊕r₀} → R` against a fixed vector `w`, over `A`. -/
def evalVec (r : ℕ) (w : Fin r → A ⧸ I ^ n) :
    ModuleCat.of A (Fin r → A ⧸ I ^ n) ⟶ ModuleCat.of A (A ⧸ I ^ n) :=
  ModuleCat.ofHom
    { toFun := fun v => ∑ j, v j * w j
      map_add' := fun v v' => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_mul_assoc] }

/-- **Evaluating a functional on `M` at `z = π(w)`** is evaluating its coordinates against
`w`. -/
theorem resEvalHom_eq_comp (w : Fin P.r₀ → A ⧸ I ^ n) :
    resEvalHom I n M.1 (P.π w) = P.presL.resShortComplex.f ≫ evalVec I P.r₀ w := by
  refine ModuleCat.hom_ext (LinearMap.ext fun lam => ?_)
  show asDual I n lam (P.π w) = ∑ j, P.dualIncl lam j * w j
  conv_lhs => rw [pi_eq_sum_smul_single I w, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  rfl

/-- **Evaluating `presSection` against the coordinates of `w`** gives the section attached to
`φ(π w)`. -/
theorem blowupHmodMap_evalVec_presSection (w : Fin P.r₀ → A ⧸ I ^ n) :
    blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map (evalVec I P.r₀ w))
        (presSection I q₀ h P φ) =
      (blowupHmodTwistedPullbackQuotientEquiv I n 0 n).symm
        ((blowupSituationOf I q₀ h).cdiv n n (φ (P.π w))) := by
  classical
  let b : Fin P.r₀ → A := fun j => (Ideal.Quotient.mk_surjective (w j)).choose
  have hb : ∀ j, Ideal.Quotient.mk (I ^ n) (b j) = w j := fun j =>
    (Ideal.Quotient.mk_surjective (w j)).choose_spec
  refine (blowupHmodMap_presSection I q₀ h P φ (evalVec I P.r₀ w)).trans ?_
  have hw : (fun j => Ideal.Quotient.mk (I ^ n) (b j)) = w := funext hb
  rw [← hw, ← sum_smul_coordSection]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : finSingleHom I P.r₀ j ≫ evalVec I P.r₀ (fun j => Ideal.Quotient.mk (I ^ n) (b j)) =
      ∑ k ∈ ({()} : Finset Unit), b j • 𝟙 (ModuleCat.of A (A ⧸ I ^ n)) := by
    rw [Finset.sum_singleton]
    exact finSingleHom_comp_eq_smul I j _ (b j) (by
      show _ = ∑ i, (Pi.single j (1 : A ⧸ I ^ n) : Fin P.r₀ → A ⧸ I ^ n) i * _
      simp [Pi.single_apply, hb])
  refine (congrArg (fun ψ => blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map ψ)
    (coordSection I q₀ h P φ j)) hc).trans ?_
  rw [blowupHmodMap_sum_smul_apply, Finset.sum_singleton, CategoryTheory.Functor.map_id]
  exact congrArg (fun t => b j • t) (ConcreteCategory.congr_hom
    (((blowupΓmod I).rightDerived 0).map_id _) (coordSection I q₀ h P φ j))

/-- **The duality input of [Stacks, Tag 0GAC] on the blowup.** For an `(A, n, c)`-module `M` and
an `A`-linear map `φ : M → Iⁿ/I^{2n}`, with `e + 2c = n` and `e ≥ q₀`, there is a section `σ'` of
`𝒪_X(e) ⊗ p^*(M^∨)~` whose evaluation against the elements of `M` is `φ` twisted down to level
`e`. This is the section `σ'` of the source, obtained there by dualizing `p^*M` and factoring
through `can : p^*(M^∨) → (p^*M)^∨`; here it is obtained from a presentation of `M` by
`exists_section_of_transD`, applied to the section `presSection` attached to `φ ∘ π`. -/
theorem exists_blowupEv_eq (hcn : c ≤ n) {e : ℕ} (hen : e + 2 * c = n) (hq : q₀ ≤ e)
    (M : ANCModule I n c) (φ : resModule I n M.1 →ₗ[A] powQuot I n n) :
    ∃ σ' : (blowupModuleSituationOf I q₀ h n c hcn).H M.dual 0 (e : ℤ),
      blowupEv I q₀ h n c hcn M e hq σ' = (powQuotLe I (Nat.le.intro hen)).comp φ := by
  classical
  obtain ⟨P⟩ := nonempty_twoStepPresentation M
  obtain ⟨σ', hσ'⟩ := exists_section_of_transD I P (f := e + c) (by omega) rfl
    (presSection I q₀ h P φ) (blowupHmodMap_transD_presSection I q₀ h P φ)
  have hne : ((e : ℕ) : ℤ) ≤ (n : ℤ) := by omega
  refine ⟨σ', LinearMap.ext fun z => ?_⟩
  obtain ⟨w, rfl⟩ := P.surjective_π z
  let b : Fin P.r₀ → A := fun j => (Ideal.Quotient.mk_surjective (w j)).choose
  have hb : ∀ j, Ideal.Quotient.mk (I ^ n) (b j) = w j := fun j =>
    (Ideal.Quotient.mk_surjective (w j)).choose_spec
  refine (blowupEv_apply I q₀ h n c hcn M e hq σ' (P.π w)).trans ?_
  show _ = powQuotLe I (Nat.le.intro hen) (φ (P.π w))
  -- the evaluation factors through the coordinates
  have h1 : blowupHmodMap I 0 ((twistedPullbackFunctor I (e : ℤ)).map
        (resEvalHom I n M.1 (P.π w))) σ' =
      blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (n : ℤ) (e : ℤ) hne
        (blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map (evalVec I P.r₀ w))
          (presSection I q₀ h P φ)) := by
    rw [resEvalHom_eq_comp]
    refine (congrArg (fun ψ => blowupHmodMap I 0 ψ σ')
      ((twistedPullbackFunctor I (e : ℤ)).map_comp _ _)).trans ?_
    refine (blowupHmodMap_comp_apply I 0 _ _ _).trans ?_
    rw [hσ']
    exact (ConcreteCategory.congr_hom
      (blowupHtr_naturality I (evalVec I P.r₀ w) 0 (n : ℤ) (e : ℤ) hne)
        (presSection I q₀ h P φ)).symm
  -- and on the coordinates it is the section attached to `φ(π w)`
  refine (congrArg (fun t => cdivInv I q₀ h n hq (blowupHmodTwistedPullbackQuotientEquiv I n 0 e t))
    h1).trans ?_
  refine (congrArg (fun t => cdivInv I q₀ h n hq (blowupHmodTwistedPullbackQuotientEquiv I n 0 e
    (blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (n : ℤ) (e : ℤ) hne t)))
    (blowupHmodMap_evalVec_presSection I q₀ h P φ w)).trans ?_
  exact cdivInv_blowupHtr_cdiv I q₀ h n n e (by omega) hq (by omega) hne (φ (P.π w))

end Section

end Stacks.LocalCohomology.UniformityIII

end
