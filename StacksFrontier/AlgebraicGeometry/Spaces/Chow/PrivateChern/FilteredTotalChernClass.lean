module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernFiltration
public import StacksFrontier.RingTheory.PowerSeries.ListProdOneAddCMulX

/-!
# The total Chern class of a module with a filtration with invertible quotients

In Situation 0EDT let `X/B` be good, let `ℒ_1, …, ℒ_r` be invertible `𝒪_X`-modules and let `ℰ`
be a finite locally free `𝒪_X`-module of rank `r` with a filtration

  `0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ`,   `ℰ_i / ℰ_{i-1} ≅ ℒ_i`.

With `x_i = c_1(ℒ_i)` the total Chern class is `c(ℰ) = ∏_{i=1}^r (1 + x_i)`; this is Stacks 0ESA.
The proof is the source's: induction along the filtration, peeling off `0 ⟶ ℒ_1 ⟶ ℰ ⟶ ℰ/ℰ_1 ⟶ 0`
with Stacks 0ES8. The Chern classes are recorded degree by degree as the coefficients of the
power series `∑_n c_n(ℰ) X^n` with coefficients in the operations on `CH_*(X)`, in which Stacks
0ES8 reads `∑ c_n(ℰ) X^n = (1 + c_1(ℒ) X) ∑ c_n(ℱ) X^n`; the total class is the sum of the
coefficients.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_of_rank_zero`: a module of rank `0` has
  `c_n = 0` for `n ≥ 1`.
* `AlgebraicGeometry.Space.PrivateChern.mk_chernCap_eq_prod_of_filtration`: the Chern classes of
  a filtered module are the coefficients of `∏ (1 + x_i X)`, granted the identity of Stacks 0ES8
  degree by degree.
* `AlgebraicGeometry.Space.PrivateChern.totalChernCap_eq_prod_of_filtration_of_succ`: the total
  Chern class is `∏ (1 + x_i)`, granted the same.
* `AlgebraicGeometry.Space.PrivateChern.totalChernCap_eq_prod_one_add_chernCap_one_of_filtration`:
  the same with `x_i = c₁(ℒ_i)` the first Chern classes of Stacks 0ERZ, granted Stacks 0ES8 in
  the form `c(ℰ') = (1 + c₁(ℒ)) c(ℱ)`.

## References

* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject ZeroObject

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX}

/-- The abelian structure of the `𝒪_X`-modules at the universe of the schemes,
`SheafOfModules.instAbelian`.

This and the three instances below are supplied as terms: once the Chern class API is imported,
instance search for them on `𝒪_X`-modules reaches an instance stated at a larger universe of
modules and stops on an unsolvable universe constraint instead of backtracking. -/
scoped instance (priority := high) instAbelianModules {D : BaseSpaceDimensionSituation.{u}}
    {X : D.Ambient} (hX₁ : IsAlgebraicSpace D.site D.base D.base_mem X) :
    Abelian (Modules.{u, u} D.site D.base D.base_mem X hX₁) :=
  SheafOfModules.instAbelian _

/-- The zero `𝒪_X`-module. -/
scoped instance (priority := high) instHasZeroObjectModules {D : BaseSpaceDimensionSituation.{u}}
    {X : D.Ambient} (hX₁ : IsAlgebraicSpace D.site D.base D.base_mem X) :
    HasZeroObject (Modules.{u, u} D.site D.base D.base_mem X hX₁) :=
  @Abelian.hasZeroObject _ _ (instAbelianModules hX₁)

/-- Subobjects of `𝒪_X`-modules have a least element. -/
scoped instance (priority := high) instHasInitialModules {D : BaseSpaceDimensionSituation.{u}}
    {X : D.Ambient} (hX₁ : IsAlgebraicSpace D.site D.base D.base_mem X) :
    HasInitial (Modules.{u, u} D.site D.base D.base_mem X hX₁) :=
  @HasZeroObject.hasInitial _ _ (instHasZeroObjectModules hX₁)

/-- Monomorphisms out of the zero `𝒪_X`-module. -/
scoped instance (priority := high) instInitialMonoClassModules
    {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient}
    (hX₁ : IsAlgebraicSpace D.site D.base D.base_mem X) :
    InitialMonoClass (Modules.{u, u} D.site D.base D.base_mem X hX₁) :=
  @HasZeroObject.initialMonoClass _ _ (instHasZeroObjectModules hX₁)

/-- **A module of rank `0` has trivial Chern classes**: its Segre operations vanish, so
`c_n = 0` for `n ≥ 1`. -/
theorem chernCap_of_rank_zero (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E 0) (n : ℕ) :
    chernCap.{u, v} E 0 hE (n + 1) = 0 := by
  rw [chernCap, chernSeq_succ]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [show segreCapOfModule.{u, v} E 0 hE (n + 1 - j) = 0 from rfl, zero_mul, mul_zero]

/-- The generating series `∑_n c_n(ℰ) X^n` of a module of rank `0` is `1`. -/
theorem mk_chernCap_of_rank_zero (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E 0) :
    PowerSeries.mk (chernCap.{u, v} E 0 hE) = 1 := by
  ext n
  cases n with
  | zero => simp [chernCap_zero]
  | succ n => simp [chernCap_of_rank_zero, PowerSeries.coeff_one]

variable (x : ∀ L : Modules.{u, u} D.site D.base D.base_mem X hX.1,
    IsInvertibleModule (goodSpace hX) L → AddMonoid.End (chowHomology.{u, v} D sX hX))

/-- Granted Stacks 0ES8 degree by degree, for `x(ℒ)` the class attached to an invertible `ℒ`:
`c_1(ℒ) = x(ℒ)`, read off the short exact sequence `0 ⟶ ℒ ⟶ ℒ ⟶ 0 ⟶ 0`. -/
theorem chernCap_one_eq_of_succ
    (h8 : ∀ (r : ℕ) (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hX) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r) (n : ℕ),
      chernCap.{u, v} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, v} T.X₃ r h₃ (n + 1) + x T.X₁ h₁ * chernCap.{u, v} T.X₃ r h₃ n)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (goodSpace hX) L) :
    chernCap.{u, v} L 1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) hL) 1 =
      x L hL := by
  let T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1) :=
    ShortComplex.mk (𝟙 L) (0 : L ⟶ 0) (by simp)
  have hT : T.ShortExact :=
    { exact := (T.exact_iff_epi (by rfl)).mpr (inferInstanceAs (Epi (𝟙 L)))
      mono_f := inferInstanceAs (Mono (𝟙 L))
      epi_g := (isZero_zero (Modules.{u, u} D.site D.base D.base_mem X hX.1)).epi T.g }
  have h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ 0 :=
    RingedSite.isFiniteLocallyFreeOfRank_zero_of_isZero _ (isZero_zero _)
  refine (h8 0 T hT hL (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) hL) h₃
    0).trans ?_
  rw [chernCap_of_rank_zero, chernCap_zero, zero_add, mul_one]

/-- **The Chern classes of a module with a filtration with invertible quotients**, granted
Stacks 0ES8 degree by degree: `∑_n c_n(ℰ) X^n = ∏_{i=1}^r (1 + c_1(ℒ_i) X)`. -/
theorem mk_chernCap_eq_prod_of_filtration
    (h8 : ∀ (r : ℕ) (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hX) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r) (n : ℕ),
      chernCap.{u, v} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, v} T.X₃ r h₃ (n + 1) + x T.X₁ h₁ * chernCap.{u, v} T.X₃ r h₃ n)
    {r : ℕ}
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E r)
    (L : Fin r → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ i, IsInvertibleModule (goodSpace hX) (L i))
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    PowerSeries.mk (chernCap.{u, v} E r hE) = (List.ofFn fun i ↦ 1 + PowerSeries.C
      (chernCap.{u, v} (L i) 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) (hL i)) 1) *
          PowerSeries.X).prod := by
  refine eq_prod_of_filtration_of_mul (goodSpace hX)
    (fun r E hE ↦ PowerSeries.mk (chernCap.{u, v} E r hE))
    (fun L hL ↦ 1 + PowerSeries.C (x L hL) * PowerSeries.X)
    (fun E hE ↦ mk_chernCap_of_rank_zero E hE) (fun r T hT h₁ h₂ h₃ ↦ ?_) hE L hL F hF h0 hr e
    |>.trans ?_
  · exact PowerSeries.mk_eq_one_add_C_mul_X_mul (by rw [chernCap_zero, chernCap_zero])
      (h8 r T hT h₁ h₂ h₃)
  · congr 1
    exact List.ofFn_inj.mpr (funext fun i ↦ by rw [chernCap_one_eq_of_succ x h8])

/-- **The total Chern class of a module with a filtration with invertible quotients**, granted
Stacks 0ES8 degree by degree: `c(ℰ) = ∏_{i=1}^r (1 + c_1(ℒ_i))`. -/
theorem totalChernCap_eq_prod_of_filtration_of_succ
    (h8 : ∀ (r : ℕ) (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hX) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r) (n : ℕ),
      chernCap.{u, v} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, v} T.X₃ r h₃ (n + 1) + x T.X₁ h₁ * chernCap.{u, v} T.X₃ r h₃ n)
    {r : ℕ}
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E r)
    (L : Fin r → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ i, IsInvertibleModule (goodSpace hX) (L i))
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    totalChernCap.{u, v} E r hE = (List.ofFn fun i ↦ 1 +
      chernCap.{u, v} (L i) 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) (hL i)) 1).prod := by
  have h := mk_chernCap_eq_prod_of_filtration x h8 E hE L hL F hF h0 hr e
  let xs : Fin r → AddMonoid.End (chowHomology.{u, v} D sX hX) := fun i ↦
    chernCap.{u, v} (L i) 1
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) (hL i)) 1
  have map_ofFn : ∀ {β : Type _} (f : AddMonoid.End (chowHomology.{u, v} D sX hX) → β),
      (List.ofFn fun i ↦ f (xs i)) = (List.ofFn xs).map f := fun f ↦ by rw [List.map_ofFn]; rfl
  change _ = (List.ofFn fun i ↦ 1 + xs i).prod
  change _ = (List.ofFn fun i ↦ 1 + PowerSeries.C (xs i) * PowerSeries.X).prod at h
  rw [map_ofFn fun y ↦ 1 + y, ← PowerSeries.sum_coeff_list_prod_one_add_C_mul_X,
    ← map_ofFn fun y ↦ 1 + PowerSeries.C y * PowerSeries.X, ← h, List.length_ofFn,
    totalChernCap]
  simp

/-- **The total Chern class of a module with a filtration with invertible quotients is
`∏ (1 + c₁(ℒ_i))`**, granted Stacks 0ES8 degree by degree in the form
`c_{n+1}(ℰ') = c_{n+1}(ℱ) + c₁(ℒ) c_n(ℱ)` for `0 ⟶ ℒ ⟶ ℰ' ⟶ ℱ ⟶ 0` with `ℒ` invertible. Let `X/B`
be good, `ℒ_1, …, ℒ_r` invertible and `ℰ` finite locally free of rank `r` with a filtration
`0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ`, `ℰ_i / ℰ_{i-1} ≅ ℒ_i`; with `x_i = c₁(ℒ_i)`,
`c(ℰ) = ∏_{i=1}^r (1 + x_i)`. -/
theorem totalChernCap_eq_prod_one_add_chernCap_one_of_filtration
    (h8 : ∀ (r : ℕ) (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (_ : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hX) T.X₁)
      (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r + 1))
      (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r) (n : ℕ),
      chernCap.{u, v} T.X₂ (r + 1) h₂ (n + 1) =
        chernCap.{u, v} T.X₃ r h₃ (n + 1) +
          chernCap.{u, v} T.X₁ 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) h₁) 1 *
            chernCap.{u, v} T.X₃ r h₃ n)
    {r : ℕ}
    (L : Fin r → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ i, IsInvertibleModule (goodSpace hX) (L i))
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E r)
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    totalChernCap.{u, v} E r hE = (List.ofFn fun i ↦ 1 +
      chernCap.{u, v} (L i) 1
        (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) (hL i)) 1).prod :=
  totalChernCap_eq_prod_of_filtration_of_succ
    (fun M hM ↦ chernCap.{u, v} M 1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
      (goodSpace hX) hM) 1) h8 E hE L hL F hF h0 hr e

end AlgebraicGeometry.Space.PrivateChern

end
