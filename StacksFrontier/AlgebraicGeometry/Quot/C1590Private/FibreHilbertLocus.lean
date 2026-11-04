module

public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.BaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FibreHilbert
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Valuative
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialFiniteDetermination
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional

/-!
# The Hilbert-polynomial loci of a flat family on `ℙⁿ_T`

Let `ℱ` be a module on `ℙⁿ_T` of finite presentation and flat over `T`. For a point `t ∈ T` the
fibrewise Hilbert function `d ↦ χ(ℙⁿ_{κ(t)}, ℱ_t(d))` is a rational polynomial in `d` (Stacks
08AC: its `n`-th backward differences are constant), and it is locally constant in `t` in each
degree (Stacks 0B9T). Hence for each `P ∈ ℚ[t]` the locus `T_P` of the points where it is `P` is
open (`AlgebraicGeometry.C1590Private.isOpen_fibreHilbertLocus`; a Hilbert function is
determined by its values at `0, …, n`), and the loci cover `T`
(`AlgebraicGeometry.C1590Private.exists_mem_fibreHilbertLocus`). The base change of a member `K`
of `Quot_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` along `g : T' ⟶ T` lies in `Quot^P(T')` exactly when `g` lands in
the locus `T_P` of the quotient
(`AlgebraicGeometry.C1590Private.baseChange_mem_hilbertFamilies_iff`). This is the argument of
`AlgebraicGeometry.ProjectiveQuot.isClopen_hilbertLocusSet` for an arbitrary flat family.

## Main definitions

* `AlgebraicGeometry.C1590Private.fibreHilbertLocus`.

## Main results

* `AlgebraicGeometry.C1590Private.isLocallyConstant_fibreHilbert`.
* `AlgebraicGeometry.C1590Private.isOpen_fibreHilbertLocus`.
* `AlgebraicGeometry.C1590Private.exists_mem_fibreHilbertLocus`.
* `AlgebraicGeometry.C1590Private.baseChange_mem_hilbertFamilies_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

namespace AlgebraicGeometry.C1590Private

open ProjectiveQuot

universe u

variable {n : ℕ}

/-- **The fibrewise Hilbert functions of a flat family are locally constant in each degree**
(Stacks 0B9T). -/
theorem isLocallyConstant_fibreHilbert {T : Scheme.{u}} {F : (projectiveSpaceOver n T).Modules}
    [F.IsFinitePresentation] (hF : IsFlatFamily F) (d : ℤ) :
    IsLocallyConstant fun t => fibreHilbert F t d := by
  have := isProper_projectiveSpaceOver n T
  have he : (fun t => fibreHilbert F t d) =
      fibreEulerCharacteristic (projectiveSpaceOver n T ↘ T) (twist d F) := by
    funext t
    have := isCoherent_fibre t F
    exact hilbertPolynomial_fibre_eq_fibreEulerCharacteristic hF t d
  rw [he]
  exact isLocallyConstant_fibreEulerCharacteristic _
    (finitePresentation_projectiveSpaceOver n _) (twist d F) inferInstance
    (isFlatOver_twist _ d _ hF.2)

/-- **The locus `T_P`** of the points of `T` at which the fibrewise Hilbert function of `ℱ` is
`P`. -/
def fibreHilbertLocus (P : Polynomial ℚ) {T : Scheme.{u}} (F : (projectiveSpaceOver n T).Modules)
    [F.IsFinitePresentation] : Set T :=
  {t | ∀ d : ℤ, (fibreHilbert F t d : ℚ) = P.eval (d : ℚ)}

/-- **The Hilbert-polynomial locus of a flat family is open.** -/
theorem isOpen_fibreHilbertLocus (P : Polynomial ℚ) {T : Scheme.{u}}
    {F : (projectiveSpaceOver n T).Modules} [F.IsFinitePresentation] (hF : IsFlatFamily F) :
    IsOpen (fibreHilbertLocus P F) := by
  refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
  refine ⟨⋂ i ∈ Finset.range (n + 1), {y' | fibreHilbert F y' i = fibreHilbert F y i}, ?_, ?_,
    Set.mem_iInter₂.2 fun i _ => rfl⟩
  · intro y' hy' d
    have hfun : fibreHilbert F y' = fibreHilbert F y := by
      have := isCoherent_fibre y F
      have := isCoherent_fibre y' F
      exact hilbertPolynomial_eq_of_forall_le _ _ n _ _ fun i hi =>
        Set.mem_iInter₂.1 hy' i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    rw [hfun]
    exact hy d
  · exact isOpen_biInter_finset fun i _ => (isLocallyConstant_fibreHilbert hF i).isOpen_fiber _

/-- **Every point lies in a Hilbert-polynomial locus** (Stacks 08AC). -/
theorem exists_mem_fibreHilbertLocus {T : Scheme.{u}} (F : (projectiveSpaceOver n T).Modules)
    [F.IsFinitePresentation] (t : T) : ∃ P : Polynomial ℚ, t ∈ fibreHilbertLocus P F := by
  have := isCoherent_fibre t F
  exact exists_polynomial_eval_eq_hilbertPolynomial _ n _

/-- **The base change of a member of `Quot(T)` lies in `Quot^P(T')` exactly when the morphism
lands in the Hilbert-polynomial locus of `P`.** -/
theorem baseChange_mem_hilbertFamilies_iff {r : ℕ} (P : Polynomial ℚ) {T' T : Scheme.{u}}
    (g : T' ⟶ T) {K : Subobject (freeModule n r T)} (hK : K ∈ families n r T) :
    haveI := hK.1
    baseChange g K ∈ hilbertFamilies n r P T' ↔
      Set.range g ⊆ fibreHilbertLocus P (quotient K) := by
  have := hK.1
  have hK' := baseChange_mem_families g hK
  have := hK'.1
  have : ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj
      (quotient K)).IsFinitePresentation :=
    Stacks.Modules.isFinitePresentation_pullback _ _ hK.1
  have hfib : ∀ t', fibreHilbert (quotient (baseChange g K)) t' =
      fibreHilbert (quotient K) (g t') :=
    fun t' => (fibreHilbert_eq_of_iso (quotientBaseChangeIso g K) t').trans
      (fibreHilbert_pullback g (quotient K) t')
  rw [mem_hilbertFamilies_iff, hasFibreHilbertPolynomial_iff]
  constructor
  · rintro ⟨-, h⟩ _ ⟨t', rfl⟩ d
    rw [← hfib t']
    exact h t' d
  · intro h
    refine ⟨hK', fun t' d => ?_⟩
    rw [hfib t']
    exact h ⟨t', rfl⟩ d

end AlgebraicGeometry.C1590Private

end
